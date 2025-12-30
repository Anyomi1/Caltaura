import os
import json
import sqlite3
import traceback
from datetime import datetime, timezone

from flask import Flask, request, redirect, url_for, render_template, render_template_string
from flask_login import LoginManager, UserMixin, login_user, login_required, logout_user, current_user
from werkzeug.security import generate_password_hash, check_password_hash

from twilio.twiml.voice_response import VoiceResponse, Gather
from twilio.rest import Client as TwilioClient

try:
    from openai import OpenAI
except Exception:
    OpenAI = None


# =========================================================
# Config (Render env vars)
# =========================================================
APP_NAME = os.getenv("APP_NAME", "Caltora BizBot")
DB_PATH = os.getenv("DB_PATH", "database.db")
SECRET_KEY = os.getenv("SECRET_KEY", "dev-secret-key-change-me")

PUBLIC_BASE_URL = os.getenv("PUBLIC_BASE_URL", "https://caltora.onrender.com")
OPENAI_MODEL = os.getenv("OPENAI_MODEL", "gpt-4.1-mini")

TWILIO_ACCOUNT_SID = os.getenv("TWILIO_ACCOUNT_SID", "")
TWILIO_AUTH_TOKEN = os.getenv("TWILIO_AUTH_TOKEN", "")

# Safety switch: keep provisioning OFF until you’re ready
ALLOW_PROVISIONING = os.getenv("ALLOW_PROVISIONING", "0") == "1"

# Beta constraints to protect you
DEFAULT_COUNTRY = os.getenv("DEFAULT_COUNTRY", "US")
MAX_NUMBERS_PER_ACCOUNT = int(os.getenv("MAX_NUMBERS_PER_ACCOUNT", "1"))


# =========================================================
# App
# =========================================================
app = Flask(__name__)
app.secret_key = SECRET_KEY

login_manager = LoginManager()
login_manager.init_app(app)
login_manager.login_view = "login"

openai_client = None
if OpenAI is not None and os.getenv("OPENAI_API_KEY"):
    try:
        openai_client = OpenAI()
    except Exception:
        openai_client = None


# =========================================================
# DB Helpers (safe migrations)
# =========================================================
_DB_READY = False

def utc_now_iso():
    return datetime.now(timezone.utc).isoformat()

def get_db():
    conn = sqlite3.connect(DB_PATH, check_same_thread=False)
    conn.row_factory = sqlite3.Row
    try:
        conn.execute("PRAGMA journal_mode=WAL;")
        conn.execute("PRAGMA synchronous=NORMAL;")
    except Exception:
        pass
    return conn

def table_exists(conn, table: str) -> bool:
    row = conn.execute(
        "SELECT name FROM sqlite_master WHERE type='table' AND name=?",
        (table,),
    ).fetchone()
    return row is not None

def table_columns(conn, table: str) -> set:
    if not table_exists(conn, table):
        return set()
    rows = conn.execute(f"PRAGMA table_info({table})").fetchall()
    return {r["name"] for r in rows}

def ensure_column(conn, table: str, col: str, col_type: str):
    cols = table_columns(conn, table)
    if col not in cols:
        conn.execute(f"ALTER TABLE {table} ADD COLUMN {col} {col_type}")

def init_db():
    conn = get_db()
    cur = conn.cursor()

    # USERS
    cur.execute(
        """
        CREATE TABLE IF NOT EXISTS users (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            username TEXT UNIQUE,
            password_hash TEXT,

            business_name TEXT,
            business_type TEXT,
            timezone TEXT,
            notify_email TEXT,

            greeting TEXT,
            faqs TEXT,
            mode TEXT,
            capture_json TEXT,
            is_onboarded INTEGER,

            bizbot_number TEXT,          -- Twilio number we assign (unique per customer)
            twilio_number_sid TEXT,      -- IncomingPhoneNumber SID
            provision_status TEXT,       -- "none" | "active" | "failed"
            provision_error TEXT,
            provisioned_at_utc TEXT,

            last_voice_utc TEXT,
            created_at_utc TEXT
        )
        """
    )

    # Safe adds
    ensure_column(conn, "users", "username", "TEXT UNIQUE")
    ensure_column(conn, "users", "password_hash", "TEXT")

    ensure_column(conn, "users", "business_name", "TEXT")
    ensure_column(conn, "users", "business_type", "TEXT")
    ensure_column(conn, "users", "timezone", "TEXT")
    ensure_column(conn, "users", "notify_email", "TEXT")

    ensure_column(conn, "users", "greeting", "TEXT")
    ensure_column(conn, "users", "faqs", "TEXT")
    ensure_column(conn, "users", "mode", "TEXT")
    ensure_column(conn, "users", "capture_json", "TEXT")
    ensure_column(conn, "users", "is_onboarded", "INTEGER")

    ensure_column(conn, "users", "bizbot_number", "TEXT")
    ensure_column(conn, "users", "twilio_number_sid", "TEXT")
    ensure_column(conn, "users", "provision_status", "TEXT")
    ensure_column(conn, "users", "provision_error", "TEXT")
    ensure_column(conn, "users", "provisioned_at_utc", "TEXT")

    ensure_column(conn, "users", "last_voice_utc", "TEXT")
    ensure_column(conn, "users", "created_at_utc", "TEXT")

    # CALL LOGS
    cur.execute(
        """
        CREATE TABLE IF NOT EXISTS call_logs (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER,
            call_sid TEXT,
            to_number TEXT,
            from_number TEXT,
            ts_utc TEXT,
            stage TEXT,
            transcript TEXT,
            bot_reply TEXT
        )
        """
    )
    ensure_column(conn, "call_logs", "user_id", "INTEGER")
    ensure_column(conn, "call_logs", "call_sid", "TEXT")
    ensure_column(conn, "call_logs", "to_number", "TEXT")
    ensure_column(conn, "call_logs", "from_number", "TEXT")
    ensure_column(conn, "call_logs", "ts_utc", "TEXT")
    ensure_column(conn, "call_logs", "stage", "TEXT")
    ensure_column(conn, "call_logs", "transcript", "TEXT")
    ensure_column(conn, "call_logs", "bot_reply", "TEXT")

    # CALL SESSIONS (multi-turn)
    cur.execute(
        """
        CREATE TABLE IF NOT EXISTS call_sessions (
            call_sid TEXT PRIMARY KEY,
            user_id INTEGER,
            stage TEXT,
            data_json TEXT,
            created_at_utc TEXT,
            updated_at_utc TEXT
        )
        """
    )
    ensure_column(conn, "call_sessions", "user_id", "INTEGER")
    ensure_column(conn, "call_sessions", "stage", "TEXT")
    ensure_column(conn, "call_sessions", "data_json", "TEXT")
    ensure_column(conn, "call_sessions", "created_at_utc", "TEXT")
    ensure_column(conn, "call_sessions", "updated_at_utc", "TEXT")

    conn.commit()
    conn.close()

def ensure_db_ready():
    global _DB_READY
    if _DB_READY:
        return
    init_db()
    _DB_READY = True

@app.before_request
def _before_any_request():
    ensure_db_ready()


# =========================================================
# Utilities
# =========================================================
def norm_phone(s: str) -> str:
    return (s or "").replace(" ", "").strip()

def safe_json(s: str, default):
    try:
        return json.loads(s) if s else default
    except Exception:
        return default

def template_greeting(business_name: str, business_type: str):
    bn = business_name or "our business"
    bt = (business_type or "").lower()
    if "clinic" in bt or "medical" in bt:
        return f"Thanks for calling {bn}. How can I help?"
    if "salon" in bt or "barber" in bt:
        return f"Thanks for calling {bn}. How can I help you today?"
    if "repair" in bt:
        return f"Thanks for calling {bn}. What can I help you with?"
    return f"Thanks for calling {bn}. How can I help?"

def template_faqs(business_type: str):
    bt = (business_type or "").lower()
    if "clinic" in bt:
        return "Hours:\nLocation:\nServices:\nBooking:\nPricing policy:\n"
    if "salon" in bt:
        return "Hours:\nLocation:\nServices:\nBooking:\nPricing:\n"
    if "repair" in bt:
        return "Hours:\nLocation:\nServices:\nDrop-off/Pickup:\nPricing:\n"
    return "Hours:\nLocation:\nServices:\nBooking:\nPricing:\n"


# =========================================================
# Twilio
# =========================================================
def twilio_client():
    if not TWILIO_ACCOUNT_SID or not TWILIO_AUTH_TOKEN:
        raise RuntimeError("Missing TWILIO_ACCOUNT_SID / TWILIO_AUTH_TOKEN")
    return TwilioClient(TWILIO_ACCOUNT_SID, TWILIO_AUTH_TOKEN)

def can_provision_for_user(user_row):
    # Hard guardrails
    if not ALLOW_PROVISIONING:
        return (False, "Provisioning is disabled on the server (ALLOW_PROVISIONING=0).")
    # Limit: 1 number per customer by default
    if user_row["bizbot_number"]:
        return (False, "You already have an active BizBot number.")
    return (True, "")


# =========================================================
# Call session + logging
# =========================================================
def get_or_create_session(call_sid: str, user_id: int):
    conn = get_db()
    row = conn.execute("SELECT * FROM call_sessions WHERE call_sid=?", (call_sid,)).fetchone()
    if row:
        conn.close()
        return row
    now = utc_now_iso()
    conn.execute(
        """
        INSERT INTO call_sessions (call_sid, user_id, stage, data_json, created_at_utc, updated_at_utc)
        VALUES (?, ?, ?, ?, ?, ?)
        """,
        (call_sid, user_id, "root", json.dumps({}), now, now),
    )
    conn.commit()
    row2 = conn.execute("SELECT * FROM call_sessions WHERE call_sid=?", (call_sid,)).fetchone()
    conn.close()
    return row2

def update_session(call_sid: str, stage: str = None, data: dict = None):
    conn = get_db()
    row = conn.execute("SELECT * FROM call_sessions WHERE call_sid=?", (call_sid,)).fetchone()
    if not row:
        conn.close()
        return
    existing = safe_json(row["data_json"], {})
    if data:
        existing.update(data)
    new_stage = stage if stage is not None else row["stage"]
    conn.execute(
        """
        UPDATE call_sessions
        SET stage=?, data_json=?, updated_at_utc=?
        WHERE call_sid=?
        """,
        (new_stage, json.dumps(existing), utc_now_iso(), call_sid),
    )
    conn.commit()
    conn.close()

def log_call(user_id: int, call_sid: str, to_number: str, from_number: str, stage: str, transcript: str, bot_reply: str):
    conn = get_db()
    conn.execute(
        """
        INSERT INTO call_logs (user_id, call_sid, to_number, from_number, ts_utc, stage, transcript, bot_reply)
        VALUES (?, ?, ?, ?, ?, ?, ?, ?)
        """,
        (user_id, call_sid, to_number, from_number, utc_now_iso(), stage, transcript, bot_reply),
    )
    conn.commit()
    conn.close()


# =========================================================
# AI (optional)
# =========================================================
def ai_reply(business_name: str, faqs: str, caller_text: str):
    if openai_client is None:
        return "Thanks. I can take a message—what’s your name and callback number?"
    developer_rules = f"""
You are BizBot, a phone receptionist for {business_name}.
Rules:
- Max 2 sentences.
- If unsure: ask one question or take a message.
- Use FAQ if relevant. Do not invent facts.
- Never mention AI/OpenAI.
"""
    user_msg = f"FAQ:\n{faqs}\n\nCaller said:\n{caller_text}\n\nWrite ONLY the next receptionist line."
    try:
        r = openai_client.responses.create(
            model=OPENAI_MODEL,
            input=[
                {"role": "developer", "content": developer_rules},
                {"role": "user", "content": user_msg},
            ],
        )
        out = (r.output_text or "").strip()
        return out or "Sorry—I didn’t catch that. What’s your name and callback number?"
    except Exception:
        return "Sorry—there was a problem. Please leave your name and callback number."


# =========================================================
# Auth
# =========================================================
class User(UserMixin):
    def __init__(self, user_id, username):
        self.id = user_id
        self.username = username

@login_manager.user_loader
def load_user(user_id):
    conn = get_db()
    row = conn.execute("SELECT id, username FROM users WHERE id=?", (user_id,)).fetchone()
    conn.close()
    if row:
        return User(row["id"], row["username"])
    return None


# =========================================================
# Errors
# =========================================================
@app.errorhandler(500)
def _err_500(e):
    print("=== 500 ===")
    traceback.print_exc()
    return "Internal Server Error (check Render logs)", 500


# =========================================================
# Landing
# =========================================================
@app.route("/")
def home():
    # Uses your templates/landing.html if present
    try:
        return render_template("landing.html")
    except Exception:
        return render_template_string(
            "<h1>{{name}}</h1><p><a href='/register'>Get started</a></p>",
            name=APP_NAME,
        )


# =========================================================
# Register/Login
# =========================================================
@app.route("/register", methods=["GET", "POST"])
def register():
    if request.method == "POST":
        username = (request.form.get("username") or "").strip()
        password = request.form.get("password") or ""
        if not username or not password:
            return "Username and password required", 400

        conn = get_db()
        try:
            conn.execute(
                """
                INSERT INTO users (username, password_hash, mode, capture_json, is_onboarded, provision_status, created_at_utc)
                VALUES (?, ?, ?, ?, ?, ?, ?)
                """,
                (
                    username,
                    generate_password_hash(password),
                    "message",
                    json.dumps({"collect_reason": True, "collect_name": True, "collect_callback": True, "collect_preferred_time": True}),
                    0,
                    "none",
                    utc_now_iso()
                ),
            )
            conn.commit()
        except sqlite3.IntegrityError:
            conn.close()
            return "Username already exists", 400
        conn.close()
        return redirect(url_for("login"))

    return render_template_string(
        """
        <h2>Create account</h2>
        <form method="post">
          Username<br><input name="username"><br><br>
          Password<br><input name="password" type="password"><br><br>
          <button type="submit">Continue</button>
        </form>
        <p><a href="/login">Login</a></p>
        """
    )

@app.route("/login", methods=["GET", "POST"])
def login():
    if request.method == "POST":
        username = (request.form.get("username") or "").strip()
        password = request.form.get("password") or ""
        conn = get_db()
        row = conn.execute("SELECT * FROM users WHERE username=?", (username,)).fetchone()
        conn.close()
        if row and check_password_hash(row["password_hash"], password):
            login_user(User(row["id"], row["username"]))
            if (row["is_onboarded"] or 0) == 0:
                return redirect(url_for("onboarding"))
            return redirect(url_for("dashboard"))
        return "Invalid credentials", 401

    return render_template_string(
        """
        <h2>Login</h2>
        <form method="post">
          Username<br><input name="username"><br><br>
          Password<br><input name="password" type="password"><br><br>
          <button type="submit">Login</button>
        </form>
        <p><a href="/register">Create account</a></p>
        """
    )

@app.route("/logout")
@login_required
def logout():
    logout_user()
    return redirect(url_for("login"))


# =========================================================
# Onboarding (simple, then they can provision number)
# =========================================================
@app.route("/onboarding", methods=["GET", "POST"])
@login_required
def onboarding():
    conn = get_db()
    user = conn.execute("SELECT * FROM users WHERE id=?", (current_user.id,)).fetchone()
    conn.close()

    if request.method == "POST":
        business_name = (request.form.get("business_name") or "").strip()
        business_type = (request.form.get("business_type") or "").strip()
        timezone_val = (request.form.get("timezone") or "").strip()
        notify_email = (request.form.get("notify_email") or "").strip()

        greeting = template_greeting(business_name, business_type)
        faqs = template_faqs(business_type)

        conn = get_db()
        conn.execute(
            """
            UPDATE users
            SET business_name=?, business_type=?, timezone=?, notify_email=?, greeting=?, faqs=?, is_onboarded=?
            WHERE id=?
            """,
            (business_name, business_type, timezone_val, notify_email, greeting, faqs, 1, current_user.id),
        )
        conn.commit()
        conn.close()
        return redirect(url_for("dashboard"))

    return render_template_string(
        """
        <h2>Quick setup</h2>
        <form method="post">
          Business name<br><input name="business_name" style="width:360px;"><br><br>
          Business type<br>
          <select name="business_type">
            <option>Clinic</option>
            <option>Salon</option>
            <option>Repair Shop</option>
            <option>Consultant</option>
            <option>Other</option>
          </select><br><br>
          Timezone<br>
          <select name="timezone">
            <option value="Asia/Riyadh">Asia/Riyadh</option>
            <option value="UTC">UTC</option>
            <option value="America/New_York">America/New_York</option>
            <option value="Europe/London">Europe/London</option>
          </select><br><br>
          Notification email (optional)<br><input name="notify_email" style="width:360px;"><br><br>
          <button type="submit">Finish</button>
        </form>
        """,
        user=user
    )


# =========================================================
# Dashboard + “Activate BizBot Number”
# =========================================================
@app.route("/dashboard")
@login_required
def dashboard():
    conn = get_db()
    user = conn.execute("SELECT * FROM users WHERE id=?", (current_user.id,)).fetchone()
    logs = conn.execute(
        """
        SELECT ts_utc, from_number, to_number, transcript, bot_reply
        FROM call_logs WHERE user_id=?
        ORDER BY id DESC LIMIT 25
        """,
        (current_user.id,),
    ).fetchall()
    conn.close()

    if not user:
        return redirect(url_for("logout"))

    connected = bool(user["last_voice_utc"])
    webhook_voice = f"{PUBLIC_BASE_URL}/voice"
    provisioning_enabled = "YES" if ALLOW_PROVISIONING else "NO"

    return render_template_string(
        """
        <h2>Dashboard</h2>
        <p>Logged in as <b>{{u.username}}</b> | <a href="/logout">Logout</a></p>

        <h3>Status</h3>
        {% if u.bizbot_number %}
          <p><b>Your BizBot Number:</b> {{u.bizbot_number}}</p>
          {% if connected %}
            <p>✅ Receiving calls. Last webhook: {{u.last_voice_utc}}</p>
          {% else %}
            <p>⏳ Number active. Waiting for first call…</p>
          {% endif %}
        {% else %}
          <p>❌ No BizBot number yet.</p>
        {% endif %}

        <h3>One-click setup (Twilio inside Caltora)</h3>
        <p><b>Provisioning enabled on server:</b> {{provisioning_enabled}}</p>
        {% if not u.bizbot_number %}
          <form method="post" action="/provision-number">
            Country (beta recommended: US)<br>
            <input name="country" value="US" style="width:120px;"><br><br>
            Area code (optional, US only)<br>
            <input name="area_code" placeholder="e.g., 212" style="width:120px;"><br><br>
            <button type="submit">Activate BizBot Number</button>
          </form>
          {% if u.provision_status == "failed" %}
            <p style="color:#b00;"><b>Provision failed:</b> {{u.provision_error}}</p>
          {% endif %}
        {% endif %}

        <h3>Call handling mode</h3>
        <p><b>Mode:</b> {{u.mode}} (message mode is safest for beta)</p>

        <h3>Recent calls</h3>
        {% if logs %}
          {% for r in logs %}
            <div style="border:1px solid #ddd; padding:10px; margin:10px 0;">
              <div><b>Time:</b> {{r.ts_utc}}</div>
              <div><b>From:</b> {{r.from_number}} <b>To:</b> {{r.to_number}}</div>
              <div><b>Caller:</b> {{r.transcript}}</div>
              <div><b>BizBot:</b> {{r.bot_reply}}</div>
            </div>
          {% endfor %}
        {% else %}
          <p>No calls logged yet.</p>
        {% endif %}
        """,
        u=user,
        logs=logs,
        connected=connected,
        webhook_voice=webhook_voice,
        provisioning_enabled=provisioning_enabled
    )


@app.route("/provision-number", methods=["POST"])
@login_required
def provision_number():
    conn = get_db()
    user = conn.execute("SELECT * FROM users WHERE id=?", (current_user.id,)).fetchone()

    ok, reason = can_provision_for_user(user)
    if not ok:
        conn.execute(
            "UPDATE users SET provision_status=?, provision_error=? WHERE id=?",
            ("failed", reason, current_user.id)
        )
        conn.commit()
        conn.close()
        return redirect(url_for("dashboard"))

    country = (request.form.get("country") or DEFAULT_COUNTRY).strip().upper()
    area_code = (request.form.get("area_code") or "").strip()

    try:
        client = twilio_client()

        # Find available numbers (beta: start with US)
        available = None
        if country == "US" and area_code:
            available = client.available_phone_numbers("US").local.list(area_code=area_code, limit=1)
        else:
            available = client.available_phone_numbers(country).local.list(limit=1)

        if not available:
            raise RuntimeError("No numbers available for that selection.")

        phone_number = available[0].phone_number

        # Buy number
        incoming = client.incoming_phone_numbers.create(
            phone_number=phone_number,
            friendly_name=f"Caltora BizBot user {current_user.id}",
        )

        # Configure webhook
        client.incoming_phone_numbers(incoming.sid).update(
            voice_url=f"{PUBLIC_BASE_URL}/voice",
            voice_method="POST",
            status_callback=f"{PUBLIC_BASE_URL}/status",
            status_callback_method="POST",
        )

        conn.execute(
            """
            UPDATE users
            SET bizbot_number=?, twilio_number_sid=?, provision_status=?, provision_error=?, provisioned_at_utc=?
            WHERE id=?
            """,
            (phone_number, incoming.sid, "active", "", utc_now_iso(), current_user.id)
        )
        conn.commit()
        conn.close()
        return redirect(url_for("dashboard"))

    except Exception as e:
        err = str(e)
        conn.execute(
            "UPDATE users SET provision_status=?, provision_error=? WHERE id=?",
            ("failed", err, current_user.id)
        )
        conn.commit()
        conn.close()
        print("Provision error:", err)
        traceback.print_exc()
        return redirect(url_for("dashboard"))


# =========================================================
# Tenant resolution by To number (bizbot_number)
# =========================================================
def find_user_by_to_number(to_number: str):
    to_number = norm_phone(to_number)
    conn = get_db()
    row = conn.execute(
        """
        SELECT * FROM users
        WHERE REPLACE(bizbot_number,' ','') = REPLACE(?, ' ', '')
        LIMIT 1
        """,
        (to_number,),
    ).fetchone()
    conn.close()
    return row


# =========================================================
# Twilio webhooks
# =========================================================
@app.route("/voice", methods=["GET", "POST"])
def voice():
    call_sid = request.values.get("CallSid", "")
    from_number = request.values.get("From", "")
    to_number = request.values.get("To", "")

    user = find_user_by_to_number(to_number)

    vr = VoiceResponse()

    if not user:
        vr.say("This number is not linked to a business yet. Please call back later.")
        vr.hangup()
        return str(vr)

    # mark connected
    conn = get_db()
    conn.execute("UPDATE users SET last_voice_utc=? WHERE id=?", (utc_now_iso(), user["id"]))
    conn.commit()
    conn.close()

    get_or_create_session(call_sid, user["id"])

    greeting = user["greeting"] or template_greeting(user["business_name"], user["business_type"])
    vr.say(greeting)

    gather = Gather(input="speech", action="/handle-input", method="POST", speechTimeout="auto", timeout=7)
    gather.say("Please tell me what you need.")
    vr.append(gather)

    vr.say("Sorry, I didn’t catch that. Goodbye.")
    vr.hangup()
    return str(vr)


@app.route("/handle-input", methods=["POST"])
def handle_input():
    call_sid = request.values.get("CallSid", "")
    from_number = request.values.get("From", "")
    to_number = request.values.get("To", "")
    speech = (request.values.get("SpeechResult") or "").strip()

    user = find_user_by_to_number(to_number)
    vr = VoiceResponse()

    if not user:
        vr.say("This number is not linked to a business yet.")
        vr.hangup()
        return str(vr)

    sess = get_or_create_session(call_sid, user["id"])
    stage = sess["stage"] or "root"
    data = safe_json(sess["data_json"], {})
    capture = safe_json(user["capture_json"], {"collect_reason": True, "collect_name": True, "collect_callback": True, "collect_preferred_time": True})

    # Default: message capture mode (stable beta)
    mode = (user["mode"] or "message").strip().lower()
    if mode == "message":
        if stage == "root":
            data["reason"] = speech
            update_session(call_sid, "ask_name", data)
            bot = "Thanks. What’s your name?"
            log_call(user["id"], call_sid, to_number, from_number, stage, speech, bot)
            vr.say(bot)

        elif stage == "ask_name":
            data["name"] = speech
            update_session(call_sid, "ask_callback", data)
            bot = "Thanks. What’s the best callback number?"
            log_call(user["id"], call_sid, to_number, from_number, stage, speech, bot)
            vr.say(bot)

        elif stage == "ask_callback":
            data["callback"] = speech
            if capture.get("collect_preferred_time", True):
                update_session(call_sid, "ask_time", data)
                bot = "Got it. What’s a good time to call you back?"
                log_call(user["id"], call_sid, to_number, from_number, stage, speech, bot)
                vr.say(bot)
            else:
                update_session(call_sid, "done", data)
                bot = "Perfect. We’ll get back to you soon. Goodbye."
                log_call(user["id"], call_sid, to_number, from_number, stage, speech, bot)
                vr.say(bot)
                vr.hangup()
                return str(vr)

        elif stage == "ask_time":
            data["preferred_time"] = speech
            update_session(call_sid, "done", data)
            bot = "Perfect. We’ll get back to you soon. Goodbye."
            log_call(user["id"], call_sid, to_number, from_number, stage, speech, bot)
            vr.say(bot)
            vr.hangup()
            return str(vr)

        else:
            bot = "Thanks for calling. Goodbye."
            log_call(user["id"], call_sid, to_number, from_number, stage, speech, bot)
            vr.say(bot)
            vr.hangup()
            return str(vr)

        gather = Gather(input="speech", action="/handle-input", method="POST", speechTimeout="auto", timeout=7)
        gather.say("Please respond after the tone.")
        vr.append(gather)
        vr.say("Goodbye.")
        return str(vr)

    # AI Mode (optional)
    bot = ai_reply(user["business_name"] or APP_NAME, user["faqs"] or "", speech)
    log_call(user["id"], call_sid, to_number, from_number, stage, speech, bot)
    vr.say(bot)

    gather = Gather(input="speech", action="/handle-input", method="POST", speechTimeout="auto", timeout=7)
    gather.say("Anything else?")
    vr.append(gather)

    vr.say("Goodbye.")
    vr.hangup()
    return str(vr)


@app.route("/status", methods=["POST"])
def status():
    # Helpful for debugging in Render logs
    call_sid = request.values.get("CallSid", "")
    call_status = request.values.get("CallStatus", "")
    to_number = request.values.get("To", "")
    from_number = request.values.get("From", "")
    print(f"[Twilio Status] CallSid={call_sid} Status={call_status} To={to_number} From={from_number}")
    return ("", 204)


if __name__ == "__main__":
    init_db()
    app.run(debug=True)
