"""
CALTAURA BizBot (Single-file Flask app) - app.py
================================================
Goal of this version:
- You can copy/paste this as app.py and run it.
- A test customer can self-serve:
  1) Create account
  2) Complete onboarding wizard
  3) Purchase subscription via Stripe Checkout (no assistance)
  4) After payment, dashboard unlocks and Twilio webhooks work for their number

Key improvements vs your current file:
- Stripe subscription checkout + customer portal + webhooks (self-serve purchase)
- Twilio signature validation URL correctness (querystring + absolute URLs)
- SMS opt-out persistence (STOP blocks future followups/jobs)
- Voice callback capture uses DTMF digits (reliable)
- Minimal built-in UI using render_template_string (no external templates required)
- Basic “subscription required” gating for app features (except health/public pages)

IMPORTANT:
- This uses SQLite for simplicity; for production, move to Postgres on Render.
- You MUST set environment variables for Stripe + Twilio for full functionality.
- You MUST configure Stripe webhook endpoint + a Stripe Price ID.

Environment variables (Render-friendly):
Core:
- SECRET_KEY (required in production)
- DB_PATH (default database.db)
- PUBLIC_BASE_URL (IMPORTANT for Twilio signature validation; e.g. https://app.caltaura.com)
- APP_NAME (default CALTAURA)

Twilio:
- TWILIO_ACCOUNT_SID
- TWILIO_AUTH_TOKEN
- TWILIO_WEBHOOK_AUTH_TOKEN (optional override; if empty, uses TWILIO_AUTH_TOKEN)
- TWILIO_MESSAGING_SERVICE_SID (optional)

OpenAI (optional):
- OPENAI_API_KEY
- OPENAI_MODEL (default gpt-4.1-mini)

SendGrid (optional):
- SENDGRID_API_KEY
- FROM_EMAIL

Jobs:
- JOBS_SHARED_SECRET (protect /jobs/tick?key=...)

Stripe (REQUIRED for self-serve purchase):
- STRIPE_SECRET_KEY
- STRIPE_WEBHOOK_SECRET
- STRIPE_PRICE_ID (default plan price; you can add more later)
- STRIPE_SUCCESS_URL (optional; default {PUBLIC_BASE_URL}/billing/success)
- STRIPE_CANCEL_URL (optional; default {PUBLIC_BASE_URL}/billing/cancel)
"""

import os
import re
import json
import hmac
import time
import sqlite3
import traceback
from datetime import datetime, timezone, timedelta
from typing import Optional, Dict, Any, List, Tuple

from flask import (
    Flask,
    request,
    redirect,
    url_for,
    abort,
    make_response,
    jsonify,
    render_template_string,
    session,
)
from flask_login import (
    LoginManager,
    UserMixin,
    login_user,
    login_required,
    logout_user,
    current_user,
)
from werkzeug.security import generate_password_hash, check_password_hash

from twilio.twiml.voice_response import VoiceResponse, Gather
from twilio.rest import Client as TwilioClient
from twilio.request_validator import RequestValidator

try:
    from openai import OpenAI
except Exception:
    OpenAI = None

try:
    from sendgrid import SendGridAPIClient
    from sendgrid.helpers.mail import Mail
except Exception:
    SendGridAPIClient = None
    Mail = None

try:
    import stripe
except Exception:
    stripe = None


# =========================================================
# CONFIG
# =========================================================
APP_NAME = os.getenv("APP_NAME", "CALTAURA")
DB_PATH = os.getenv("DB_PATH", "database.db")
SECRET_KEY = os.getenv("SECRET_KEY", "dev-secret-key-change-me")

PUBLIC_BASE_URL = (os.getenv("PUBLIC_BASE_URL", "").strip() or "").rstrip("/")
OPENAI_MODEL = os.getenv("OPENAI_MODEL", "gpt-4.1-mini")

TWILIO_ACCOUNT_SID = os.getenv("TWILIO_ACCOUNT_SID", "")
TWILIO_AUTH_TOKEN = os.getenv("TWILIO_AUTH_TOKEN", "")
TWILIO_WEBHOOK_AUTH_TOKEN = os.getenv("TWILIO_WEBHOOK_AUTH_TOKEN", "")
TWILIO_MESSAGING_SERVICE_SID = os.getenv("TWILIO_MESSAGING_SERVICE_SID", "")

SENDGRID_API_KEY = os.getenv("SENDGRID_API_KEY", "")
FROM_EMAIL = os.getenv("FROM_EMAIL", f"no-reply@{(os.getenv('MAIL_DOMAIN','caltaura.com') or 'caltaura.com')}")

JOBS_SHARED_SECRET = os.getenv("JOBS_SHARED_SECRET", "")

MAX_CALL_STEPS = int(os.getenv("MAX_CALL_STEPS", "10"))
MISSED_CALL_SMS_ENABLED = os.getenv("MISSED_CALL_SMS_ENABLED", "1") == "1"
MISSED_CALL_FOLLOWUP_MINUTES = int(os.getenv("MISSED_CALL_FOLLOWUP_MINUTES", "25"))
MISSED_CALL_FOLLOWUP2_MINUTES = int(os.getenv("MISSED_CALL_FOLLOWUP2_MINUTES", "180"))

# Basic anti-abuse for website assistant endpoint (in-memory, per-process)
ASSISTANT_RL_WINDOW_SECONDS = int(os.getenv("ASSISTANT_RL_WINDOW_SECONDS", "60"))
ASSISTANT_RL_MAX_PER_WINDOW = int(os.getenv("ASSISTANT_RL_MAX_PER_WINDOW", "20"))

# Stripe
STRIPE_SECRET_KEY = os.getenv("STRIPE_SECRET_KEY", "")
STRIPE_WEBHOOK_SECRET = os.getenv("STRIPE_WEBHOOK_SECRET", "")
STRIPE_PRICE_ID = os.getenv("STRIPE_PRICE_ID", "")  # required for checkout
STRIPE_SUCCESS_URL = os.getenv("STRIPE_SUCCESS_URL", "")  # optional override
STRIPE_CANCEL_URL = os.getenv("STRIPE_CANCEL_URL", "")    # optional override


# =========================================================
# APP INIT
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

if stripe is not None and STRIPE_SECRET_KEY:
    stripe.api_key = STRIPE_SECRET_KEY


# =========================================================
# TIME / UTILS
# =========================================================
def utc_now() -> datetime:
    return datetime.now(timezone.utc)


def utc_now_iso() -> str:
    return utc_now().isoformat()


def now_plus_minutes(m: int) -> str:
    return (utc_now() + timedelta(minutes=m)).isoformat()


def short(s: str, n: int = 280) -> str:
    s = (s or "").strip()
    return s if len(s) <= n else (s[:n] + "…")


def safe_json(s: str, default):
    try:
        return json.loads(s) if s else default
    except Exception:
        return default


def norm_phone(s: str) -> str:
    s = (s or "").strip()
    s = re.sub(r"\s+", "", s)
    return s


def normalize_bool_checkbox(v: Optional[str]) -> int:
    return 1 if (v == "on" or v == "1" or v is True) else 0


def require_base_url() -> str:
    """
    Base URL used for generating absolute links and Twilio signature validation.
    In production behind Render, you MUST set PUBLIC_BASE_URL (recommended).
    """
    if PUBLIC_BASE_URL:
        return PUBLIC_BASE_URL.rstrip("/")

    proto = request.headers.get("X-Forwarded-Proto", request.scheme)
    host = request.headers.get("X-Forwarded-Host", request.host)
    return f"{proto}://{host}".rstrip("/")


def get_client_ip() -> str:
    fwd = request.headers.get("X-Forwarded-For", "")
    if fwd:
        return fwd.split(",")[0].strip()
    return request.remote_addr or "unknown"


# =========================================================
# DB HELPERS + MIGRATIONS (simple)
# =========================================================
_DB_READY = False


def get_db() -> sqlite3.Connection:
    conn = sqlite3.connect(DB_PATH, check_same_thread=False)
    conn.row_factory = sqlite3.Row
    try:
        conn.execute("PRAGMA journal_mode=WAL;")
        conn.execute("PRAGMA synchronous=NORMAL;")
    except Exception:
        pass
    return conn


def table_exists(conn: sqlite3.Connection, table: str) -> bool:
    row = conn.execute(
        "SELECT name FROM sqlite_master WHERE type='table' AND name=?",
        (table,),
    ).fetchone()
    return row is not None


def table_columns(conn: sqlite3.Connection, table: str) -> set:
    if not table_exists(conn, table):
        return set()
    rows = conn.execute(f"PRAGMA table_info({table})").fetchall()
    return {r["name"] for r in rows}


def ensure_column(conn: sqlite3.Connection, table: str, col: str, col_type: str) -> None:
    cols = table_columns(conn, table)
    if col not in cols:
        conn.execute(f"ALTER TABLE {table} ADD COLUMN {col} {col_type}")


def init_db() -> None:
    conn = get_db()
    cur = conn.cursor()

    # USERS (tenants)
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
            booking_link TEXT,

            after_hours_enabled INTEGER,
            after_hours_message TEXT,
            greeting TEXT,
            escalation_keywords TEXT,

            mode TEXT,                  -- "message" or "ai"
            capture_json TEXT,          -- intake fields json
            is_onboarded INTEGER,

            bizbot_number TEXT,         -- Twilio number connected to this tenant (E.164)
            twilio_number_sid TEXT,

            -- Billing (Stripe)
            billing_status TEXT,         -- none|pending|active|trialing|past_due|canceled
            stripe_customer_id TEXT,
            stripe_subscription_id TEXT,
            stripe_price_id TEXT,
            paid_since_utc TEXT,

            created_at_utc TEXT
        )
        """
    )

    # leads
    cur.execute(
        """
        CREATE TABLE IF NOT EXISTS leads (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER,
            status TEXT,
            source TEXT,                 -- call|sms|web|email
            name TEXT,
            phone TEXT,
            email TEXT,
            service_needed TEXT,
            preferred_time TEXT,
            urgency TEXT,
            notes TEXT,
            tags TEXT,
            assigned_to TEXT,
            opted_out INTEGER,
            last_inbound_utc TEXT,
            last_outbound_utc TEXT,
            created_at_utc TEXT,
            updated_at_utc TEXT
        )
        """
    )

    # interactions (unified inbox)
    cur.execute(
        """
        CREATE TABLE IF NOT EXISTS interactions (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER,
            lead_id INTEGER,
            channel TEXT,               -- call|sms|web|email|system
            direction TEXT,             -- inbound|outbound|internal
            external_id TEXT,           -- callSid / messageSid
            content TEXT,
            meta_json TEXT,
            ts_utc TEXT
        )
        """
    )

    # call sessions (multi-turn capture)
    cur.execute(
        """
        CREATE TABLE IF NOT EXISTS call_sessions (
            call_sid TEXT PRIMARY KEY,
            user_id INTEGER,
            lead_id INTEGER,
            stage TEXT,
            step_count INTEGER,
            data_json TEXT,
            flags_json TEXT,
            created_at_utc TEXT,
            updated_at_utc TEXT
        )
        """
    )

    # knowledge base items
    cur.execute(
        """
        CREATE TABLE IF NOT EXISTS kb_items (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER,
            title TEXT,
            content TEXT,
            created_at_utc TEXT
        )
        """
    )

    # playbooks
    cur.execute(
        """
        CREATE TABLE IF NOT EXISTS playbooks (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER,
            vertical TEXT,
            config_json TEXT,
            created_at_utc TEXT
        )
        """
    )

    # jobs (background follow-ups)
    cur.execute(
        """
        CREATE TABLE IF NOT EXISTS jobs (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER,
            lead_id INTEGER,
            job_type TEXT,               -- sms_followup|email_notify|system
            run_at_utc TEXT,
            payload_json TEXT,
            status TEXT,                 -- queued|done|failed
            attempts INTEGER,
            last_error TEXT,
            created_at_utc TEXT,
            updated_at_utc TEXT
        )
        """
    )

    conn.commit()
    conn.close()


def migrate_db() -> None:
    """
    Adds missing columns for older DBs.
    """
    conn = get_db()

    # Users migrations
    if table_exists(conn, "users"):
        ensure_column(conn, "users", "username", "TEXT")
        ensure_column(conn, "users", "password_hash", "TEXT")
        ensure_column(conn, "users", "business_name", "TEXT")
        ensure_column(conn, "users", "business_type", "TEXT")
        ensure_column(conn, "users", "timezone", "TEXT")
        ensure_column(conn, "users", "notify_email", "TEXT")
        ensure_column(conn, "users", "booking_link", "TEXT")
        ensure_column(conn, "users", "after_hours_enabled", "INTEGER")
        ensure_column(conn, "users", "after_hours_message", "TEXT")
        ensure_column(conn, "users", "greeting", "TEXT")
        ensure_column(conn, "users", "escalation_keywords", "TEXT")
        ensure_column(conn, "users", "mode", "TEXT")
        ensure_column(conn, "users", "capture_json", "TEXT")
        ensure_column(conn, "users", "is_onboarded", "INTEGER")
        ensure_column(conn, "users", "bizbot_number", "TEXT")
        ensure_column(conn, "users", "twilio_number_sid", "TEXT")

        ensure_column(conn, "users", "billing_status", "TEXT")
        ensure_column(conn, "users", "stripe_customer_id", "TEXT")
        ensure_column(conn, "users", "stripe_subscription_id", "TEXT")
        ensure_column(conn, "users", "stripe_price_id", "TEXT")
        ensure_column(conn, "users", "paid_since_utc", "TEXT")

        ensure_column(conn, "users", "created_at_utc", "TEXT")

    # leads migrations
    if table_exists(conn, "leads"):
        ensure_column(conn, "leads", "urgency", "TEXT")
        ensure_column(conn, "leads", "notes", "TEXT")
        ensure_column(conn, "leads", "tags", "TEXT")
        ensure_column(conn, "leads", "assigned_to", "TEXT")
        ensure_column(conn, "leads", "opted_out", "INTEGER")
        ensure_column(conn, "leads", "last_inbound_utc", "TEXT")
        ensure_column(conn, "leads", "last_outbound_utc", "TEXT")
        ensure_column(conn, "leads", "created_at_utc", "TEXT")
        ensure_column(conn, "leads", "updated_at_utc", "TEXT")

    # interactions migrations
    if table_exists(conn, "interactions"):
        ensure_column(conn, "interactions", "meta_json", "TEXT")

    # call_sessions migrations
    if table_exists(conn, "call_sessions"):
        ensure_column(conn, "call_sessions", "flags_json", "TEXT")

    # jobs migrations
    if table_exists(conn, "jobs"):
        ensure_column(conn, "jobs", "attempts", "INTEGER")
        ensure_column(conn, "jobs", "last_error", "TEXT")

    conn.commit()
    conn.close()


def ensure_db_ready() -> None:
    global _DB_READY
    if _DB_READY:
        return
    init_db()
    migrate_db()
    _DB_READY = True


@app.before_request
def _before_any_request():
    ensure_db_ready()


# =========================================================
# DEFAULTS
# =========================================================
def template_greeting(business_name: str, business_type: str) -> str:
    bn = business_name or APP_NAME
    return f"Thanks for calling {bn}. How can I help?"


def default_escalation_keywords() -> str:
    return "emergency,urgent,asap,complaint,refund,lawyer,police,bleeding,heart attack,stolen,fire"


def default_capture_json() -> dict:
    return {
        "collect_reason": True,
        "collect_name": True,
        "collect_callback": True,
        "collect_preferred_time": True,
        "collect_urgency": False,
    }


# =========================================================
# SIMPLE HTML UI (NO external template files needed)
# =========================================================
def html_layout(title: str, body_html: str, *, show_nav: bool = True) -> str:
    base = require_base_url()
    auth = bool(getattr(current_user, "is_authenticated", False))
    nav = ""
    if show_nav:
        nav_items = []
        nav_items.append(f'<a class="nav-link" href="{url_for("home")}">Home</a>')
        nav_items.append(f'<a class="nav-link" href="{url_for("pricing")}">Pricing</a>')
        if auth:
            nav_items.append(f'<a class="nav-link" href="{url_for("dashboard")}">Dashboard</a>')
            nav_items.append(f'<a class="nav-link" href="{url_for("leads")}">Leads</a>')
            nav_items.append(f'<a class="nav-link" href="{url_for("kb")}">KB</a>')
            nav_items.append(f'<a class="nav-link" href="{url_for("playbooks")}">Playbooks</a>')
            nav_items.append(f'<a class="nav-link" href="{url_for("settings")}">Settings</a>')
            nav_items.append(f'<a class="nav-link" href="{url_for("billing")}">Billing</a>')
            nav_items.append(f'<a class="nav-link" href="{url_for("logout")}">Logout</a>')
        else:
            nav_items.append(f'<a class="nav-link" href="{url_for("login")}">Login</a>')
            nav_items.append(f'<a class="nav-link" href="{url_for("register")}">Get started</a>')

        nav = f"""
        <nav class="navbar navbar-expand-lg navbar-dark bg-dark">
          <div class="container-fluid">
            <a class="navbar-brand" href="{url_for("home")}">{APP_NAME}</a>
            <button class="navbar-toggler" type="button" data-bs-toggle="collapse" data-bs-target="#navb">
              <span class="navbar-toggler-icon"></span>
            </button>
            <div class="collapse navbar-collapse" id="navb">
              <div class="navbar-nav">
                {''.join([f'<div class="nav-item">{x}</div>' for x in nav_items])}
              </div>
            </div>
          </div>
        </nav>
        """

    return render_template_string(
        f"""
<!doctype html>
<html>
<head>
  <meta charset="utf-8" />
  <meta name="viewport" content="width=device-width, initial-scale=1" />
  <title>{title} - {APP_NAME}</title>
  <link href="https://cdn.jsdelivr.net/npm/bootstrap@5.3.3/dist/css/bootstrap.min.css" rel="stylesheet">
  <style>
    body {{ background:#0b0f14; color:#e9eef5; }}
    .card {{ background:#111826; border:1px solid #1f2a3a; }}
    .muted {{ color:#9fb0c7; }}
    a {{ color:#9fd3ff; }}
    input, textarea, select {{ background:#0b1220 !important; color:#e9eef5 !important; border:1px solid #22324a !important; }}
    .btn-primary {{ background:#2b7cff; border-color:#2b7cff; }}
    .badge-soft {{ background:#1a2435; border:1px solid #2a3a55; color:#cfe1ff; }}
    code {{ color:#cfe1ff; }}
  </style>
</head>
<body>
  {nav}
  <div class="container py-4" style="max-width: 1040px;">
    {body_html}
    <hr class="mt-4" />
    <p class="muted small">Base URL: <code>{base}</code></p>
  </div>
  <script src="https://cdn.jsdelivr.net/npm/bootstrap@5.3.3/dist/js/bootstrap.bundle.min.js"></script>
</body>
</html>
"""
    )


def flash_once(msg: str, kind: str = "info"):
    session["flash"] = {"msg": msg, "kind": kind, "ts": time.time()}


def consume_flash() -> str:
    f = session.pop("flash", None)
    if not f:
        return ""
    kind = f.get("kind", "info")
    msg = f.get("msg", "")
    cls = {"info": "alert-info", "success": "alert-success", "danger": "alert-danger", "warning": "alert-warning"}.get(kind, "alert-info")
    return f'<div class="alert {cls}">{msg}</div>'


# =========================================================
# BILLING HELPERS
# =========================================================
def billing_is_configured() -> bool:
    return bool(stripe is not None and STRIPE_SECRET_KEY and STRIPE_WEBHOOK_SECRET and STRIPE_PRICE_ID)


def user_billing_status(user_row) -> str:
    return (user_row.get("billing_status") or "none").strip().lower()


def billing_active(user_row) -> bool:
    s = user_billing_status(user_row)
    return s in ("active", "trialing")


def billing_required_guard() -> Optional[Any]:
    """
    Enforce that logged-in users must be onboarded + have active billing to use core app pages.
    """
    if not current_user.is_authenticated:
        return None

    conn = get_db()
    u = conn.execute("SELECT * FROM users WHERE id=?", (int(current_user.id),)).fetchone()
    conn.close()
    if not u:
        logout_user()
        return redirect(url_for("login"))

    if int(u.get("is_onboarded") or 0) == 0 and request.endpoint not in ("onboarding", "logout", "health", "home", "pricing", "login", "register", "billing", "billing_start", "billing_success", "billing_cancel", "stripe_webhook"):
        return redirect(url_for("onboarding"))

    # If Stripe not configured, allow usage (so dev/local works) but show warning
    if not billing_is_configured():
        return None

    # Allow billing routes even if not active
    if request.endpoint in ("billing", "billing_start", "billing_success", "billing_cancel", "stripe_webhook", "logout", "health", "home", "pricing"):
        return None

    if not billing_active(u):
        return redirect(url_for("billing"))

    return None


@app.before_request
def _billing_guard():
    resp = billing_required_guard()
    if resp is not None:
        return resp


# =========================================================
# TWILIO + SECURITY
# =========================================================
def twilio_client() -> TwilioClient:
    if not TWILIO_ACCOUNT_SID or not TWILIO_AUTH_TOKEN:
        raise RuntimeError("Missing TWILIO_ACCOUNT_SID or TWILIO_AUTH_TOKEN.")
    return TwilioClient(TWILIO_ACCOUNT_SID, TWILIO_AUTH_TOKEN)


def twilio_validator() -> RequestValidator:
    token = TWILIO_WEBHOOK_AUTH_TOKEN or TWILIO_AUTH_TOKEN
    return RequestValidator(token)


def twilio_signed_url() -> str:
    base = require_base_url().rstrip("/")
    qs = request.query_string.decode("utf-8") if request.query_string else ""
    if qs:
        return f"{base}{request.path}?{qs}"
    return f"{base}{request.path}"


def validate_twilio_request() -> bool:
    """
    Validates Twilio signature for POST webhooks.
    Twilio uses the full URL of the webhook configured in console.
    You MUST set PUBLIC_BASE_URL correctly in production.
    """
    try:
        sig = request.headers.get("X-Twilio-Signature", "")
        if not sig:
            return False
        url = twilio_signed_url()
        post_vars = request.form.to_dict(flat=True)
        return twilio_validator().validate(url, post_vars, sig)
    except Exception:
        return False


# =========================================================
# LEADS / INBOX HELPERS
# =========================================================
def lead_statuses() -> List[str]:
    return ["new", "qualified", "booked", "won", "lost"]


def find_lead_by_phone(user_id: int, phone: str):
    phone = norm_phone(phone)
    if not phone:
        return None
    conn = get_db()
    row = conn.execute(
        "SELECT * FROM leads WHERE user_id=? AND REPLACE(phone,' ','')=REPLACE(?,' ','') ORDER BY id DESC LIMIT 1",
        (user_id, phone),
    ).fetchone()
    conn.close()
    return row


def create_lead(user_id: int, source: str, phone: str = "", name: str = "", email: str = ""):
    now = utc_now_iso()
    conn = get_db()
    conn.execute(
        """
        INSERT INTO leads (
            user_id, status, source, name, phone, email,
            opted_out, created_at_utc, updated_at_utc, last_inbound_utc
        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """,
        (user_id, "new", source, name, phone, email, 0, now, now, now),
    )
    conn.commit()
    row = conn.execute(
        "SELECT * FROM leads WHERE user_id=? ORDER BY id DESC LIMIT 1",
        (user_id,),
    ).fetchone()
    conn.close()
    return row


def update_lead(lead_id: int, **fields):
    if not fields:
        return
    conn = get_db()
    sets = []
    vals = []
    for k, v in fields.items():
        sets.append(f"{k}=?")
        vals.append(v)
    sets.append("updated_at_utc=?")
    vals.append(utc_now_iso())
    vals.append(lead_id)
    conn.execute(f"UPDATE leads SET {', '.join(sets)} WHERE id=?", vals)
    conn.commit()
    conn.close()


def add_interaction(user_id: int, lead_id: int, channel: str, direction: str, content: str,
                    external_id: str = "", meta: dict = None):
    conn = get_db()
    conn.execute(
        """
        INSERT INTO interactions (user_id, lead_id, channel, direction, external_id, content, meta_json, ts_utc)
        VALUES (?, ?, ?, ?, ?, ?, ?, ?)
        """,
        (user_id, lead_id, channel, direction, external_id, content, json.dumps(meta or {}), utc_now_iso()),
    )
    conn.commit()
    conn.close()


def schedule_job(user_id: int, lead_id: int, job_type: str, run_at_utc: str, payload: dict):
    conn = get_db()
    conn.execute(
        """
        INSERT INTO jobs (user_id, lead_id, job_type, run_at_utc, payload_json, status, attempts, created_at_utc, updated_at_utc)
        VALUES (?, ?, ?, ?, ?, 'queued', 0, ?, ?)
        """,
        (user_id, lead_id, job_type, run_at_utc, json.dumps(payload), utc_now_iso(), utc_now_iso()),
    )
    conn.commit()
    conn.close()


# =========================================================
# KNOWLEDGE BASE (lightweight retrieval)
# =========================================================
def kb_search(user_id: int, query: str, limit: int = 5):
    q = (query or "").lower()
    q_tokens = set(re.findall(r"[a-z0-9]+", q))
    if not q_tokens:
        return []
    conn = get_db()
    rows = conn.execute("SELECT id, title, content FROM kb_items WHERE user_id=?", (user_id,)).fetchall()
    conn.close()

    scored = []
    for r in rows:
        text = (r["title"] or "") + "\n" + (r["content"] or "")
        tokens = set(re.findall(r"[a-z0-9]+", text.lower()))
        score = len(tokens.intersection(q_tokens))
        if score > 0:
            scored.append((score, r))
    scored.sort(key=lambda x: x[0], reverse=True)
    return [x[1] for x in scored[:limit]]


def build_business_context(user_row, query: str):
    kb = kb_search(user_row["id"], query, limit=4)
    kb_text = ""
    for item in kb:
        kb_text += f"\n[KB] {item['title']}\n{item['content']}\n"

    base = f"""
Business: {user_row.get('business_name') or APP_NAME}
Type: {user_row.get('business_type') or ''}
Booking link: {user_row.get('booking_link') or ''}
After-hours enabled: {user_row.get('after_hours_enabled') or 0}
After-hours message: {user_row.get('after_hours_message') or ''}
Escalation keywords: {user_row.get('escalation_keywords') or default_escalation_keywords()}
"""
    return (base + "\n" + kb_text).strip()


# =========================================================
# AI “ONE BRAIN” (voice + sms)
# =========================================================
def ai_compose_reply(user_row, channel: str, caller_text: str, lead_context: dict = None) -> str:
    """
    Output should be short, actionable, and safe.
    """
    if openai_client is None:
        bl = (user_row.get("booking_link") or "").strip()
        if bl:
            return f"Thanks — to book, use: {bl}. Reply with your name + best callback time if you prefer."
        return "Thanks — please reply with your name and best callback time, and we’ll get back to you."

    business_ctx = build_business_context(user_row, caller_text)
    lead_ctx = json.dumps(lead_context or {}, ensure_ascii=False)

    developer_rules = f"""
You are CALTAURA, a receptionist + lead conversion assistant for a small business.
Rules:
- Never mention AI, OpenAI, “model”, system prompts, or policies.
- Keep responses short and businesslike.
- If asked about hours/pricing/policies: only use Business Context. If unknown, say you’ll confirm and take a message.
- Always attempt lead conversion: ask for name + service needed + preferred time OR send booking link if available.
- Escalate if urgent/sensitive: offer immediate callback / staff escalation (without inventing staff names).
- SMS: 1–2 messages max, under ~320 chars if possible.
- Voice: 1–2 sentences max; ask ONE question at a time.
- Respect opt-out: if they say STOP/UNSUBSCRIBE, acknowledge and stop.
"""

    user_msg = f"""
Channel: {channel}

Business Context:
{business_ctx}

Lead context (json):
{lead_ctx}

Customer said:
{caller_text}

Write ONLY the next response the receptionist should say/send.
"""

    try:
        r = openai_client.responses.create(
            model=OPENAI_MODEL,
            input=[
                {"role": "developer", "content": developer_rules},
                {"role": "user", "content": user_msg},
            ],
        )
        out = (r.output_text or "").strip()
        return out or "Sorry — could you share your name and the best time to reach you?"
    except Exception:
        return "Sorry — could you share your name and the best time to reach you?"


# =========================================================
# AUTH
# =========================================================
class User(UserMixin):
    def __init__(self, user_id: int, username: str):
        self.id = user_id
        self.username = username


@login_manager.user_loader
def load_user(user_id):
    conn = get_db()
    row = conn.execute("SELECT id, username FROM users WHERE id=?", (user_id,)).fetchone()
    conn.close()
    if row:
        return User(int(row["id"]), row["username"] or "")
    return None


# =========================================================
# ERROR HANDLERS
# =========================================================
@app.errorhandler(404)
def _err_404(e):
    return "Not Found", 404


@app.errorhandler(500)
def _err_500(e):
    print("=== 500 ===")
    traceback.print_exc()
    return "Internal Server Error (check server logs)", 500


# =========================================================
# BILLING (Stripe)
# =========================================================
def set_user_billing(user_id: int, **fields):
    if not fields:
        return
    conn = get_db()
    sets = []
    vals = []
    for k, v in fields.items():
        sets.append(f"{k}=?")
        vals.append(v)
    vals.append(int(user_id))
    conn.execute(f"UPDATE users SET {', '.join(sets)} WHERE id=?", vals)
    conn.commit()
    conn.close()


def find_user_by_stripe_customer(customer_id: str):
    if not customer_id:
        return None
    conn = get_db()
    row = conn.execute("SELECT * FROM users WHERE stripe_customer_id=? LIMIT 1", (customer_id,)).fetchone()
    conn.close()
    return row


@app.route("/billing")
@login_required
def billing():
    conn = get_db()
    u = conn.execute("SELECT * FROM users WHERE id=?", (int(current_user.id),)).fetchone()
    conn.close()

    status = user_billing_status(u)
    flash_html = consume_flash()

    if not billing_is_configured():
        body = f"""
        {flash_html}
        <div class="card p-4">
          <h3>Billing</h3>
          <p class="muted">Stripe is not configured. The app will run, but self-serve purchase is disabled until you set Stripe env vars.</p>
          <ul class="muted">
            <li>Set <code>STRIPE_SECRET_KEY</code>, <code>STRIPE_WEBHOOK_SECRET</code>, <code>STRIPE_PRICE_ID</code></li>
          </ul>
        </div>
        """
        return html_layout("Billing", body)

    portal_btn = ""
    if u.get("stripe_customer_id"):
        portal_btn = f"""
          <form method="POST" action="{url_for("billing_portal")}">
            <button class="btn btn-outline-light">Manage subscription</button>
          </form>
        """

    body = f"""
    {flash_html}
    <div class="card p-4">
      <h3>Billing</h3>
      <p class="muted">Status: <span class="badge badge-soft">{status}</span></p>
      <hr/>
      <p>To use {APP_NAME} you need an active subscription.</p>
      <div class="d-flex gap-2 flex-wrap">
        <form method="POST" action="{url_for("billing_start")}">
          <button class="btn btn-primary">Start subscription</button>
        </form>
        {portal_btn}
      </div>
      <hr/>
      <p class="muted small">
        After payment, access is unlocked automatically by Stripe webhooks. If you pay and it doesn’t unlock, check your webhook configuration.
      </p>
    </div>
    """
    return html_layout("Billing", body)


@app.route("/billing/start", methods=["POST"])
@login_required
def billing_start():
    if not billing_is_configured():
        flash_once("Stripe is not configured. Set STRIPE_* env vars.", "danger")
        return redirect(url_for("billing"))

    conn = get_db()
    u = conn.execute("SELECT * FROM users WHERE id=?", (int(current_user.id),)).fetchone()
    conn.close()

    base = require_base_url()
    success_url = STRIPE_SUCCESS_URL or f"{base}{url_for('billing_success')}" + "?session_id={CHECKOUT_SESSION_ID}"
    cancel_url = STRIPE_CANCEL_URL or f"{base}{url_for('billing_cancel')}"

    try:
        # Create Checkout Session for subscription
        cs = stripe.checkout.Session.create(
            mode="subscription",
            line_items=[{"price": STRIPE_PRICE_ID, "quantity": 1}],
            success_url=success_url,
            cancel_url=cancel_url,
            customer_email=u.get("notify_email") or None,
            client_reference_id=str(u["id"]),
            metadata={"user_id": str(u["id"]), "username": u.get("username") or ""},
            subscription_data={"metadata": {"user_id": str(u["id"]), "username": u.get("username") or ""}},
            allow_promotion_codes=True,
        )
        # mark pending
        set_user_billing(int(u["id"]), billing_status="pending", stripe_price_id=STRIPE_PRICE_ID)
        return redirect(cs.url)
    except Exception as e:
        flash_once(f"Could not start checkout: {e}", "danger")
        return redirect(url_for("billing"))


@app.route("/billing/success")
@login_required
def billing_success():
    session_id = (request.args.get("session_id") or "").strip()
    flash_html = consume_flash()

    body = f"""
    {flash_html}
    <div class="card p-4">
      <h3>Payment received</h3>
      <p class="muted">If your access is not unlocked within a minute, your Stripe webhook may not be configured. Check /stripe/webhook.</p>
      <p class="muted small">Session ID: <code>{session_id or "n/a"}</code></p>
      <a class="btn btn-primary" href="{url_for("dashboard")}">Go to dashboard</a>
      <a class="btn btn-outline-light ms-2" href="{url_for("billing")}">Billing</a>
    </div>
    """
    return html_layout("Billing success", body)


@app.route("/billing/cancel")
@login_required
def billing_cancel():
    flash_once("Checkout was canceled.", "warning")
    return redirect(url_for("billing"))


@app.route("/billing/portal", methods=["POST"])
@login_required
def billing_portal():
    if not billing_is_configured():
        flash_once("Stripe is not configured.", "danger")
        return redirect(url_for("billing"))

    conn = get_db()
    u = conn.execute("SELECT * FROM users WHERE id=?", (int(current_user.id),)).fetchone()
    conn.close()

    if not u.get("stripe_customer_id"):
        flash_once("No Stripe customer found yet. Start a subscription first.", "warning")
        return redirect(url_for("billing"))

    try:
        ps = stripe.billing_portal.Session.create(
            customer=u["stripe_customer_id"],
            return_url=f"{require_base_url()}{url_for('billing')}",
        )
        return redirect(ps.url)
    except Exception as e:
        flash_once(f"Could not open portal: {e}", "danger")
        return redirect(url_for("billing"))


@app.route("/stripe/webhook", methods=["POST"])
def stripe_webhook():
    if not billing_is_configured():
        return ("Stripe not configured", 400)

    payload = request.data
    sig = request.headers.get("Stripe-Signature", "")

    try:
        event = stripe.Webhook.construct_event(payload, sig, STRIPE_WEBHOOK_SECRET)
    except Exception as e:
        print("Stripe webhook signature failed:", e)
        return ("Invalid signature", 400)

    etype = event["type"]
    data = event["data"]["object"]

    try:
        if etype == "checkout.session.completed":
            # session contains customer + subscription
            customer_id = data.get("customer")
            subscription_id = data.get("subscription")
            user_id = None

            # prefer metadata
            md = data.get("metadata") or {}
            if md.get("user_id"):
                user_id = int(md["user_id"])
            elif data.get("client_reference_id"):
                user_id = int(data["client_reference_id"])

            if user_id and customer_id:
                set_user_billing(
                    user_id,
                    stripe_customer_id=customer_id,
                    stripe_subscription_id=subscription_id or "",
                    billing_status="active",
                    paid_since_utc=utc_now_iso(),
                )

        elif etype in ("customer.subscription.created", "customer.subscription.updated"):
            customer_id = data.get("customer")
            status = (data.get("status") or "").lower()
            subscription_id = data.get("id")

            # map Stripe statuses -> our statuses
            mapped = "pending"
            if status in ("active",):
                mapped = "active"
            elif status in ("trialing",):
                mapped = "trialing"
            elif status in ("past_due", "unpaid"):
                mapped = "past_due"
            elif status in ("canceled", "incomplete_expired"):
                mapped = "canceled"
            else:
                mapped = status or "pending"

            u = find_user_by_stripe_customer(customer_id)
            # If not found by customer id, try metadata user_id on subscription
            if not u:
                md = data.get("metadata") or {}
                if md.get("user_id"):
                    uid = int(md["user_id"])
                    conn = get_db()
                    u = conn.execute("SELECT * FROM users WHERE id=?", (uid,)).fetchone()
                    conn.close()

            if u:
                set_user_billing(
                    int(u["id"]),
                    stripe_customer_id=customer_id or (u.get("stripe_customer_id") or ""),
                    stripe_subscription_id=subscription_id or (u.get("stripe_subscription_id") or ""),
                    billing_status=mapped,
                    paid_since_utc=utc_now_iso() if mapped in ("active", "trialing") else (u.get("paid_since_utc") or ""),
                )

        elif etype == "customer.subscription.deleted":
            customer_id = data.get("customer")
            u = find_user_by_stripe_customer(customer_id)
            if u:
                set_user_billing(int(u["id"]), billing_status="canceled")

    except Exception as e:
        print("Stripe webhook processing error:", e)
        traceback.print_exc()
        return ("Webhook error", 500)

    return ("", 200)


# =========================================================
# PUBLIC PAGES
# =========================================================
@app.route("/")
def home():
    flash_html = consume_flash()
    body = f"""
    {flash_html}
    <div class="card p-4">
      <h2>{APP_NAME}</h2>
      <p class="muted">
        AI receptionist + lead capture for small businesses.
        Answer calls, capture the lead, and follow up automatically.
      </p>
      <div class="d-flex gap-2 flex-wrap">
        <a class="btn btn-primary" href="{url_for("register")}">Get started</a>
        <a class="btn btn-outline-light" href="{url_for("pricing")}">See pricing</a>
      </div>
      <hr/>
      <p class="muted small">
        Self-serve setup: create account → onboarding wizard → pay → connect Twilio number → go live.
      </p>
    </div>
    """
    return html_layout("Home", body, show_nav=True)


@app.route("/pricing")
def pricing():
    base = require_base_url()
    configured = billing_is_configured()
    body = f"""
    <div class="card p-4">
      <h2>Pricing</h2>
      <p class="muted">Start with one plan. You can add tiers later.</p>
      <div class="card p-3">
        <h4>Pro Plan</h4>
        <ul class="muted">
          <li>Inbound call intake (voice)</li>
          <li>Inbound SMS assistant</li>
          <li>Dashboard + lead pipeline</li>
          <li>Missed call follow-ups (SMS)</li>
        </ul>
        <p class="muted small">Billing handled by Stripe Checkout.</p>
        <a class="btn btn-primary" href="{url_for("register")}">Start</a>
      </div>
      <hr/>
      <p class="muted small">
        Stripe configured: <b>{"YES" if configured else "NO"}</b><br/>
        Base URL: <code>{base}</code>
      </p>
    </div>
    """
    return html_layout("Pricing", body)


@app.route("/health")
def health():
    return {"ok": True, "app": APP_NAME, "time_utc": utc_now_iso()}


# =========================================================
# REGISTER / LOGIN
# =========================================================
@app.route("/register", methods=["GET", "POST"])
def register():
    flash_html = consume_flash()
    if request.method == "POST":
        username = (request.form.get("username") or "").strip()
        password = request.form.get("password") or ""
        agree = request.form.get("agree") or ""

        if not username or not password:
            flash_once("Username and password required.", "danger")
            return redirect(url_for("register"))

        if agree != "yes":
            flash_once("You must agree to the Terms and Privacy Policy to continue.", "warning")
            return redirect(url_for("register"))

        conn = get_db()
        try:
            conn.execute(
                """
                INSERT INTO users (
                    username, password_hash,
                    business_name, business_type, timezone,
                    notify_email, booking_link,
                    after_hours_enabled, after_hours_message,
                    greeting, escalation_keywords,
                    mode, capture_json, is_onboarded,
                    bizbot_number,
                    billing_status, stripe_price_id,
                    created_at_utc
                )
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                """,
                (
                    username,
                    generate_password_hash(password),
                    APP_NAME,
                    "Service Business",
                    "America/New_York",
                    "",
                    "",
                    0,
                    "Thanks for calling. We’re currently closed. Please leave a message.",
                    template_greeting(APP_NAME, "Service Business"),
                    default_escalation_keywords(),
                    "message",
                    json.dumps(default_capture_json()),
                    0,
                    "",
                    "none",
                    STRIPE_PRICE_ID or "",
                    utc_now_iso(),
                ),
            )
            conn.commit()
        except sqlite3.IntegrityError:
            conn.close()
            flash_once("Username already exists.", "danger")
            return redirect(url_for("register"))

        # Auto-login then onboarding
        row = conn.execute("SELECT id, username FROM users WHERE username=?", (username,)).fetchone()
        conn.close()
        login_user(User(int(row["id"]), row["username"] or ""))
        return redirect(url_for("onboarding"))

    body = f"""
    {flash_html}
    <div class="card p-4">
      <h3>Create your account</h3>
      <form method="POST" class="mt-3">
        <div class="mb-3">
          <label class="form-label">Username</label>
          <input name="username" class="form-control" placeholder="yourbusiness" required />
        </div>
        <div class="mb-3">
          <label class="form-label">Password</label>
          <input type="password" name="password" class="form-control" required />
        </div>
        <div class="form-check mb-3">
          <input class="form-check-input" type="checkbox" value="yes" id="agree" name="agree">
          <label class="form-check-label" for="agree">
            I agree to the Terms and Privacy Policy.
          </label>
        </div>
        <button class="btn btn-primary">Continue</button>
      </form>
      <p class="muted small mt-3">Already have an account? <a href="{url_for("login")}">Login</a></p>
    </div>
    """
    return html_layout("Register", body)


@app.route("/login", methods=["GET", "POST"])
def login():
    flash_html = consume_flash()
    next_url = request.args.get("next") or ""
    if request.method == "POST":
        username = (request.form.get("username") or "").strip()
        password = request.form.get("password") or ""
        next_url = request.form.get("next") or next_url

        conn = get_db()
        row = conn.execute("SELECT * FROM users WHERE username=?", (username,)).fetchone()
        conn.close()

        if row and row.get("password_hash") and check_password_hash(row["password_hash"], password):
            login_user(User(int(row["id"]), row.get("username") or ""))

            if (row.get("is_onboarded") or 0) == 0:
                return redirect(url_for("onboarding"))

            # If billing configured, direct them to billing if not active
            if billing_is_configured() and not billing_active(row):
                return redirect(url_for("billing"))

            if next_url and next_url.startswith("/"):
                return redirect(next_url)
            return redirect(url_for("dashboard"))

        flash_once("Invalid credentials.", "danger")
        return redirect(url_for("login"))

    body = f"""
    {flash_html}
    <div class="card p-4">
      <h3>Login</h3>
      <form method="POST" class="mt-3">
        <input type="hidden" name="next" value="{next_url}">
        <div class="mb-3">
          <label class="form-label">Username</label>
          <input name="username" class="form-control" required />
        </div>
        <div class="mb-3">
          <label class="form-label">Password</label>
          <input type="password" name="password" class="form-control" required />
        </div>
        <button class="btn btn-primary">Login</button>
      </form>
      <p class="muted small mt-3">No account? <a href="{url_for("register")}">Create one</a></p>
    </div>
    """
    return html_layout("Login", body)


@app.route("/logout")
@login_required
def logout():
    logout_user()
    return redirect(url_for("login"))


# =========================================================
# ONBOARDING (Wizard)
# =========================================================
@app.route("/onboarding", methods=["GET", "POST"])
@login_required
def onboarding():
    flash_html = consume_flash()

    conn = get_db()
    u = conn.execute("SELECT * FROM users WHERE id=?", (int(current_user.id),)).fetchone()
    conn.close()

    if request.method == "POST":
        business_name = (request.form.get("business_name") or "").strip()
        business_type = (request.form.get("business_type") or "").strip()
        timezone_val = (request.form.get("timezone") or "").strip()
        notify_email = (request.form.get("notify_email") or "").strip()
        booking_link = (request.form.get("booking_link") or "").strip()
        after_hours_enabled = normalize_bool_checkbox(request.form.get("after_hours_enabled"))
        after_hours_message = (request.form.get("after_hours_message") or "").strip()
        bizbot_number = norm_phone(request.form.get("bizbot_number") or "")

        greeting = (request.form.get("greeting") or "").strip() or template_greeting(business_name, business_type)
        escalation_keywords = (request.form.get("escalation_keywords") or "").strip() or default_escalation_keywords()

        if bizbot_number and not bizbot_number.startswith("+"):
            flash_once("Twilio number must be in E.164 format (e.g., +19195551234).", "warning")
            return redirect(url_for("onboarding"))

        conn = get_db()
        conn.execute(
            """
            UPDATE users
            SET business_name=?, business_type=?, timezone=?, notify_email=?,
                booking_link=?, after_hours_enabled=?, after_hours_message=?,
                greeting=?, escalation_keywords=?,
                bizbot_number=?,
                is_onboarded=1
            WHERE id=?
            """,
            (
                business_name or APP_NAME,
                business_type or "Service Business",
                timezone_val or "America/New_York",
                notify_email,
                booking_link,
                after_hours_enabled,
                after_hours_message or "Thanks for calling. We’re currently closed. Please leave a message.",
                greeting,
                escalation_keywords,
                bizbot_number,
                int(current_user.id),
            ),
        )
        conn.commit()
        conn.close()

        # If billing is configured, send them to billing if not active
        if billing_is_configured():
            conn = get_db()
            u2 = conn.execute("SELECT * FROM users WHERE id=?", (int(current_user.id),)).fetchone()
            conn.close()
            if not billing_active(u2):
                return redirect(url_for("billing"))

        return redirect(url_for("dashboard"))

    base = require_base_url()
    webhook_voice = f"{base}/voice"
    webhook_sms = f"{base}/sms"
    webhook_status = f"{base}/status"

    body = f"""
    {flash_html}
    <div class="card p-4">
      <h3>Onboarding Wizard</h3>
      <p class="muted">Complete this once. Then purchase and go live.</p>

      <div class="card p-3 mb-3">
        <p class="muted mb-1"><b>Twilio webhooks</b> (configure in Twilio Console for your number):</p>
        <ul class="muted small mb-0">
          <li>Voice (POST): <code>{webhook_voice}</code></li>
          <li>SMS (POST): <code>{webhook_sms}</code></li>
          <li>Status callback (POST): <code>{webhook_status}</code></li>
        </ul>
      </div>

      <form method="POST">
        <div class="row">
          <div class="col-md-6 mb-3">
            <label class="form-label">Business name</label>
            <input name="business_name" class="form-control" value="{(u.get('business_name') or APP_NAME)}" required />
          </div>
          <div class="col-md-6 mb-3">
            <label class="form-label">Business type</label>
            <input name="business_type" class="form-control" value="{(u.get('business_type') or 'Service Business')}" />
          </div>
        </div>

        <div class="row">
          <div class="col-md-6 mb-3">
            <label class="form-label">Timezone</label>
            <input name="timezone" class="form-control" value="{(u.get('timezone') or 'America/New_York')}" />
            <div class="muted small mt-1">Example: America/New_York</div>
          </div>
          <div class="col-md-6 mb-3">
            <label class="form-label">Notification email (optional)</label>
            <input name="notify_email" class="form-control" value="{(u.get('notify_email') or '')}" />
          </div>
        </div>

        <div class="mb-3">
          <label class="form-label">Booking link (optional)</label>
          <input name="booking_link" class="form-control" value="{(u.get('booking_link') or '')}" placeholder="https://calendly.com/..." />
        </div>

        <div class="mb-3">
          <label class="form-label">Your Twilio number (E.164) connected to this account</label>
          <input name="bizbot_number" class="form-control" value="{(u.get('bizbot_number') or '')}" placeholder="+19195551234" />
          <div class="muted small mt-1">This is the number Twilio will send webhooks from/to for this business.</div>
        </div>

        <div class="form-check mb-2">
          <input class="form-check-input" type="checkbox" id="afterh" name="after_hours_enabled" {"checked" if int(u.get("after_hours_enabled") or 0)==1 else ""}>
          <label class="form-check-label" for="afterh">Enable after-hours message</label>
        </div>

        <div class="mb-3">
          <label class="form-label">After-hours message</label>
          <textarea name="after_hours_message" class="form-control" rows="2">{(u.get("after_hours_message") or "Thanks for calling. We’re currently closed. Please leave a message.")}</textarea>
        </div>

        <div class="mb-3">
          <label class="form-label">Greeting</label>
          <input name="greeting" class="form-control" value="{(u.get('greeting') or template_greeting(u.get('business_name') or APP_NAME, u.get('business_type') or 'Service Business'))}" />
        </div>

        <div class="mb-3">
          <label class="form-label">Escalation keywords (comma-separated)</label>
          <input name="escalation_keywords" class="form-control" value="{(u.get('escalation_keywords') or default_escalation_keywords())}" />
        </div>

        <button class="btn btn-primary">Save & Continue</button>
      </form>

      <hr/>
      <p class="muted small">
        Next step: purchase subscription in Billing (if enabled), then place test calls/SMS to verify lead capture.
      </p>
    </div>
    """
    return html_layout("Onboarding", body)


# =========================================================
# DASHBOARD / LEADS / THREAD
# =========================================================
@app.route("/dashboard")
@login_required
def dashboard():
    conn = get_db()
    u = conn.execute("SELECT * FROM users WHERE id=?", (int(current_user.id),)).fetchone()

    stats = conn.execute(
        """
        SELECT
          (SELECT COUNT(*) FROM leads WHERE user_id=?) as leads_total,
          (SELECT COUNT(*) FROM leads WHERE user_id=? AND status='new') as leads_new,
          (SELECT COUNT(*) FROM leads WHERE user_id=? AND status='booked') as leads_booked,
          (SELECT COUNT(*) FROM interactions WHERE user_id=? AND channel='call') as calls_total,
          (SELECT COUNT(*) FROM interactions WHERE user_id=? AND channel='sms') as sms_total
        """,
        (int(current_user.id), int(current_user.id), int(current_user.id), int(current_user.id), int(current_user.id)),
    ).fetchone()

    latest = conn.execute(
        """
        SELECT l.id, l.status, l.name, l.phone, l.service_needed, l.updated_at_utc
        FROM leads l
        WHERE l.user_id=?
        ORDER BY l.updated_at_utc DESC
        LIMIT 10
        """,
        (int(current_user.id),),
    ).fetchall()
    conn.close()

    base = require_base_url()
    status = user_billing_status(u)
    billing_banner = ""
    if billing_is_configured() and not billing_active(u):
        billing_banner = f'<div class="alert alert-warning">Billing status is <b>{status}</b>. <a href="{url_for("billing")}">Complete subscription</a> to go live.</div>'

    rows_html = ""
    for r in latest:
        rows_html += f"""
        <tr>
          <td><a href="{url_for("lead_detail", lead_id=int(r['id']))}">#{int(r['id'])}</a></td>
          <td><span class="badge badge-soft">{r['status'] or ''}</span></td>
          <td>{(r['name'] or '')}</td>
          <td>{(r['phone'] or '')}</td>
          <td class="muted">{short(r['service_needed'] or '', 60)}</td>
          <td class="muted small">{(r['updated_at_utc'] or '')}</td>
        </tr>
        """

    body = f"""
    {billing_banner}
    <div class="card p-4">
      <h3>Dashboard</h3>
      <p class="muted">Welcome, <b>{u.get('username')}</b></p>
      <div class="row">
        <div class="col-md-3"><div class="card p-3 mb-3"><div class="muted">Total leads</div><div class="h4">{stats['leads_total']}</div></div></div>
        <div class="col-md-3"><div class="card p-3 mb-3"><div class="muted">New leads</div><div class="h4">{stats['leads_new']}</div></div></div>
        <div class="col-md-3"><div class="card p-3 mb-3"><div class="muted">Booked</div><div class="h4">{stats['leads_booked']}</div></div></div>
        <div class="col-md-3"><div class="card p-3 mb-3"><div class="muted">Calls logged</div><div class="h4">{stats['calls_total']}</div></div></div>
      </div>

      <hr/>
      <h5>Go-live checklist</h5>
      <ul class="muted">
        <li>Set <code>PUBLIC_BASE_URL</code> to <code>{base}</code> (must match Twilio webhook host)</li>
        <li>Configure Twilio webhooks: <code>{base}/voice</code>, <code>{base}/sms</code>, <code>{base}/status</code></li>
        <li>Place a test call and send a test SMS to confirm lead capture</li>
        <li>Set up a cron to call <code>{base}/jobs/tick?key=...</code> every 1–5 minutes</li>
      </ul>

      <hr/>
      <h5>Latest leads</h5>
      <div class="table-responsive">
        <table class="table table-dark table-striped align-middle">
          <thead><tr><th>ID</th><th>Status</th><th>Name</th><th>Phone</th><th>Need</th><th>Updated</th></tr></thead>
          <tbody>{rows_html or '<tr><td colspan="6" class="muted">No leads yet.</td></tr>'}</tbody>
        </table>
      </div>
    </div>
    """
    return html_layout("Dashboard", body)


@app.route("/leads")
@login_required
def leads():
    q = (request.args.get("q") or "").strip()
    status = (request.args.get("status") or "").strip().lower()

    conn = get_db()
    params = [int(current_user.id)]
    where = "WHERE user_id=?"
    if status and status in lead_statuses():
        where += " AND status=?"
        params.append(status)
    if q:
        where += " AND (phone LIKE ? OR name LIKE ? OR email LIKE ? OR service_needed LIKE ?)"
        like = f"%{q}%"
        params.extend([like, like, like, like])

    rows = conn.execute(
        f"""
        SELECT id, status, name, phone, email, service_needed, preferred_time, opted_out, updated_at_utc
        FROM leads
        {where}
        ORDER BY updated_at_utc DESC
        LIMIT 200
        """,
        params,
    ).fetchall()
    conn.close()

    options = "".join([f'<option value="{s}" {"selected" if s==status else ""}>{s}</option>' for s in [""] + lead_statuses()])
    rows_html = ""
    for r in rows:
        oo = "YES" if int(r.get("opted_out") or 0) == 1 else "NO"
        rows_html += f"""
        <tr>
          <td><a href="{url_for("lead_detail", lead_id=int(r['id']))}">#{int(r['id'])}</a></td>
          <td><span class="badge badge-soft">{r['status']}</span></td>
          <td>{r['name'] or ''}</td>
          <td>{r['phone'] or ''}</td>
          <td class="muted">{short(r['service_needed'] or '', 60)}</td>
          <td class="muted small">{oo}</td>
          <td class="muted small">{r['updated_at_utc'] or ''}</td>
        </tr>
        """

    body = f"""
    <div class="card p-4">
      <h3>Leads</h3>
      <form class="row g-2 mb-3" method="GET">
        <div class="col-md-6">
          <input name="q" class="form-control" value="{q}" placeholder="Search name/phone/email/need..." />
        </div>
        <div class="col-md-3">
          <select name="status" class="form-control">{options}</select>
        </div>
        <div class="col-md-3 d-grid">
          <button class="btn btn-primary">Filter</button>
        </div>
      </form>

      <div class="d-flex gap-2 mb-3">
        <a class="btn btn-outline-light" href="{url_for("export_leads_csv")}">Export CSV</a>
      </div>

      <div class="table-responsive">
        <table class="table table-dark table-striped align-middle">
          <thead><tr><th>ID</th><th>Status</th><th>Name</th><th>Phone</th><th>Need</th><th>Opted out</th><th>Updated</th></tr></thead>
          <tbody>{rows_html or '<tr><td colspan="7" class="muted">No leads found.</td></tr>'}</tbody>
        </table>
      </div>
    </div>
    """
    return html_layout("Leads", body)


@app.route("/leads/<int:lead_id>", methods=["GET", "POST"])
@login_required
def lead_detail(lead_id: int):
    conn = get_db()
    lead = conn.execute(
        "SELECT * FROM leads WHERE id=? AND user_id=?",
        (int(lead_id), int(current_user.id)),
    ).fetchone()

    if not lead:
        conn.close()
        return "Lead not found", 404

    u = conn.execute("SELECT * FROM users WHERE id=?", (int(current_user.id),)).fetchone()

    if request.method == "POST":
        action = (request.form.get("action") or "").strip()

        if action == "update":
            status = (request.form.get("status") or lead["status"] or "new").strip().lower()
            if status not in lead_statuses():
                status = lead["status"] or "new"

            name = (request.form.get("name") or lead["name"] or "").strip()
            email = (request.form.get("email") or lead["email"] or "").strip()
            service_needed = (request.form.get("service_needed") or lead["service_needed"] or "").strip()
            preferred_time = (request.form.get("preferred_time") or lead["preferred_time"] or "").strip()
            notes = (request.form.get("notes") or lead["notes"] or "").strip()
            opted_out = normalize_bool_checkbox(request.form.get("opted_out"))

            update_lead(
                int(lead_id),
                status=status,
                name=name,
                email=email,
                service_needed=service_needed,
                preferred_time=preferred_time,
                notes=notes,
                opted_out=opted_out,
            )

        if action == "sms":
            msg = (request.form.get("message") or "").strip()
            if msg:
                try:
                    # Block if opted out
                    if int(lead.get("opted_out") or 0) == 1:
                        raise RuntimeError("Lead has opted out of SMS.")
                    sid = send_sms_for_user(u, to_number=lead["phone"], body=msg)
                    add_interaction(int(current_user.id), int(lead_id), "sms", "outbound", msg, external_id=sid or "", meta={"manual": True})
                    update_lead(int(lead_id), last_outbound_utc=utc_now_iso())
                except Exception as e:
                    add_interaction(int(current_user.id), int(lead_id), "system", "internal", f"SMS send failed: {e}", meta={"error": True})

        conn.close()
        return redirect(url_for("lead_detail", lead_id=int(lead_id)))

    thread = conn.execute(
        """
        SELECT channel, direction, content, ts_utc
        FROM interactions
        WHERE user_id=? AND lead_id=?
        ORDER BY id ASC
        """,
        (int(current_user.id), int(lead_id)),
    ).fetchall()
    conn.close()

    statuses_opts = "".join([f'<option value="{s}" {"selected" if s==(lead["status"] or "") else ""}>{s}</option>' for s in lead_statuses()])
    thread_html = ""
    for t in thread:
        thread_html += f"""
        <div class="card p-2 mb-2">
          <div class="d-flex justify-content-between">
            <div><span class="badge badge-soft">{t['channel']}</span> <span class="badge badge-soft">{t['direction']}</span></div>
            <div class="muted small">{t['ts_utc']}</div>
          </div>
          <div class="mt-2">{(t['content'] or '').replace('<','&lt;').replace('>','&gt;')}</div>
        </div>
        """

    oo_checked = "checked" if int(lead.get("opted_out") or 0) == 1 else ""

    body = f"""
    <div class="card p-4">
      <h3>Lead #{int(lead['id'])}</h3>
      <p class="muted">Phone: <code>{lead.get('phone') or ''}</code></p>

      <form method="POST" class="card p-3 mb-3">
        <input type="hidden" name="action" value="update" />
        <div class="row">
          <div class="col-md-3 mb-2">
            <label class="form-label">Status</label>
            <select name="status" class="form-control">{statuses_opts}</select>
          </div>
          <div class="col-md-3 mb-2">
            <label class="form-label">Name</label>
            <input name="name" class="form-control" value="{lead.get('name') or ''}" />
          </div>
          <div class="col-md-3 mb-2">
            <label class="form-label">Email</label>
            <input name="email" class="form-control" value="{lead.get('email') or ''}" />
          </div>
          <div class="col-md-3 mb-2">
            <label class="form-label">Preferred time</label>
            <input name="preferred_time" class="form-control" value="{lead.get('preferred_time') or ''}" />
          </div>
        </div>
        <div class="mb-2">
          <label class="form-label">Service needed</label>
          <input name="service_needed" class="form-control" value="{lead.get('service_needed') or ''}" />
        </div>
        <div class="mb-2">
          <label class="form-label">Notes</label>
          <textarea name="notes" class="form-control" rows="3">{lead.get('notes') or ''}</textarea>
        </div>
        <div class="form-check mb-2">
          <input class="form-check-input" type="checkbox" id="oo" name="opted_out" {oo_checked}>
          <label class="form-check-label" for="oo">SMS opted out (do not text)</label>
        </div>
        <button class="btn btn-primary">Save</button>
      </form>

      <form method="POST" class="card p-3 mb-3">
        <input type="hidden" name="action" value="sms" />
        <h5>Send SMS</h5>
        <div class="mb-2">
          <textarea name="message" class="form-control" rows="2" placeholder="Message..."></textarea>
        </div>
        <button class="btn btn-outline-light">Send</button>
        <p class="muted small mt-2">Requires: Twilio configured + tenant has bizbot_number.</p>
      </form>

      <h5>Thread</h5>
      {thread_html or '<p class="muted">No messages yet.</p>'}
    </div>
    """
    return html_layout("Lead detail", body)


@app.route("/export/leads.csv")
@login_required
def export_leads_csv():
    conn = get_db()
    rows = conn.execute(
        """
        SELECT id,status,source,name,phone,email,service_needed,preferred_time,urgency,opted_out,created_at_utc,updated_at_utc
        FROM leads
        WHERE user_id=?
        ORDER BY id DESC
        """,
        (int(current_user.id),),
    ).fetchall()
    conn.close()

    header = ["id", "status", "source", "name", "phone", "email", "service_needed", "preferred_time", "urgency", "opted_out", "created_at_utc", "updated_at_utc"]
    lines = [",".join(header)]
    for r in rows:
        vals = [str(r.get(h) or "").replace('"', '""') for h in header]
        lines.append(",".join([f'"{v}"' for v in vals]))
    out = "\n".join(lines)

    resp = make_response(out)
    resp.headers["Content-Type"] = "text/csv"
    resp.headers["Content-Disposition"] = 'attachment; filename="caltaura-leads.csv"'
    return resp


# =========================================================
# SETTINGS + KB + PLAYBOOKS
# =========================================================
@app.route("/settings", methods=["GET", "POST"])
@login_required
def settings():
    flash_html = consume_flash()
    conn = get_db()
    u = conn.execute("SELECT * FROM users WHERE id=?", (int(current_user.id),)).fetchone()
    conn.close()

    if request.method == "POST":
        mode = (request.form.get("mode") or "message").strip().lower()
        if mode not in ("message", "ai"):
            mode = "message"

        booking_link = (request.form.get("booking_link") or "").strip()
        notify_email = (request.form.get("notify_email") or "").strip()
        after_hours_enabled = normalize_bool_checkbox(request.form.get("after_hours_enabled"))
        after_hours_message = (request.form.get("after_hours_message") or "").strip()
        greeting = (request.form.get("greeting") or "").strip()
        escalation_keywords = (request.form.get("escalation_keywords") or "").strip()
        bizbot_number = norm_phone(request.form.get("bizbot_number") or "")

        if bizbot_number and not bizbot_number.startswith("+"):
            flash_once("Twilio number must be in E.164 format (e.g., +19195551234).", "warning")
            return redirect(url_for("settings"))

        conn = get_db()
        conn.execute(
            """
            UPDATE users
            SET mode=?, booking_link=?, notify_email=?,
                after_hours_enabled=?, after_hours_message=?,
                greeting=?, escalation_keywords=?,
                bizbot_number=?
            WHERE id=?
            """,
            (
                mode,
                booking_link,
                notify_email,
                after_hours_enabled,
                after_hours_message,
                greeting,
                escalation_keywords,
                bizbot_number,
                int(current_user.id),
            ),
        )
        conn.commit()
        conn.close()
        flash_once("Settings saved.", "success")
        return redirect(url_for("settings"))

    mode_opts = f"""
      <option value="message" {"selected" if (u.get("mode") or "message")=="message" else ""}>Message Capture (recommended)</option>
      <option value="ai" {"selected" if (u.get("mode") or "")=="ai" else ""}>AI Mode</option>
    """

    body = f"""
    {flash_html}
    <div class="card p-4">
      <h3>Settings</h3>
      <form method="POST" class="mt-3">
        <div class="mb-3">
          <label class="form-label">Mode</label>
          <select name="mode" class="form-control">{mode_opts}</select>
        </div>
        <div class="mb-3">
          <label class="form-label">Booking link</label>
          <input name="booking_link" class="form-control" value="{u.get('booking_link') or ''}" />
        </div>
        <div class="mb-3">
          <label class="form-label">Notification email</label>
          <input name="notify_email" class="form-control" value="{u.get('notify_email') or ''}" />
        </div>
        <div class="mb-3">
          <label class="form-label">Your Twilio number (E.164)</label>
          <input name="bizbot_number" class="form-control" value="{u.get('bizbot_number') or ''}" placeholder="+19195551234" />
        </div>
        <div class="form-check mb-2">
          <input class="form-check-input" type="checkbox" id="afterh2" name="after_hours_enabled" {"checked" if int(u.get("after_hours_enabled") or 0)==1 else ""}>
          <label class="form-check-label" for="afterh2">Enable after-hours message</label>
        </div>
        <div class="mb-3">
          <label class="form-label">After-hours message</label>
          <textarea name="after_hours_message" class="form-control" rows="2">{u.get('after_hours_message') or ''}</textarea>
        </div>
        <div class="mb-3">
          <label class="form-label">Greeting</label>
          <input name="greeting" class="form-control" value="{u.get('greeting') or ''}" />
        </div>
        <div class="mb-3">
          <label class="form-label">Escalation keywords</label>
          <input name="escalation_keywords" class="form-control" value="{u.get('escalation_keywords') or ''}" />
        </div>
        <button class="btn btn-primary">Save</button>
      </form>
    </div>
    """
    return html_layout("Settings", body)


@app.route("/kb", methods=["GET", "POST"])
@login_required
def kb():
    if request.method == "POST":
        title = (request.form.get("title") or "").strip()
        content = (request.form.get("content") or "").strip()
        if title and content:
            conn = get_db()
            conn.execute(
                "INSERT INTO kb_items (user_id, title, content, created_at_utc) VALUES (?, ?, ?, ?)",
                (int(current_user.id), title, content, utc_now_iso()),
            )
            conn.commit()
            conn.close()
        return redirect(url_for("kb"))

    conn = get_db()
    items = conn.execute(
        "SELECT id, title, content, created_at_utc FROM kb_items WHERE user_id=? ORDER BY id DESC LIMIT 200",
        (int(current_user.id),),
    ).fetchall()
    conn.close()

    items_html = ""
    for it in items:
        items_html += f"""
        <div class="card p-3 mb-2">
          <div class="d-flex justify-content-between">
            <div><b>{(it['title'] or '').replace('<','&lt;').replace('>','&gt;')}</b></div>
            <form method="POST" action="{url_for('kb_delete', item_id=int(it['id']))}">
              <button class="btn btn-sm btn-outline-light">Delete</button>
            </form>
          </div>
          <div class="muted mt-2">{(it['content'] or '').replace('<','&lt;').replace('>','&gt;')}</div>
          <div class="muted small mt-2">{it['created_at_utc']}</div>
        </div>
        """

    body = f"""
    <div class="card p-4">
      <h3>Knowledge Base</h3>
      <form method="POST" class="card p-3 mb-3">
        <div class="mb-2">
          <input name="title" class="form-control" placeholder="FAQ title..." />
        </div>
        <div class="mb-2">
          <textarea name="content" class="form-control" rows="3" placeholder="Answer..."></textarea>
        </div>
        <button class="btn btn-primary">Add</button>
      </form>
      {items_html or '<p class="muted">No KB items yet.</p>'}
    </div>
    """
    return html_layout("KB", body)


@app.route("/kb/delete/<int:item_id>", methods=["POST"])
@login_required
def kb_delete(item_id: int):
    conn = get_db()
    conn.execute("DELETE FROM kb_items WHERE id=? AND user_id=?", (int(item_id), int(current_user.id)))
    conn.commit()
    conn.close()
    return redirect(url_for("kb"))


PLAYBOOK_PRESETS = {
    "general": {
        "label": "General Service Business",
        "intake_questions": ["What do you need help with?", "Your name?", "Best callback time?"],
        "sms_templates": {
            "missed_call_1": "Sorry we missed you — reply with your name + what you need, and we’ll get back to you shortly.",
            "missed_call_2": "Just checking in — still need help? Reply with the service and best time to reach you.",
        },
    },
    "home_services": {
        "label": "Home Services (Plumber/Electrician/HVAC)",
        "intake_questions": ["What service do you need?", "How urgent is it?", "Best callback time?"],
        "sms_templates": {
            "missed_call_1": "Sorry we missed you — reply with your name + what you need, and we’ll get you booked.",
            "missed_call_2": "Quick follow-up — still need help? Reply YES and tell us the service + best time.",
        },
    },
    "med_spa": {
        "label": "Med Spa",
        "intake_questions": ["Which treatment?", "Preferred day/time?", "Best callback number?"],
        "sms_templates": {
            "missed_call_1": "Sorry we missed you — reply with your name + treatment, and we’ll confirm availability.",
            "missed_call_2": "Follow-up — want to book? Reply with preferred day/time and we’ll reserve a slot.",
        },
    },
}


@app.route("/playbooks", methods=["GET", "POST"])
@login_required
def playbooks():
    conn = get_db()
    existing = conn.execute(
        "SELECT * FROM playbooks WHERE user_id=? ORDER BY id DESC LIMIT 1",
        (int(current_user.id),),
    ).fetchone()

    if request.method == "POST":
        vertical = (request.form.get("vertical") or "general").strip()
        if vertical not in PLAYBOOK_PRESETS:
            vertical = "general"
        config = PLAYBOOK_PRESETS[vertical]
        conn.execute(
            "INSERT INTO playbooks (user_id, vertical, config_json, created_at_utc) VALUES (?, ?, ?, ?)",
            (int(current_user.id), vertical, json.dumps(config), utc_now_iso()),
        )
        conn.commit()
        conn.close()
        return redirect(url_for("playbooks"))

    conn.close()

    opts = "".join([f'<option value="{k}">{v["label"]}</option>' for k, v in PLAYBOOK_PRESETS.items()])
    existing_html = ""
    if existing:
        cfg = safe_json(existing.get("config_json"), {})
        existing_html = f"""
        <div class="card p-3 mt-3">
          <div class="muted">Active preset:</div>
          <div><b>{existing.get("vertical")}</b></div>
          <div class="muted small mt-2"><code>{json.dumps(cfg, indent=2)[:1200].replace('<','&lt;')}</code></div>
        </div>
        """

    body = f"""
    <div class="card p-4">
      <h3>Playbooks</h3>
      <form method="POST" class="row g-2 align-items-end">
        <div class="col-md-8">
          <label class="form-label">Choose preset</label>
          <select name="vertical" class="form-control">{opts}</select>
        </div>
        <div class="col-md-4 d-grid">
          <button class="btn btn-primary">Apply</button>
        </div>
      </form>
      {existing_html}
    </div>
    """
    return html_layout("Playbooks", body)


def get_latest_playbook(user_id: int):
    conn = get_db()
    row = conn.execute(
        "SELECT * FROM playbooks WHERE user_id=? ORDER BY id DESC LIMIT 1",
        (int(user_id),),
    ).fetchone()
    conn.close()
    if not row:
        return None
    return safe_json(row.get("config_json"), {})


# =========================================================
# WEB LEAD CAPTURE (public)
# =========================================================
@app.route("/lead", methods=["POST"])
def web_lead():
    name = (request.form.get("name") or "").strip()
    phone = norm_phone(request.form.get("phone") or "")
    email = (request.form.get("email") or "").strip()
    message = (request.form.get("message") or "").strip()

    tenant_username = (request.form.get("tenant_username") or "").strip()
    to_number = norm_phone(request.form.get("to_number") or "")

    conn = get_db()
    u = None
    if to_number:
        u = conn.execute(
            "SELECT * FROM users WHERE REPLACE(bizbot_number,' ','')=REPLACE(?,' ','') LIMIT 1",
            (to_number,),
        ).fetchone()
    elif tenant_username:
        u = conn.execute("SELECT * FROM users WHERE username=? LIMIT 1", (tenant_username,)).fetchone()
    else:
        u = conn.execute("SELECT * FROM users ORDER BY id ASC LIMIT 1").fetchone()
    conn.close()

    if not u:
        return "No tenant configured", 400

    # Optional: if billing configured, only accept web leads for active tenants
    if billing_is_configured() and not billing_active(u):
        return "Service inactive for this business", 403

    lead = find_lead_by_phone(int(u["id"]), phone) if phone else None
    if not lead:
        lead = create_lead(int(u["id"]), "web", phone=phone, name=name, email=email)

    update_lead(
        int(lead["id"]),
        last_inbound_utc=utc_now_iso(),
        service_needed=message or (lead.get("service_needed") or ""),
        name=name or (lead.get("name") or ""),
        email=email or (lead.get("email") or ""),
    )

    add_interaction(int(u["id"]), int(lead["id"]), "web", "inbound", message or "(web lead submitted)",
                    external_id="", meta={"name": name, "email": email})

    notify_owner(u, lead, f"New website lead: {name or phone}", message or "")

    return "OK", 200


# =========================================================
# NOTIFICATIONS (SendGrid) + SMS
# =========================================================
def notify_owner(user_row, lead_row, subject: str, message: str):
    try:
        add_interaction(int(user_row["id"]), int(lead_row["id"]), "system", "internal", f"{subject}\n{message}", meta={"notify": True})
    except Exception:
        pass

    if user_row.get("notify_email") and SENDGRID_API_KEY and SendGridAPIClient and Mail:
        try:
            sg = SendGridAPIClient(SENDGRID_API_KEY)
            mail = Mail(
                from_email=FROM_EMAIL,
                to_emails=user_row["notify_email"],
                subject=f"{APP_NAME}: {subject}",
                html_content=f"<p><b>{subject}</b></p><p>{message}</p><p>Lead: {(lead_row.get('name') or '')} {(lead_row.get('phone') or '')}</p>",
            )
            sg.send(mail)
        except Exception:
            print("SendGrid notify failed")
            traceback.print_exc()


def send_sms_for_user(user_row, to_number: str, body: str) -> Optional[str]:
    to_number = norm_phone(to_number)
    if not to_number:
        return None

    # block opt-outs at caller level is handled elsewhere; here only send
    client = twilio_client()
    from_number = user_row.get("bizbot_number") or ""

    kwargs = {"to": to_number, "body": body}

    if TWILIO_MESSAGING_SERVICE_SID:
        kwargs["messaging_service_sid"] = TWILIO_MESSAGING_SERVICE_SID
    else:
        if not from_number:
            raise RuntimeError("No BizBot number configured for outbound SMS.")
        kwargs["from_"] = from_number

    msg = client.messages.create(**kwargs)
    return getattr(msg, "sid", None)


# =========================================================
# TENANT RESOLUTION (incoming call/sms -> correct business)
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
# CALL SESSION HELPERS
# =========================================================
def update_call_session(call_sid: str, stage: str = None, data: dict = None, flags: dict = None, bump_step: bool = True):
    conn = get_db()
    row = conn.execute("SELECT * FROM call_sessions WHERE call_sid=?", (call_sid,)).fetchone()
    if not row:
        conn.close()
        return

    existing_data = safe_json(row.get("data_json"), {})
    existing_flags = safe_json(row.get("flags_json"), {})

    if isinstance(data, dict):
        existing_data.update(data)
    if isinstance(flags, dict):
        existing_flags.update(flags)

    new_stage = stage if stage is not None else (row.get("stage") or "root")
    step_count = int(row.get("step_count") or 0) + (1 if bump_step else 0)

    conn.execute(
        """
        UPDATE call_sessions
        SET stage=?, step_count=?, data_json=?, flags_json=?, updated_at_utc=?
        WHERE call_sid=?
        """,
        (new_stage, step_count, json.dumps(existing_data), json.dumps(existing_flags), utc_now_iso(), call_sid),
    )
    conn.commit()
    conn.close()


def finalize_intake(user_row, lead_id: int, data: dict, source: str):
    name = (data.get("name") or "").strip()
    callback = (data.get("callback") or "").strip()
    reason = (data.get("reason") or "").strip()
    preferred_time = (data.get("preferred_time") or "").strip()

    if callback:
        update_lead(lead_id, phone=callback)

    update_lead(
        lead_id,
        name=name,
        service_needed=reason,
        preferred_time=preferred_time,
        status="qualified",
        last_inbound_utc=utc_now_iso(),
    )

    add_interaction(int(user_row["id"]), int(lead_id), "system", "internal",
                    f"Intake captured ({source}): name={name}, reason={reason}, time={preferred_time}",
                    meta={"data": data})
    notify_owner(user_row, {"id": lead_id, "name": name, "phone": callback}, "Lead captured", f"{name} — {reason} — {preferred_time}")


# =========================================================
# TWILIO VOICE WEBHOOKS
# =========================================================
def tenant_service_active(user_row) -> bool:
    # If billing isn't configured, do not block (dev-friendly).
    if not billing_is_configured():
        return True
    return billing_active(user_row)


@app.route("/voice", methods=["POST"])
def voice():
    if TWILIO_AUTH_TOKEN and not validate_twilio_request():
        return ("Invalid signature", 403)

    call_sid = request.values.get("CallSid", "")
    from_number = request.values.get("From", "")
    to_number = request.values.get("To", "")

    vr = VoiceResponse()
    user = find_user_by_to_number(to_number)
    if not user:
        vr.say("This number is not linked to a business yet. Please call back later.")
        vr.hangup()
        return str(vr)

    if not tenant_service_active(user):
        vr.say("This service is currently inactive for this business. Please contact the business directly.")
        vr.hangup()
        return str(vr)

    # create/find lead
    lead = find_lead_by_phone(int(user["id"]), from_number)
    if not lead:
        lead = create_lead(int(user["id"]), "call", phone=from_number)

    update_lead(int(lead["id"]), last_inbound_utc=utc_now_iso())
    add_interaction(int(user["id"]), int(lead["id"]), "call", "inbound",
                    f"Incoming call started (CallSid {call_sid})",
                    external_id=call_sid, meta={"from": from_number, "to": to_number})

    # sessions
    conn = get_db()
    existing = conn.execute("SELECT * FROM call_sessions WHERE call_sid=?", (call_sid,)).fetchone()
    if not existing:
        conn.execute(
            """
            INSERT INTO call_sessions (call_sid, user_id, lead_id, stage, step_count, data_json, flags_json, created_at_utc, updated_at_utc)
            VALUES (?, ?, ?, 'root', 0, ?, ?, ?, ?)
            """,
            (
                call_sid,
                int(user["id"]),
                int(lead["id"]),
                json.dumps({}),
                json.dumps({"had_speech": False, "missed": False}),
                utc_now_iso(),
                utc_now_iso(),
            ),
        )
        conn.commit()
    conn.close()

    # after-hours
    if int(user.get("after_hours_enabled") or 0) == 1:
        vr.say(user.get("after_hours_message") or "We’re currently closed. Please leave a message.")
    else:
        vr.say(user.get("greeting") or template_greeting(user.get("business_name"), user.get("business_type")))

    action_url = f"{require_base_url()}/handle-input"
    gather = Gather(
        input="speech",
        action=action_url,
        method="POST",
        speechTimeout="auto",
        timeout=7,
    )
    gather.say("Please tell me what you need.")
    vr.append(gather)

    vr.say("Sorry, I didn’t catch that. Goodbye.")
    vr.hangup()
    return str(vr)


@app.route("/handle-input", methods=["POST"])
def handle_input():
    if TWILIO_AUTH_TOKEN and not validate_twilio_request():
        return ("Invalid signature", 403)

    call_sid = request.values.get("CallSid", "")
    from_number = request.values.get("From", "")
    to_number = request.values.get("To", "")

    # speech or digits
    speech = (request.values.get("SpeechResult") or "").strip()
    digits = (request.values.get("Digits") or "").strip()

    vr = VoiceResponse()
    user = find_user_by_to_number(to_number)
    if not user:
        vr.say("This number is not linked to a business yet.")
        vr.hangup()
        return str(vr)

    if not tenant_service_active(user):
        vr.say("This service is currently inactive for this business.")
        vr.hangup()
        return str(vr)

    conn = get_db()
    sess = conn.execute("SELECT * FROM call_sessions WHERE call_sid=?", (call_sid,)).fetchone()
    conn.close()

    if not sess:
        vr.say("Sorry, something went wrong. Please call back later.")
        vr.hangup()
        return str(vr)

    if int(sess.get("step_count") or 0) > MAX_CALL_STEPS:
        vr.say("Sorry, something went wrong. Please call back later.")
        vr.hangup()
        return str(vr)

    lead_id = int(sess["lead_id"])
    data = safe_json(sess.get("data_json"), {})
    flags = safe_json(sess.get("flags_json"), {"had_speech": False, "missed": False})
    stage = (sess.get("stage") or "root").strip()
    mode = (user.get("mode") or "message").strip().lower()

    # Determine input for this step
    step_input = speech
    if stage == "ask_callback" and digits:
        step_input = digits

    if not step_input:
        flags["missed"] = True
        update_call_session(call_sid, stage=stage, data=data, flags=flags, bump_step=True)
        bot = "Sorry, I didn’t catch that. Please call back, or we can text you a booking link."
        add_interaction(int(user["id"]), lead_id, "call", "internal", bot, external_id=call_sid, meta={"no_input": True})
        vr.say(bot)
        vr.hangup()
        return str(vr)

    flags["had_speech"] = True

    # escalation detection (speech only)
    escalation_keywords = (user.get("escalation_keywords") or default_escalation_keywords()).lower().split(",")
    is_urgent = bool(speech) and any(k.strip() and k.strip() in speech.lower() for k in escalation_keywords)

    # MESSAGE CAPTURE MODE
    if mode == "message":
        # Store inbound
        add_interaction(int(user["id"]), lead_id, "call", "inbound", step_input, external_id=call_sid, meta={"stage": stage})

        if stage == "root":
            data["reason"] = step_input
            update_call_session(call_sid, stage="ask_name", data=data, flags=flags)
            vr.say("Thanks. What’s your name?")
            action_url = f"{require_base_url()}/handle-input"
            g = Gather(input="speech", action=action_url, method="POST", speechTimeout="auto", timeout=7)
            g.say("Please say your name.")
            vr.append(g)
            vr.say("Goodbye.")
            return str(vr)

        elif stage == "ask_name":
            data["name"] = step_input
            update_call_session(call_sid, stage="ask_callback", data=data, flags=flags)
            vr.say("Thanks. Please enter your callback number on the keypad.")
            action_url = f"{require_base_url()}/handle-input"
            g = Gather(input="dtmf", action=action_url, method="POST", timeout=12, num_digits=10)
            g.say("Enter your 10 digit callback number now.")
            vr.append(g)
            vr.say("Goodbye.")
            return str(vr)

        elif stage == "ask_callback":
            # digits captured
            data["callback"] = step_input
            update_call_session(call_sid, stage="ask_time", data=data, flags=flags)
            vr.say("Got it. What’s a good time to call you back?")
            action_url = f"{require_base_url()}/handle-input"
            g = Gather(input="speech", action=action_url, method="POST", speechTimeout="auto", timeout=7)
            g.say("Please say a good time.")
            vr.append(g)
            vr.say("Goodbye.")
            return str(vr)

        elif stage == "ask_time":
            data["preferred_time"] = step_input
            update_call_session(call_sid, stage="done", data=data, flags=flags)
            finalize_intake(user, lead_id, data, source="call")
            vr.say("Perfect. We’ll get back to you soon. Goodbye.")
            vr.hangup()
            return str(vr)

        vr.say("Thanks for calling. Goodbye.")
        vr.hangup()
        return str(vr)

    # AI MODE
    lead_context = {"lead_id": lead_id, "phone": from_number, "stage": stage}
    bot = ai_compose_reply(user, "voice", step_input, lead_context=lead_context)

    add_interaction(int(user["id"]), lead_id, "call", "inbound", step_input, external_id=call_sid, meta={"stage": stage})
    add_interaction(int(user["id"]), lead_id, "call", "outbound", bot, external_id=call_sid, meta={"stage": "ai"})

    if is_urgent:
        bot = f"{bot} If this is urgent, say ‘urgent’ and we’ll arrange the fastest callback."

    vr.say(bot)
    action_url = f"{require_base_url()}/handle-input"
    g = Gather(input="speech", action=action_url, method="POST", speechTimeout="auto", timeout=7)
    g.say("Anything else?")
    vr.append(g)
    vr.say("Goodbye.")
    vr.hangup()
    return str(vr)


# =========================================================
# TWILIO STATUS CALLBACK (missed-call recovery trigger)
# =========================================================
@app.route("/status", methods=["POST"])
def status():
    if TWILIO_AUTH_TOKEN and not validate_twilio_request():
        return ("Invalid signature", 403)

    call_sid = request.values.get("CallSid", "")
    to_number = request.values.get("To", "")

    user = find_user_by_to_number(to_number)
    if not user:
        return ("", 204)

    if not tenant_service_active(user):
        return ("", 204)

    conn = get_db()
    sess = conn.execute("SELECT * FROM call_sessions WHERE call_sid=?", (call_sid,)).fetchone()
    conn.close()
    if not sess:
        return ("", 204)

    lead_id = int(sess["lead_id"])
    flags = safe_json(sess.get("flags_json"), {})
    had_speech = bool(flags.get("had_speech"))
    missed = bool(flags.get("missed"))

    if MISSED_CALL_SMS_ENABLED and (missed or not had_speech):
        conn = get_db()
        lead = conn.execute("SELECT * FROM leads WHERE id=? AND user_id=?", (lead_id, int(user["id"]))).fetchone()
        conn.close()
        if lead and lead.get("phone") and int(lead.get("opted_out") or 0) == 0:
            schedule_missed_call_recovery(user, lead, call_sid)

    return ("", 204)


def schedule_missed_call_recovery(user_row, lead_row, call_sid: str):
    if int(lead_row.get("opted_out") or 0) == 1:
        return

    last_out = lead_row.get("last_outbound_utc")
    if last_out:
        try:
            dt = datetime.fromisoformat(last_out.replace("Z", "+00:00"))
            if (utc_now() - dt) < timedelta(minutes=5):
                return
        except Exception:
            pass

    pb = get_latest_playbook(int(user_row["id"]))
    t1 = pb.get("sms_templates", {}).get("missed_call_1") if pb else None
    t2 = pb.get("sms_templates", {}).get("missed_call_2") if pb else None

    booking = (user_row.get("booking_link") or "").strip()

    msg1 = (t1 or "Sorry we missed you — reply with your name + what you need, and we’ll get back to you.")
    if booking:
        msg1 = f"{msg1} Book here: {booking}"

    payload1 = {"to": lead_row["phone"], "body": msg1, "reason": "missed_call_1", "call_sid": call_sid}
    schedule_job(int(user_row["id"]), int(lead_row["id"]), "sms_followup", utc_now_iso(), payload1)

    msg2 = (t2 or "Quick follow-up — still need help? Reply YES with the service + best time.")
    if booking:
        msg2 = f"{msg2} Booking: {booking}"

    payload2 = {"to": lead_row["phone"], "body": msg2, "reason": "missed_call_2", "call_sid": call_sid}
    schedule_job(int(user_row["id"]), int(lead_row["id"]), "sms_followup", now_plus_minutes(MISSED_CALL_FOLLOWUP_MINUTES), payload2)

    payload3 = {
        "to": lead_row["phone"],
        "body": "Last check-in — reply anytime and we’ll help you book.",
        "reason": "missed_call_3",
        "call_sid": call_sid,
    }
    schedule_job(int(user_row["id"]), int(lead_row["id"]), "sms_followup", now_plus_minutes(MISSED_CALL_FOLLOWUP2_MINUTES), payload3)


# =========================================================
# TWILIO SMS WEBHOOK
# =========================================================
@app.route("/sms", methods=["POST"])
def sms():
    if TWILIO_AUTH_TOKEN and not validate_twilio_request():
        return ("Invalid signature", 403)

    from_number = norm_phone(request.values.get("From", ""))
    to_number = norm_phone(request.values.get("To", ""))
    body = (request.values.get("Body", "") or "").strip()
    msg_sid = request.values.get("MessageSid", "")

    user = find_user_by_to_number(to_number)
    if not user:
        return ("", 204)

    if not tenant_service_active(user):
        # still must respond with TwiML, but keep it quiet
        return str(_sms_twiml("This service is currently inactive for this business."))

    lead = find_lead_by_phone(int(user["id"]), from_number)
    if not lead:
        lead = create_lead(int(user["id"]), "sms", phone=from_number)

    update_lead(int(lead["id"]), last_inbound_utc=utc_now_iso())
    add_interaction(int(user["id"]), int(lead["id"]), "sms", "inbound", body, external_id=msg_sid)

    upper = body.strip().upper()

    # STOP handling (persist)
    if upper in ("STOP", "UNSUBSCRIBE", "CANCEL", "END", "QUIT"):
        update_lead(int(lead["id"]), opted_out=1)
        add_interaction(int(user["id"]), int(lead["id"]), "system", "internal", "User opted out via STOP.", meta={"optout": True})
        return str(_sms_twiml("You’re unsubscribed. Reply START to rejoin."))

    # START re-subscribe
    if upper == "START":
        update_lead(int(lead["id"]), opted_out=0)
        return str(_sms_twiml("You’re re-subscribed. How can we help?"))

    # If opted out, ignore further conversation
    if int(lead.get("opted_out") or 0) == 1:
        return str(_sms_twiml("You’re unsubscribed. Reply START to rejoin."))

    if upper in ("HELP", "INFO"):
        return str(_sms_twiml(f"{APP_NAME}: Reply with what you need and we’ll help you book."))

    lead_ctx = {
        "lead_id": int(lead["id"]),
        "name": lead.get("name"),
        "phone": lead.get("phone"),
        "status": lead.get("status"),
    }
    reply = ai_compose_reply(user, "sms", body, lead_context=lead_ctx)

    add_interaction(int(user["id"]), int(lead["id"]), "sms", "outbound", reply, external_id="", meta={"ai": True})
    update_lead(int(lead["id"]), last_outbound_utc=utc_now_iso())

    return str(_sms_twiml(reply))


def _sms_twiml(message: str):
    from twilio.twiml.messaging_response import MessagingResponse
    resp = MessagingResponse()
    resp.message(message)
    return resp


# =========================================================
# JOB RUNNER (Render cron /jobs/tick)
# =========================================================
@app.route("/jobs/tick")
def jobs_tick():
    if JOBS_SHARED_SECRET:
        if (request.args.get("key") or "") != JOBS_SHARED_SECRET:
            return ("Forbidden", 403)

    now = utc_now_iso()
    conn = get_db()
    jobs = conn.execute(
        """
        SELECT * FROM jobs
        WHERE status='queued' AND run_at_utc <= ?
        ORDER BY id ASC
        LIMIT 25
        """,
        (now,),
    ).fetchall()
    conn.close()

    processed = 0
    for j in jobs:
        processed += 1
        try:
            payload = safe_json(j.get("payload_json"), {})
            if j.get("job_type") == "sms_followup":
                run_sms_job(j, payload)
            else:
                mark_job_done(int(j["id"]))
        except Exception as e:
            mark_job_failed(int(j["id"]), str(e))

    return {"ok": True, "processed": processed, "time_utc": now}


def run_sms_job(job_row, payload: dict):
    user_id = int(job_row["user_id"])
    lead_id = int(job_row["lead_id"])

    conn = get_db()
    u = conn.execute("SELECT * FROM users WHERE id=?", (user_id,)).fetchone()
    lead = conn.execute("SELECT * FROM leads WHERE id=? AND user_id=?", (lead_id, user_id)).fetchone()
    conn.close()

    if not u or not lead:
        mark_job_done(int(job_row["id"]))
        return

    if billing_is_configured() and not billing_active(u):
        mark_job_done(int(job_row["id"]))
        return

    if int(lead.get("opted_out") or 0) == 1:
        mark_job_done(int(job_row["id"]))
        return

    to = payload.get("to") or lead.get("phone")
    body = (payload.get("body") or "").strip()
    if not to or not body:
        mark_job_done(int(job_row["id"]))
        return

    sid = send_sms_for_user(u, to_number=to, body=body)
    add_interaction(user_id, lead_id, "sms", "outbound", body, external_id=sid or "", meta={"job": True, "reason": payload.get("reason")})
    update_lead(lead_id, last_outbound_utc=utc_now_iso())
    mark_job_done(int(job_row["id"]))


def mark_job_done(job_id: int):
    conn = get_db()
    conn.execute("UPDATE jobs SET status='done', updated_at_utc=? WHERE id=?", (utc_now_iso(), int(job_id)))
    conn.commit()
    conn.close()


def mark_job_failed(job_id: int, err: str):
    conn = get_db()
    conn.execute(
        "UPDATE jobs SET status='failed', last_error=?, attempts=COALESCE(attempts,0)+1, updated_at_utc=? WHERE id=?",
        (short(err, 500), utc_now_iso(), int(job_id)),
    )
    conn.commit()
    conn.close()


# =========================================================
# LOCAL RUN
# =========================================================
if __name__ == "__main__":
    ensure_db_ready()
    app.run(debug=True, host="127.0.0.1", port=5000)
