"""
app.py — Benzino Institutional Signal Engine Dashboard
Dashboard-only Streamlit app wired to Supabase scanner tables.

Reads background scanner output from:
  - scanner_signals
  - prop_firm_state
  - prop_firm_trades

Manages app-side user state in:
  - users
  - user_settings
  - user_watchlists
  - user_telegram_settings

The scanner remains the engine. This app is the dashboard, journal, coach,
Explain AI, watchlist manager, and settings console.
"""

from __future__ import annotations

import os
import base64
import re
import json
import html
import uuid
import hashlib
import secrets
import smtplib
import ssl
from email.message import EmailMessage
from datetime import datetime, timezone, timedelta
from zoneinfo import ZoneInfo
from urllib.parse import urlsplit, urlunsplit, parse_qsl, urlencode
from pathlib import Path

import numpy as np
import pandas as pd
import streamlit as st
import plotly.express as px
import plotly.graph_objects as go
import requests

try:
    from st_aggrid import AgGrid, GridOptionsBuilder, JsCode
except Exception:  # pragma: no cover
    AgGrid = None
    GridOptionsBuilder = None
    JsCode = None

try:
    import psycopg2
    from psycopg2.extras import RealDictCursor
except Exception:  # pragma: no cover
    psycopg2 = None
    RealDictCursor = None

# ═══════════════════════════════════════════════════════════════════════════════
# CONFIG
# ═══════════════════════════════════════════════════════════════════════════════

APP_VERSION = "v7.2-full-ui-cleanup"
BASE_DIR = Path(__file__).resolve().parent
ASSETS_DIR = BASE_DIR / "assets"
LOGO_PATH = ASSETS_DIR / "benzino_logo.png"


def image_to_data_uri(path: Path) -> str:
    """Load the Benzino logo from assets/ instead of embedding a huge Base64 string in app.py."""
    try:
        with open(path, "rb") as f:
            encoded = base64.b64encode(f.read()).decode("utf-8")
        return f"data:image/png;base64,{encoded}"
    except Exception:
        return ""


BRAND_LOGO_DATA_URI = image_to_data_uri(LOGO_PATH)
DEFAULT_TIMEZONE = "Africa/Nairobi"
ADMIN_USERNAMES = set()  # Admin is now assigned by database role: first created profile only.
VALID_GRADES = {"A+", "A", "B", "C"}
SIGNAL_TIMEFRAMES = ["All", "15m", "1h", "4h", "1d"]

ASSET_UNIVERSE = {
    "XAUUSD": {"name": "XAUUSD", "ticker": "GC=F", "group": "Commodities"},
    "XAGUSD": {"name": "XAGUSD", "ticker": "SI=F", "group": "Commodities"},
    "OIL": {"name": "OIL", "ticker": "CL=F", "group": "Commodities"},
    "BRENT": {"name": "BRENT", "ticker": "BZ=F", "group": "Commodities"},
    "NATGAS": {"name": "NATGAS", "ticker": "NG=F", "group": "Commodities"},
    "COPPER": {"name": "COPPER", "ticker": "HG=F", "group": "Commodities"},
    "EURUSD": {"name": "EURUSD", "ticker": "EURUSD=X", "group": "Forex Majors"},
    "GBPUSD": {"name": "GBPUSD", "ticker": "GBPUSD=X", "group": "Forex Majors"},
    "USDJPY": {"name": "USDJPY", "ticker": "JPY=X", "group": "Forex Majors"},
    "USDCHF": {"name": "USDCHF", "ticker": "CHF=X", "group": "Forex Majors"},
    "USDCAD": {"name": "USDCAD", "ticker": "CAD=X", "group": "Forex Majors"},
    "AUDUSD": {"name": "AUDUSD", "ticker": "AUDUSD=X", "group": "Forex Majors"},
    "NZDUSD": {"name": "NZDUSD", "ticker": "NZDUSD=X", "group": "Forex Majors"},
    "GBPJPY": {"name": "GBPJPY", "ticker": "GBPJPY=X", "group": "Forex Crosses"},
    "EURJPY": {"name": "EURJPY", "ticker": "EURJPY=X", "group": "Forex Crosses"},
    "AUDJPY": {"name": "AUDJPY", "ticker": "AUDJPY=X", "group": "Forex Crosses"},
    "NZDJPY": {"name": "NZDJPY", "ticker": "NZDJPY=X", "group": "Forex Crosses"},
    "CADJPY": {"name": "CADJPY", "ticker": "CADJPY=X", "group": "Forex Crosses"},
    "CHFJPY": {"name": "CHFJPY", "ticker": "CHFJPY=X", "group": "Forex Crosses"},
    "EURGBP": {"name": "EURGBP", "ticker": "EURGBP=X", "group": "Forex Crosses"},
    "EURAUD": {"name": "EURAUD", "ticker": "EURAUD=X", "group": "Forex Crosses"},
    "EURNZD": {"name": "EURNZD", "ticker": "EURNZD=X", "group": "Forex Crosses"},
    "EURCAD": {"name": "EURCAD", "ticker": "EURCAD=X", "group": "Forex Crosses"},
    "EURCHF": {"name": "EURCHF", "ticker": "EURCHF=X", "group": "Forex Crosses"},
    "GBPAUD": {"name": "GBPAUD", "ticker": "GBPAUD=X", "group": "Forex Crosses"},
    "GBPNZD": {"name": "GBPNZD", "ticker": "GBPNZD=X", "group": "Forex Crosses"},
    "GBPCAD": {"name": "GBPCAD", "ticker": "GBPCAD=X", "group": "Forex Crosses"},
    "GBPCHF": {"name": "GBPCHF", "ticker": "GBPCHF=X", "group": "Forex Crosses"},
    "AUDCAD": {"name": "AUDCAD", "ticker": "AUDCAD=X", "group": "Forex Crosses"},
    "AUDNZD": {"name": "AUDNZD", "ticker": "AUDNZD=X", "group": "Forex Crosses"},
    "AUDCHF": {"name": "AUDCHF", "ticker": "AUDCHF=X", "group": "Forex Crosses"},
    "NZDCAD": {"name": "NZDCAD", "ticker": "NZDCAD=X", "group": "Forex Crosses"},
    "NZDCHF": {"name": "NZDCHF", "ticker": "NZDCHF=X", "group": "Forex Crosses"},
    "BTCUSD": {"name": "BTCUSD", "ticker": "BTC-USD", "group": "Crypto"},
    "ETHUSD": {"name": "ETHUSD", "ticker": "ETH-USD", "group": "Crypto"},
    "SP500": {"name": "SP500", "ticker": "^GSPC", "group": "Indices"},
    "NAS100": {"name": "NAS100", "ticker": "^NDX", "group": "Indices"},
    "DOW30": {"name": "DOW30", "ticker": "^DJI", "group": "Indices"},
    "NVDA": {"name": "NVDA", "ticker": "NVDA", "group": "Equities"},
    "MU": {"name": "MU", "ticker": "MU", "group": "Equities"},
}
DEFAULT_ASSETS = ["XAUUSD", "GBPJPY", "BTCUSD", "EURUSD", "OIL"]

DEFAULT_SETTINGS = {
    "account_size": 10000.0,
    "leverage": 100,
    "risk_pct": 1.0,
    "preferred_timeframe": "1h",
    "view_timeframe": "1h",
    "display_timezone": DEFAULT_TIMEZONE,
    "tracking_started_at": "",
    "selected_asset_keys": DEFAULT_ASSETS,
    "telegram_chat_ids": "",
    "telegram_watchlist_enabled": True,
    "telegram_all_signals_enabled": False,
}

# ═══════════════════════════════════════════════════════════════════════════════
# DATABASE
# ═══════════════════════════════════════════════════════════════════════════════

def get_secret_value(key: str, fallback: str = "") -> str:
    try:
        v = st.secrets.get(key, None)
        if v not in (None, ""):
            return str(v).strip()
    except Exception:
        pass
    try:
        for section in ("database", "postgres", "supabase", "connections"):
            block = st.secrets.get(section, None)
            if isinstance(block, dict):
                for nested_key in (key, key.lower(), "url", "uri", "connection_string"):
                    v = block.get(nested_key, None)
                    if v not in (None, ""):
                        return str(v).strip()
    except Exception:
        pass
    return os.getenv(key, fallback).strip()


def first_secret(*keys: str, fallback: str = "") -> str:
    for key in keys:
        value = get_secret_value(key, "")
        if value:
            return value
    return fallback


DATABASE_URL = first_secret(
    "CLOUD_DATABASE_URL",
    "DATABASE_URL",
    "SUPABASE_DATABASE_URL",
    "SUPABASE_DB_URL",
    "POSTGRES_DATABASE_URL",
    "POSTGRES_URL",
)


def clean_database_url(url: str) -> str:
    url = str(url or "").strip()
    if not url:
        return ""
    if url.startswith("postgres://"):
        url = "postgresql://" + url[len("postgres://"):]
    parts = urlsplit(url)
    allowed = {
        "sslmode", "connect_timeout", "application_name", "target_session_attrs",
        "keepalives", "keepalives_idle", "keepalives_interval", "keepalives_count",
    }
    pairs = [(k, v) for k, v in parse_qsl(parts.query, keep_blank_values=True) if k in allowed]
    if "supabase" in parts.netloc.lower() and not any(k == "sslmode" for k, _ in pairs):
        pairs.append(("sslmode", "require"))
    return urlunsplit((parts.scheme, parts.netloc, parts.path, urlencode(pairs), parts.fragment))


def db_connect():
    if not DATABASE_URL:
        raise RuntimeError("DATABASE_URL / CLOUD_DATABASE_URL is not configured.")
    if psycopg2 is None:
        raise RuntimeError("psycopg2-binary is not installed.")
    return psycopg2.connect(clean_database_url(DATABASE_URL), cursor_factory=RealDictCursor)


def execute(sql: str, params: tuple = ()) -> None:
    conn = db_connect()
    try:
        with conn:
            with conn.cursor() as cur:
                cur.execute(sql, params)
    finally:
        conn.close()


def read_df(sql: str, params: tuple = ()) -> pd.DataFrame:
    conn = db_connect()
    try:
        with conn.cursor() as cur:
            cur.execute(sql, params)
            rows = cur.fetchall()
        return pd.DataFrame([dict(r) for r in rows])
    except Exception as exc:
        st.warning(f"Database read failed: {exc}")
        return pd.DataFrame()
    finally:
        conn.close()


def init_tables() -> None:
    ddl = """
    CREATE TABLE IF NOT EXISTS users (
        username TEXT PRIMARY KEY,
        email TEXT,
        password_hash TEXT NOT NULL,
        salt TEXT NOT NULL,
        created_at TEXT NOT NULL,
        role TEXT NOT NULL DEFAULT 'user'
    );
    CREATE TABLE IF NOT EXISTS remember_tokens (
        token_hash TEXT PRIMARY KEY,
        username TEXT NOT NULL,
        created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
        expires_at TIMESTAMPTZ NOT NULL,
        last_used_at TIMESTAMPTZ
    );
    CREATE INDEX IF NOT EXISTS idx_remember_tokens_username
        ON remember_tokens(username);
    CREATE TABLE IF NOT EXISTS user_settings (
        username TEXT PRIMARY KEY,
        settings_json TEXT NOT NULL,
        updated_at TEXT NOT NULL
    );
    CREATE TABLE IF NOT EXISTS user_watchlists (
        scan_owner TEXT NOT NULL,
        asset TEXT NOT NULL,
        ticker TEXT NOT NULL,
        enabled BOOLEAN DEFAULT TRUE,
        created_at TIMESTAMPTZ DEFAULT NOW(),
        PRIMARY KEY (scan_owner, asset)
    );
    CREATE TABLE IF NOT EXISTS user_telegram_settings (
        scan_owner TEXT PRIMARY KEY,
        telegram_chat_id TEXT,
        alerts_enabled BOOLEAN DEFAULT FALSE,
        watchlist_alerts BOOLEAN DEFAULT TRUE,
        all_signals_alerts BOOLEAN DEFAULT FALSE,
        updated_at TIMESTAMPTZ DEFAULT NOW()
    );
    CREATE TABLE IF NOT EXISTS scanner_signals (
        signal_id TEXT PRIMARY KEY,
        created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
        scan_owner TEXT,
        asset TEXT,
        ticker TEXT,
        timeframe TEXT,
        signal TEXT,
        grade TEXT,
        confidence NUMERIC,
        edge_score NUMERIC,
        ml_prob NUMERIC,
        entry NUMERIC,
        sl NUMERIC,
        tp NUMERIC,
        rr NUMERIC,
        regime TEXT,
        rsi NUMERIC,
        atr NUMERIC,
        trend_1h TEXT,
        trend_15m TEXT,
        reason TEXT,
        candle_close TIMESTAMPTZ,
        strategy_votes JSONB,
        mtf_score NUMERIC,
        mtf_context JSONB,
        alert_sent BOOLEAN DEFAULT FALSE,
        status TEXT DEFAULT 'SHADOW',
        bars_open INTEGER DEFAULT 0,
        exit_price NUMERIC,
        exit_reason TEXT,
        exit_at TIMESTAMPTZ,
        r_multiple NUMERIC,
        shadow_outcome TEXT,
        shadow_r_multiple NUMERIC,
        shadow_exit_price NUMERIC,
        shadow_closed_at TIMESTAMPTZ
    );
    CREATE TABLE IF NOT EXISTS scanner_runtime_log (
        run_id TEXT PRIMARY KEY,
        started_at TIMESTAMPTZ,
        finished_at TIMESTAMPTZ,
        total_seconds NUMERIC,
        assets_scanned INTEGER,
        signals_saved INTEGER,
        shadow_saved INTEGER,
        open_trades INTEGER,
        alerted INTEGER,
        timeframes_scanned TEXT,
        fastest_asset_seconds NUMERIC,
        slowest_asset_seconds NUMERIC,
        avg_asset_seconds NUMERIC,
        created_at TIMESTAMPTZ DEFAULT NOW()
    );

    CREATE TABLE IF NOT EXISTS prop_firm_state (
        scan_owner TEXT PRIMARY KEY,
        starting_balance NUMERIC,
        current_equity NUMERIC,
        daily_pnl NUMERIC DEFAULT 0,
        daily_reset_date DATE,
        trading_days INTEGER DEFAULT 0,
        status TEXT DEFAULT 'ACTIVE',
        updated_at TIMESTAMPTZ DEFAULT NOW()
    );
    CREATE TABLE IF NOT EXISTS prop_firm_trades (
        trade_id TEXT PRIMARY KEY,
        signal_id TEXT REFERENCES scanner_signals(signal_id),
        scan_owner TEXT,
        asset TEXT,
        grade TEXT,
        r_multiple NUMERIC,
        pnl_cash NUMERIC,
        closed_at TIMESTAMPTZ DEFAULT NOW()
    );
    """
    conn = db_connect()
    try:
        with conn:
            with conn.cursor() as cur:
                cur.execute(ddl)
                cur.execute("ALTER TABLE users ADD COLUMN IF NOT EXISTS role TEXT NOT NULL DEFAULT 'user'")
                cur.execute("ALTER TABLE users ADD COLUMN IF NOT EXISTS email TEXT")
                cur.execute("ALTER TABLE user_telegram_settings ADD COLUMN IF NOT EXISTS alerts_enabled BOOLEAN DEFAULT FALSE")
                cur.execute("ALTER TABLE user_telegram_settings ADD COLUMN IF NOT EXISTS updated_at TIMESTAMPTZ DEFAULT NOW()")
                # Admin policy: the earliest account becomes the only admin.
                # Every later profile remains a normal user, regardless of username.
                cur.execute("""
                    UPDATE users
                    SET role = 'admin'
                    WHERE username = (
                        SELECT username FROM users ORDER BY created_at ASC LIMIT 1
                    )
                    AND NOT EXISTS (SELECT 1 FROM users WHERE role = 'admin')
                """)
                cur.execute("""
                    UPDATE users
                    SET role = 'user'
                    WHERE role = 'admin'
                      AND username <> (SELECT username FROM users ORDER BY created_at ASC LIMIT 1)
                """)
                cur.execute("ALTER TABLE scanner_signals ADD COLUMN IF NOT EXISTS mtf_score NUMERIC")
                cur.execute("ALTER TABLE scanner_signals ADD COLUMN IF NOT EXISTS mtf_context JSONB")
                cur.execute("ALTER TABLE scanner_signals ADD COLUMN IF NOT EXISTS shadow_closed_at TIMESTAMPTZ")
                cur.execute("ALTER TABLE scanner_signals ADD COLUMN IF NOT EXISTS shadow_exit_price NUMERIC")
                cur.execute("ALTER TABLE scanner_signals ADD COLUMN IF NOT EXISTS shadow_r_multiple NUMERIC")
                cur.execute("ALTER TABLE scanner_signals ADD COLUMN IF NOT EXISTS shadow_outcome TEXT")
                # Migration/fix: Telegram delivery must never control journal status.
                # A+/A/B/C BUY/SELL setups are active journal trades; NO TRADE/HOLD stays SHADOW.
                cur.execute(
                    """
                    UPDATE scanner_signals
                    SET status = 'OPEN'
                    WHERE grade IN ('A+', 'A', 'B', 'C')
                      AND signal IN ('BUY', 'SELL')
                      AND COALESCE(status, 'SHADOW') = 'SHADOW'
                      AND exit_at IS NULL
                    """
                )
    finally:
        conn.close()

# ═══════════════════════════════════════════════════════════════════════════════
# AUTH / SETTINGS
# ═══════════════════════════════════════════════════════════════════════════════

def normalize_username(username: str) -> str:
    username = str(username or "").strip().lower()
    username = re.sub(r"[^a-z0-9_\-.]", "", username)
    return username[:40]


def generate_salt() -> str:
    return os.urandom(32).hex()


def hash_password(password: str, salt: str) -> str:
    return hashlib.pbkdf2_hmac(
        "sha256", str(password).encode(), str(salt).encode(), iterations=260_000
    ).hex()


def normalize_email(email: str) -> str:
    return str(email or "").strip().lower()[:254]


def create_user(username: str, password: str, email: str = "") -> tuple[bool, str]:
    username = normalize_username(username)
    email = normalize_email(email)
    if len(username) < 2:
        return False, "Use at least 2 characters for username."
    if email and not re.match(r"^[^@\s]+@[^@\s]+\.[^@\s]+$", email):
        return False, "Enter a valid email address."
    if len(password) < 4:
        return False, "Use at least 4 characters for PIN/password."

    created_at = datetime.now(timezone.utc).isoformat()
    settings = DEFAULT_SETTINGS.copy()
    settings["tracking_started_at"] = created_at
    salt = generate_salt()
    pw_hash = hash_password(password, salt)

    try:
        conn = db_connect()
        with conn:
            with conn.cursor() as cur:
                cur.execute("SELECT COUNT(*) AS user_count FROM users")
                count_row = cur.fetchone()
                existing_users = int(count_row.get("user_count", 0) if isinstance(count_row, dict) else count_row[0])
                role = "admin" if existing_users == 0 else "user"
                cur.execute(
                    "INSERT INTO users(username, email, password_hash, salt, created_at, role) VALUES (%s,%s,%s,%s,%s,%s)",
                    (username, email, pw_hash, salt, created_at, role),
                )
                cur.execute(
                    "INSERT INTO user_settings(username, settings_json, updated_at) VALUES (%s,%s,%s)",
                    (username, json.dumps(settings), created_at),
                )
                for asset in DEFAULT_ASSETS:
                    meta = ASSET_UNIVERSE[asset]
                    cur.execute(
                        """
                        INSERT INTO user_watchlists(scan_owner, asset, ticker, enabled)
                        VALUES (%s,%s,%s,TRUE)
                        ON CONFLICT (scan_owner, asset) DO UPDATE
                        SET ticker = EXCLUDED.ticker, enabled = TRUE
                        """,
                        (username, asset, meta["ticker"]),
                    )
        conn.close()
        return True, "Account created."
    except Exception as exc:
        msg = str(exc).lower()
        if "duplicate" in msg or "unique" in msg:
            return False, "That username already exists."
        return False, f"Could not create account: {exc}"


def validate_login(username: str, password: str) -> bool:
    username = normalize_username(username)
    df = read_df("SELECT password_hash, salt FROM users WHERE username = %s", (username,))
    if df.empty:
        return False
    return hash_password(password, str(df.iloc[0]["salt"])) == str(df.iloc[0]["password_hash"])


def remember_token_hash(token: str) -> str:
    return hashlib.sha256(str(token or "").encode("utf-8")).hexdigest()


def create_remember_token(username: str, days: int = 30) -> str:
    """Create a persistent login token and store only its hash in Supabase."""
    username = normalize_username(username)
    token = secrets.token_urlsafe(48)
    token_hash = remember_token_hash(token)
    expires_at = (datetime.now(timezone.utc) + timedelta(days=days)).isoformat()
    try:
        execute(
            """
            INSERT INTO remember_tokens(token_hash, username, expires_at)
            VALUES (%s,%s,%s)
            """,
            (token_hash, username, expires_at),
        )
    except Exception:
        # If a deployed DB has not run init_tables yet, create the table lazily once.
        try:
            execute(
                """
                CREATE TABLE IF NOT EXISTS remember_tokens (
                    token_hash TEXT PRIMARY KEY,
                    username TEXT NOT NULL,
                    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
                    expires_at TIMESTAMPTZ NOT NULL,
                    last_used_at TIMESTAMPTZ
                )
                """
            )
            execute(
                "CREATE INDEX IF NOT EXISTS idx_remember_tokens_username ON remember_tokens(username)"
            )
            execute(
                """
                INSERT INTO remember_tokens(token_hash, username, expires_at)
                VALUES (%s,%s,%s)
                """,
                (token_hash, username, expires_at),
            )
        except Exception:
            return ""
    return token


def username_from_remember_token(token: str) -> str:
    """Return username for a valid remember-me token, otherwise blank."""
    token = str(token or "").strip()
    if not token:
        return ""
    token_hash = remember_token_hash(token)
    try:
        df = read_df(
            """
            SELECT username
            FROM remember_tokens
            WHERE token_hash = %s
              AND expires_at > NOW()
            LIMIT 1
            """,
            (token_hash,),
        )
        if df.empty:
            return ""
        username = normalize_username(df.iloc[0].get("username", ""))
        if username:
            execute(
                "UPDATE remember_tokens SET last_used_at = NOW() WHERE token_hash = %s",
                (token_hash,),
            )
        return username
    except Exception:
        return ""


def revoke_remember_token(token: str) -> None:
    token = str(token or "").strip()
    if not token:
        return
    try:
        execute("DELETE FROM remember_tokens WHERE token_hash = %s", (remember_token_hash(token),))
    except Exception:
        pass


def get_query_param_value(key: str, default: str = "") -> str:
    try:
        value = st.query_params.get(key, default)
        if isinstance(value, list):
            return str(value[0] if value else default)
        return str(value if value is not None else default)
    except Exception:
        return default


def set_auth_mode(mode: str) -> None:
    st.session_state.auth_mode = mode
    try:
        # Keep everything on the same Streamlit page. We do not use href links
        # for auth navigation because browsers may open them as a new page/tab.
        if "auth_mode" in st.query_params:
            del st.query_params["auth_mode"]
    except Exception:
        pass


def smtp_configured() -> bool:
    return bool(get_secret_value("SMTP_HOST") and get_secret_value("SMTP_USERNAME") and get_secret_value("SMTP_PASSWORD"))


def send_reset_email(to_email: str, username: str, temporary_password: str) -> tuple[bool, str]:
    """Send a temporary password using SMTP secrets.

    Required Streamlit/GitHub secrets:
      SMTP_HOST, SMTP_PORT, SMTP_USERNAME, SMTP_PASSWORD, SMTP_FROM_EMAIL
    Optional:
      SMTP_USE_SSL=true/false
    """
    to_email = normalize_email(to_email)
    if not to_email:
        return False, "No email address is saved for this user."

    host = get_secret_value("SMTP_HOST")
    port = int(get_secret_value("SMTP_PORT", "587") or 587)
    user = get_secret_value("SMTP_USERNAME")
    password = get_secret_value("SMTP_PASSWORD")
    from_email = get_secret_value("SMTP_FROM_EMAIL", user)
    use_ssl = get_secret_value("SMTP_USE_SSL", "false").lower() in {"1", "true", "yes", "y"}
    if not host or not user or not password:
        return False, "SMTP is not configured yet. Add SMTP_HOST, SMTP_USERNAME, SMTP_PASSWORD and SMTP_FROM_EMAIL to secrets."

    msg = EmailMessage()
    msg["Subject"] = "Benzino password reset"
    msg["From"] = from_email
    msg["To"] = to_email
    msg.set_content(
        f"Hello {username},\n\n"
        f"Your Benzino temporary password is: {temporary_password}\n\n"
        "Log in with this password, then change it from Settings.\n\n"
        "If you did not request this reset, contact the admin immediately.\n"
    )
    try:
        if use_ssl:
            with smtplib.SMTP_SSL(host, port, context=ssl.create_default_context(), timeout=20) as server:
                server.login(user, password)
                server.send_message(msg)
        else:
            with smtplib.SMTP(host, port, timeout=20) as server:
                server.starttls(context=ssl.create_default_context())
                server.login(user, password)
                server.send_message(msg)
        return True, "Reset password sent to the saved email address."
    except Exception as exc:
        return False, f"Email send failed: {exc}"


def reset_password_by_email(username_or_email: str) -> tuple[bool, str]:
    lookup = str(username_or_email or "").strip().lower()
    if not lookup:
        return False, "Enter your username or saved email address."
    df = read_df("SELECT username, email FROM users WHERE username = %s OR email = %s", (normalize_username(lookup), normalize_email(lookup)))
    if df.empty:
        return False, "No matching user was found."
    username = str(df.iloc[0]["username"])
    email = normalize_email(df.iloc[0].get("email", ""))
    if not email:
        return False, "This profile has no saved email address. Ask the admin to update it."
    temporary_password = secrets.token_urlsafe(8)
    salt = generate_salt()
    pw_hash = hash_password(temporary_password, salt)
    execute("UPDATE users SET password_hash = %s, salt = %s WHERE username = %s", (pw_hash, salt, username))
    ok, msg = send_reset_email(email, username, temporary_password)
    if not ok:
        return False, msg
    return True, msg


def change_user_password(username: str, current_password: str, new_password: str) -> tuple[bool, str]:
    username = normalize_username(username)
    if not validate_login(username, current_password):
        return False, "Current password is incorrect."
    if len(new_password or "") < 4:
        return False, "Use at least 4 characters for the new password."
    salt = generate_salt()
    pw_hash = hash_password(new_password, salt)
    execute("UPDATE users SET password_hash = %s, salt = %s WHERE username = %s", (pw_hash, salt, username))
    return True, "Password changed."


def update_user_email(username: str, email: str) -> tuple[bool, str]:
    email = normalize_email(email)
    if email and not re.match(r"^[^@\s]+@[^@\s]+\.[^@\s]+$", email):
        return False, "Enter a valid email address."
    execute("UPDATE users SET email = %s WHERE username = %s", (email, normalize_username(username)))
    return True, "Email updated."


def active_username() -> str:
    return normalize_username(st.session_state.get("auth_user", ""))


def is_admin() -> bool:
    username = active_username()
    if not username:
        return False
    df = read_df("SELECT role FROM users WHERE username = %s", (username,))
    if df.empty:
        return False
    return str(df.iloc[0].get("role", "user")).lower() == "admin"


def user_role(username: str) -> str:
    df = read_df("SELECT role FROM users WHERE username = %s", (normalize_username(username),))
    if df.empty:
        return "user"
    role = str(df.iloc[0].get("role", "user")).lower()
    return "admin" if role == "admin" else "user"


def load_settings(username: str) -> dict:
    settings = DEFAULT_SETTINGS.copy()
    df = read_df("SELECT settings_json FROM user_settings WHERE username = %s", (username,))
    if not df.empty:
        try:
            loaded = json.loads(df.iloc[0]["settings_json"])
            if isinstance(loaded, dict):
                settings.update(loaded)
        except Exception:
            pass
    if not settings.get("tracking_started_at"):
        users = read_df("SELECT created_at FROM users WHERE username = %s", (username,))
        settings["tracking_started_at"] = users.iloc[0]["created_at"] if not users.empty else datetime.now(timezone.utc).isoformat()
        save_settings(username, settings)
    return settings


def save_settings(username: str, settings: dict) -> None:
    execute(
        """
        INSERT INTO user_settings(username, settings_json, updated_at)
        VALUES (%s,%s,%s)
        ON CONFLICT (username) DO UPDATE
        SET settings_json = EXCLUDED.settings_json, updated_at = EXCLUDED.updated_at
        """,
        (username, json.dumps(settings), datetime.now(timezone.utc).isoformat()),
    )


def render_auth_gate() -> None:
    if st.session_state.get("auth_user"):
        return

    remembered_token = get_query_param_value("remember_token", "")
    remembered_username = username_from_remember_token(remembered_token)
    if remembered_username:
        st.session_state.auth_user = remembered_username
        st.rerun()

    # Login-only layout: no sidebar, no top blank panel, one centered two-column card.
    st.markdown(
        """
        <style>
        html, body, #root, .stApp, [data-testid="stAppViewContainer"], [data-testid="stMain"] {
            height: 100vh !important;
            max-height: 100vh !important;
            overflow: hidden !important;
        }
        header, [data-testid="stToolbar"], [data-testid="stSidebar"], [data-testid="collapsedControl"] { display:none !important; }
        [data-testid="stAppViewContainer"] > .main, section.main {
            margin-left:0 !important;
            height:100vh !important;
            max-height:100vh !important;
            overflow:hidden !important;
        }
        [data-testid="stAppViewContainer"] > .main .block-container, [data-testid="stMainBlockContainer"] {
            max-width: 1480px !important;
            padding-top: 0 !important;
            padding-bottom: 0 !important;
            padding-left: 6vw !important;
            padding-right: 6vw !important;
            min-height: 100vh !important;
            height: 100vh !important;
            max-height: 100vh !important;
            overflow: hidden !important;
            display: flex !important;
            align-items: center !important;
            justify-content: center !important;
        }
        [data-testid="stMainBlockContainer"] > div {
            width: 100% !important;
        }
        div[data-testid="stHorizontalBlock"]:has(.benzino-login-left-exact) {
            height: min(720px, calc(100vh - 48px));
            min-height: 0;
            border: 1px solid #244363;
            border-radius: 18px;
            overflow: hidden;
            background: radial-gradient(circle at 50% 0%, rgba(16,38,58,.45), rgba(7,17,31,.88));
            box-shadow: 0 28px 80px rgba(0,0,0,.34);
        }
        div[data-testid="stHorizontalBlock"]:has(.benzino-login-left-exact) > div:first-child {
            border-right: 1px solid #244363;
            display: flex;
            align-items: center;
            justify-content: center;
            padding: 34px 34px !important;
        }
        div[data-testid="stHorizontalBlock"]:has(.benzino-login-left-exact) > div:nth-child(2) {
            display: flex;
            align-items: center;
            justify-content: center;
            padding: 34px 44px !important;
        }
        div[data-testid="stHorizontalBlock"]:has(.benzino-login-left-exact) > div:nth-child(2) [data-testid="stVerticalBlock"] {
            max-width: 650px;
            margin: 0 auto;
        }
        .benzino-login-left-exact { text-align:center; width:100%; }
        .benzino-login-logo-exact {
            width:min(430px, 32vw);
            max-width:100%;
            height:auto;
            image-rendering:auto;
            border-radius: 0;
            border: 0;
            box-shadow:none;
            display:block;
            margin:0 auto 34px;
        }
        .benzino-login-tagline-exact {
            color:#E8EDF2;
            font-size:22px;
            font-weight:800;
            line-height:1.38;
            margin-top:20px;
            text-align:center;
        }
        .benzino-login-note-exact {
            color:#8BAAB8;
            font-size:16px;
            font-weight:850;
            margin-top:18px;
            text-align:center;
        }
        .benzino-login-head-exact {
            text-align:center;
            margin:0 0 26px;
        }
        .benzino-login-title-exact {
            color:#E8EDF2;
            font-size:30px;
            font-weight:950;
            line-height:1.1;
            margin-bottom:12px;
        }
        .benzino-login-sub-exact {
            color:#8BAAB8;
            font-size:18px;
            font-weight:850;
        }
        
        .benzino-signin-loading {
            display:flex;
            align-items:center;
            justify-content:center;
            gap:10px;
            margin-top:14px;
            color:#8BAAB8;
            font-size:14px;
            font-weight:800;
        }
        .benzino-signin-spinner {
            width:16px;
            height:16px;
            border:2px solid rgba(139,170,184,.25);
            border-top:2px solid #00D4A3;
            border-radius:50%;
            animation: benzino-spin 0.9s linear infinite;
        }
        @keyframes benzino-spin {
            from { transform: rotate(0deg); }
            to { transform: rotate(360deg); }
        }

.benzino-login-footer-exact {
            text-align:center;
            color:#8BAAB8;
            font-size:14px;
            font-weight:850;
            margin:26px 0 10px;
        }
        .benzino-login-footer-exact a,
        .benzino-login-footer-exact span {
            color:#00D4A3;
            margin-left:8px;
            font-weight:950;
            text-decoration:none;
        }
        .benzino-login-link-exact {
            color:#00D4A3 !important;
            font-size:14px;
            font-weight:950;
            text-decoration:none !important;
        }
        .benzino-login-link-exact:hover,
        .benzino-login-footer-exact a:hover {
            color:#00D4A3 !important;
            text-decoration:none !important;
        }
        div[data-testid="stHorizontalBlock"]:has(.benzino-login-left-exact) button[kind="secondary"] {
            background: transparent !important;
            border: 0 !important;
            color: #00D4A3 !important;
            padding: 0 !important;
            min-height: 18px !important;
            height: 18px !important;
            font-size:14px !important;
            font-weight:950 !important;
            box-shadow:none !important;
            line-height:1 !important;
            margin:0 !important;
        }
        div[data-testid="stHorizontalBlock"]:has(.benzino-login-left-exact) button[kind="secondary"] p {
            color: #00D4A3 !important;
            font-size:14px !important;
            font-weight:950 !important;
            line-height:1 !important;
            margin:0 !important;
            white-space: nowrap !important;
        }
        div[data-testid="stHorizontalBlock"]:has(.benzino-login-left-exact) button[kind="secondary"] {
            width: 100% !important;
            min-width: 0 !important;
            white-space: nowrap !important;
            display: flex !important;
            justify-content: flex-end !important;
            align-items: center !important;
            text-align: right !important;
            padding-right: 0 !important;
            margin-left: auto !important;
        }

        div[data-testid="stHorizontalBlock"]:has(.benzino-login-left-exact) button[kind="secondary"] > div {
            width: 100% !important;
            display: flex !important;
            justify-content: flex-end !important;
        }
        div[data-testid="stHorizontalBlock"]:has(.benzino-login-left-exact) button[kind="secondary"]:hover {
            color:#00D4A3 !important;
            background: transparent !important;
            border: 0 !important;
        }
        .benzino-inline-footer-row {
            display:flex;
            align-items:center;
            justify-content:center;
            gap:10px;
            margin:26px 0 10px;
            color:#8BAAB8;
            font-size:14px;
            font-weight:850;
        }
        .benzino-auth-link-slot {
            display:flex;
            align-items:center;
            justify-content:flex-start;
            height:24px;
            margin-top:26px;
        }
        div[data-testid="stHorizontalBlock"]:has(.benzino-login-left-exact) input {
            height: 44px !important;
            min-height: 44px !important;
            padding: 8px 14px !important;
            line-height: 1.2 !important;
            box-sizing: border-box !important;
            background:#10263A !important;
            border:1px solid #244363 !important;
            border-radius:10px !important;
            color:#E8EDF2 !important;
            font-size:15px !important;
            outline:none !important;
            box-shadow:none !important;
        }
        div[data-testid="stHorizontalBlock"]:has(.benzino-login-left-exact) input:focus,
        div[data-testid="stHorizontalBlock"]:has(.benzino-login-left-exact) input:focus-visible,
        div[data-testid="stHorizontalBlock"]:has(.benzino-login-left-exact) [data-baseweb="input"]:focus-within,
        div[data-testid="stHorizontalBlock"]:has(.benzino-login-left-exact) [data-baseweb="input"]:has(input:focus) {
            border-color:#00D4A3 !important;
            outline:none !important;
            box-shadow:0 0 0 1px rgba(0,212,163,.35) inset !important;
        }
        div[data-testid="stHorizontalBlock"]:has(.benzino-login-left-exact) [data-baseweb="input"] {
            height: 44px !important;
            min-height: 44px !important;
            border-radius:10px !important;
            overflow:hidden !important;
        }
        div[data-testid="stHorizontalBlock"]:has(.benzino-login-left-exact) [data-baseweb="input"] > div {
            height: 44px !important;
            min-height: 44px !important;
            align-items:center !important;
        }
        div[data-testid="stHorizontalBlock"]:has(.benzino-login-left-exact) button[kind="primary"] {
            min-height: 50px !important;
            border-radius:10px !important;
            font-size:18px !important;
            font-weight:900 !important;
            background:linear-gradient(90deg,#0CB98E,#00C896) !important;
            border-color:#00D4A3 !important;
            color:#FFFFFF !important;
        }
        @media (max-width: 900px) {
            div[data-testid="stHorizontalBlock"]:has(.benzino-login-left-exact) { min-height:auto; }
            div[data-testid="stHorizontalBlock"]:has(.benzino-login-left-exact) > div:first-child { border-right:0; border-bottom:1px solid #244363; }
            .benzino-login-logo-exact { width:min(420px, 80vw); }
        }

    .modebar, .modebar-container { display:none !important; }
</style>
        """,
        unsafe_allow_html=True,
    )

    auth_mode = str(st.session_state.get("auth_mode", "login") or "login").lower()
    if auth_mode not in {"login", "create", "reset"}:
        auth_mode = "login"
        st.session_state.auth_mode = "login"

    left, right = st.columns([1, 1.05], gap="large", vertical_alignment="center")

    with left:
        st.markdown(
            f"""
            <div class='benzino-login-left-exact'>
                <img class='benzino-login-logo-exact' src='{BRAND_LOGO_DATA_URI}' alt='Benzino logo'>
                <div class='benzino-login-tagline-exact'>Institutional-Grade Analysis.<br>Retail-Accessible Edge.</div>
                <div class='benzino-login-note-exact'>Data. Discipline. Edge. All in one engine.</div>
            </div>
            """,
            unsafe_allow_html=True,
        )

    with right:
        if auth_mode == "login":
            if st.session_state.get("login_loading", False):
                st.markdown(
                    "<div class='benzino-signin-loading'><div class='benzino-signin-spinner'></div><span>Signing you in shortly...</span></div>",
                    unsafe_allow_html=True,
                )

            st.markdown(
                """
                <div class='benzino-login-head-exact'>
                  <div class='benzino-login-title-exact'>Welcome Back</div>
                  <div class='benzino-login-sub-exact'>Sign in to access your dashboard</div>
                </div>
                """,
                unsafe_allow_html=True,
            )

            username = st.text_input("Username", placeholder="Enter your username", key="login_user")
            password = st.text_input("Password", placeholder="Enter your password", type="password", key="login_pass")

            remember_col, forgot_col = st.columns([1, 1])
            with remember_col:
                st.checkbox("Remember me", key="remember_me")
            with forgot_col:
                st.markdown("<div style='height:8px;'></div>", unsafe_allow_html=True)
                _forgot_spacer, _forgot_button = st.columns([0.55, 0.45])
                with _forgot_button:
                    if st.button("Forgot password?", key="forgot_password_link"):
                        set_auth_mode("reset")
                        st.rerun()

            if st.button("🔒  Login", type="primary", width="stretch"):
                st.session_state.login_loading = True
                st.markdown(
                    "<div class='benzino-signin-loading'><div class='benzino-signin-spinner'></div><span>Signing you in shortly...</span></div>",
                    unsafe_allow_html=True,
                )
                if validate_login(username, password):
                    clean_user = normalize_username(username)
                    st.session_state.auth_user = clean_user
                    st.session_state.auth_mode = "login"
                    if st.session_state.get("remember_me"):
                        token = create_remember_token(clean_user)
                        if token:
                            st.query_params["remember_token"] = token
                    else:
                        try:
                            if "remember_token" in st.query_params:
                                revoke_remember_token(get_query_param_value("remember_token", ""))
                                del st.query_params["remember_token"]
                        except Exception:
                            pass
                    st.rerun()
                else:
                    st.session_state.login_loading = False
                    st.session_state.login_loading = False
                    st.error("Invalid username or password.")

            if not st.session_state.get("login_loading", False):
                st.markdown("<div class='benzino-inline-footer-row'><span>Don't have an account?</span></div>", unsafe_allow_html=True)
                _footer_l, _footer_c, _footer_r = st.columns([0.44, 0.18, 0.38], vertical_alignment="center")
                with _footer_c:
                    if st.button("Create One", key="create_one_link"):
                        set_auth_mode("create")
                        st.rerun()

        elif auth_mode == "create":
            st.markdown(
                """
                <div class='benzino-login-head-exact'>
                  <div class='benzino-login-title-exact'>Create Account</div>
                  <div class='benzino-login-sub-exact'>Set up your Benzino dashboard access</div>
                </div>
                """,
                unsafe_allow_html=True,
            )
            new_user = st.text_input("Choose username", key="create_user")
            new_email = st.text_input("Email for password reset", key="create_email")
            new_pass = st.text_input("Choose PIN / password", type="password", key="create_pass")
            if st.button("Create account", type="primary", width="stretch"):
                ok, msg = create_user(new_user, new_pass, new_email)
                if ok:
                    with st.spinner("Creating profile and loading dashboard…"):
                        st.session_state.auth_user = normalize_username(new_user)
                    st.success(msg)
                    st.rerun()
                else:
                    st.error(msg)
            st.markdown("<div class='benzino-inline-footer-row'><span>Already have an account?</span></div>", unsafe_allow_html=True)
            _footer_l, _footer_c, _footer_r = st.columns([0.44, 0.18, 0.38], vertical_alignment="center")
            with _footer_c:
                if st.button("Sign In", key="sign_in_link"):
                    set_auth_mode("login")
                    st.rerun()

        else:
            st.markdown(
                """
                <div class='benzino-login-head-exact'>
                  <div class='benzino-login-title-exact'>Reset Password</div>
                  <div class='benzino-login-sub-exact'>Get a temporary password by email</div>
                </div>
                """,
                unsafe_allow_html=True,
            )
            lookup = st.text_input("Username or saved email", key="reset_lookup")
            st.caption("A temporary password will be sent to the email saved on the profile.")
            if st.button("Send reset password", type="primary", width="stretch"):
                ok, msg = reset_password_by_email(lookup)
                if ok:
                    st.success(msg)
                else:
                    st.error(msg)
            st.markdown("<div class='benzino-inline-footer-row'><span>Remembered your password?</span></div>", unsafe_allow_html=True)
            _footer_l, _footer_c, _footer_r = st.columns([0.42, 0.22, 0.36], vertical_alignment="center")
            with _footer_c:
                if st.button("Back to Login", key="back_login_link"):
                    set_auth_mode("login")
                    st.rerun()

    st.stop()

# ═══════════════════════════════════════════════════════════════════════════════
# DATA HELPERS
# ═══════════════════════════════════════════════════════════════════════════════

def load_user_watchlist(username: str) -> dict[str, str]:
    df = read_df(
        "SELECT asset, ticker FROM user_watchlists WHERE scan_owner = %s AND enabled = TRUE ORDER BY asset",
        (username,),
    )
    if df.empty:
        return {asset: ASSET_UNIVERSE[asset]["ticker"] for asset in DEFAULT_ASSETS}
    return {str(r["asset"]): str(r["ticker"]) for _, r in df.iterrows() if str(r["asset"]) in ASSET_UNIVERSE}


def save_user_watchlist(username: str, selected_assets: list[str]) -> None:
    conn = db_connect()
    try:
        with conn:
            with conn.cursor() as cur:
                cur.execute("UPDATE user_watchlists SET enabled = FALSE WHERE scan_owner = %s", (username,))
                for asset in selected_assets:
                    meta = ASSET_UNIVERSE[asset]
                    cur.execute(
                        """
                        INSERT INTO user_watchlists(scan_owner, asset, ticker, enabled)
                        VALUES (%s,%s,%s,TRUE)
                        ON CONFLICT (scan_owner, asset) DO UPDATE
                        SET ticker = EXCLUDED.ticker, enabled = TRUE
                        """,
                        (username, asset, meta["ticker"]),
                    )
    finally:
        conn.close()


def load_prop_firm_state() -> dict:
    """
    Read the ONE authoritative, scanner-maintained FTMO-style ledger.

    This is the server-side source of truth: it's posted to exclusively by the
    scanner the instant an A+/A trade closes (see scanner.py update_prop_firm),
    using the scanner's own fixed ACCOUNT_SIZE/RISK_PER_TRADE configuration.
    It does NOT move when someone drags the sidebar account-size/risk sliders —
    those sliders only affect the personalised "User Journal" what-if numbers.
    """
    df = read_df("SELECT * FROM prop_firm_state ORDER BY updated_at DESC LIMIT 1")
    if df.empty:
        return {
            "scan_owner": "benzino_system", "starting_balance": 10000.0, "current_equity": 10000.0,
            "daily_pnl": 0.0, "daily_reset_date": "", "trading_days": 0, "status": "ACTIVE", "updated_at": "",
        }
    row = df.iloc[0].to_dict()
    for k in ["starting_balance", "current_equity", "daily_pnl", "trading_days"]:
        row[k] = float(pd.to_numeric(row.get(k), errors="coerce") or 0)
    return row


def load_prop_firm_trades(limit: int = 500) -> pd.DataFrame:
    """Closed A+/A trades that have actually been posted to the official ledger."""
    df = read_df(
        """
        SELECT pft.*, ss.timeframe, ss.entry, ss.sl, ss.tp, ss.exit_reason, ss.created_at AS signal_created_at
        FROM prop_firm_trades pft
        LEFT JOIN scanner_signals ss ON ss.signal_id = pft.signal_id
        ORDER BY pft.closed_at DESC
        LIMIT %s
        """,
        (limit,),
    )
    if df.empty:
        return df
    return numeric_cols(df, ["r_multiple", "pnl_cash", "entry", "sl", "tp"])


def prop_firm_monte_carlo(trades_df: pd.DataFrame, state: dict, runs: int = 2000) -> dict:
    """
    Bootstrap the REAL closed A+/A R-multiples to estimate forward pass/fail odds
    from the CURRENT equity position. Falls back to a conservative placeholder
    distribution until at least 10 real closed trades exist.
    """
    starting = float(state.get("starting_balance") or 10000.0)
    current = float(state.get("current_equity") or starting)
    risk_cash = starting * 0.01  # matches scanner RISK_PER_TRADE default; informational only

    r_values = trades_df["r_multiple"].dropna().tolist() if not trades_df.empty else []
    used_placeholder = len(r_values) < 10
    if used_placeholder:
        r_values = [1.5, -1, 2.0, -1, 1.2, -1, 1.8, -1, 0.9, -1]

    target = starting * 1.10
    daily_floor_frac = 0.05
    total_floor = starting * 0.90

    rng = np.random.default_rng(7)
    passes = fails = unresolved = 0
    for _ in range(runs):
        equity = current
        trades_today = 0
        day_start = equity
        for step in range(60):
            if trades_today >= 3:
                day_start = equity
                trades_today = 0
            r = float(rng.choice(r_values))
            equity += risk_cash * r
            trades_today += 1
            if equity >= target:
                passes += 1
                break
            if equity <= total_floor or equity <= day_start - starting * daily_floor_frac:
                fails += 1
                break
        else:
            unresolved += 1
    total = max(1, passes + fails + unresolved)
    return {
        "pass_pct": passes / total * 100,
        "fail_pct": fails / total * 100,
        "unresolved_pct": unresolved / total * 100,
        "used_placeholder": used_placeholder,
        "sample_size": len(trades_df) if not trades_df.empty else 0,
    }


def numeric_cols(df: pd.DataFrame, cols: list[str]) -> pd.DataFrame:
    df = df.copy()
    for c in cols:
        if c in df.columns:
            df[c] = pd.to_numeric(df[c], errors="coerce")
    return df


def session_name(ts) -> str:
    try:
        hour = pd.to_datetime(ts, utc=True).tz_convert(NAIROBI_TZ).hour
    except Exception:
        return "Unknown"
    if 0 <= hour < 7:
        return "Asia"
    if 7 <= hour < 12:
        return "London AM"
    if 12 <= hour < 17:
        return "London/NY Overlap"
    if 17 <= hour < 22:
        return "New York PM"
    return "Late / Rollover"


def load_signals_for_user(username: str, settings: dict, include_all_admin: bool = False) -> pd.DataFrame:
    tracking_started = settings.get("tracking_started_at") or "1970-01-01T00:00:00Z"
    df = read_df(
        """
        SELECT * FROM scanner_signals
        WHERE created_at >= %s
        ORDER BY created_at DESC
        LIMIT 5000
        """,
        (tracking_started,),
    )
    if df.empty:
        return df
    if not include_all_admin:
        watchlist_assets = set(load_user_watchlist(username).keys())
        if watchlist_assets:
            df = df[df["asset"].astype(str).isin(watchlist_assets)]
    df = numeric_cols(df, ["confidence", "edge_score", "ml_prob", "entry", "sl", "tp", "rr", "rsi", "atr", "exit_price", "r_multiple", "bars_open", "mtf_score", "shadow_r_multiple"])
    df["created_at"] = pd.to_datetime(df["created_at"], errors="coerce", utc=True)
    df["created_at_eat"] = df["created_at"].apply(fmt_nairobi)
    df["session"] = df["created_at"].apply(session_name)
    return df


def load_all_system_signals(settings: dict, limit: int = 50000) -> pd.DataFrame:
    """Load the complete scanner history from Supabase.

    This intentionally ignores the logged-in user's watchlist and activation date.
    It powers the System Performance view, showing how the full scanner universe
    is performing across every saved asset, timeframe, grade, and session.
    """
    df = read_df(
        """
        SELECT * FROM scanner_signals
        ORDER BY created_at DESC
        LIMIT %s
        """,
        (limit,),
    )
    if df.empty:
        return df
    df = numeric_cols(df, ["confidence", "edge_score", "ml_prob", "entry", "sl", "tp", "rr", "rsi", "atr", "exit_price", "r_multiple", "bars_open", "mtf_score", "shadow_r_multiple"])
    df["created_at"] = pd.to_datetime(df["created_at"], errors="coerce", utc=True)
    df["created_at_eat"] = df["created_at"].apply(fmt_nairobi)
    df["session"] = df["created_at"].apply(session_name)
    return enrich_position_sizing(df, settings)


def apply_timeframe_view(df: pd.DataFrame, settings: dict) -> pd.DataFrame:
    """Filter dashboard rows to the selected timeframe, while keeping All available."""
    if df is None or df.empty or "timeframe" not in df.columns:
        return df
    tf = str(settings.get("view_timeframe") or settings.get("preferred_timeframe") or "All")
    if tf.lower() == "all":
        return df
    return df[df["timeframe"].astype(str).str.lower().eq(tf.lower())].copy()


def performance_by_timeframe(df: pd.DataFrame, settings: dict, prop_mode: bool = False) -> pd.DataFrame:
    """Return system performance split by signal timeframe."""
    if df is None or df.empty or "timeframe" not in df.columns:
        return pd.DataFrame()
    rows = []
    for tf, group in df.groupby(df["timeframe"].astype(str)):
        perf = compute_user_performance(group.copy(), settings, prop_mode=prop_mode)
        rows.append({
            "Timeframe": tf,
            "Balance": perf["current_balance"],
            "RealisedPnL": perf["realised_pnl"],
            "ROI_%": perf["roi_pct"],
            "Open": perf["open_count"],
            "Closed": perf["closed_count"],
            "WinRate_%": perf["win_rate"],
            "MarginInUse": perf["margin_in_use"],
        })
    if not rows:
        return pd.DataFrame()
    order = {"15m": 0, "1h": 1, "4h": 2, "1d": 3}
    out = pd.DataFrame(rows)
    out["_order"] = out["Timeframe"].map(order).fillna(99)
    return out.sort_values("_order").drop(columns=["_order"])


def enrich_position_sizing(df: pd.DataFrame, settings: dict) -> pd.DataFrame:
    df = df.copy()
    account = float(settings.get("account_size", 10000) or 10000)
    risk_pct = float(settings.get("risk_pct", 1.0) or 1.0) / 100.0
    leverage = max(1.0, float(settings.get("leverage", 100) or 100))
    risk_cash = account * risk_pct
    if df.empty:
        return df
    df["stop_distance"] = (df["entry"] - df["sl"]).abs()
    df["position_size"] = np.where(df["stop_distance"] > 0, risk_cash / df["stop_distance"], 0)
    df["notional"] = df["position_size"] * df["entry"]
    df["margin_required"] = df["notional"] / leverage
    df["risk_cash"] = risk_cash
    return df


def outcome_label(row) -> str:
    status = str(row.get("status", "")).upper()
    if "TP" in status:
        return "WIN"
    if "SL" in status:
        return "LOSS"
    if "EXPIRED" in status or "CLOSED" in status:
        r = pd.to_numeric(row.get("r_multiple"), errors="coerce")
        if pd.isna(r):
            return "CLOSED"
        return "WIN" if r > 0 else "LOSS" if r < 0 else "BREAKEVEN"
    if status == "OPEN":
        return "OPEN"
    return "SHADOW"


def compute_user_performance(df: pd.DataFrame, settings: dict, prop_mode: bool = False) -> dict:
    """Compute dynamic account performance from the user-filtered scanner journal.

    PnL is based on the user's selected account size and risk %, so changing the
    app controls immediately restates the personal system ledger. Closed trades
    use r_multiple from scanner outcomes. Open trades reserve risk and margin but
    do not add unrealised PnL because the scanner table does not store live mark
    prices yet.
    """
    account = float(settings.get("account_size", 10000) or 10000)
    risk_pct = float(settings.get("risk_pct", 1.0) or 1.0) / 100.0
    leverage = max(1.0, float(settings.get("leverage", 100) or 100))
    risk_cash = account * risk_pct

    out = {
        "starting_balance": account,
        "current_balance": account,
        "realised_pnl": 0.0,
        "roi_pct": 0.0,
        "risk_cash": risk_cash,
        "open_risk": 0.0,
        "margin_in_use": 0.0,
        "open_count": 0,
        "closed_count": 0,
        "win_rate": 0.0,
        "trading_days": 0,
        "status": "ACTIVE",
        "target_balance": account * 1.10,
        "daily_loss_limit": account * 0.05,
        "max_loss_limit": account * 0.10,
    }
    if df is None or df.empty:
        return out

    trades = df[df["grade"].astype(str).isin(["A+", "A", "B", "C"])].copy()
    if prop_mode:
        trades = trades[trades["grade"].astype(str).isin(["A+", "A"])].copy()
    if trades.empty:
        return out

    trades = numeric_cols(trades, ["r_multiple", "entry", "sl", "margin_required"])
    status = trades["status"].astype(str).str.upper()
    open_trades = trades[status.eq("OPEN")].copy()
    closed = trades[status.str.contains("CLOSED|EXPIRED|TP|SL", na=False)].copy()

    out["open_count"] = int(len(open_trades))
    out["closed_count"] = int(len(closed))
    out["open_risk"] = float(len(open_trades) * risk_cash)
    if "margin_required" in open_trades.columns:
        out["margin_in_use"] = float(pd.to_numeric(open_trades["margin_required"], errors="coerce").fillna(0).sum())
    else:
        out["margin_in_use"] = 0.0

    if not closed.empty:
        closed["pnl_cash"] = pd.to_numeric(closed["r_multiple"], errors="coerce").fillna(0) * risk_cash
        realised = float(closed["pnl_cash"].sum())
        out["realised_pnl"] = realised
        out["current_balance"] = account + realised
        out["roi_pct"] = (realised / account) * 100 if account else 0.0
        wins = closed["pnl_cash"] > 0
        out["win_rate"] = float(wins.sum() / len(closed) * 100) if len(closed) else 0.0
        try:
            out["trading_days"] = int(pd.to_datetime(closed["created_at"], utc=True, errors="coerce").dt.date.nunique())
        except Exception:
            out["trading_days"] = 0

    if prop_mode:
        balance = out["current_balance"]
        if balance <= account * 0.90:
            out["status"] = "FAILED - Max loss breached"
        elif out["realised_pnl"] <= -account * 0.05:
            out["status"] = "FAILED - Daily loss risk"
        elif balance >= account * 1.10 and out["trading_days"] >= 4:
            out["status"] = "PASSED"
        else:
            out["status"] = "ACTIVE"
    return out


def render_performance_strip(df: pd.DataFrame, settings: dict, prop_mode: bool = False) -> None:
    perf = compute_user_performance(df, settings, prop_mode=prop_mode)
    c1, c2, c3, c4, c5 = st.columns(5)
    with c1: metric_card("Balance", f"${perf['current_balance']:,.2f}", f"Start ${perf['starting_balance']:,.0f}")
    with c2: metric_card("Realised PnL", f"${perf['realised_pnl']:+,.2f}", f"ROI {perf['roi_pct']:+.2f}%")
    with c3: metric_card("Open risk", f"${perf['open_risk']:,.2f}", f"{perf['open_count']} open trade(s)")
    with c4: metric_card("Margin in use", f"${perf['margin_in_use']:,.2f}", f"Leverage 1:{int(settings.get('leverage', 100))}")
    with c5: metric_card("Win rate", f"{perf['win_rate']:.2f}%", f"{perf['closed_count']} closed")
    if prop_mode:
        st.caption(f"FTMO-style status: {perf['status']} · Target ${perf['target_balance']:,.2f} · Max daily loss ${perf['daily_loss_limit']:,.2f} · Max total loss ${perf['max_loss_limit']:,.2f}")


def add_trade_pnl_columns(df: pd.DataFrame, settings: dict) -> pd.DataFrame:
    """Add user-account PnL columns for open and closed trade tables.

    The scanner updates r_multiple when TP, SL, or expiry resolves a trade.
    This app converts that R result into cash using the selected account size
    and risk %, so balances update automatically on refresh after each closure.
    """
    out = df.copy()
    if out.empty:
        return out
    account = float(settings.get("account_size", 10000) or 10000)
    risk_pct = float(settings.get("risk_pct", 1.0) or 1.0) / 100.0
    risk_cash = account * risk_pct
    out = numeric_cols(out, ["r_multiple", "rr"])
    out["risk_cash"] = risk_cash
    out["pnl_cash"] = pd.to_numeric(out.get("r_multiple", 0), errors="coerce").fillna(0) * risk_cash
    out["potential_tp_cash"] = pd.to_numeric(out.get("rr", 0), errors="coerce").fillna(0) * risk_cash
    out["potential_sl_cash"] = -risk_cash
    try:
        order = out.sort_values("created_at", ascending=True).index
        cumulative = out.loc[order, "pnl_cash"].cumsum() + account
        out.loc[order, "balance_after"] = cumulative
    except Exception:
        out["balance_after"] = account + out["pnl_cash"].cumsum()
    return out


def compute_dashboard_summary(df: pd.DataFrame, settings: dict) -> dict:
    """Derive the extra stats the redesigned Dashboard needs from real signal/trade data.

    Everything here is computed from the same watchlist-scoped, timeframe-filtered
    dataframe the rest of the dashboard uses (load_signals_for_user -> apply_timeframe_view).
    No mocked numbers: if there are no closed trades yet, the relevant fields read 0.
    """
    out = {
        "todays_pnl": 0.0,
        "todays_pnl_pct": 0.0,
        "total_trades": 0,
        "winning_trades": 0,
        "losing_trades": 0,
        "win_rate": 0.0,
        "profit_factor": 0.0,
        "equity_series": pd.DataFrame(columns=["created_at", "balance_after"]),
    }
    if df is None or df.empty:
        return out

    account = float(settings.get("account_size", 10000) or 10000)
    priced = add_trade_pnl_columns(df, settings)
    status = priced.get("status", pd.Series(dtype=str)).astype(str).str.upper()
    closed = priced[status.str.contains("CLOSED|EXPIRED|TP|SL", na=False)].copy()
    closed = closed[closed["grade"].astype(str).isin(VALID_GRADES)]

    if closed.empty:
        return out

    closed = closed.sort_values("created_at")
    out["equity_series"] = closed[["created_at", "balance_after"]].dropna()

    wins = closed["pnl_cash"] > 0
    losses = closed["pnl_cash"] < 0
    out["total_trades"] = int(len(closed))
    out["winning_trades"] = int(wins.sum())
    out["losing_trades"] = int(losses.sum())
    out["win_rate"] = float(wins.sum() / len(closed) * 100) if len(closed) else 0.0

    gross_profit = float(closed.loc[wins, "pnl_cash"].sum())
    gross_loss = float(-closed.loc[losses, "pnl_cash"].sum())
    out["profit_factor"] = (gross_profit / gross_loss) if gross_loss > 0 else (gross_profit if gross_profit > 0 else 0.0)

    try:
        today_eat = pd.Timestamp.now(tz=NAIROBI_TZ).date()
        closed_eat = closed["created_at"].apply(to_nairobi)
        today_mask = closed_eat.apply(lambda ts: ts.date() == today_eat if ts is not None else False)
        todays_pnl = float(closed.loc[today_mask, "pnl_cash"].sum())
        out["todays_pnl"] = todays_pnl
        out["todays_pnl_pct"] = (todays_pnl / account * 100) if account else 0.0
    except Exception:
        pass

    return out


def render_balance_curve(df: pd.DataFrame, settings: dict, title: str = "Balance curve") -> None:
    """Render realised balance curve from closed trades when evidence exists."""
    if df is None or df.empty:
        return
    view = add_trade_pnl_columns(df.copy(), settings)
    status = view.get("status", pd.Series(dtype=str)).astype(str).str.upper()
    closed = view[status.str.contains("CLOSED|EXPIRED|TP|SL", na=False)].copy()
    if closed.empty:
        return
    closed = closed.sort_values("created_at")
    fig = px.line(closed, x="created_at", y="balance_after", color="timeframe" if "timeframe" in closed.columns else None, title=title)
    st.plotly_chart(fig, use_container_width=True)



NAIROBI_TZ = ZoneInfo("Africa/Nairobi")


def to_nairobi(value):
    try:
        ts = pd.to_datetime(value, utc=True, errors="coerce")
        if pd.isna(ts):
            return None
        return ts.tz_convert(NAIROBI_TZ)
    except Exception:
        return None


def fmt_nairobi(value, include_tz: bool = True) -> str:
    ts = to_nairobi(value)
    if ts is None:
        return ""
    suffix = " EAT" if include_tz else ""
    return ts.strftime(f"%Y-%m-%d %H:%M{suffix}")


def time_ago(value) -> str:
    ts = to_nairobi(value)
    if ts is None:
        return "Unknown age"
    now = pd.Timestamp.now(tz=NAIROBI_TZ)
    mins = max(0, int((now - ts).total_seconds() // 60))
    if mins < 1:
        return "Generated just now"
    if mins < 60:
        return f"Generated {mins} min ago"
    hours = mins // 60
    if hours < 24:
        return f"Generated {hours} hr ago"
    days = hours // 24
    return f"Generated {days} day(s) ago"


def age_ago(value) -> str:
    """Compact table age label without the 'Generated' prefix."""
    ts = to_nairobi(value)
    if ts is None:
        return "Unknown"
    now = pd.Timestamp.now(tz=NAIROBI_TZ)
    mins = max(0, int((now - ts).total_seconds() // 60))
    if mins < 1:
        return "Just now"
    if mins < 60:
        return f"{mins} min ago"
    hours = mins // 60
    if hours < 24:
        return f"{hours} hr ago"
    days = hours // 24
    return f"{days} day(s) ago"


def decayed_confidence_value(confidence, created_at, timeframe: str = "1h") -> float:
    """Return urgency-adjusted system agreement.

    This must never increase the original agreement. The previous version
    decayed toward 50%, which accidentally lifted low-agreement signals
    such as 40% to 41%+. Here, age only reduces urgency.
    """
    base = float(pd.to_numeric(confidence, errors="coerce") if confidence is not None else 0)
    base = max(0.0, min(100.0, base))
    ts = to_nairobi(created_at)
    if ts is None:
        return base
    age_hours = max(0.0, (pd.Timestamp.now(tz=NAIROBI_TZ) - ts).total_seconds() / 3600)
    half_life = {"15m": 3, "1h": 8, "4h": 24, "1d": 96}.get(str(timeframe).lower(), 8)
    decay = 0.5 ** (age_hours / half_life)
    return float(max(0.0, min(base, base * decay)))


def parse_jsonish(value) -> dict:
    if isinstance(value, dict):
        return value
    if isinstance(value, str) and value.strip():
        try:
            out = json.loads(value)
            return out if isinstance(out, dict) else {}
        except Exception:
            return {}
    return {}


def format_votes(votes: dict) -> str:
    if not votes:
        return "No strategy-vote payload was stored for this row."
    parts = []
    for name, payload in votes.items():
        if not isinstance(payload, dict):
            continue
        display = strategy_display_name(name)
        direction = payload.get("direction", "NEUTRAL")
        strength = payload.get("strength", 0)
        try: strength = float(strength)
        except Exception: strength = 0
        tone = "strong" if strength >= .65 else "moderate" if strength >= .35 else "weak"
        parts.append(f"**{display}** voted **{direction}** with {tone} strength ({strength:.2f}).")
    return " ".join(parts) if parts else "No valid strategy votes were stored."


STRATEGY_NAME_MAP = {
    "RSI2": "RSI-2 Mean Reversion",
    "TSMOM": "Time-Series Momentum",
    "Donchian": "Donchian Channel Breakout",
    "MLEnsemble": "Machine Learning Ensemble",
    "MTFConfirmation": "Multi-Timeframe Confirmation",
}

STRATEGY_DESCRIPTION_MAP = {
    "RSI2": "Short-term mean-reversion vote. It looks for stretched RSI-2 readings, ideally with the broader trend filter rather than blindly fading price.",
    "TSMOM": "Time-Series Momentum vote. It checks whether the asset's own recent return profile supports continuation in the same direction.",
    "Donchian": "Breakout vote. It checks whether price is pushing through a recent high/low channel with enough directional structure to avoid weak breakouts.",
    "MLEnsemble": "Machine-learning vote. It combines logistic regression, random forest, and gradient boosting probabilities into one model-driven directional bias.",
    "MTFConfirmation": "Multi-timeframe vote. It checks whether the entry timeframe agrees with the higher-timeframe context instead of trading against the larger structure.",
}


def strategy_display_name(name: str) -> str:
    return STRATEGY_NAME_MAP.get(str(name), str(name))


def strategy_description(name: str) -> str:
    return STRATEGY_DESCRIPTION_MAP.get(str(name), "Strategy vote stored by the scanner.")


def mini_markdown_to_html(text: str) -> str:
    escaped = html.escape(str(text or ""))
    escaped = re.sub(r"\*\*(.+?)\*\*", r"<strong>\1</strong>", escaped)
    return escaped.replace("\n", "<br>")


def render_strategy_confluence(votes: dict) -> None:
    """Render strategy confluence with the same AgGrid styling as the rest of the app."""
    if not votes:
        return
    rows = []
    for name, payload in votes.items():
        if not isinstance(payload, dict):
            continue
        display = strategy_display_name(name)
        desc = strategy_description(name)
        direction = str(payload.get("direction", "NEUTRAL") or "NEUTRAL").upper()
        try:
            strength = float(payload.get("strength") or 0)
        except Exception:
            strength = 0.0
        rows.append({
            "Strategy": display,
            "Vote": direction,
            "Strength": strength,
            "Reason": desc,
        })
    if not rows:
        return
    render_benzino_aggrid(
        pd.DataFrame(rows),
        key="strategy_confluence_grid",
        height=282,
        page_size=5,
        pinned=["Strategy"],
        numeric_cols_right=["Strength"],
        enable_search=False,
        show_footer=False,
        use_pagination=False,
    )

def rich_signal_explanation(row: pd.Series) -> str:
    asset = str(row.get("asset", ""))
    tf = str(row.get("timeframe", ""))
    signal = str(row.get("signal", ""))
    grade = str(row.get("grade", ""))
    status = str(row.get("status", ""))
    reason = str(row.get("reason", ""))
    rr = float(pd.to_numeric(row.get("rr"), errors="coerce") or 0)
    edge = float(pd.to_numeric(row.get("edge_score"), errors="coerce") or 0)
    conf = float(pd.to_numeric(row.get("confidence"), errors="coerce") or 50)
    dconf = decayed_confidence_value(conf, row.get("created_at"), tf)
    mtf_score = float(pd.to_numeric(row.get("mtf_score"), errors="coerce") or 0)
    votes = parse_jsonish(row.get("strategy_votes"))
    mtf = parse_jsonish(row.get("mtf_context"))
    mtf_line = ""
    if mtf:
        bits = []
        for k, v in mtf.items():
            if isinstance(v, dict):
                bits.append(f"{k}: {v.get('direction','NEUTRAL')} ({float(v.get('strength') or 0):.2f})")
        mtf_line = " ".join(bits)
    decision = "blocked as a research-only NO TRADE" if grade == "NO TRADE" or signal == "HOLD" else f"accepted as an active {signal} setup"
    return (
        f"**{asset} · {tf} · {time_ago(row.get('created_at'))}**  \n\n"
        f"The engine {decision}. The final grade is **{grade}** and current status is **{status}**. "
        f"Raw confidence was **{conf:.2f}%**, but after age decay it currently reads about **{dconf:.2f}%**. "
        f"That decay matters because older signals should lose urgency even if the original setup was clean. "
        f"The setup carries an edge score of **{edge:.2f}**, RR of **{rr:.2f}R**, and MTF alignment of **{mtf_score:.0f}%**.\n\n"
        f"**Strategy reasoning:** {format_votes(votes)}\n\n"
        f"**Multi-timeframe context:** {mtf_line or 'No detailed MTF context was stored.'}\n\n"
        f"**Final interpretation:** {reason}"
    )


def rich_open_trade_explanation(row: pd.Series) -> str:
    """Explain AI, case 2 of 3: a currently OPEN journal trade (A+/A/B/C, not yet resolved)."""
    asset = str(row.get("asset", ""))
    tf = str(row.get("timeframe", ""))
    signal = str(row.get("signal", ""))
    grade = str(row.get("grade", ""))
    reason = str(row.get("reason", ""))
    entry = float(pd.to_numeric(row.get("entry"), errors="coerce") or 0)
    sl = float(pd.to_numeric(row.get("sl"), errors="coerce") or 0)
    tp = float(pd.to_numeric(row.get("tp"), errors="coerce") or 0)
    rr = float(pd.to_numeric(row.get("rr"), errors="coerce") or 0)
    bars_open = int(pd.to_numeric(row.get("bars_open"), errors="coerce") or 0)
    votes = parse_jsonish(row.get("strategy_votes"))
    age = time_ago(row.get("created_at"))
    return (
        f"**{asset} · {tf} · {signal} · Grade {grade}**  \n\n"
        f"This trade is still **OPEN**, opened **{age}**, and has lived through **{bars_open}** "
        f"{tf} candle(s) so far without hitting take-profit or stop-loss. Entry **{entry:.5f}**, "
        f"stop **{sl:.5f}**, target **{tp:.5f}**, planned risk:reward **{rr:.2f}R**.\n\n"
        f"**Why it was opened:** {reason}\n\n"
        f"**Strategy reasoning at entry:** {format_votes(votes)}\n\n"
        f"**What to watch:** the trade auto-expires if neither level is hit within the configured bar limit "
        f"for {tf}. No manual action is required — the scanner re-checks this exact trade every run and will "
        f"resolve it via TP, SL, or expiry, after which it moves into the closed-trade Explain AI case."
    )


def rich_closed_trade_explanation(row: pd.Series) -> str:
    asset = str(row.get("asset", ""))
    tf = str(row.get("timeframe", ""))
    signal = str(row.get("signal", ""))
    grade = str(row.get("grade", ""))
    outcome = outcome_label(row)
    r_mult = float(pd.to_numeric(row.get("r_multiple"), errors="coerce") or 0)
    exit_reason = str(row.get("exit_reason", ""))
    reason = str(row.get("reason", ""))
    if outcome == "WIN":
        lesson = "The market rewarded the confluence. Coach should look for whether the winning pattern came from timeframe alignment, grade quality, session timing, or asset behaviour, then prioritise repeating that condition."
    elif outcome == "LOSS":
        lesson = "The setup failed after entry. This should be reviewed for timing risk, volatility expansion, weak MTF confirmation, or a strategy vote that was not strong enough. Losses are not ignored; they become filters for the next version of the playbook."
    else:
        lesson = "The trade closed without a clean TP/SL lesson. Treat it as a timing and expiry-management review rather than a pure win/loss signal."
    return (
        f"**{asset} · {tf} · {signal} · Grade {grade}**  \n\n"
        f"This trade closed as **{outcome}** via **{exit_reason or 'recorded close'}** with **{r_mult:+.2f}R**. "
        f"The original reason was: {reason}\n\n"
        f"**What Explain AI learns:** {lesson}"
    )


def render_ai_card(title: str, body: str) -> None:
    # Keep the title outside the card; the explanatory narrative itself sits inside.
    st.markdown(f"<h3 style='margin:18px 0 8px;color:#E8EDF2'>{html.escape(title)}</h3>", unsafe_allow_html=True)
    st.markdown(f"<div class='ai-card'>{mini_markdown_to_html(body)}</div>", unsafe_allow_html=True)

def load_runtime_health() -> tuple[pd.DataFrame, dict]:
    """Load scanner runtime stats for the System Health panel."""
    df = read_df(
        """
        SELECT *
        FROM scanner_runtime_log
        ORDER BY started_at DESC
        LIMIT 100
        """
    )
    summary = {
        "last_seconds": 0.0,
        "fastest_seconds": 0.0,
        "slowest_seconds": 0.0,
        "avg_seconds": 0.0,
        "last_started_at": "",
        "last_timeframes": "",
        "runs": 0,
    }
    if df.empty:
        return df, summary
    df = numeric_cols(df, ["total_seconds", "assets_scanned", "signals_saved", "shadow_saved", "open_trades", "alerted", "fastest_asset_seconds", "slowest_asset_seconds", "avg_asset_seconds"])
    try:
        df["started_at"] = pd.to_datetime(df["started_at"], errors="coerce", utc=True)
        df["finished_at"] = pd.to_datetime(df["finished_at"], errors="coerce", utc=True)
    except Exception:
        pass
    summary["runs"] = int(len(df))
    summary["last_seconds"] = float(df.iloc[0].get("total_seconds") or 0)
    summary["fastest_seconds"] = float(df["total_seconds"].min())
    summary["slowest_seconds"] = float(df["total_seconds"].max())
    summary["avg_seconds"] = float(df["total_seconds"].mean())
    summary["last_started_at"] = fmt_nairobi(df.iloc[0].get("started_at", ""))
    summary["last_timeframes"] = str(df.iloc[0].get("timeframes_scanned") or "")
    return df, summary


def render_system_health_panel() -> None:
    """Small runtime tracker showing scanner performance since logging started."""
    runtime_df, summary = load_runtime_health()
    if runtime_df.empty:
        st.info("No scanner runtime logs yet. Run the scanner once after this update and refresh the dashboard.")
        return

    c1, c2, c3, c4 = st.columns(4)
    with c1: metric_card("Last run", f"{summary['last_seconds']:.2f}s", summary["last_started_at"])
    with c2: metric_card("Fastest run", f"{summary['fastest_seconds']:.2f}s", f"{summary['runs']} logged run(s)")
    with c3: metric_card("Slowest run", f"{summary['slowest_seconds']:.2f}s")
    with c4: metric_card("Average run", f"{summary['avg_seconds']:.2f}s", f"Last TFs: {summary['last_timeframes']}")

    st.markdown("<div class='section-gap'></div>", unsafe_allow_html=True)
    view_source = runtime_df.copy()
    if "started_at" in view_source.columns:
        started_series = pd.to_datetime(view_source["started_at"], errors="coerce", utc=True)
        available_dates = sorted(started_series.dt.tz_convert(NAIROBI_TZ).dt.date.dropna().unique(), reverse=True)
        if available_dates:
            selected_date = st.selectbox("Drill down by run date", ["All dates"] + [str(d) for d in available_dates], key="system_health_date_filter")
            if selected_date != "All dates":
                selected_date_obj = pd.to_datetime(selected_date).date()
                view_source = view_source[started_series.dt.tz_convert(NAIROBI_TZ).dt.date.eq(selected_date_obj)]

    cols = ["started_at", "timeframes_scanned", "total_seconds", "assets_scanned", "signals_saved", "open_trades", "alerted", "shadow_saved", "fastest_asset_seconds", "slowest_asset_seconds", "avg_asset_seconds"]
    view = view_source[[c for c in cols if c in view_source.columns]].copy()
    if "started_at" in view.columns:
        view["started_at"] = view["started_at"].apply(fmt_nairobi)
    render_benzino_aggrid(
        view.head(50),
        key="system_health_runs",
        title="Scanner Run History",
        height=320,
        page_size=10,
        pinned=["started_at", "timeframes_scanned"],
        numeric_cols_right=["total_seconds", "assets_scanned", "signals_saved", "shadow_saved", "open_trades", "alerted"],
        enable_search=False,
    )


def explain_signal(row: pd.Series) -> str:
    return rich_signal_explanation(row)


# ═══════════════════════════════════════════════════════════════════════════════
# UI HELPERS
# ═══════════════════════════════════════════════════════════════════════════════


def aggrid_badge_renderers() -> dict:
    """Shared JavaScript badge renderers used by every AgGrid table in Benzino.

    Uses real DOM nodes, not HTML strings, so AgGrid renders badges instead of
    displaying long <span>...</span> text in Journal, Coach, Explain AI, and
    System Performance tables.
    """
    if JsCode is None:
        return {}
    return {
        "signal": JsCode("""
        class SignalRenderer {
          init(params) {
            const v = (params.value || '').toString().toUpperCase();
            const span = document.createElement('span');
            if (v.includes('BUY')) { span.className = 'ag-signal-badge ag-buy'; span.innerHTML = '↗ BUY'; }
            else if (v.includes('SELL')) { span.className = 'ag-signal-badge ag-sell'; span.innerHTML = '↘ SELL'; }
            else { span.className = 'ag-signal-badge ag-neutral'; span.innerHTML = v || '—'; }
            this.eGui = span;
          }
          getGui() { return this.eGui; }
        }
        """),
        "grade": JsCode("""
        class GradeRenderer {
          init(params) {
            const raw = (params.value || '—').toString().toUpperCase();
            let cls = 'ag-grade-no-trade';
            let label = raw === 'NO TRADE' ? 'No Trade' : raw;
            if (raw === 'A+') cls = 'ag-grade-ap';
            else if (raw === 'A') cls = 'ag-grade-a';
            else if (raw === 'B') cls = 'ag-grade-b';
            else if (raw === 'C') cls = 'ag-grade-c';
            const span = document.createElement('span');
            span.className = 'ag-grade-badge ' + cls;
            span.innerText = label;
            this.eGui = span;
          }
          getGui() { return this.eGui; }
        }
        """),
        "status": JsCode("""
        class StatusRenderer {
          init(params) {
            const raw = (params.value || '—').toString();
            const v = raw.toUpperCase();
            const span = document.createElement('span');

            span.className = 'ag-status-badge';

            let bg = 'rgba(139,158,176,.16)';
            let color = '#A9BBC9';

            if (v.includes('TP') || v.includes('WIN')) {
              bg = 'rgba(0,212,163,.18)';
              color = '#00D4A3';
            } else if (v.includes('SL') || v.includes('LOSS')) {
              bg = 'rgba(255,93,93,.18)';
              color = '#FF5D5D';
            } else if (v.includes('EXPIRED')) {
              bg = 'rgba(214,168,78,.18)';
              color = '#D6A84E';
            } else if (v.includes('ENABLED') || v.includes('OPEN') || v.includes('ACTIVE') || v === 'YES') {
              bg = 'rgba(0,212,163,.16)';
              color = '#00D4A3';
            } else if (v.includes('CLOSED')) {
              bg = 'rgba(76,140,255,.14)';
              color = '#7AA6FF';
            }

            span.style.background = bg;
            span.style.color = color;
            span.innerText = raw;
            this.eGui = span;
          }
          getGui() { return this.eGui; }
        }
        """),
        "outcome": JsCode("""
        class OutcomeRenderer {
          init(params) {
            const raw = (params.value || '—').toString().toUpperCase();
            const span = document.createElement('span');
            span.className = 'ag-status-badge';

            let bg = 'rgba(139,158,176,.16)';
            let color = '#A9BBC9';

            if (raw === 'WIN') {
              bg = 'rgba(0,212,163,.18)';
              color = '#00D4A3';
            } else if (raw === 'LOSS') {
              bg = 'rgba(255,93,93,.18)';
              color = '#FF5D5D';
            } else if (raw === 'BREAKEVEN') {
              bg = 'rgba(214,168,78,.18)';
              color = '#D6A84E';
            } else if (raw.includes('OPEN')) {
              bg = 'rgba(214,168,78,.18)';
              color = '#D6A84E';
            }

            span.style.background = bg;
            span.style.color = color;
            span.innerText = raw;
            this.eGui = span;
          }
          getGui() { return this.eGui; }
        }
        """),
    }


def benzino_aggrid_css() -> dict:
    """One dark Benzino AgGrid skin shared across Generated Signals, Journal, Watchlist, Admin and Challenge tables."""
    return {
        ".ag-root-wrapper": {"background-color": "#07111F !important", "border": "1px solid #1E3050 !important", "border-radius": "14px !important", "overflow": "hidden !important"},
        ".ag-header": {"background-color": "#0B1A2B !important", "border-bottom": "1px solid #203A59 !important"},
        ".ag-header-cell-label": {"color": "#C9D5E3 !important", "font-weight": "900 !important", "font-size": "var(--font-table-header) !important"},
        ".ag-row": {"background-color": "#07111F !important", "border-bottom": "1px solid #13263B !important"},
        ".ag-row-hover": {"background-color": "#0D2033 !important"},
        ".ag-cell": {"color": "#DDE7F1 !important", "font-size": "var(--font-table-body) !important", "display": "flex !important", "align-items": "center !important"},
        ".ag-paging-panel": {"background-color": "#07111F !important", "color": "#8BAAB8 !important", "border-top": "1px solid #16263B !important"},
        ".ag-signal-badge": {"font-weight": "950 !important", "border-radius": "999px !important", "padding": "4px 9px !important", "font-size": "11.5px !important"},
        ".ag-buy": {"background": "rgba(0,212,163,.14) !important", "color": "#00D4A3 !important"},
        ".ag-sell": {"background": "rgba(255,93,93,.14) !important", "color": "#FF5D5D !important"},
        ".ag-neutral": {"background": "rgba(139,158,176,.14) !important", "color": "#A9BBC9 !important"},
        ".ag-grade-badge, .ag-status-badge": {"display": "inline-flex !important", "align-items": "center !important", "justify-content": "center !important", "border-radius": "999px !important", "padding": "4px 9px !important", "font-size": "11.5px !important", "font-weight": "950 !important"},
        ".ag-grade-ap": {"background": "rgba(0,212,163,.18) !important", "color": "#00D4A3 !important"},
        ".ag-grade-a": {"background": "rgba(76,140,255,.18) !important", "color": "#7AA6FF !important"},
        ".ag-grade-b": {"background": "rgba(214,168,78,.18) !important", "color": "#D6A84E !important"},
        ".ag-grade-c": {"background": "rgba(255,93,93,.18) !important", "color": "#FF5D5D !important"},
        ".ag-grade-no-trade": {"background": "rgba(137,95,255,.18) !important", "color": "#A98CFF !important"},
        ".ag-status-active": {"background": "rgba(0,212,163,.16) !important", "color": "#00D4A3 !important"},
        ".ag-status-win": {"background": "rgba(78,196,214,.22) !important", "color": "#4EC4D6 !important"},
        ".ag-status-loss": {"background": "rgba(255,93,93,.18) !important", "color": "#FF5D5D !important"},
        ".ag-status-expired": {"background": "rgba(214,168,78,.18) !important", "color": "#D6A84E !important"},
        ".ag-status-skipped": {"background": "rgba(139,158,176,.16) !important", "color": "#A9BBC9 !important"},
        ".ag-status-closed": {"background": "rgba(76,140,255,.14) !important", "color": "#7AA6FF !important"},
    }



def format_market_price(value):
    """
    Display market prices with the precision the instrument needs.
    Keeps up to 6 decimals for FX / low-price assets and removes unnecessary
    trailing zeroes without forcing every asset to 2dp.
    """
    try:
        if value is None or pd.isna(value):
            return ""
        x = float(str(value).replace(",", ""))
        if not np.isfinite(x):
            return ""
        s = f"{x:.6f}".rstrip("0").rstrip(".")
        if "." in s:
            whole, frac = s.split(".", 1)
            if len(frac) == 1:
                s += "0"
        return s
    except Exception:
        return "" if value is None else str(value)


def is_price_display_column(col_name: str) -> bool:
    """Detect price columns everywhere in the app: Entry, SL, TP, exits, OHLC, etc."""
    c = str(col_name or "").strip().lower()
    c = c.replace("_", " ").replace("-", " ")
    c = re.sub(r"\s+", " ", c)

    exact = {
        "entry", "sl", "tp", "stop loss", "take profit",
        "exit", "exit price", "price",
        "hypothetical entry", "hypothetical sl", "hypothetical tp", "hypothetical exit",
        "shadow exit price", "open", "high", "low", "close",
    }
    if c in exact:
        return True

    price_tokens = (
        "entry", " sl", "sl ", " tp", "tp ", "stop loss", "take profit",
        "exit price", "hypothetical exit", "hypothetical entry", "hypothetical sl", "hypothetical tp",
    )
    non_price_tokens = ("score", "rate", "ratio", "confidence", "r multiple", "win", "loss", "risk", "margin", "pnl", "balance")
    return any(tok in f" {c} " for tok in price_tokens) and not any(tok in c for tok in non_price_tokens)


def render_benzino_aggrid(
    df: pd.DataFrame,
    key: str,
    height: int = 360,
    page_size: int = 10,
    column_order=None,
    pinned=None,
    badge_cols=None,
    numeric_cols_right=None,
    enable_search: bool = True,
    title=None,
    show_filter_button: bool = False,
    show_footer: bool = True,
    use_pagination: bool = True,
):
    """Shared Benzino AgGrid renderer.

    Used across: Generated Signals, Journal/Trade History, Scanner Performance Analytics,
    Watchlist Manager, Review Queue, User Management, and Challenge Mode.
    Falls back to st.dataframe if streamlit-aggrid is unavailable.
    """
    if df is None or df.empty:
        st.info("No rows to display yet.")
        return None

    view = df.copy()

    # Auto-sort every table with an Age/Created At pair newest-first.
    if "Age" in view.columns and "Created At" in view.columns:
        _sort_created = pd.to_datetime(view["Created At"].astype(str).str.replace(" EAT", "", regex=False), errors="coerce")
        view = view.assign(_benzino_sort_created=_sort_created).sort_values("_benzino_sort_created", ascending=False).drop(columns=["_benzino_sort_created"])

    if column_order:
        ordered = [c for c in column_order if c in view.columns]
        rest = [c for c in view.columns if c not in ordered]
        view = view[ordered + rest]

    # Market-aware table formatting:
    # Price columns keep up to 6 decimals where needed, while non-price metrics
    # remain at 2 decimals for readability.
    for _col in view.columns:
        if is_price_display_column(_col):
            view[_col] = view[_col].apply(format_market_price)
        elif pd.api.types.is_numeric_dtype(view[_col]):
            view[_col] = view[_col].apply(
                lambda x: "" if pd.isna(x) else (
                    f"{float(x):.2f}" if isinstance(x, (int, float, np.integer, np.floating)) else x
                )
            )

    search_value = ""
    status_col_name = next((c for c in view.columns if str(c).strip().lower() == "status"), None)
    if title or enable_search or show_filter_button or status_col_name:
        if status_col_name:
            left, status_col, search_col = st.columns([0.58, 0.18, 0.24], vertical_alignment="center")
            with left:
                if title:
                    st.markdown(f"<div class='benzino-panel-title'>{html.escape(title)}</div>", unsafe_allow_html=True)
            with status_col:
                status_options = ["All"] + sorted([str(v) for v in view[status_col_name].dropna().astype(str).unique() if str(v).strip()])
                selected_status = st.selectbox("Status", status_options, label_visibility="collapsed", key=f"{key}_status_filter")
            with search_col:
                if enable_search:
                    search_value = st.text_input("Search", placeholder="Search...", label_visibility="collapsed", key=f"{key}_search")
                elif show_filter_button:
                    st.button("⚱ Filter", key=f"{key}_filter_btn", width="stretch")
            if selected_status != "All":
                view = view[view[status_col_name].astype(str).eq(selected_status)].copy()
        elif enable_search and show_filter_button:
            left, filter_col, search_col = st.columns([0.62, 0.12, 0.26], vertical_alignment="center")
            with left:
                if title:
                    st.markdown(f"<div class='benzino-panel-title'>{html.escape(title)}</div>", unsafe_allow_html=True)
            with filter_col:
                st.button("⚱ Filter", key=f"{key}_filter_btn", width="stretch")
            with search_col:
                search_value = st.text_input("Search", placeholder="Search...", label_visibility="collapsed", key=f"{key}_search")
        else:
            left, right = st.columns([0.72, 0.28], vertical_alignment="center")
            with left:
                if title:
                    st.markdown(f"<div class='benzino-panel-title'>{html.escape(title)}</div>", unsafe_allow_html=True)
            with right:
                if enable_search:
                    search_value = st.text_input("Search", placeholder="Search...", label_visibility="collapsed", key=f"{key}_search")
                elif show_filter_button:
                    st.button("⚱ Filter", key=f"{key}_filter_btn", width="stretch")

    if AgGrid is None or GridOptionsBuilder is None:
        st.dataframe(view, width="stretch", hide_index=True)
        return None

    renderers = aggrid_badge_renderers()
    gb = GridOptionsBuilder.from_dataframe(view)
    gb.configure_default_column(sortable=True, filter=True, resizable=True, wrapText=False, autoHeight=False)
    if use_pagination:
        gb.configure_pagination(paginationAutoPageSize=False, paginationPageSize=page_size)
    gb.configure_grid_options(
        rowHeight=42,
        headerHeight=44,
        suppressMenuHide=True,
        domLayout="normal",
        enableCellTextSelection=True,
        animateRows=True,
        suppressRowClickSelection=True,
        suppressPaginationPanel=not show_footer,
        pagination=use_pagination,
        quickFilterText=search_value or None,
    )

    pinned = pinned or []
    badge_cols = badge_cols or {}
    numeric_cols_right = numeric_cols_right or []
    for col in view.columns:
        kwargs = {}
        if col in pinned:
            kwargs["pinned"] = "left"
        if col in badge_cols and badge_cols[col] in renderers:
            kwargs["cellRenderer"] = renderers[badge_cols[col]]
        if col in numeric_cols_right:
            kwargs["cellStyle"] = {"textAlign": "right", "fontWeight": "700"}
        if kwargs:
            gb.configure_column(col, **kwargs)

    response = AgGrid(
        view,
        gridOptions=gb.build(),
        height=height,
        fit_columns_on_grid_load=False,
        theme="balham",
        allow_unsafe_jscode=True,
        custom_css=benzino_aggrid_css(),
        key=key,
    )
    return response


def prepare_signal_table(df: pd.DataFrame, settings=None, limit: int = 300) -> pd.DataFrame:
    """Consistent signal table columns for dashboard, Explain AI and research tabs."""
    if df is None or df.empty:
        return pd.DataFrame()
    view = df.copy()

    # Friendly sequential display ID. The database ID remains untouched;
    # this only changes how Signal ID is shown in the app.
    if "signal_id" in view.columns and "created_at" in view.columns:
        _ranked = view[["signal_id", "created_at"]].drop_duplicates("signal_id").copy()
        _ranked["_created_sort"] = pd.to_datetime(_ranked["created_at"], errors="coerce", utc=True)
        _ranked = _ranked.sort_values(["_created_sort", "signal_id"], ascending=[True, True]).reset_index(drop=True)
        _ranked["Signal ID Display"] = [f"Benzino-{i:02d}" for i in range(1, len(_ranked) + 1)]
        _id_map = dict(zip(_ranked["signal_id"].astype(str), _ranked["Signal ID Display"]))
        view["signal_id"] = view["signal_id"].astype(str).map(_id_map).fillna(view["signal_id"].astype(str))

    view = view.head(limit)
    if "created_at" in view.columns:
        view["Age"] = view["created_at"].apply(age_ago)
        view["Created At"] = view["created_at"].apply(fmt_nairobi)
    if "confidence" in view.columns:
        view["Decayed Confidence"] = view.apply(lambda r: f"{decayed_confidence_value(r.get('confidence'), r.get('created_at'), r.get('timeframe')):.2f}%", axis=1)
        view["Confidence"] = pd.to_numeric(view["confidence"], errors="coerce").map(lambda x: f"{x:.2f}%" if pd.notna(x) else "")
    rename = {
        "asset": "Asset", "timeframe": "Timeframe", "signal": "Signal", "grade": "Grade",
        "entry": "Entry", "sl": "SL", "tp": "TP", "rr": "RR", "status": "Status",
        "ticker": "Ticker", "signal_id": "Signal ID", "scan_owner": "Scan Owner",
        "edge_score": "Edge Score", "ml_prob": "ML Prob", "mtf_score": "MTF Score",
        "r_multiple": "R Multiple", "exit_reason": "Exit Reason", "session": "Session",
        "reason": "Reason", "outcome": "Outcome",
        "shadow_outcome": "Hypothetical Outcome",
        "shadow_r_multiple": "Hypothetical R",
        "shadow_exit_price": "Hypothetical Exit",
    }
    view = view.rename(columns={k: v for k, v in rename.items() if k in view.columns})
    order = ["Asset", "Signal", "Grade", "Age", "Entry", "SL", "TP", "Status", "Confidence", "Decayed Confidence", "RR", "Hypothetical Outcome", "Hypothetical R", "Hypothetical Exit", "Outcome", "R Multiple", "Edge Score", "MTF Score", "Session", "Reason", "Ticker", "Timeframe", "Created At", "Signal ID", "Scan Owner"]
    return view[[c for c in order if c in view.columns] + [c for c in view.columns if c not in order]]


def apply_theme() -> None:
    st.set_page_config(page_title="Benzino ISE", page_icon="📡", layout="wide")
    st.markdown("""
    <style>

    :root {
        --font-page-title: 42px;
        --font-page-subtitle: 17px;
        --font-section-title: 24px;
        --font-panel-title: 20px;
        --font-card-title: 13px;
        --font-kpi-value: 26px;
        --font-card-caption: 14px;
        --font-table-header: 13px;
        --font-table-body: 12.5px;
        --font-control: 14px;
    }
    h1, .benzino-page-title { font-size:var(--font-page-title) !important; line-height:1.08 !important; font-weight:900 !important; color:#E8EDF2 !important; }
    h2, .benzino-section-title { font-size:var(--font-section-title) !important; line-height:1.15 !important; font-weight:850 !important; color:#E8EDF2 !important; }
    h3, .benzino-panel-title, div[data-testid="stMarkdownContainer"] h3 { font-size:var(--font-panel-title) !important; line-height:1.2 !important; font-weight:850 !important; color:#E8EDF2 !important; }
    p, .benzino-page-subtitle, .stCaptionContainer { font-size:var(--font-page-subtitle) !important; color:#8BAAB8 !important; }

    html, body, [class*="css"] { font-family: Inter, -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Arial, sans-serif; }
    * { box-sizing: border-box; }
    .stApp { background:#07111F; color:#E8EDF2; }
    [data-testid="stSidebar"] { background:#081827; border-right:1px solid #1E3050; }
    [data-testid="stSidebar"] .block-container { padding-top:22px; padding-bottom:22px; }
    .sidebar-logo { text-align:center; padding:10px 0 18px; }
    .sidebar-dish { font-size:58px; line-height:1; margin-bottom:6px; }
    .sidebar-brand { color:#00D4A3; font-weight:950; font-size:34px; letter-spacing:1.5px; }
    .sidebar-subtitle { color:#8BAAB8; font-size:15px; font-weight:750; margin-top:8px; }
    .side-divider { height:1px; background:#1E3050; margin:18px 0 22px; }
    .metric-card { background:#0F2235; border:1px solid #1E3050; border-radius:18px; padding:18px; min-height:112px; box-shadow:0 0 0 1px rgba(0,212,163,0.02); overflow:hidden; }
    .compact-card { background:#0F2235; border:1px solid #1E3050; border-radius:16px; padding:14px 16px; margin:10px 0; }
    .metric-label { color:#8BAAB8; font-size:var(--font-card-title); font-weight:800; text-transform:uppercase; letter-spacing:.5px; }
    .metric-value { color:#E8EDF2; font-size:var(--font-kpi-value); font-weight:950; margin-top:4px; line-height:1.15; overflow-wrap:anywhere; }
    .soft-card { background:#0F2235; border:1px solid #1E3050; border-radius:18px; padding:20px; margin:16px 0; line-height:1.55; }
    .ai-card { background:linear-gradient(180deg,#10283D 0%,#0F2235 100%); border:1px solid #244363; border-radius:18px; padding:22px; margin:16px 0 24px; line-height:1.65; font-size:var(--font-table-body); }
    .green { color:#00D4A3; }
    .red { color:#FF5D5D; }
    .muted { color:#8BAAB8; }
    .section-gap { height:22px; }
    .strategy-table-wrap { background:#0F2235; border:1px solid #1E3050; border-radius:16px; overflow:hidden; margin-top:10px; }
    table.strategy-table { width:100%; border-collapse:collapse; font-size:15px; }
    table.strategy-table th { text-align:left; color:#8BAAB8; background:#111A2A; padding:12px 14px; font-weight:850; }
    table.strategy-table td { padding:12px 14px; border-top:1px solid #22344A; color:#E8EDF2; }
    table.strategy-table td[title] { cursor:help; }
    .stTabs [data-baseweb="tab-list"] { gap: 8px; border-bottom: 1px solid #1E3050; }
    .stTabs [data-baseweb="tab"] { background:#0F2235; border:1px solid #1E3050; border-radius:12px 12px 0 0; color:#8BAAB8; padding:10px 16px; }
    .stTabs [aria-selected="true"] { color:#00D4A3 !important; border-bottom-color:#00D4A3 !important; }

    .stTabs [data-baseweb="tab-highlight"] { background-color:#00D4A3 !important; }
    .stTabs [aria-selected="true"] p { color:#00D4A3 !important; }
    

    /* Benzino segmented controls */
    [data-testid="stSegmentedControl"] { margin-top: -4px; margin-bottom: 10px; }
    [data-testid="stSegmentedControl"] button {
        background: rgba(16,31,53,.95) !important;
        border: 1px solid rgba(64,92,127,.75) !important;
        color: #8BAAB8 !important;
        min-width: 70px !important;
        height: 38px !important;
        border-radius: 0 !important;
        font-weight: 850 !important;
        outline: none !important;
        box-shadow: none !important;
    }
    [data-testid="stSegmentedControl"] button:first-child { border-radius:10px 0 0 10px !important; }
    [data-testid="stSegmentedControl"] button:last-child { border-radius:0 10px 10px 0 !important; }

    /* Force selected segmented-control item to Benzino green.
       Streamlit/BaseWeb can expose the selected state through different attrs/classes
       depending on version, so this intentionally covers all common selected states. */
    [data-testid="stSegmentedControl"] button[aria-pressed="true"],
    [data-testid="stSegmentedControl"] button[aria-selected="true"],
    [data-testid="stSegmentedControl"] button[aria-checked="true"],
    [data-testid="stSegmentedControl"] button[data-selected="true"],
    [data-testid="stSegmentedControl"] button:has(input:checked),
    [data-testid="stSegmentedControl"] label:has(input:checked),
    [data-testid="stSegmentedControl"] [role="radio"][aria-checked="true"],
    [data-testid="stSegmentedControl"] [role="option"][aria-selected="true"] {
        background: linear-gradient(135deg,#00C896,#00A67D) !important;
        color: #FFFFFF !important;
        border: 1px solid #00D4A3 !important;
        box-shadow: 0 0 0 1px rgba(0,212,163,.35) inset, 0 0 12px rgba(0,212,163,.14) !important;
        outline: none !important;
    }

    
    /* Force Benzino green selected state for equity curve segmented controls */
    [data-testid="stSegmentedControl"] button[aria-pressed="true"],
    [data-testid="stSegmentedControl"] button[aria-selected="true"],
    [data-testid="stSegmentedControl"] button[aria-checked="true"],
    [data-testid="stSegmentedControl"] button[data-selected="true"],
    [data-testid="stSegmentedControl"] [role="radio"][aria-checked="true"],
    [data-testid="stSegmentedControl"] [role="option"][aria-selected="true"] {
        border-color: #00C896 !important;
        box-shadow: 0 0 0 1px #00C896 inset !important;
        outline: none !important;
    }

    [data-testid="stSegmentedControl"] *:focus,
    [data-testid="stSegmentedControl"] *:focus-visible,
    [data-testid="stSegmentedControl"] *:active {
        outline: none !important;
        box-shadow: none !important;
    }


    /* Remove Streamlit theme focus ring; it was showing as red around selected pills. */
    [data-testid="stSegmentedControl"] button:focus,
    [data-testid="stSegmentedControl"] button:focus-visible,
    [data-testid="stSegmentedControl"] button:active,
    [data-testid="stSegmentedControl"] label:focus,
    [data-testid="stSegmentedControl"] label:focus-visible,
    [data-testid="stSegmentedControl"] [role="radio"]:focus,
    [data-testid="stSegmentedControl"] [role="radio"]:focus-visible {
        outline: none !important;
        border-color: #00D4A3 !important;
        box-shadow: 0 0 0 1px rgba(0,212,163,.28) inset !important;
    }

    .benzino-equity-range {
        display:flex;
        justify-content:flex-end;
        align-items:center;
        margin-top:-42px;
        margin-bottom:14px;
        width:100%;
    }

    /* REAL fix: Streamlit's actual selected-segment button uses kind="segmented_controlActive"
       and data-testid="stBaseButton-segmented_controlActive" — confirmed via browser devtools.
       None of the aria-pressed/aria-selected/aria-checked/data-selected guesses above ever
       matched the real DOM, which is why the border stayed red (Streamlit's default) despite
       every previous attempt. This rule targets the actual element. */
    button[kind="segmented_controlActive"],
    [data-testid="stBaseButton-segmented_controlActive"] {
        background: linear-gradient(135deg, #00C896, #00A67D) !important;
        border: 1px solid #00C896 !important;
        border-color: #00C896 !important;
        color: #FFFFFF !important;
        box-shadow: 0 0 0 1px rgba(0,200,150,.35) inset !important;
        outline: none !important;
    }

    button[kind="segmented_controlActive"]:focus,
    button[kind="segmented_controlActive"]:focus-visible,
    button[kind="segmented_controlActive"]:active,
    [data-testid="stBaseButton-segmented_controlActive"]:focus,
    [data-testid="stBaseButton-segmented_controlActive"]:focus-visible {
        border-color: #00C896 !important;
        outline: none !important;
        box-shadow: 0 0 0 1px rgba(0,200,150,.35) inset !important;
    }

    /* FINAL dashboard override: Equity Curve segmented selector active/focus color */
    [data-testid="stSegmentedControl"] button[aria-pressed="true"],
    [data-testid="stSegmentedControl"] button[aria-selected="true"],
    [data-testid="stSegmentedControl"] button[aria-checked="true"],
    [data-testid="stSegmentedControl"] button[data-selected="true"],
    [data-testid="stSegmentedControl"] [role="radio"][aria-checked="true"],
    [data-testid="stSegmentedControl"] [role="option"][aria-selected="true"],
    [data-testid="stSegmentedControl"] div[aria-checked="true"],
    [data-testid="stSegmentedControl"] label:has(input:checked),
    [data-testid="stSegmentedControl"] label:has(input:checked) div,
    [data-testid="stSegmentedControl"] input:checked + div {
        background: linear-gradient(135deg,#00C896,#00A67D) !important;
        border-color: #00C896 !important;
        color: #FFFFFF !important;
        outline-color: #00C896 !important;
        box-shadow: 0 0 0 1px rgba(0,200,150,.35) inset !important;
    }

    [data-testid="stSegmentedControl"] button:focus,
    [data-testid="stSegmentedControl"] button:focus-visible,
    [data-testid="stSegmentedControl"] [role="radio"]:focus,
    [data-testid="stSegmentedControl"] [role="radio"]:focus-visible,
    [data-testid="stSegmentedControl"] label:focus-within,
    [data-testid="stSegmentedControl"] div:focus,
    [data-testid="stSegmentedControl"] div:focus-visible {
        border-color: #00C896 !important;
        outline: none !important;
        box-shadow: 0 0 0 1px rgba(0,200,150,.35) inset !important;
    }


    /* Force Equity Curve selector selected state to Benzino green */
    div[data-testid="stHorizontalBlock"]:has(.benzino-equity-range) [data-testid="stSegmentedControl"] {
        justify-content: flex-end !important;
    }

    div[data-testid="stHorizontalBlock"]:has(.benzino-equity-range) [data-testid="stSegmentedControl"] button[aria-pressed="true"],
    div[data-testid="stHorizontalBlock"]:has(.benzino-equity-range) [data-testid="stSegmentedControl"] button[aria-selected="true"],
    div[data-testid="stHorizontalBlock"]:has(.benzino-equity-range) [data-testid="stSegmentedControl"] [role="radio"][aria-checked="true"] {
        background: linear-gradient(135deg, #00C896, #00A67D) !important;
        border-color: #00C896 !important;
        color: #FFFFFF !important;
        box-shadow: none !important;
        outline: none !important;
    }

    div[data-testid="stHorizontalBlock"]:has(.benzino-equity-range) [data-testid="stSegmentedControl"] button:focus,
    div[data-testid="stHorizontalBlock"]:has(.benzino-equity-range) [data-testid="stSegmentedControl"] button:focus-visible,
    div[data-testid="stHorizontalBlock"]:has(.benzino-equity-range) [data-testid="stSegmentedControl"] [role="radio"]:focus,
    div[data-testid="stHorizontalBlock"]:has(.benzino-equity-range) [data-testid="stSegmentedControl"] [role="radio"]:focus-visible {
        border-color: #00C896 !important;
        box-shadow: none !important;
        outline: none !important;
    }


    .benzino-equity-range + div [data-testid="stSegmentedControl"],
    [data-testid="stSegmentedControl"] {
        display:flex !important;
        justify-content:flex-end !important;
    }

    [data-testid="stSegmentedControl"] button {
        border-color:#3A3E48 !important;
        color:#8BAAB8 !important;
        box-shadow:none !important;
        outline:none !important;
    }

    [data-testid="stSegmentedControl"] button[aria-pressed="true"],
    [data-testid="stSegmentedControl"] button[aria-selected="true"],
    [data-testid="stSegmentedControl"] button[aria-checked="true"],
    [data-testid="stSegmentedControl"] button[data-selected="true"],
    [data-testid="stSegmentedControl"] [role="radio"][aria-checked="true"],
    [data-testid="stSegmentedControl"] [role="option"][aria-selected="true"] {
        background:linear-gradient(135deg,#00C896,#00A67D) !important;
        color:#FFFFFF !important;
        border-color:#00C896 !important;
        box-shadow:0 0 0 1px rgba(0,212,163,.25) inset !important;
        outline:none !important;
    }

    [data-testid="stSegmentedControl"] button:focus,
    [data-testid="stSegmentedControl"] button:focus-visible,
    [data-testid="stSegmentedControl"] button:active,
    [data-testid="stSegmentedControl"] *:focus,
    [data-testid="stSegmentedControl"] *:focus-visible {
        outline:none !important;
        box-shadow:0 0 0 1px rgba(0,212,163,.25) inset !important;
        border-color:#00C896 !important;
    }
    .grade-legend-grid { display:grid; grid-template-columns:1fr 1fr; gap:2px 18px; margin-top:-8px; }
    .grade-legend-item { display:flex; align-items:center; justify-content:space-between; border-bottom:1px solid rgba(32,58,89,.55); padding:3px 0; gap:10px; min-height:25px; }
    .grade-legend-name { display:flex; align-items:center; gap:8px; color:#8BAAB8; font-weight:900; font-size:13px; }
    .grade-legend-value { color:#E8EDF2; font-weight:950; white-space:nowrap; font-size:13px; }

    [data-testid="stSegmentedControl"] button[aria-checked="true"],
    [data-testid="stSegmentedControl"] [aria-checked="true"] {
        background: linear-gradient(135deg, #00C896, #00A67D) !important;
        color: #FFFFFF !important;
        border: 1px solid #00D4A3 !important;
        box-shadow: 0 0 0 1px rgba(0,212,163,.35) inset !important;
        outline: none !important;
    }


    div[data-testid="stDataFrame"] { border:1px solid #1E3050; border-radius:14px; overflow:hidden; margin-top:12px; }

    /* Primary form/submit buttons (e.g. "Save watchlist", "Activate Settings"):
       force green background with fully opaque WHITE text on every possible
       internal wrapper Streamlit/BaseWeb renders the label in.
       Confirmed via devtools: st.form_submit_button(type="primary") renders
       kind="primaryFormSubmit" / data-testid="stBaseButton-primaryFormSubmit"
       — NOT plain kind="primary" like a regular st.button. Every rule below
       must include both kinds or form-submit buttons stay on Streamlit's
       default red with zero custom styling applied. */
    button[kind="primary"],
    button[kind="primary"] div,
    button[kind="primary"] p,
    button[kind="primary"] span,
    button[kind="primaryFormSubmit"],
    button[kind="primaryFormSubmit"] div,
    button[kind="primaryFormSubmit"] p,
    button[kind="primaryFormSubmit"] span,
    [data-testid="stFormSubmitButton"] button,
    [data-testid="stFormSubmitButton"] button div,
    [data-testid="stFormSubmitButton"] button p,
    [data-testid="stFormSubmitButton"] button span,
    [data-testid="baseButton-primary"],
    [data-testid="baseButton-primary"] div,
    [data-testid="baseButton-primary"] p,
    [data-testid="baseButton-primary"] span,
    [data-testid="stBaseButton-primaryFormSubmit"],
    [data-testid="stBaseButton-primaryFormSubmit"] div,
    [data-testid="stBaseButton-primaryFormSubmit"] p,
    [data-testid="stBaseButton-primaryFormSubmit"] span {
        color: #FFFFFF !important;
        opacity: 1 !important;
    }
    button[kind="primary"],
    button[kind="primaryFormSubmit"],
    [data-testid="baseButton-primary"],
    [data-testid="stBaseButton-primaryFormSubmit"] {
        background: #00A97F !important;
        border-color: #00D4A3 !important;
    }
    .stDownloadButton button[kind="primary"] * { color:#FFFFFF !important; }

    /* Multiselect tags (e.g. Watchlist asset pills): give these a distinct
       colour from the green "Save watchlist" action button so the two don't
       visually blend together. Slate-blue matches the existing neutral/closed
       badge colour used elsewhere in the app (ag-status-closed).
       Confirmed via devtools: the real element is a <span data-baseweb="tag">,
       not a <div> — the earlier div-only selector never matched anything. */
    span[data-baseweb="tag"],
    div[data-baseweb="tag"] {
        background-color: #3D5A8A !important;
        border-color: #7AA6FF !important;
        color: #FFFFFF !important;
    }
    span[data-baseweb="tag"] *,
    div[data-baseweb="tag"] * {
        color: #FFFFFF !important;
    }
    span[data-baseweb="tag"] svg,
    div[data-baseweb="tag"] svg {
        fill: #FFFFFF !important;
    }

    input, textarea, div[data-baseweb="select"] > div { border-radius:12px !important; }
    .danger-button button { background:#8B1E2D !important; border-color:#FF5D5D !important; color:#fff !important; }
    .grey-note { background:#111A2A; border:1px solid #26364A; border-radius:14px; padding:12px 14px; color:#A9BBC9; }

    /* Disabled buttons (e.g. "Activate Settings" while alerts are already
       active, or "Deactivate alerts" while inactive): force a clearly greyed
       look that overrides the green primary/danger styling above, so the
       mutually-exclusive activate/deactivate pair reads as genuinely
       unclickable rather than just a slightly dimmed version of the action. */
    button:disabled,
    button[disabled],
    button:disabled *,
    button[disabled] * {
        background: #1C2B40 !important;
        border-color: #2A3D57 !important;
        color: #5C7088 !important;
        opacity: 1 !important;
        cursor: not-allowed !important;
    }
    
    /* ===== Minimal Benzino branding update ===== */
    .benzino-login-wrap {
        max-width: 1320px;
        margin: 0 auto;
        min-height: calc(100vh - 75px);
        display: flex;
        align-items: center;
    }
    .benzino-login-left {
        background: linear-gradient(145deg,#10263A 0%,#0B1A2B 100%);
        border: 1px solid #203A59;
        border-radius: 26px;
        padding: 34px 34px;
        min-height: 610px;
        display: flex;
        align-items: center;
        justify-content: center;
        text-align: center;
        box-shadow: 0 24px 70px rgba(0,0,0,.30);
    }
    .benzino-login-logo {
        width: min(390px, 42vw);
        max-width: 100%;
        border-radius: 26px;
        box-shadow: 0 24px 55px rgba(0,0,0,.45);
        border: 1px solid rgba(214,168,78,.28);
    }
    .benzino-login-tagline {
        color: #E8EDF2;
        font-size: 22px;
        font-weight: 900;
        line-height: 1.4;
        margin-top: 28px;
    }
    .benzino-login-note {
        color: #8BAAB8;
        font-size: 14px;
        font-weight: 800;
        margin-top: 18px;
    }
    .benzino-login-form-head {
        background: linear-gradient(145deg,#10263A 0%,#0B1A2B 100%);
        border: 1px solid #203A59;
        border-radius: 22px;
        padding: 30px 24px;
        text-align: center;
        margin-bottom: 22px;
        box-shadow: 0 18px 48px rgba(0,0,0,.24);
    }
    .benzino-login-title {
        color: #E8EDF2;
        font-size: 38px;
        font-weight: 950;
        line-height: 1.1;
    }
    .benzino-login-subtitle {
        color: #8BAAB8;
        font-size: 17px;
        font-weight: 750;
        margin-top: 10px;
    }
    .benzino-topbar {
        display: flex;
        align-items: center;
        justify-content: flex-end;
        margin: 0 0 14px;
    }
    .benzino-user-card {
        display: flex;
        align-items: center;
        gap: 12px;
        min-width: 230px;
        background: linear-gradient(145deg,#10263A 0%,#0B1A2B 100%);
        border: 1px solid rgba(137,95,255,.55);
        border-radius: 18px;
        padding: 10px 14px;
        box-shadow: 0 14px 38px rgba(0,0,0,.22);
    }
    .benzino-user-logo {
        width: 42px;
        height: 42px;
        object-fit: cover;
        border-radius: 12px;
        border: 1px solid rgba(214,168,78,.25);
    }
    .benzino-user-name {
        color: #E8EDF2;
        font-size: 18px;
        font-weight: 950;
        line-height: 1.05;
    }
    .benzino-user-role {
        color: #8BAAB8;
        font-size: 11px;
        font-weight: 900;
        text-transform: uppercase;
        letter-spacing: .9px;
        margin-top: 4px;
    }
    .benzino-sidebar-logo-img {
        width: 190px;
        max-width: 100%;
        border-radius: 24px;
        box-shadow: 0 18px 45px rgba(0,0,0,.34);
        border: 1px solid rgba(214,168,78,.25);
    }
    .benzino-sidebar-logo-only {
        text-align: center;
        padding: 8px 0 18px;
    }

    
    /* ===== Benzino requested login + account dropdown polish ===== */
    .benzino-login-card-exact {
        background: linear-gradient(145deg,#10263A 0%,#0B1A2B 100%);
        border: 1px solid #203A59;
        border-radius: 14px;
        padding: 28px 26px 22px;
        box-shadow: 0 20px 54px rgba(0,0,0,.30);
        margin-bottom: 18px;
    }
    .benzino-login-title-exact {
        text-align: center;
        color: #E8EDF2;
        font-size: 28px;
        font-weight: 950;
        line-height: 1.05;
        margin-bottom: 7px;
    }
    .benzino-login-sub-exact {
        text-align: center;
        color: #8BAAB8;
        font-size: 14px;
        font-weight: 750;
        margin-bottom: 24px;
    }
    .benzino-login-footer-exact {
        text-align: center;
        color: #8BAAB8;
        font-size: 13px;
        font-weight: 800;
        margin-top: 16px;
    }
    .benzino-login-footer-exact span {
        color: #00D4A3;
        margin-left: 8px;
        font-weight: 950;
    }
    .benzino-account-menu details {
        background: linear-gradient(145deg,#10263A 0%,#0B1A2B 100%) !important;
        border: 1px solid rgba(137,95,255,.55) !important;
        border-radius: 18px !important;
        box-shadow: 0 14px 38px rgba(0,0,0,.22);
    }
    .benzino-user-card {
        display: flex;
        align-items: center;
        gap: 12px;
        min-width: 100%;
        background: linear-gradient(145deg,#10263A 0%,#0B1A2B 100%);
        border: 1px solid #203A59;
        border-radius: 16px;
        padding: 10px 14px;
    }
    .benzino-user-logo {
        width: 42px;
        height: 42px;
        object-fit: cover;
        border-radius: 12px;
        border: 1px solid rgba(214,168,78,.25);
    }
    .benzino-user-name {
        color: #E8EDF2;
        font-size: 18px;
        font-weight: 950;
        line-height: 1.05;
    }
    .benzino-user-role {
        color: #8BAAB8;
        font-size: 11px;
        font-weight: 900;
        text-transform: uppercase;
        letter-spacing: .9px;
        margin-top: 4px;
    }



    /* ===== v5 dashboard UI match polish ===== */
    [data-testid="stAppViewContainer"] > .main .block-container {
        padding-top: 1.35rem !important;
        padding-left: 2.2rem !important;
        padding-right: 2.2rem !important;
        max-width: 100% !important;
    }
    [data-testid="stSidebar"] { min-width: 285px !important; width: 285px !important; }
    [data-testid="stSidebar"] .block-container { padding: 24px 18px 18px !important; }
    .benzino-sidebar-logo-img { width: 210px !important; height:auto !important; border-radius: 0 !important; image-rendering:auto !important; }
    .benzino-sidebar-logo-only { padding: 6px 0 20px !important; }
    .side-divider { margin: 18px 0 18px !important; }
    .benzino-refresh-wrap { margin: 4px 0 26px; }
    .benzino-side-title { color:#8BAAB8; font-size:12px; font-weight:950; letter-spacing:1.4px; margin:10px 0 10px; text-transform:uppercase; }
    [data-testid="stSidebar"] div[role="radiogroup"] { gap: 9px; }
    [data-testid="stSidebar"] label[data-baseweb="radio"] {
        width: 100%;
        padding: 12px 12px;
        margin: 0 0 8px 0;
        border-radius: 9px;
        color: #C9D5E3 !important;
        font-weight: 850;
        transition: all .15s ease;
    }
    [data-testid="stSidebar"] label[data-baseweb="radio"]:has(input:checked) {
        background: linear-gradient(90deg, rgba(0,212,163,.20), rgba(16,38,58,.72));
        border-left: 4px solid #00D4A3;
        color: #E8EDF2 !important;
    }
    [data-testid="stSidebar"] label[data-baseweb="radio"] > div:first-child { display:none !important; }
    [data-testid="stSidebar"] [data-testid="stVerticalBlock"] > div:has(.benzino-version-pill) { margin-top: 36px !important; }
    .benzino-version-pill { border:1px solid #244363; border-radius:9px; padding:9px 12px; color:#C9D5E3; font-size:12px; text-align:center; background:#0B1A2B; }
    .benzino-page-topbar { margin-bottom: 22px; }
    .benzino-account-menu details, .benzino-control-menu details {
        background: linear-gradient(145deg,#10263A 0%,#0B1A2B 100%) !important;
        border: 1px solid #244363 !important;
        border-radius: 10px !important;
        min-height: 52px;
        box-shadow: none !important;
    }
    .benzino-account-menu summary, .benzino-control-menu summary {
        color:#E8EDF2 !important;
        font-weight:900 !important;
        font-size:15px !important;
        white-space:nowrap !important;
    }
    .benzino-account-menu button[kind="secondary"] { color:#FF5D5D !important; border-color:#244363 !important; }
    .benzino-control-menu { min-width: 285px; }
    .benzino-account-menu { min-width: 210px; }
    .benzino-login-shell-card {
        border:1px solid #244363;
        border-radius:10px;
        min-height: calc(100vh - 48px);
        display:flex;
        align-items:center;
        padding:26px;
        background: radial-gradient(circle at 50% 0%, rgba(16,38,58,.38), rgba(7,17,31,.18));
    }
    .benzino-login-left { min-height: 520px !important; border-radius: 0 !important; background: transparent !important; border: 0 !important; box-shadow:none !important; }
    .benzino-login-card-exact { max-width: 520px; margin: 0 auto 18px !important; }
    .benzino-login-logo { width:min(430px, 42vw) !important; box-shadow:none !important; border:0 !important; border-radius:0 !important; }
    @media (max-width: 900px){ .benzino-control-menu, .benzino-account-menu { min-width: 100%; } }

    /* ===== v6 dashboard redesign: icon stat cards, equity panel, donut, generated table ===== */
    .benzino-stat-card {
        background: linear-gradient(145deg,#10263A 0%,#0B1A2B 100%);
        border: 1px solid #203A59;
        border-radius: 18px;
        padding: 18px 52px 16px 18px;
        height: 118px;
        min-height: 118px;
        max-height: 118px;
        position: relative;
        display: flex;
        align-items: center;
        justify-content: flex-start;
        overflow: hidden;
    }
    .benzino-stat-card > div:first-child {
        width: calc(100% - 6px);
        transform: translateY(3px);
    }
    .benzino-stat-card-no-icon { padding-right:18px !important; }
    .benzino-stat-card-no-icon .benzino-stat-label { max-width:100% !important; text-transform:uppercase; letter-spacing:.5px; }
    .benzino-stat-label {
        color:#8BAAB8;
        font-size:clamp(11px, .72vw, 13px);
        font-weight:850;
        line-height:1.16;
        white-space:normal;
        max-width: 135px;
    }
    .benzino-stat-value {
        color:#E8EDF2;
        font-size:clamp(21px, 1.45vw, 27px);
        font-weight:950;
        margin-top:10px;
        line-height:1.05;
        white-space:nowrap;
        letter-spacing:-.4px;
    }
    .benzino-stat-note {
        font-size:clamp(10px, .68vw, 12px);
        font-weight:800;
        margin-top:8px;
        line-height:1.16;
        max-width: 160px;
        white-space:normal;
    }
    .benzino-stat-note.up { color:#00D4A3; }
    .benzino-stat-note.down { color:#FF5D5D; }
    .benzino-stat-note.flat { color:#8BAAB8; }
    .benzino-stat-icon {
        width: 30px; height: 30px; min-width:30px; border-radius: 9px;
        display:flex; align-items:center; justify-content:center;
        font-size: 15px;
        position:absolute;
        top:18px;
        right:16px;
        z-index:1;
        opacity:.95;
    }
    .benzino-stat-icon.teal { background: rgba(0,212,163,.16); color:#00D4A3; }
    .benzino-stat-icon.gold { background: rgba(214,168,78,.16); color:#D6A84E; }
    .benzino-stat-icon.purple { background: rgba(137,95,255,.16); color:#A98CFF; }

    .benzino-panel {
        background: linear-gradient(145deg,#10263A 0%,#0B1A2B 100%);
        border: 1px solid #203A59;
        border-radius: 18px;
        padding: 20px 22px;
        margin-top: 18px;
    }
    .benzino-panel-head { display:flex; align-items:center; justify-content:space-between; margin-bottom:14px; gap:12px; }
    .benzino-panel-title { color:#E8EDF2; font-size:17px; font-weight:900; }
    .benzino-panel-pill { color:#00D4A3; font-size:13px; font-weight:900; background:rgba(0,212,163,.12); border-radius:8px; padding:4px 10px; }

    .benzino-grade-pill { display:inline-block; border-radius:7px; padding:3px 10px; font-weight:900; font-size:12.5px; }
    .benzino-grade-pill.grade-Ap { background:rgba(0,212,163,.18); color:#00D4A3; }
    .benzino-grade-pill.grade-A { background:rgba(76,140,255,.18); color:#7AA6FF; }
    .benzino-grade-pill.grade-B { background:rgba(214,168,78,.18); color:#D6A84E; }
    .benzino-grade-pill.grade-C { background:rgba(255,93,93,.18); color:#FF5D5D; }
    .benzino-dir-pill { font-weight:900; font-size:13px; }
    .benzino-dir-pill.buy { color:#00D4A3; }
    .benzino-dir-pill.sell { color:#FF5D5D; }
    .benzino-status-pill { display:inline-block; border-radius:7px; padding:3px 10px; font-weight:850; font-size:12.5px; }
    .benzino-status-pill.open { background:rgba(0,212,163,.16); color:#00D4A3; }
    .benzino-status-pill.closed { background:rgba(139,158,176,.16); color:#A9BBC9; }

    .benzino-summary-row { display:flex; align-items:center; justify-content:space-between; padding:11px 0; border-bottom:1px solid #16263B; line-height:1.15; }
    .benzino-summary-row:last-child { border-bottom:none; }
    .benzino-summary-label { color:#8BAAB8; font-size:14px; font-weight:850; }
    .benzino-summary-value { color:#E8EDF2; font-size:14px; font-weight:950; }
    .benzino-summary-value.green { color:#00D4A3; }
    .benzino-summary-value.red { color:#FF5D5D; }

    .benzino-empty-note { color:#8BAAB8; font-size:14px; padding:18px 4px; }

    .benzino-generated-toolbar {
        display:flex;
        align-items:center;
        justify-content:space-between;
        gap:14px;
        margin-bottom:10px;
    }
    .benzino-generated-actions {
        display:flex;
        align-items:center;
        gap:10px;
        min-width: 330px;
        justify-content:flex-end;
    }
    .benzino-filter-pill {
        border:1px solid #244363;
        border-radius:8px;
        padding:8px 13px;
        color:#C9D5E3;
        font-weight:850;
        background:rgba(7,17,31,.45);
        white-space:nowrap;
    }
    .benzino-generated-count {
        color:#8BAAB8;
        font-size:12px;
        font-weight:750;
        margin-top:8px;
    }
    .benzino-html-table-wrap {
        border:1px solid #16263B;
        border-radius:10px;
        overflow:auto;
        max-height:520px;
    }
    table.benzino-html-table {
        width:100%;
        border-collapse:collapse;
        font-size:12px;
    }
    table.benzino-html-table th {
        text-align:left;
        color:#C9D5E3;
        background:#0B1A2B;
        padding:10px 9px;
        border-bottom:1px solid #203A59;
        white-space:nowrap;
        position:sticky;
        top:0;
        z-index:1;
    }
    table.benzino-html-table td {
        color:#C9D5E3;
        padding:9px;
        border-bottom:1px solid #16263B;
        white-space:nowrap;
    }
    .sig-buy { color:#00D4A3; font-weight:950; }
    .sig-sell { color:#FF5D5D; font-weight:950; }
    .badge {
        display:inline-flex;
        align-items:center;
        justify-content:center;
        border-radius:6px;
        padding:2px 7px;
        font-size:11px;
        font-weight:900;
        line-height:1.3;
    }
    .badge-active, .badge-open { background:rgba(0,212,163,.16); color:#00D4A3; }
    .badge-skipped, .badge-closed { background:rgba(139,158,176,.16); color:#A9BBC9; }
    .badge-grade-ap { background:rgba(0,212,163,.18); color:#00D4A3; }
    .badge-grade-a { background:rgba(76,140,255,.18); color:#7AA6FF; }
    .badge-grade-b { background:rgba(214,168,78,.18); color:#D6A84E; }
    .badge-grade-c { background:rgba(255,93,93,.18); color:#FF5D5D; }
    .badge-grade-no-trade { background:rgba(137,95,255,.18); color:#A98CFF; }

    

    /* v5.4: keep sidebar locked and move dashboard content higher */
    [data-testid="stSidebar"] {
        height: 100vh !important;
        overflow: hidden !important;
    }
    [data-testid="stSidebar"] > div,
    [data-testid="stSidebar"] .block-container {
        height: 100vh !important;
        overflow: hidden !important;
    }
    [data-testid="stSidebar"] .block-container {
        padding-top: 18px !important;
        padding-bottom: 14px !important;
    }
    .benzino-sidebar-logo-img {
        max-height: 248px !important;
        object-fit: contain !important;
    }
    .benzino-version-pill {
        margin-top: 64px !important;
    }
    [data-testid="stAppViewContainer"] > .main .block-container {
        padding-top: 0 !important;
    }
    div[data-testid="stHorizontalBlock"]:has(.benzino-control-menu) {
        margin-bottom: -78px !important;
        position: relative;
        z-index: 20;
        pointer-events: auto;
    }
    .benzino-control-menu, .benzino-account-menu {
        pointer-events: auto;
    }
    .benzino-page-title {
        margin-top: 0 !important;
    }

    /* v5.5: tighten main content and suppress Plotly keyword deprecation banners */
    div[data-testid="stAlert"]:has(code) { display:none !important; }
    .benzino-dashboard-top-spacer { height: 0 !important; margin:0 !important; padding:0 !important; }

    /* v5.6: hard-lock login page and sidebar scrolling */
    body:has(#benzino-login-anchor),
    html:has(#benzino-login-anchor),
    .stApp:has(#benzino-login-anchor),
    [data-testid="stAppViewContainer"]:has(#benzino-login-anchor),
    [data-testid="stMain"]:has(#benzino-login-anchor),
    [data-testid="stMainBlockContainer"]:has(#benzino-login-anchor) {
        height: 100vh !important;
        max-height: 100vh !important;
        overflow: hidden !important;
    }
    [data-testid="stSidebar"], [data-testid="stSidebar"] * { scrollbar-width: none !important; }
    [data-testid="stSidebar"]::-webkit-scrollbar,
    [data-testid="stSidebar"] *::-webkit-scrollbar { display:none !important; }

</style>
    """, unsafe_allow_html=True)


def metric_card(label: str, value: str, note: str = "") -> None:
    """Standard Benzino KPI card used across all pages."""
    st.markdown(
        f"""
        <div class='benzino-stat-card benzino-stat-card-no-icon'>
          <div>
            <div class='benzino-stat-label'>{html.escape(label)}</div>
            <div class='benzino-stat-value'>{html.escape(str(value))}</div>
            {f"<div class='benzino-stat-note flat'>{html.escape(note)}</div>" if note else ""}
          </div>
        </div>
        """,
        unsafe_allow_html=True,
    )


def stat_card(label: str, value: str, note: str = "", icon: str = "●", tone: str = "teal", note_tone: str = "flat") -> None:
    """Icon-badge stat card used on the redesigned Dashboard page."""
    st.markdown(
        f"""
        <div class='benzino-stat-card'>
          <div>
            <div class='benzino-stat-label'>{html.escape(label)}</div>
            <div class='benzino-stat-value'>{html.escape(str(value))}</div>
            {f"<div class='benzino-stat-note {html.escape(note_tone)}'>{html.escape(note)}</div>" if note else ""}
          </div>
          <div class='benzino-stat-icon {html.escape(tone)}'>{icon}</div>
        </div>
        """,
        unsafe_allow_html=True,
    )


def page_header(title: str, subtitle: str) -> None:
    st.markdown(f"<h1 class='benzino-page-title' style='color:#E8EDF2;margin-bottom:0'>{html.escape(title)}</h1>", unsafe_allow_html=True)
    st.markdown(f"<div class='muted' style='margin-bottom:14px'>{html.escape(subtitle)}</div>", unsafe_allow_html=True)



def render_user_topbar(username: str, settings: dict) -> dict:
    role = user_role(username).title()
    left, control_col, account_col = st.columns([0.58, 0.24, 0.18], vertical_alignment="top")
    with control_col:
        st.markdown("<div class='benzino-control-menu'>", unsafe_allow_html=True)
        with st.expander("☷  Control Panel", expanded=False):
            current_account = float(settings.get("account_size", 10000) or 10000)
            account_text = st.text_input("Account size", value=f"{current_account:,.0f}", key="top_account_size")
            account = parse_account_size(account_text, current_account)
            leverage = st.number_input("Leverage", min_value=1, max_value=500, value=int(settings.get("leverage", 100)), step=1, key="top_leverage")
            risk_pct = st.number_input("Risk per trade (%)", min_value=0.1, max_value=10.0, value=float(settings.get("risk_pct", 1.0)), step=0.1, key="top_risk_pct")
            preferred_tf = st.selectbox(
                "Preferred timeframe",
                ["15m", "1h", "4h", "1d"],
                index=["15m", "1h", "4h", "1d"].index(str(settings.get("preferred_timeframe", "1h"))) if str(settings.get("preferred_timeframe", "1h")) in ["15m", "1h", "4h", "1d"] else 1,
                key="top_preferred_tf",
            )
            st.markdown(
                f"""
                <div class='compact-card'>
                  <div class='metric-label'>Account parameters</div>
                  <div style='font-weight:850;margin-top:6px;'>Risk: ${account * risk_pct / 100:,.2f}</div>
                  <div class='muted'>Leverage 1:{int(leverage)} · Preferred TF {preferred_tf}</div>
                </div>
                """, unsafe_allow_html=True
            )
            new_settings = settings.copy()
            new_settings.update({"account_size": account, "leverage": leverage, "risk_pct": risk_pct, "preferred_timeframe": preferred_tf, "view_timeframe": preferred_tf})
            if new_settings != settings:
                save_settings(username, new_settings)
                settings = new_settings
        st.markdown("</div>", unsafe_allow_html=True)

    with account_col:
        st.markdown("<div class='benzino-account-menu'>", unsafe_allow_html=True)
        with st.expander(f"👤  {username}⌄", expanded=False):
            if st.button("↪  Logout", key="topbar_logout", width="stretch"):
                revoke_remember_token(get_query_param_value("remember_token", ""))
                try:
                    if "remember_token" in st.query_params:
                        del st.query_params["remember_token"]
                except Exception:
                    pass
                st.session_state.pop("auth_user", None)
                st.session_state.auth_mode = "login"
                st.rerun()
        st.markdown("</div>", unsafe_allow_html=True)
    return settings


def parse_account_size(value: str, fallback: float = 10000.0) -> float:
    try:
        cleaned = re.sub(r"[^0-9.]", "", str(value or ""))
        return float(cleaned) if cleaned else float(fallback)
    except Exception:
        return float(fallback)


def sidebar_controls(username: str, settings: dict) -> str:
    with st.sidebar:
        st.markdown(
            f"""
            <div class='benzino-sidebar-logo-only'>
              <img class='benzino-sidebar-logo-img' src='{BRAND_LOGO_DATA_URI}' alt='Benzino logo'>
            </div>
            """,
            unsafe_allow_html=True,
        )
        st.markdown("<div class='benzino-refresh-wrap'>", unsafe_allow_html=True)
        if st.button("⟳  Refresh Data", width="stretch", key="sidebar_refresh_data"):
            with st.spinner("Refreshing dashboard from Supabase…"):
                st.cache_data.clear()
            st.rerun()
        st.markdown("</div>", unsafe_allow_html=True)
        st.markdown("<div class='benzino-side-title'>Main Menu</div>", unsafe_allow_html=True)
        page = st.radio(
            "Main Menu",
            ["Dashboard", "Asset Deep Dive", "Market News", "Workflow", "Settings"],
            label_visibility="collapsed",
            key="main_navigation",
        )
        st.markdown(f"<div class='benzino-version-pill'>{APP_VERSION}</div>", unsafe_allow_html=True)
    return page


# ═══════════════════════════════════════════════════════════════════════════════
# PAGES
# ═══════════════════════════════════════════════════════════════════════════════

def render_opportunity_board(username: str, settings: dict) -> None:
    page_header("Dashboard", "Real-time overview of your trading system")
    with st.spinner("Loading latest saved Supabase data…"):
        raw_df = enrich_position_sizing(load_signals_for_user(username, settings), settings)
        df = apply_timeframe_view(raw_df, settings)
    if df.empty:
        st.info("No scanner rows yet for your watchlist/timeframe since account activation. Confirm your watchlist is saved, wait for the GitHub cron, then refresh dashboard.")
        return

    trade_df = df[df["grade"].astype(str).isin(VALID_GRADES)].copy()
    no_trade_df = df[df["grade"].astype(str).eq("NO TRADE")].copy()
    open_df = trade_df[trade_df["status"].astype(str).str.upper().eq("OPEN")]

    perf = compute_user_performance(df, settings, prop_mode=False)
    extra = compute_dashboard_summary(df, settings)

    # ---- Top stat row: Account Balance / Today's P&L / Active Trades / Journaled Trades / Win Rate ----
    c1, c2, c3, c4, c5 = st.columns(5)
    with c1:
        stat_card(
            "Account Balance", f"${perf['current_balance']:,.2f}",
            f"Starting ${perf['starting_balance']:,.0f}", icon="$", tone="teal", note_tone="flat",
        )
    with c2:
        pnl_tone = "up" if extra["todays_pnl"] > 0 else ("down" if extra["todays_pnl"] < 0 else "flat")
        stat_card(
            "Today's P&L", f"${extra['todays_pnl']:+,.2f}",
            f"{extra['todays_pnl_pct']:+.2f}%", icon="◷", tone="purple", note_tone=pnl_tone,
        )
    with c3:
        stat_card(
            "Active Trades", f"{len(open_df):,}",
            f"Across {open_df['asset'].nunique() if not open_df.empty else 0} assets", icon="◉", tone="gold", note_tone="flat",
        )
    with c4:
        stat_card(
            "Journaled Trades", f"{len(trade_df):,}",
            "A+/A/B/C setups", icon="▦", tone="purple", note_tone="flat",
        )
    with c5:
        stat_card(
            "Win Rate", f"{extra['win_rate']:.2f}%",
            "Since activation", icon="◎", tone="teal", note_tone="flat",
        )

    st.markdown("<div class='section-gap'></div>", unsafe_allow_html=True)

    # ---- Equity curve + Signals by grade donut: equal-height bordered cards ----
    left, right = st.columns([1.55, 1])
    with left:
        with st.container(border=True, height=440):
            st.markdown("<div class='benzino-panel-title'>Equity Curve</div>", unsafe_allow_html=True)
            eq = extra["equity_series"]
            if eq.empty:
                st.markdown("<div class='benzino-empty-note'>No closed trades yet — the equity curve fills in as journaled trades resolve.</div>", unsafe_allow_html=True)
            else:
                st.markdown("<div class='benzino-equity-range'>", unsafe_allow_html=True)
                period = st.segmented_control(
                    "",
                    options=["7D", "30D", "90D", "6M", "ALL"],
                    default="ALL",
                    selection_mode="single",
                    label_visibility="collapsed",
                    key="dash_equity_period",
                )
                st.markdown("</div>", unsafe_allow_html=True)
                view = eq.copy()
                period_days = {"7D": 7, "30D": 30, "90D": 90, "6M": 180, "ALL": None}
                selected_days = period_days.get(period or "ALL")
                if selected_days:
                    cutoff = pd.Timestamp.now(tz="UTC") - pd.Timedelta(days=selected_days)
                    view = view[pd.to_datetime(view["created_at"], utc=True, errors="coerce") >= cutoff]
                if view.empty:
                    st.markdown("<div class='benzino-empty-note'>No closed trades in this period.</div>", unsafe_allow_html=True)
                else:
                    fig = px.area(view, x="created_at", y="balance_after")
                    fig.update_traces(line_color="#00D4A3", fillcolor="rgba(0,212,163,0.18)")
                    fig.update_layout(
                        paper_bgcolor="rgba(0,0,0,0)", plot_bgcolor="rgba(0,0,0,0)",
                        font_color="#8BAAB8", margin=dict(l=10, r=10, t=10, b=10),
                        xaxis_title=None, yaxis_title=None, height=310,
                    )
                    fig.update_xaxes(gridcolor="#16263B")
                    fig.update_yaxes(gridcolor="#16263B")
                    st.plotly_chart(fig, use_container_width=True)

    with right:
        with st.container(border=True, height=440):
            st.markdown("<div class='benzino-panel-title'>Performance by Grade</div>", unsafe_allow_html=True)
            grade_order = ["A+", "A", "B", "C", "NO TRADE"]
            grade_colors = {"A+": "#00D4A3", "A": "#4C8CFF", "B": "#D6A84E", "C": "#FF5D5D", "NO TRADE": "#7C5CFF"}
            counts = df["grade"].astype(str).value_counts().reindex(grade_order).fillna(0).astype(int)
            counts = counts[counts > 0]
            if counts.empty:
                st.markdown("<div class='benzino-empty-note'>No performance data yet for this watchlist/timeframe.</div>", unsafe_allow_html=True)
            else:
                total = int(counts.sum())
                fig = go.Figure(data=[go.Pie(
                    labels=counts.index.tolist(),
                    values=counts.values.tolist(),
                    hole=0.54,
                    marker=dict(colors=[grade_colors.get(g, "#8BAAB8") for g in counts.index]),
                    textinfo="none",
                    hovertemplate="%{label}<br>%{value} trade(s)<br>%{percent}<extra></extra>",
                    sort=False,
                )])
                fig.update_layout(
                    paper_bgcolor="rgba(0,0,0,0)", plot_bgcolor="rgba(0,0,0,0)",
                    showlegend=False, margin=dict(l=2, r=2, t=0, b=0), height=288,
                    annotations=[dict(text=f"<b>{total}</b><br><span style='font-size:11px'>Total Trades</span>", x=0.5, y=0.5, font=dict(size=24, color="#E8EDF2"), showarrow=False)],
                )
                fig.update_traces(domain=dict(x=[0.07, 0.93], y=[0.03, 0.97]))
                st.plotly_chart(fig, use_container_width=True, config={"displayModeBar": False})
                legend_parts = ["<div class='grade-legend-grid'>"]
                for g in counts.index:
                    pct = counts[g] / total * 100 if total else 0
                    safe_g = html.escape(str(g))
                    safe_color = grade_colors.get(g, "#8BAAB8")
                    legend_parts.append(
                        f"<div class='grade-legend-item'>"
                        f"<span class='grade-legend-name'><span style='color:{safe_color};font-size:16px;'>■</span>{safe_g}</span>"
                        f"<span class='grade-legend-value'>{pct:.2f}% ({int(counts[g])})</span>"
                        f"</div>"
                    )
                legend_parts.append("</div>")
                st.markdown("".join(legend_parts), unsafe_allow_html=True)


    st.markdown("<div class='section-gap'></div>", unsafe_allow_html=True)

    # ---- Generated signals: full Supabase table, ordered and styled for trading readability ----
    with st.container(border=True):
        generated = df.copy()
        if "signal_id" in generated.columns and "created_at" in generated.columns:
            _sig_rank = generated[["signal_id", "created_at"]].drop_duplicates("signal_id").copy()
            _sig_rank["_created_sort"] = pd.to_datetime(_sig_rank["created_at"], errors="coerce", utc=True)
            _sig_rank = _sig_rank.sort_values(["_created_sort", "signal_id"], ascending=[True, True]).reset_index(drop=True)
            _sig_rank["display_signal_id"] = [f"Benzino-{i:02d}" for i in range(1, len(_sig_rank) + 1)]
            _sig_map = dict(zip(_sig_rank["signal_id"].astype(str), _sig_rank["display_signal_id"]))
            generated["signal_id"] = generated["signal_id"].astype(str).map(_sig_map).fillna(generated["signal_id"].astype(str))
        if "created_at" in generated.columns:
            generated = generated.sort_values("created_at", ascending=False)
        generated = generated.head(100).copy()

        # Top toolbar: title + real filter controls + search.
        title_col, signal_filter_col, grade_filter_col, search_col = st.columns([5.2, 1.15, 1.15, 2.3], vertical_alignment="center")
        with title_col:
            st.markdown("<div class='benzino-panel-title'>Generated Signals</div>", unsafe_allow_html=True)
        with signal_filter_col:
            signal_filter = st.selectbox(
                "Signal filter",
                ["All", "BUY", "SELL", "HOLD", "NO TRADE"],
                index=0,
                label_visibility="collapsed",
                key="generated_signals_signal_filter",
            )
        with grade_filter_col:
            grade_filter = st.selectbox(
                "Grade filter",
                ["All", "A+", "A", "B", "C", "NO TRADE"],
                index=0,
                label_visibility="collapsed",
                key="generated_signals_grade_filter",
            )
        with search_col:
            table_search = st.text_input(
                "Search generated signals",
                value="",
                placeholder="Search…",
                label_visibility="collapsed",
                key="generated_signals_search",
            )

        if generated.empty:
            st.markdown("<div class='benzino-empty-note'>No generated scanner signals yet for this watchlist/timeframe.</div>", unsafe_allow_html=True)
        else:
            display_df = generated.copy()

            # Age column: clear trader-friendly timing such as "5 mins ago".
            if "created_at" in display_df.columns:
                display_df["age"] = display_df["created_at"].apply(age_ago)
            else:
                display_df["age"] = "—"

            # Normalize aliases for decayed confidence so it sits beside confidence.
            for _src, _dst in [
                ("decayed_conf", "decayed_confidence"),
                ("decayed_confidence_pct", "decayed_confidence"),
                ("confidence_decayed", "decayed_confidence"),
                ("urgency_adjusted_confidence", "decayed_confidence"),
                ("time_decayed_confidence", "decayed_confidence"),
            ]:
                if _dst not in display_df.columns and _src in display_df.columns:
                    display_df[_dst] = display_df[_src]

            if "decayed_confidence" not in display_df.columns:
                display_df["decayed_confidence"] = display_df.apply(
                    lambda r: decayed_confidence_value(r.get("confidence"), r.get("created_at"), r.get("timeframe")),
                    axis=1,
                )

            # Ensure status exists for badge rendering.
            if "status" not in display_df.columns:
                display_df["status"] = display_df.apply(
                    lambda r: "Skipped" if str(r.get("grade", "")).upper() == "NO TRADE" or str(r.get("signal", "")).upper() in ["HOLD", "NO TRADE"] else "Active",
                    axis=1,
                )

            # Apply toolbar filters before formatting/renaming.
            if signal_filter != "All" and "signal" in display_df.columns:
                display_df = display_df[display_df["signal"].astype(str).str.upper().eq(signal_filter)].copy()
            if grade_filter != "All" and "grade" in display_df.columns:
                display_df = display_df[display_df["grade"].astype(str).str.upper().eq(grade_filter)].copy()

            # Format timestamps after age is derived.
            for col in list(display_df.columns):
                if "created_at" in col.lower() or col.lower().endswith("_at"):
                    display_df[col] = display_df[col].apply(fmt_nairobi)

            # Required business-readable order. Everything else remains visible after the core fields.
            priority = [
                "asset", "signal", "grade", "age",
                "entry", "sl", "tp", "status", "confidence", "decayed_confidence", "rr",
            ]
            tail = ["ticker", "timeframe", "created_at", "signal_id", "scan_owner"]
            front = [c for c in priority if c in display_df.columns]
            tail_cols = [c for c in tail if c in display_df.columns]
            rest = [c for c in display_df.columns if c not in front and c not in tail_cols]
            display_df = display_df[front + rest + tail_cols]

            rename_map = {
                "asset": "Asset",
                "timeframe": "Timeframe",
                "signal": "Signal",
                "grade": "Grade",
                "age": "Age",
                "entry": "Entry",
                "sl": "SL",
                "tp": "TP",
                "confidence": "Confidence",
                "decayed_confidence": "Decayed Confidence",
                "rr": "RR",
                "status": "Status",
                "ticker": "Ticker",
                "created_at": "Created At",
                "signal_id": "Signal ID",
                "scan_owner": "Scan Owner",
            }
            display_df = display_df.rename(columns=rename_map)

            # Search across the final display table.
            if table_search:
                mask = display_df.astype(str).apply(
                    lambda col: col.str.contains(table_search, case=False, na=False)
                ).any(axis=1)
                display_df = display_df[mask].copy()

            def _fmt_money(x):
                if pd.isna(x) or str(x).strip() == "":
                    return "—"
                n = pd.to_numeric(x, errors="coerce")
                if pd.notna(n):
                    return f"{float(n):,.2f}"
                return str(x)

            def _fmt_pct(x):
                if pd.isna(x) or str(x).strip() == "":
                    return "—"
                n = pd.to_numeric(x, errors="coerce")
                if pd.notna(n):
                    # Scanner stores some probabilities as 0-1 and others as 0-100. Handle both.
                    if 0 <= float(n) <= 1:
                        n = float(n) * 100
                    return f"{float(n):.2f}%"
                return str(x)

            def _fmt_rr(x):
                if pd.isna(x) or str(x).strip() == "":
                    return "—"
                n = pd.to_numeric(x, errors="coerce")
                return f"{float(n):.2f}" if pd.notna(n) else str(x)

            for money_col in ["Entry", "SL", "TP"]:
                if money_col in display_df.columns:
                    display_df[money_col] = display_df[money_col].apply(_fmt_money)
            for pct_col in ["Confidence", "Decayed Confidence"]:
                if pct_col in display_df.columns:
                    display_df[pct_col] = display_df[pct_col].apply(_fmt_pct)
            if "RR" in display_df.columns:
                display_df["RR"] = display_df["RR"].apply(_fmt_rr)

            if AgGrid is not None and GridOptionsBuilder is not None and JsCode is not None:
                signal_renderer = JsCode("""
                class SignalRenderer {
                  init(params) {
                    const v = (params.value || '').toString().toUpperCase();
                    const span = document.createElement('span');
                    if (v.includes('BUY')) { span.className = 'ag-signal-badge ag-buy'; span.innerHTML = '↗ BUY'; }
                    else if (v.includes('SELL')) { span.className = 'ag-signal-badge ag-sell'; span.innerHTML = '↘ SELL'; }
                    else { span.className = 'ag-signal-badge ag-neutral'; span.innerHTML = v || '—'; }
                    this.eGui = span;
                  }
                  getGui() { return this.eGui; }
                }
                """)
                grade_renderer = JsCode("""
                class GradeRenderer {
                  init(params) {
                    const raw = (params.value || '—').toString().toUpperCase();
                    const clean = raw.replace('+','p').replace(/\s+/g,'-').toLowerCase();
                    const span = document.createElement('span');
                    span.className = 'ag-grade-badge ag-grade-' + clean;
                    span.innerText = raw;
                    this.eGui = span;
                  }
                  getGui() { return this.eGui; }
                }
                """)
                status_renderer = JsCode("""
                class StatusRenderer {
                  init(params) {
                    const raw = (params.value || '—').toString();
                    const v = raw.toUpperCase();
                    const span = document.createElement('span');

                    // Mirrors the Python outcome_label() logic so badge colour always
                    // matches the real trade outcome, not just the raw status string:
                    //   - TP in status            -> win (green)
                    //   - SL in status            -> loss (red)
                    //   - EXPIRED or CLOSED       -> look at r_multiple sign:
                    //         r > 0 -> win (green), r < 0 -> loss (red), r == 0/missing -> neutral (grey)
                    //   - OPEN / ACTIVE           -> active (green)
                    //   - SHADOW / SKIP / NO TRADE / HOLD -> neutral (grey)
                    let cls = 'ag-status-skipped';

                    if (v.includes('TP')) {
                      cls = 'ag-status-win';
                    } else if (v.includes('SL')) {
                      cls = 'ag-status-loss';
                    } else if (v.includes('EXPIRED') || v.includes('CLOSED')) {
                      const r = parseFloat(params.data ? params.data.r_multiple : NaN);
                      if (isNaN(r) || r === 0) cls = 'ag-status-skipped';
                      else if (r > 0) cls = 'ag-status-win';
                      else cls = 'ag-status-loss';
                    } else if (v.includes('ACTIVE') || v.includes('OPEN')) {
                      cls = 'ag-status-active';
                    } else if (v.includes('SHADOW') || v.includes('SKIP') || v.includes('NO TRADE') || v.includes('HOLD')) {
                      cls = 'ag-status-skipped';
                    }

                    span.className = 'ag-status-badge ' + cls;
                    span.innerText = raw;
                    this.eGui = span;
                  }
                  getGui() { return this.eGui; }
                }
                """)

                gb = GridOptionsBuilder.from_dataframe(display_df)
                gb.configure_default_column(
                    sortable=True,
                    filter=True,
                    resizable=True,
                    wrapText=False,
                    autoHeight=False,
                    suppressMovable=False,
                )
                gb.configure_pagination(paginationAutoPageSize=False, paginationPageSize=10)
                gb.configure_grid_options(
                    rowHeight=42,
                    headerHeight=44,
                    suppressMenuHide=True,
                    domLayout="normal",
                    enableCellTextSelection=True,
                    animateRows=True,
                    suppressRowClickSelection=True,
                    quickFilterText=table_search or None,
                )

                column_widths = {
                    "Asset": 116,
                    "Timeframe": 110,
                    "Signal": 112,
                    "Grade": 94,
                    "Age": 128,
                    "Entry": 118,
                    "SL": 118,
                    "TP": 118,
                    "Confidence": 124,
                    "Decayed Confidence": 168,
                    "RR": 88,
                    "Status": 116,
                    "Ticker": 116,
                    "Created At": 168,
                    "Signal ID": 160,
                    "Scan Owner": 142,
                }
                for col, width in column_widths.items():
                    if col in display_df.columns:
                        gb.configure_column(col, width=width, pinned="left" if col in ["Asset", "Signal", "Grade", "Age"] else None)
                if "Signal" in display_df.columns:
                    gb.configure_column("Signal", cellRenderer=signal_renderer)
                if "Grade" in display_df.columns:
                    gb.configure_column("Grade", cellRenderer=grade_renderer)
                if "Status" in display_df.columns:
                    gb.configure_column("Status", cellRenderer=status_renderer)
                for numeric_col in ["Entry", "SL", "TP", "Confidence", "Decayed Confidence", "RR"]:
                    if numeric_col in display_df.columns:
                        gb.configure_column(numeric_col, cellStyle={"textAlign": "right", "fontWeight": "700"})

                grid_options = gb.build()
                aggrid_css = {
                    ".ag-root-wrapper": {
                        "background-color": "#07111F !important",
                        "border": "1px solid #1E3050 !important",
                        "border-radius": "14px !important",
                        "overflow": "hidden !important",
                    },
                    ".ag-header": {
                        "background-color": "#0B1A2B !important",
                        "border-bottom": "1px solid #203A59 !important",
                    },
                    ".ag-header-cell-label": {
                        "color": "#C9D5E3 !important",
                        "font-weight": "900 !important",
                        "font-size": "var(--font-table-header) !important",
                    },
                    ".ag-row": {
                        "background-color": "#07111F !important",
                        "border-bottom": "1px solid #13263B !important",
                    },
                    ".ag-row-hover": {"background-color": "#0D2033 !important"},
                    ".ag-cell": {
                        "color": "#DDE7F1 !important",
                        "font-size": "var(--font-table-body) !important",
                        "display": "flex !important",
                        "align-items": "center !important",
                    },
                    ".ag-paging-panel": {
                        "background-color": "#07111F !important",
                        "color": "#8BAAB8 !important",
                        "border-top": "1px solid #16263B !important",
                    },
                    ".ag-signal-badge": {
                        "font-weight": "950 !important",
                        "border-radius": "999px !important",
                        "padding": "4px 9px !important",
                        "font-size": "11.5px !important",
                    },
                    ".ag-buy": {"background": "rgba(0,212,163,.14) !important", "color": "#00D4A3 !important"},
                    ".ag-sell": {"background": "rgba(255,93,93,.14) !important", "color": "#FF5D5D !important"},
                    ".ag-neutral": {"background": "rgba(139,158,176,.14) !important", "color": "#A9BBC9 !important"},
                    ".ag-grade-badge, .ag-status-badge": {
                        "display": "inline-flex !important",
                        "align-items": "center !important",
                        "justify-content": "center !important",
                        "border-radius": "999px !important",
                        "padding": "4px 9px !important",
                        "font-size": "11.5px !important",
                        "font-weight": "950 !important",
                    },
                    ".ag-grade-ap": {"background": "rgba(0,212,163,.18) !important", "color": "#00D4A3 !important"},
                    ".ag-grade-a": {"background": "rgba(76,140,255,.18) !important", "color": "#7AA6FF !important"},
                    ".ag-grade-b": {"background": "rgba(214,168,78,.18) !important", "color": "#D6A84E !important"},
                    ".ag-grade-c": {"background": "rgba(255,93,93,.18) !important", "color": "#FF5D5D !important"},
                    ".ag-grade-no-trade": {"background": "rgba(137,95,255,.18) !important", "color": "#A98CFF !important"},
                    ".ag-status-active": {"background": "rgba(0,212,163,.16) !important", "color": "#00D4A3 !important"},
                    ".ag-status-win": {"background": "rgba(78,196,214,.22) !important", "color": "#4EC4D6 !important"},
                    ".ag-status-loss": {"background": "rgba(255,93,93,.18) !important", "color": "#FF5D5D !important"},
                    ".ag-status-expired": {"background": "rgba(214,168,78,.18) !important", "color": "#D6A84E !important"},
                    ".ag-status-skipped": {"background": "rgba(139,158,176,.16) !important", "color": "#A9BBC9 !important"},
                    ".ag-status-closed": {"background": "rgba(76,140,255,.14) !important", "color": "#7AA6FF !important"},
                }
                AgGrid(
                    display_df,
                    gridOptions=grid_options,
                    height=486,
                    fit_columns_on_grid_load=False,
                    theme="balham",
                    allow_unsafe_jscode=True,
                    custom_css=aggrid_css,
                    key="generated_signals_aggrid",
                )
            else:
                st.warning("streamlit-aggrid is not available in this environment, so the generated signals table is using the fallback renderer. Add streamlit-aggrid to requirements.txt and redeploy.")
                def _badge_grade(v):
                    cls = "badge-grade-" + str(v).lower().replace("+", "p").replace(" ", "-")
                    return f"<span class='badge {cls}'>{html.escape(str(v))}</span>"
                def _badge_status(v):
                    s = str(v)
                    cls = "badge-active" if s.lower() in ["active", "open"] else ("badge-skipped" if "skip" in s.lower() else "badge-closed")
                    return f"<span class='badge {cls}'>{html.escape(s)}</span>"
                def _signal(v):
                    s = str(v).upper()
                    if "BUY" in s:
                        return "<span class='sig-buy'>↗ BUY</span>"
                    if "SELL" in s:
                        return "<span class='sig-sell'>↘ SELL</span>"
                    return html.escape(str(v))

                html_df = display_df.copy()
                if "Signal" in html_df.columns:
                    html_df["Signal"] = html_df["Signal"].apply(_signal)
                if "Grade" in html_df.columns:
                    html_df["Grade"] = html_df["Grade"].apply(_badge_grade)
                if "Status" in html_df.columns:
                    html_df["Status"] = html_df["Status"].apply(_badge_status)

                headers = "".join(f"<th>{html.escape(str(c))}</th>" for c in html_df.columns)
                rows = []
                for _, r in html_df.iterrows():
                    rows.append("<tr>" + "".join(f"<td>{r[c]}</td>" for c in html_df.columns) + "</tr>")
                st.markdown(
                    f"<div class='benzino-html-table-wrap'><table class='benzino-html-table'><thead><tr>{headers}</tr></thead><tbody>{''.join(rows)}</tbody></table></div>",
                    unsafe_allow_html=True,
                )

    if not no_trade_df.empty:
        st.caption(f"{len(no_trade_df):,} NO TRADE shadow signal(s) tracked silently in the background for this watchlist/timeframe.")

def render_asset_deep_dive(username: str, settings: dict) -> None:
    page_header("Asset Deep Dive", "Explain the latest scanner evidence, trade plan, strategy votes, and historical outcome profile.")
    with st.spinner("Loading asset evidence from Supabase…"):
        raw_df = enrich_position_sizing(load_signals_for_user(username, settings), settings)
        df = apply_timeframe_view(raw_df, settings)
    if df.empty:
        st.info("No scanner data available yet for this timeframe.")
        return
    assets = sorted(df["asset"].dropna().astype(str).unique())
    selected = st.selectbox("Select asset", assets)
    adf = df[df["asset"].astype(str).eq(selected)].sort_values("created_at", ascending=False)
    latest = adf.iloc[0]

    c1, c2, c3, c4 = st.columns(4)
    with c1: metric_card("Latest signal", str(latest.get("signal", "")), f"{latest.get('timeframe', '')} · Grade {latest.get('grade', '')}")
    with c2: metric_card("System agreement", f"{float(latest.get('confidence') or 0):.2f}%", f"Urgency-adjusted {decayed_confidence_value(latest.get('confidence'), latest.get('created_at'), latest.get('timeframe')):.2f}%")
    with c3: metric_card("RR", f"{float(latest.get('rr') or 0):.2f}R", str(latest.get("status", "")))
    with c4: metric_card("Generated", time_ago(latest.get("created_at")), fmt_nairobi(latest.get("created_at")))

    explain_source = adf.head(10).copy()
    st.subheader("Signal explanation for this asset")
    st.caption(
        "This explains the latest generated signals for the selected asset, including journaled setups and blocked No Trade ideas. "
        "Use it to understand why the scanner produced the decision, not only why a trade was blocked."
    )
    if explain_source.empty:
        st.info("No recent generated signals for this asset yet.")
        row = latest
    else:
        options = explain_source.apply(lambda r: f"{r.get('asset')} · {r.get('timeframe')} · {r.get('signal')} · Grade {r.get('grade')} · {time_ago(r.get('created_at'))} · {r.get('signal_id')}", axis=1).tolist()
        choice = st.selectbox("Choose one of the last 10 generated signals", options)
        sid = choice.split(" · ")[-1]
        row = explain_source[explain_source["signal_id"].astype(str).eq(sid)].iloc[0]
        st.markdown(f"<div class='ai-card'>{mini_markdown_to_html(rich_signal_explanation(row))}</div>", unsafe_allow_html=True)

    st.caption("Multi-timeframe and strategy confluence below reflect the selected generated signal above.")
    mtf_context = parse_jsonish(row.get("mtf_context"))
    if mtf_context:
        st.subheader("Multi-timeframe confirmation")
        rows = []
        for tf, payload in mtf_context.items():
            if isinstance(payload, dict):
                direction = str(payload.get("direction", "NEUTRAL") or "NEUTRAL").upper()
                strength = pd.to_numeric(payload.get("strength"), errors="coerce")
                strength_val = 0.0 if pd.isna(strength) else float(strength)
                raw_reason = str(payload.get("reason") or payload.get("explanation") or payload.get("context") or "").strip()
                if strength_val >= 0.70:
                    reason = f"Strong {direction.lower()} confirmation: structure, momentum, and higher-timeframe bias are aligned, so this timeframe added conviction."
                elif strength_val >= 0.40:
                    reason = f"Partial {direction.lower()} confirmation: direction agrees, but momentum or structure is not clean enough to drive the signal alone."
                else:
                    reason = f"Weak {direction.lower()} evidence: this timeframe conflicts with the trade plan or lacks momentum, reducing final conviction."
                if raw_reason and len(raw_reason) < 120:
                    reason = raw_reason
                rows.append({"Timeframe": tf, "Direction": direction, "Strength": strength_val, "Reason": reason})
        if rows:
            render_benzino_aggrid(pd.DataFrame(rows), key="asset_mtf_context", height=182, page_size=5, pinned=["Timeframe"], numeric_cols_right=["Strength"], enable_search=False, show_footer=False, use_pagination=False)
        st.caption(f"MTF score: {float(row.get('mtf_score') or 0):.0f}%")

    votes = parse_jsonish(row.get("strategy_votes"))
    if votes:
        st.subheader("Strategy confluence")
        render_strategy_confluence(votes)

    hist = adf.copy()
    hist["created_at_eat"] = hist["created_at"].apply(fmt_nairobi)
    cols = ["created_at", "created_at_eat", "asset", "ticker", "timeframe", "signal", "grade", "status", "confidence", "edge_score", "mtf_score", "rr", "r_multiple", "exit_reason", "session"]
    hist_view = prepare_signal_table(hist[[c for c in cols if c in hist.columns]].head(100))
    title_col, sig_col, grade_col, search_col = st.columns([5.0, 1.15, 1.15, 2.4], vertical_alignment="center")
    with title_col:
        st.markdown("<div class='benzino-panel-title'>History for selected asset</div>", unsafe_allow_html=True)
    with sig_col:
        hist_signal_filter = st.selectbox("Signal", ["All", "BUY", "SELL", "HOLD", "NO TRADE"], label_visibility="collapsed", key="asset_history_signal_filter")
    with grade_col:
        hist_grade_filter = st.selectbox("Grade", ["All", "A+", "A", "B", "C", "NO TRADE"], label_visibility="collapsed", key="asset_history_grade_filter")
    with search_col:
        hist_search = st.text_input("Search asset history", placeholder="Search…", label_visibility="collapsed", key="asset_history_search")
    if hist_signal_filter != "All" and "Signal" in hist_view.columns:
        hist_view = hist_view[hist_view["Signal"].astype(str).str.upper().str.contains(hist_signal_filter, na=False)]
    if hist_grade_filter != "All" and "Grade" in hist_view.columns:
        hist_view = hist_view[hist_view["Grade"].astype(str).str.upper().eq(hist_grade_filter.upper())]
    if hist_search:
        q = str(hist_search).lower().strip()
        hist_view = hist_view[hist_view.astype(str).apply(lambda col: col.str.lower().str.contains(q, na=False)).any(axis=1)]

    # History table order: Status belongs immediately after Age so the lifecycle is clear before metrics.
    hist_order = ["Asset", "Signal", "Grade", "Age", "Status"]
    hist_view = hist_view[[c for c in hist_order if c in hist_view.columns] + [c for c in hist_view.columns if c not in hist_order]]

    render_benzino_aggrid(hist_view, key="asset_history", height=420, page_size=10, pinned=["Asset", "Signal", "Grade", "Age"], badge_cols={"Signal":"signal", "Grade":"grade", "Status":"status", "Outcome":"outcome"}, numeric_cols_right=["Confidence", "Decayed Confidence", "RR", "R Multiple", "Edge Score", "MTF Score"], enable_search=False)


def asset_group_for_asset(asset: str) -> str:
    asset = str(asset or "").upper().strip()
    meta = ASSET_UNIVERSE.get(asset, {})
    return str(meta.get("group") or "Other")


def render_system_performance(system_df: pd.DataFrame, settings: dict) -> None:
    """Render total system performance using every scanner row in Supabase."""
    st.subheader("Total System Performance")
    st.caption(
        "This view ignores individual user watchlists and uses all scanner data currently saved in Supabase. "
        "It refreshes whenever the app reloads and gives you the global Benzino engine performance picture."
    )

    if system_df is None or system_df.empty:
        st.info("No system-wide scanner data is available in Supabase yet.")
        return

    system_df = system_df.copy()
    system_df["outcome"] = system_df.apply(outcome_label, axis=1)
    system_df["asset_group"] = system_df["asset"].apply(asset_group_for_asset)

    graded = system_df[system_df["grade"].astype(str).isin(VALID_GRADES)].copy()
    no_trade = system_df[system_df["grade"].astype(str).eq("NO TRADE")].copy()
    open_trades = graded[graded["status"].astype(str).str.upper().eq("OPEN")].copy()
    closed = graded[graded["outcome"].isin(["WIN", "LOSS", "BREAKEVEN", "CLOSED"])].copy()
    resolved = closed.copy()

    win_rate = (closed["outcome"].eq("WIN").sum() / len(closed) * 100) if len(closed) else 0.0
    avg_r = pd.to_numeric(closed.get("r_multiple", pd.Series(dtype=float)), errors="coerce").mean() if len(closed) else 0.0

    c1, c2, c3, c4, c5 = st.columns(5)
    with c1: metric_card("All scanner rows", f"{len(system_df):,}", "Full Supabase history")
    with c2: metric_card("Journaled setups", f"{len(graded):,}", "A+/A/B/C")
    with c3: metric_card("Open trades", f"{len(open_trades):,}", "Across all assets")
    with c4: metric_card("Closed trades", f"{len(closed):,}", "Resolved journal setups")
    with c5: metric_card("System win rate", f"{win_rate:.2f}%", f"Avg {avg_r:+.2f}R")

    if resolved.empty:
        st.info("System-wide closed WIN/LOSS sample is not large enough yet for split analysis.")
        return

    st.markdown("<div class='section-gap'></div>", unsafe_allow_html=True)
    st.subheader("System split analysis")

    g1, g2 = st.columns(2)
    with g1:
        grade_perf = closed.groupby("grade", as_index=False).agg(
            win_rate=("outcome", lambda x: (x == "WIN").sum() / len(x) * 100 if len(x) else 0),
            trades=("signal_id", "count"),
            avg_r=("r_multiple", "mean"),
        ).sort_values("grade")
        st.markdown("**By grade**")
        render_benzino_aggrid(grade_perf, key="system_perf_grade", height=240, page_size=10, pinned=["grade"], badge_cols={"grade":"grade", "Grade":"grade"}, numeric_cols_right=[c for c in grade_perf.columns if c not in ["grade", "Grade"]], enable_search=False, show_footer=False, use_pagination=False)

    with g2:
        session_perf = closed.groupby("session", as_index=False).agg(
            win_rate=("outcome", lambda x: (x == "WIN").sum() / len(x) * 100 if len(x) else 0),
            trades=("signal_id", "count"),
            avg_r=("r_multiple", "mean"),
        ).sort_values("trades", ascending=False)
        st.markdown("**By session**")
        render_benzino_aggrid(session_perf, key="system_perf_session", height=240, page_size=10, pinned=["session"], numeric_cols_right=[c for c in session_perf.columns if c not in ["session", "Session"]], enable_search=False, show_footer=False, use_pagination=False)

    a1, a2 = st.columns(2)
    with a1:
        timeframe_perf = closed.groupby("timeframe", as_index=False).agg(
            win_rate=("outcome", lambda x: (x == "WIN").sum() / len(x) * 100 if len(x) else 0),
            trades=("signal_id", "count"),
            avg_r=("r_multiple", "mean"),
        ).sort_values("timeframe")
        st.markdown("**By timeframe**")
        render_benzino_aggrid(timeframe_perf, key="system_perf_timeframe_split", height=240, page_size=10, pinned=["timeframe"], numeric_cols_right=[c for c in timeframe_perf.columns if c != "timeframe"], enable_search=False, show_footer=False, use_pagination=False)

    with a2:
        asset_perf = closed.groupby("asset", as_index=False).agg(
            win_rate=("outcome", lambda x: (x == "WIN").sum() / len(x) * 100 if len(x) else 0),
            trades=("signal_id", "count"),
            avg_r=("r_multiple", "mean"),
        ).sort_values(["trades", "win_rate"], ascending=[False, False])
        st.markdown("**By asset**")
        render_benzino_aggrid(asset_perf.head(30), key="system_perf_asset", height=240, page_size=10, pinned=["asset"], numeric_cols_right=[c for c in asset_perf.columns if c != "asset"], enable_search=False, show_footer=False, use_pagination=False)

    st.markdown("<div class='section-gap'></div>", unsafe_allow_html=True)
    latest_cols = ["created_at", "asset", "asset_group", "timeframe", "signal", "grade", "status", "outcome", "r_multiple", "rr", "session", "signal_id"]
    latest_source = system_df[[c for c in latest_cols if c in system_df.columns]].head(300).copy()

    # Outcome should describe resolved result only. Status already tells the user whether a row is open/closed/shadow.
    if not latest_source.empty:
        latest_source["outcome"] = latest_source.apply(
            lambda r: (
                "WIN" if pd.to_numeric(r.get("r_multiple"), errors="coerce") > 0 else
                "LOSS" if pd.to_numeric(r.get("r_multiple"), errors="coerce") < 0 else
                "—"
            ),
            axis=1,
        )

    latest_view = prepare_signal_table(latest_source)
    title_col, sig_col, grade_col, search_col = st.columns([5.0, 1.15, 1.15, 2.4], vertical_alignment="center")
    with title_col:
        st.markdown("<div class='benzino-panel-title'>Latest system scanner rows</div>", unsafe_allow_html=True)
    with sig_col:
        system_signal_filter = st.selectbox("Signal", ["All", "BUY", "SELL", "HOLD", "NO TRADE"], label_visibility="collapsed", key="system_latest_signal_filter")
    with grade_col:
        system_grade_filter = st.selectbox("Grade", ["All", "A+", "A", "B", "C", "NO TRADE"], label_visibility="collapsed", key="system_latest_grade_filter")
    with search_col:
        system_latest_search = st.text_input("Search latest system rows", placeholder="Search…", label_visibility="collapsed", key="system_latest_search")
    if system_signal_filter != "All" and "Signal" in latest_view.columns:
        latest_view = latest_view[latest_view["Signal"].astype(str).str.upper().str.contains(system_signal_filter, na=False)]
    if system_grade_filter != "All" and "Grade" in latest_view.columns:
        latest_view = latest_view[latest_view["Grade"].astype(str).str.upper().eq(system_grade_filter.upper())]
    if system_latest_search:
        q = str(system_latest_search).lower().strip()
        latest_view = latest_view[latest_view.astype(str).apply(lambda col: col.str.lower().str.contains(q, na=False)).any(axis=1)]

    # Latest system rows: status immediately after age; keep one Created At field; Signal ID at the very end.
    for duplicate_created_col in ["created_at_eat", "signal_created_at", "Signal Created At"]:
        if duplicate_created_col in latest_view.columns:
            latest_view = latest_view.drop(columns=[duplicate_created_col])
    latest_order = ["Asset", "Signal", "Grade", "Age", "Status", "Outcome"]
    latest_tail = ["Signal ID"]
    latest_view = latest_view[[c for c in latest_order if c in latest_view.columns] + [c for c in latest_view.columns if c not in latest_order + latest_tail] + [c for c in latest_tail if c in latest_view.columns]]

    render_benzino_aggrid(latest_view, key="system_latest_signals", height=480, page_size=10, pinned=["Asset", "Signal", "Grade", "Age"], badge_cols={"Signal":"signal", "Grade":"grade", "Status":"status", "Outcome":"outcome"}, numeric_cols_right=["Confidence", "Decayed Confidence", "RR", "R Multiple", "Edge Score", "MTF Score"], enable_search=False)



NEWS_KEYWORDS_HIGH = {
    "fed", "fomc", "cpi", "inflation", "nfp", "payrolls", "unemployment",
    "interest rate", "rate decision", "central bank", "ecb", "boe", "boj",
    "war", "conflict", "sanction", "tariff", "opec", "inventory", "earnings",
    "guidance", "sec", "etf", "halving", "regulation"
}
NEWS_POSITIVE_WORDS = {"surge", "rally", "gain", "beat", "beats", "bullish", "record", "upgrade", "growth", "strong", "recover"}
NEWS_NEGATIVE_WORDS = {"fall", "falls", "drop", "slump", "miss", "misses", "bearish", "downgrade", "weak", "risk", "loss", "plunge"}


def get_news_api_key() -> str:
    return first_secret("NEWS_API_KEY", "NEWS_API", "NEWSAPI_KEY", fallback=os.getenv("NEWS_API_KEY", ""))


def asset_news_query(asset: str) -> str:
    mapping = {
        "XAUUSD": "gold OR XAUUSD",
        "XAGUSD": "silver OR XAGUSD",
        "OIL": "crude oil OR WTI",
        "BRENT": "brent crude oil",
        "NATGAS": "natural gas",
        "BTCUSD": "bitcoin OR BTC",
        "ETHUSD": "ethereum OR ETH",
        "SP500": "S&P 500 OR SP500",
        "NAS100": "Nasdaq 100 OR NAS100",
        "DOW30": "Dow Jones",
    }
    if asset in mapping:
        return mapping[asset]
    if asset.endswith("USD") or asset.endswith("JPY") or asset.endswith("CHF") or asset.endswith("CAD") or asset.endswith("AUD") or asset.endswith("NZD") or asset.endswith("GBP"):
        return f"{asset} OR forex OR currency"
    return asset


def score_news_impact(asset: str, title: str, description: str, published_at: str) -> tuple[str, int, str]:
    text_blob = f"{title or ''} {description or ''}".lower()
    keyword_hits = sum(1 for k in NEWS_KEYWORDS_HIGH if k in text_blob)
    pos_hits = sum(1 for k in NEWS_POSITIVE_WORDS if k in text_blob)
    neg_hits = sum(1 for k in NEWS_NEGATIVE_WORDS if k in text_blob)

    sentiment_score = pos_hits - neg_hits
    sentiment = "Positive" if sentiment_score > 0 else "Negative" if sentiment_score < 0 else "Neutral"

    impact = 25
    impact += min(45, keyword_hits * 15)
    impact += min(20, abs(sentiment_score) * 8)

    try:
        published = pd.to_datetime(published_at, utc=True, errors="coerce")
        if pd.notna(published):
            hours_old = (pd.Timestamp.now(tz="UTC") - published).total_seconds() / 3600
            if hours_old <= 6:
                impact += 15
            elif hours_old <= 24:
                impact += 8
    except Exception:
        pass

    impact = int(max(0, min(100, impact)))
    label = "HIGH" if impact >= 80 else "MEDIUM" if impact >= 50 else "LOW"
    return label, impact, sentiment


@st.cache_data(ttl=900, show_spinner=False)
def fetch_news_for_watchlist(asset_list: tuple[str, ...], api_key: str) -> pd.DataFrame:
    if not api_key:
        return pd.DataFrame()
    rows = []
    for asset in asset_list:
        query = asset_news_query(asset)
        try:
            resp = requests.get(
                "https://newsapi.org/v2/everything",
                params={
                    "q": query,
                    "language": "en",
                    "sortBy": "publishedAt",
                    "pageSize": 8,
                    "apiKey": api_key,
                },
                timeout=12,
            )
            payload = resp.json() if resp is not None else {}
            for item in payload.get("articles", [])[:8]:
                title = item.get("title") or ""
                desc = item.get("description") or ""
                impact_label, impact_score, sentiment = score_news_impact(asset, title, desc, item.get("publishedAt", ""))
                rows.append({
                    "Asset": asset,
                    "Headline": title,
                    "Source": (item.get("source") or {}).get("name", ""),
                    "Published": fmt_nairobi(item.get("publishedAt", "")),
                    "Sentiment": sentiment,
                    "Impact": impact_label,
                    "Impact Score": impact_score,
                    "URL": item.get("url", ""),
                })
        except Exception as exc:
            rows.append({
                "Asset": asset,
                "Headline": f"News fetch failed: {exc}",
                "Source": "NewsAPI",
                "Published": "",
                "Sentiment": "Neutral",
                "Impact": "LOW",
                "Impact Score": 0,
                "URL": "",
            })
    return pd.DataFrame(rows)


def render_market_news(username: str, settings: dict) -> None:
    page_header("Market News", "Watchlist news, sentiment, and impact scoring.")
    api_key = get_news_api_key()
    if not api_key:
        st.warning("NEWS_API_KEY is not configured in Streamlit secrets.")
        return

    watchlist_assets = tuple(load_user_watchlist(username).keys() or DEFAULT_ASSETS)
    st.caption("News is pulled from your saved watchlist and refreshed every 15 minutes.")

    news_df = fetch_news_for_watchlist(watchlist_assets, api_key)
    if news_df.empty:
        st.info("No news returned for the current watchlist yet.")
        return

    a_col, i_col, s_col = st.columns([1.4, 1.2, 1.2], vertical_alignment="center")
    with a_col:
        asset_filter = st.selectbox("Asset", ["All"] + list(watchlist_assets), label_visibility="collapsed", key="news_asset_filter")
    with i_col:
        impact_filter = st.selectbox("Impact", ["All", "HIGH", "MEDIUM", "LOW"], label_visibility="collapsed", key="news_impact_filter")
    with s_col:
        sentiment_filter = st.selectbox("Sentiment", ["All", "Positive", "Neutral", "Negative"], label_visibility="collapsed", key="news_sentiment_filter")

    view = news_df.copy()
    if asset_filter != "All":
        view = view[view["Asset"].astype(str).eq(asset_filter)]
    if impact_filter != "All":
        view = view[view["Impact"].astype(str).eq(impact_filter)]
    if sentiment_filter != "All":
        view = view[view["Sentiment"].astype(str).eq(sentiment_filter)]

    render_benzino_aggrid(
        view[["Asset", "Headline", "Source", "Published", "Sentiment", "Impact", "Impact Score"]],
        key="market_news_table",
        title="Watchlist News",
        height=560,
        page_size=12,
        pinned=["Asset"],
        badge_cols={"Sentiment": "status", "Impact": "grade"},
        numeric_cols_right=["Impact Score"],
    )


def render_workflow(username: str, settings: dict) -> None:
    page_header("Workflow", "User journal, prop-firm mode, No Trade tracker, Coach AI, and Explain AI.")
    raw_df = enrich_position_sizing(load_signals_for_user(username, settings), settings)
    system_raw_df = load_all_system_signals(settings)
    system_df = apply_timeframe_view(system_raw_df, settings)
    df = apply_timeframe_view(raw_df, settings)
    if df.empty and (system_raw_df is None or system_raw_df.empty):
        st.info("No journal data available yet for this timeframe. Try View performance timeframe = All.")
        return
    if df.empty:
        st.info("No user-watchlist journal data available yet for this timeframe. The System Performance tab may still contain full Supabase data.")
        df = pd.DataFrame(columns=raw_df.columns if raw_df is not None else [])
    df["outcome"] = df.apply(outcome_label, axis=1)
    trades = df[df["grade"].astype(str).isin(VALID_GRADES)].copy()
    no_trade_source = df.copy()
    if no_trade_source.empty and raw_df is not None and not raw_df.empty:
        no_trade_source = raw_df.copy()
        if "outcome" not in no_trade_source.columns:
            no_trade_source["outcome"] = no_trade_source.apply(outcome_label, axis=1)

    no_trades = no_trade_source[
        no_trade_source["grade"].astype(str).str.upper().eq("NO TRADE")
        & no_trade_source["signal"].astype(str).str.upper().isin(["BUY", "SELL"])
    ].copy()
    open_trades = trades[trades["status"].astype(str).str.upper().eq("OPEN")]
    closed_trades = trades[trades["outcome"].isin(["WIN", "LOSS", "BREAKEVEN", "CLOSED"])]

    t1, t2, t3, t4, t5, t6 = st.tabs(["User Journal", "System Performance", "Prop Firm", "No Trade Tracker", "Coach AI", "Explain AI"])

    with t1:
        c1, c2, c3, c4 = st.columns(4)
        resolved = closed_trades[closed_trades["outcome"].isin(["WIN", "LOSS", "BREAKEVEN", "CLOSED"])]
        won_trades = int(closed_trades["outcome"].astype(str).eq("WIN").sum()) if not closed_trades.empty else 0
        with c1: metric_card("Total journaled", f"{len(trades):,}", "A+/A/B/C setups")
        with c2: metric_card("Open", f"{len(open_trades):,}", "Currently active")
        with c3: metric_card("Closed", f"{len(closed_trades):,}", "Resolved trades")
        with c4: metric_card("Won", f"{won_trades:,}", "Winning trades")

        st.subheader("Account performance")
        render_performance_strip(trades, settings, prop_mode=False)
        if len(resolved):
            st.markdown("<div class='section-gap'></div>", unsafe_allow_html=True)
            st.subheader("User split analysis")
            ug1, ug2 = st.columns(2)
            with ug1:
                grade_perf = resolved.groupby("grade", as_index=False).agg(win_rate=("outcome", lambda x: (x == "WIN").sum() / len(x) * 100 if len(x) else 0), trades=("signal_id", "count"))
                st.markdown("**By grade**")
                render_benzino_aggrid(grade_perf, key="journal_grade_perf", height=240, page_size=10, pinned=["grade"], badge_cols={"grade":"grade", "Grade":"grade"}, numeric_cols_right=[c for c in grade_perf.columns if c not in ["grade", "Grade"]], enable_search=False, show_footer=False, use_pagination=False)
            with ug2:
                session_perf = resolved.groupby("session", as_index=False).agg(win_rate=("outcome", lambda x: (x == "WIN").sum() / len(x) * 100 if len(x) else 0), trades=("signal_id", "count"))
                st.markdown("**By session**")
                render_benzino_aggrid(session_perf, key="journal_session_perf", height=240, page_size=10, pinned=["session"], numeric_cols_right=[c for c in session_perf.columns if c not in ["session", "Session"]], enable_search=False, show_footer=False, use_pagination=False)
            ut1, ut2 = st.columns(2)
            with ut1:
                timeframe_perf = resolved.groupby("timeframe", as_index=False).agg(win_rate=("outcome", lambda x: (x == "WIN").sum() / len(x) * 100 if len(x) else 0), trades=("signal_id", "count"))
                st.markdown("**By timeframe**")
                render_benzino_aggrid(timeframe_perf, key="journal_timeframe_perf", height=240, page_size=10, pinned=["timeframe"], numeric_cols_right=[c for c in timeframe_perf.columns if c != "timeframe"], enable_search=False, show_footer=False, use_pagination=False)
            with ut2:
                asset_perf = resolved.groupby("asset", as_index=False).agg(win_rate=("outcome", lambda x: (x == "WIN").sum() / len(x) * 100 if len(x) else 0), trades=("signal_id", "count"))
                st.markdown("**By asset**")
                render_benzino_aggrid(asset_perf.sort_values("trades", ascending=False), key="journal_asset_perf", height=240, page_size=10, pinned=["asset"], numeric_cols_right=[c for c in asset_perf.columns if c != "asset"], enable_search=False, show_footer=False, use_pagination=False)

        def _render_journal_signal_grid(source_df: pd.DataFrame, table_title: str, key_prefix: str, cols: list[str], badge_map: dict, numeric_right: list[str]) -> None:
            prepared = prepare_signal_table(source_df[[c for c in cols if c in source_df.columns]].head(200))
            title_col, sig_col, grade_col, search_col = st.columns([5.0, 1.15, 1.15, 2.4], vertical_alignment="center")
            with title_col:
                st.markdown(f"<div class='benzino-panel-title'>{html.escape(table_title)}</div>", unsafe_allow_html=True)
            with sig_col:
                signal_choice = st.selectbox("Signal", ["All", "BUY", "SELL", "HOLD", "NO TRADE"], label_visibility="collapsed", key=f"{key_prefix}_signal_filter")
            with grade_col:
                grade_choice = st.selectbox("Grade", ["All", "A+", "A", "B", "C", "NO TRADE"], label_visibility="collapsed", key=f"{key_prefix}_grade_filter")
            with search_col:
                search_choice = st.text_input(f"Search {table_title}", placeholder="Search…", label_visibility="collapsed", key=f"{key_prefix}_search")
            if signal_choice != "All" and "Signal" in prepared.columns:
                prepared = prepared[prepared["Signal"].astype(str).str.upper().str.contains(signal_choice, na=False)]
            if grade_choice != "All" and "Grade" in prepared.columns:
                prepared = prepared[prepared["Grade"].astype(str).str.upper().eq(grade_choice.upper())]
            if search_choice:
                q = str(search_choice).lower().strip()
                prepared = prepared[prepared.astype(str).apply(lambda col: col.str.lower().str.contains(q, na=False)).any(axis=1)]
            render_benzino_aggrid(
                prepared,
                key=key_prefix,
                height=420,
                page_size=10,
                pinned=["Asset", "Signal", "Grade", "Age"],
                badge_cols=badge_map,
                numeric_cols_right=numeric_right,
                enable_search=False,
                title=None,
            )

        open_view = add_trade_pnl_columns(open_trades, settings)
        open_cols = ["created_at", "created_at_eat", "asset", "timeframe", "signal", "grade", "entry", "sl", "tp", "rr", "risk_cash", "potential_tp_cash", "potential_sl_cash", "bars_open", "session"]
        _render_journal_signal_grid(
            open_view,
            "Open trades",
            "journal_open_trades",
            open_cols,
            {"Signal":"signal", "Grade":"grade", "Status":"status"},
            ["Entry", "SL", "TP", "RR", "risk_cash", "potential_tp_cash", "potential_sl_cash"],
        )
        closed_view = add_trade_pnl_columns(closed_trades, settings)
        closed_cols = ["created_at", "created_at_eat", "asset", "timeframe", "signal", "grade", "status", "outcome", "r_multiple", "pnl_cash", "balance_after", "exit_reason", "session"]
        _render_journal_signal_grid(
            closed_view,
            "Closed trades",
            "journal_closed_trades",
            closed_cols,
            {"Signal":"signal", "Grade":"grade", "Status":"status", "Outcome":"outcome"},
            ["RR", "R Multiple", "pnl_cash", "balance_after"],
        )
        render_balance_curve(trades, settings, title="User Journal Balance Curve")


    with t2:
        # System Performance must use the full Supabase scanner history, not the user's
        # currently selected View Performance timeframe. The user's journal tab is
        # timeframe-scoped; this tab is intentionally global/system-wide.
        render_system_performance(system_raw_df, settings)

    with t3:
        prop_state = load_prop_firm_state()
        prop_trades = load_prop_firm_trades()
        challenge_tf = str(settings.get("preferred_timeframe") or settings.get("view_timeframe") or "1h")
        if not prop_trades.empty and "timeframe" in prop_trades.columns:
            prop_trades = prop_trades[prop_trades["timeframe"].astype(str).str.lower().eq(challenge_tf.lower())].copy()

        st.caption(
            f"This tab shows the official scanner-maintained FTMO-style ledger. It uses the scanner's fixed "
            f"account size and risk-per-trade, not the sidebar what-if controls. Rules in view: selected timeframe "
            f"{challenge_tf}; 10% profit target; 5% max daily loss; 10% max total loss; minimum 4 trading days; "
            f"max 3 entries per day; one open trade per asset; no second entry on the same asset until the first resolves. "
            f"These entry rules must also be enforced in scanner.py for future trade creation."
        )

        starting = float(prop_state.get("starting_balance") or 10000.0)
        current = float(prop_state.get("current_equity") or starting)
        daily_pnl = float(prop_state.get("daily_pnl") or 0.0)
        trading_days = int(prop_state.get("trading_days") or 0)
        status = str(prop_state.get("status") or "ACTIVE")
        roi_pct = (current / starting - 1) * 100 if starting else 0.0
        progress_to_target = max(0.0, min(1.0, (current - starting) / (starting * 0.10))) if starting else 0.0

        status_color = "green" if status == "PASSED" else "red" if status == "FAILED" else ""
        c1, c2, c3, c4, c5 = st.columns(5)
        with c1: metric_card("Official equity", f"${current:,.2f}", f"Start ${starting:,.0f}")
        with c2: metric_card("ROI to target", f"{roi_pct:+.2f}%", "Target +10.00%")
        with c3: metric_card("Today's P/L", f"${daily_pnl:+,.2f}", f"Daily floor -${starting*0.05:,.0f}")
        with c4: metric_card("Trading days", f"{trading_days}", "Minimum 4 required")
        with c5: metric_card("Challenge status", status, "")

        st.markdown(f"<div class='compact-card'><b class='{status_color}'>{html.escape(status)}</b> · Progress to 10% target: {progress_to_target*100:.0f}%</div>", unsafe_allow_html=True)
        st.progress(progress_to_target)

        if status == "FAILED":
            st.error("This challenge has breached its daily or max loss limit. Coach AI below will flag this — no new A+/A trades should be treated as challenge-eligible until the ledger is reset.")
        elif status == "PASSED":
            st.success("This challenge has reached its 10% profit target with the minimum trading days satisfied.")

        st.markdown("<div class='section-gap'></div>", unsafe_allow_html=True)
        st.subheader("Official closed A+/A trades")
        if prop_trades.empty:
            st.info("No A+/A trades have closed yet. This table fills in automatically the moment the scanner resolves one.")
        else:
            view = prop_trades.copy()
            if "closed_at" in view.columns:
                view["closed_at"] = view["closed_at"].apply(fmt_nairobi)
            if "signal_created_at" in view.columns:
                view["signal_created_at"] = view["signal_created_at"].apply(fmt_nairobi)
            cols = ["closed_at", "asset", "timeframe", "grade", "r_multiple", "pnl_cash", "exit_reason", "entry", "sl", "tp"]
            render_benzino_aggrid(view[[c for c in cols if c in view.columns]].head(300), key="challenge_closed_trades", height=420, page_size=10, pinned=["closed_at", "asset"], badge_cols={"grade":"grade", "Grade":"grade"}, numeric_cols_right=["r_multiple", "pnl_cash", "entry", "sl", "tp"])

            running = prop_trades.sort_values("closed_at").copy()
            running["equity"] = starting + pd.to_numeric(running["pnl_cash"], errors="coerce").fillna(0).cumsum()
            fig = go.Figure()
            fig.add_trace(go.Scatter(y=running["equity"], mode="lines+markers", name="Official equity"))
            fig.add_hline(y=starting, line_dash="dot", annotation_text="Starting balance")
            fig.add_hline(y=starting * 1.10, line_dash="dot", line_color="#00D4A3", annotation_text="10% target")
            fig.add_hline(y=starting * 0.90, line_dash="dot", line_color="#FF5D5D", annotation_text="10% max loss")
            fig.update_layout(template="plotly_dark", paper_bgcolor="#0F2235", plot_bgcolor="#0F2235",
                             height=360, margin=dict(t=30, b=20), title="Official prop-firm equity curve")
            st.plotly_chart(fig, use_container_width=True)

        st.markdown("<div class='section-gap'></div>", unsafe_allow_html=True)
        st.subheader("Pass / fail probability")
        mc = prop_firm_monte_carlo(prop_trades, prop_state)
        m1, m2, m3 = st.columns(3)
        with m1: metric_card("Pass probability", f"{mc['pass_pct']:.2f}%", f"From current equity, {mc['sample_size']} real closed trade(s)")
        with m2: metric_card("Breach probability", f"{mc['fail_pct']:.2f}%", "Within next 60 simulated trades")
        with m3: metric_card("Unresolved", f"{mc['unresolved_pct']:.2f}%", "Neither hit in 60 trades")
        if mc["used_placeholder"]:
            st.caption("Fewer than 10 real closed A+/A trades exist, so this uses a conservative placeholder R-distribution. It will automatically switch to your real trade history once enough A+/A trades close.")

        st.markdown("<div class='section-gap'></div>", unsafe_allow_html=True)
        with st.expander("Personal what-if comparison (uses YOUR sidebar account size, not the official ledger)", expanded=False):
            st.caption("This box is for curiosity only — it asks 'what if I personally risked A+/A setups at MY chosen account size and risk %?'. It is intentionally separate from the official challenge above.")
            prop_source = trades[trades["grade"].astype(str).isin(["A+", "A"])].copy()
            render_performance_strip(prop_source, settings, prop_mode=True)

    with t4:
        st.write("These are blocked Buy/Sell ideas that were rejected as No Trade because risk/reward or agreement was too weak to journal as real trades. HOLD rows are excluded because they have no trade direction, entry thesis, TP/SL path, or meaningful hypothetical outcome.")
        no_trades_resolved = no_trades[no_trades["shadow_outcome"].notna()].copy() if "shadow_outcome" in no_trades.columns else pd.DataFrame()
        h1, h2, h3, h4 = st.columns(4)
        with h1: metric_card("Total No Trade ideas", f"{len(no_trades):,}", "Never alerted, never journaled")
        with h2: metric_card("Hypothetically resolved", f"{len(no_trades_resolved):,}", "Scanner checked TP/SL/expiry")
        if not no_trades_resolved.empty:
            hyp_wins = no_trades_resolved["shadow_outcome"].astype(str).eq("SHADOW_TP")
            hyp_win_rate = (hyp_wins.sum() / len(no_trades_resolved) * 100) if len(no_trades_resolved) else 0.0
            with h3: metric_card("Hypothetical win rate", f"{hyp_win_rate:.2f}%", "Not part of real journal win rate")
            with h4: metric_card("Hypothetical avg R", f"{pd.to_numeric(no_trades_resolved['shadow_r_multiple'], errors='coerce').mean():+.2f}R", "Across resolved blocked ideas")
            st.markdown(
                "<div class='grey-note'>⚠️ These figures describe what would have happened if every blocked idea "
                "had been taken anyway. They are shadow research only and are <b>excluded</b> from the real "
                "User Journal and Prop Firm win rates above, by design.</div>",
                unsafe_allow_html=True,
            )
        else:
            with h3: metric_card("Hypothetical win rate", "—", "Waiting for candles to resolve")
            with h4: metric_card("Hypothetical avg R", "—", "")
        st.markdown("<div class='section-gap'></div>", unsafe_allow_html=True)
        no_trade_cols = ["created_at_eat", "asset", "timeframe", "signal", "grade", "status", "entry", "sl", "tp", "rr", "confidence", "edge_score", "shadow_outcome", "shadow_r_multiple", "shadow_exit_price", "reason", "session"]
        render_benzino_aggrid(prepare_signal_table(no_trades[[c for c in no_trade_cols if c in no_trades.columns]].head(300)), key="no_trade_tracker", title="Research Queue", height=460, page_size=10, pinned=["Asset", "Signal", "Grade", "Age"], badge_cols={"Signal":"signal", "Grade":"grade", "Status":"status", "Hypothetical Outcome":"outcome"}, numeric_cols_right=["Entry", "SL", "TP", "Confidence", "Decayed Confidence", "RR", "Edge Score", "Hypothetical R", "Hypothetical Exit", "R Multiple"])

    with t5:
        st.subheader("Coach AI")
        st.caption("Coach AI reviews your journal patterns and translates trade history into practical behaviour, risk, and execution guidance.")
        prop_state = load_prop_firm_state()
        prop_status = str(prop_state.get("status") or "ACTIVE")
        prop_notes = []
        if prop_status == "FAILED":
            prop_notes.append("🚨 The **official prop challenge has FAILED** (daily or max loss breached). Coach AI strongly recommends pausing new A+/A entries until the ledger is reviewed — continuing to risk capital against a failed challenge defeats the purpose of grading by confluence in the first place.")
        elif prop_status == "PASSED":
            prop_notes.append("🏆 The **official prop challenge has PASSED** its 10% target with the minimum trading days met. Coach AI suggests locking in this result rather than continuing to risk it on the same ledger.")
        else:
            roi_now = (float(prop_state.get("current_equity") or 0) / float(prop_state.get("starting_balance") or 1) - 1) * 100
            prop_notes.append(f"Official challenge status: **ACTIVE**, currently at **{roi_now:+.2f}%** toward the 10% target. Coach AI will flag this immediately if it ever moves to FAILED or PASSED.")

        if len(closed_trades) < 10:
            render_ai_card(
                "Building Evidence",
                "\n\n".join([f"- {n}" for n in prop_notes]) +
                f"\n\n- Coach has **{len(closed_trades)}** closed journal trades. It will avoid declaring a best "
                "asset/session until there is enough evidence (minimum 5 closed trades per group). Keep "
                "collecting data, but watch open exposure and avoid changing the rules too early."
            )
        else:
            resolved = closed_trades[closed_trades["outcome"].isin(["WIN", "LOSS", "BREAKEVEN", "CLOSED"])].copy()
            notes = list(prop_notes)
            if not resolved.empty:
                asset_perf = resolved.groupby("asset").agg(win_rate=("outcome", lambda x: ((x == "WIN").sum() / len(x)) if len(x) else 0), trades=("signal_id", "count"), avg_r=("r_multiple", "mean")).reset_index()
                asset_perf = asset_perf[asset_perf["trades"] >= 5].sort_values(["win_rate", "avg_r"], ascending=False)
                if not asset_perf.empty:
                    best = asset_perf.iloc[0]
                    notes.append(f"Your strongest supported asset is **{best['asset']}**: {best['trades']} closed trades, {best['win_rate']*100:.2f}% win rate, average {best['avg_r']:+.2f}R. Treat this as the playbook to repeat, not just a lucky asset.")
                weak = resolved.groupby("asset").agg(win_rate=("outcome", lambda x: ((x == "WIN").sum() / len(x)) if len(x) else 0), trades=("signal_id", "count"), avg_r=("r_multiple", "mean")).reset_index()
                weak = weak[weak["trades"] >= 5].sort_values(["win_rate", "avg_r"], ascending=True)
                if not weak.empty:
                    w = weak.iloc[0]
                    notes.append(f"Your weakest supported area is **{w['asset']}**: {w['trades']} closed trades and {w['win_rate']*100:.2f}% win rate. Reduce size or demand stronger MTF confirmation here until the numbers improve.")
                session_perf = resolved.groupby("session").agg(win_rate=("outcome", lambda x: ((x == "WIN").sum() / len(x)) if len(x) else 0), trades=("signal_id", "count"), avg_r=("r_multiple", "mean")).reset_index()
                session_perf = session_perf[session_perf["trades"] >= 5].sort_values(["win_rate", "avg_r"], ascending=False)
                if not session_perf.empty:
                    srow = session_perf.iloc[0]
                    notes.append(f"Best supported session is **{srow['session']}** with {srow['trades']} closed trades and {srow['win_rate']*100:.2f}% win rate. Prioritise this session when similar grades appear.")
            if len(open_trades) >= 3:
                notes.append("Exposure warning: three or more trades are open. The coach would slow down new entries until at least one trade resolves, especially in prop-firm mode.")
            a_count = len(open_trades[open_trades["grade"].isin(["A+", "A"])])
            b_count = len(open_trades[open_trades["grade"].isin(["B", "C"])])
            notes.append(f"Current open quality mix: **{a_count}** A+/A trade(s) and **{b_count}** B/C trade(s). Prop-firm focus should stay on A+/A only; B/C is research/journal learning fuel.")
            body = "\n\n".join([f"- {n}" for n in notes])
            render_ai_card("Trade Management Guidance", body)



    with t6:
        st.subheader("Explain AI")
        st.caption(
            "Explain AI starts with closed outcomes by default because resolved trades provide the clearest lessons. "
            "You can also review open journal trades and blocked No Trade ideas to understand the full signal lifecycle."
        )
        # Review Outcomes: only closed trades should appear here.
        review_frames = []
        if not closed_trades.empty:
            tmp = closed_trades.sort_values("created_at", ascending=False).head(75).copy()
            tmp["Review Case"] = "Closed Outcome"
            review_frames.append(tmp)
        if review_frames:
            review_queue = pd.concat(review_frames, ignore_index=True, sort=False)
            review_display = prepare_signal_table(review_queue, limit=75)
            cols = ["Review Case"] + [c for c in review_display.columns if c != "Review Case"]
            review_display = review_display[cols]
            title_col, sig_col, grade_col, status_col, search_col = st.columns([4.0, 1.1, 1.1, 1.25, 2.2], vertical_alignment="center")
            with title_col:
                st.markdown("<div class='benzino-panel-title'>Review Outcomes</div>", unsafe_allow_html=True)
            with sig_col:
                explain_signal_filter = st.selectbox("Signal", ["All", "BUY", "SELL"], label_visibility="collapsed", key="explain_review_signal_filter")
            with grade_col:
                explain_grade_filter = st.selectbox("Grade", ["All", "A+", "A", "B", "C"], label_visibility="collapsed", key="explain_review_grade_filter")
            with status_col:
                _status_options = ["All"] + sorted(review_display["Status"].dropna().astype(str).unique().tolist()) if "Status" in review_display.columns else ["All"]
                explain_status_filter = st.selectbox("Status", _status_options, label_visibility="collapsed", key="explain_review_status_filter")
            with search_col:
                explain_review_search = st.text_input("Search Explain AI review outcomes", placeholder="Search…", label_visibility="collapsed", key="explain_review_search")
            if explain_signal_filter != "All" and "Signal" in review_display.columns:
                review_display = review_display[review_display["Signal"].astype(str).str.upper().str.contains(explain_signal_filter, na=False)]
            if explain_grade_filter != "All" and "Grade" in review_display.columns:
                review_display = review_display[review_display["Grade"].astype(str).str.upper().eq(explain_grade_filter.upper())]
            if explain_status_filter != "All" and "Status" in review_display.columns:
                review_display = review_display[review_display["Status"].astype(str).eq(explain_status_filter)]
            if explain_review_search:
                q = str(explain_review_search).lower().strip()
                review_display = review_display[review_display.astype(str).apply(lambda col: col.str.lower().str.contains(q, na=False)).any(axis=1)]
            render_benzino_aggrid(review_display, key="explain_ai_review_queue", height=360, page_size=8, pinned=["Review Case", "Asset"], badge_cols={"Signal":"signal", "Grade":"grade", "Status":"status", "Outcome":"outcome"}, numeric_cols_right=["Confidence", "Decayed Confidence", "RR", "R Multiple", "Edge Score", "MTF Score"], enable_search=False)

        case = st.selectbox(
            "Choose a case",
            ["📄 Closed outcome", "📂 Open journal trade", "⛔ Blocked NO TRADE idea"],
            index=0,
        )

        if "Blocked NO TRADE" in case:
            blocked_latest = no_trades.sort_values("created_at", ascending=False).head(8).copy()
            if blocked_latest.empty:
                st.info("No No Trade ideas recorded yet for this timeframe.")
            else:
                options = blocked_latest.apply(lambda r: f"{r.get('asset')} · {r.get('timeframe')} · {r.get('signal')} · {time_ago(r.get('created_at'))} · {r.get('signal_id')}", axis=1).tolist()
                choice = st.selectbox("Choose one of the last 8 blocked ideas", options, key="explain_blocked")
                sid = choice.split(" · ")[-1]
                row = blocked_latest[blocked_latest["signal_id"].astype(str).eq(sid)].iloc[0]
                render_ai_card("Why This Was Blocked", rich_signal_explanation(row))

        elif "Open journal trade" in case:
            open_latest = open_trades.sort_values("created_at", ascending=False).head(8).copy()
            if open_latest.empty:
                st.info("No open journal trades right now. This case will populate the next time an A+/A/B/C setup is graded.")
            else:
                options = open_latest.apply(lambda r: f"{r.get('asset')} · {r.get('timeframe')} · {r.get('signal')} · {r.get('grade')} · {time_ago(r.get('created_at'))} · {r.get('signal_id')}", axis=1).tolist()
                choice = st.selectbox("Choose one of the last 8 open trades", options, key="explain_open")
                sid = choice.split(" · ")[-1]
                row = open_latest[open_latest["signal_id"].astype(str).eq(sid)].iloc[0]
                render_ai_card("Why This Trade Is Still Open", rich_open_trade_explanation(row))

        else:
            closed_latest = closed_trades.sort_values("created_at", ascending=False).head(8).copy()
            if closed_latest.empty:
                st.info("No closed trades yet. Explain AI will focus on closed outcomes once TP, SL, or expiry appears.")
            else:
                options = closed_latest.apply(lambda r: f"{r.get('asset')} · {r.get('timeframe')} · {r.get('outcome')} · {r.get('grade')} · {fmt_nairobi(r.get('created_at'))} · {r.get('signal_id')}", axis=1).tolist()
                choice = st.selectbox("Choose one of the last 8 closed trades", options, key="explain_closed")
                sid = choice.split(" · ")[-1]
                row = closed_latest[closed_latest["signal_id"].astype(str).eq(sid)].iloc[0]
                render_ai_card("Closed Trade Lesson", rich_closed_trade_explanation(row))




def user_win_rate_for_admin(username: str, user_settings: dict | None = None) -> str:
    """Closed-trade win rate for the admin user-management table."""
    try:
        settings = DEFAULT_SETTINGS.copy()
        if isinstance(user_settings, dict):
            settings.update(user_settings)
        df = load_signals_for_user(username, settings)
        if df.empty:
            return "0.00%"
        df["outcome"] = df.apply(outcome_label, axis=1)
        trades = df[df["grade"].astype(str).isin(VALID_GRADES)].copy()
        closed = trades[trades["outcome"].isin(["WIN", "LOSS", "BREAKEVEN", "CLOSED"])].copy()
        if closed.empty:
            return "0.00%"
        wins = closed["outcome"].astype(str).eq("WIN").sum()
        return f"{wins / len(closed) * 100:.2f}%"
    except Exception:
        return "0.00%"


def render_settings(username: str, settings: dict) -> None:
    page_header("Settings", "Profile, watchlist, Telegram routing, activation date, and reset tools.")

    tab_profile, tab_watchlist, tab_telegram, tab_health, tab_reset = st.tabs(["Profile", "Watchlist", "Telegram", "System Health", "Reset"])
    with tab_profile:
        users = read_df("SELECT username, email, created_at, role FROM users WHERE username = %s", (username,))
        created = users.iloc[0]["created_at"] if not users.empty else "Unknown"
        current_email = str(users.iloc[0].get("email") or "") if not users.empty else ""
        c1, c2, c3, c4 = st.columns(4)
        with c1: metric_card("Username", username, user_role(username).title())
        with c2: metric_card("Created", fmt_nairobi(created))
        with c3: metric_card("Tracking since", fmt_nairobi(settings.get("tracking_started_at", "")))
        with c4: metric_card("Preferred TF", str(settings.get("preferred_timeframe", "1h")), "Used across dashboard")
        st.markdown("<div class='compact-card'>Admin policy: the first created profile is the only admin. All later profiles are standard users.</div>", unsafe_allow_html=True)
        if is_admin():
            all_users = read_df("SELECT username, email, role, created_at FROM users ORDER BY created_at ASC")
            if not all_users.empty:
                all_users = all_users.copy()
                settings_rows = read_df("SELECT username, settings_json, updated_at FROM user_settings")
                watch_rows = read_df("SELECT scan_owner, asset FROM user_watchlists WHERE enabled = TRUE ORDER BY scan_owner, asset")
                telegram_rows = read_df("SELECT scan_owner, alerts_enabled FROM user_telegram_settings")

                settings_map = {}
                if not settings_rows.empty:
                    for _, sr in settings_rows.iterrows():
                        try:
                            payload = json.loads(sr.get("settings_json") or "{}")
                        except Exception:
                            payload = {}
                        settings_map[str(sr.get("username"))] = payload if isinstance(payload, dict) else {}

                watch_map = {}
                if not watch_rows.empty:
                    for owner, grp in watch_rows.groupby("scan_owner"):
                        watch_map[str(owner)] = ", ".join(grp["asset"].astype(str).tolist())

                telegram_map = {}
                if not telegram_rows.empty:
                    for _, tr in telegram_rows.iterrows():
                        telegram_map[str(tr.get("scan_owner"))] = bool(tr.get("alerts_enabled"))

                all_users["watchlist"] = all_users["username"].astype(str).map(watch_map).fillna("")
                all_users["watchlist_count"] = all_users["watchlist"].apply(lambda x: len([v for v in str(x).split(",") if v.strip()]))
                all_users["account_size"] = all_users["username"].astype(str).map(lambda u: settings_map.get(u, {}).get("account_size", ""))
                all_users["account_size"] = all_users["account_size"].apply(lambda v: f"{float(v):,.0f}" if str(v).strip() not in {"", "None", "nan"} else "")
                all_users["risk_pct"] = all_users["username"].astype(str).map(lambda u: settings_map.get(u, {}).get("risk_pct", ""))
                all_users["leverage"] = all_users["username"].astype(str).map(lambda u: settings_map.get(u, {}).get("leverage", ""))
                all_users["preferred_timeframe"] = all_users["username"].astype(str).map(lambda u: settings_map.get(u, {}).get("preferred_timeframe", ""))
                all_users["win_rate"] = all_users["username"].astype(str).map(lambda u: user_win_rate_for_admin(u, settings_map.get(u, {})))
                all_users["tracking_started_at"] = all_users["username"].astype(str).map(lambda u: settings_map.get(u, {}).get("tracking_started_at", ""))
                all_users["telegram_activated"] = all_users["username"].astype(str).map(lambda u: "Yes" if telegram_map.get(u) else "No")
                all_users["created_at"] = all_users["created_at"].apply(fmt_nairobi)
                all_users["tracking_started_at"] = all_users["tracking_started_at"].apply(fmt_nairobi)
                user_cols = ["username", "email", "role", "win_rate", "watchlist_count", "watchlist", "account_size", "risk_pct", "leverage", "preferred_timeframe", "telegram_activated", "created_at", "tracking_started_at"]
                all_users = all_users[[c for c in user_cols if c in all_users.columns]]
                render_benzino_aggrid(all_users, key="admin_user_management", title="User Management", height=360, page_size=10, pinned=["username"], numeric_cols_right=["win_rate", "watchlist_count", "account_size", "risk_pct", "leverage"], badge_cols={"telegram_activated": "status"})


        with st.expander("Profile email and password", expanded=False):
            email_value = st.text_input("Email for password reset", value=current_email, key="profile_email")
            if st.button("Save email", type="secondary"):
                ok, msg = update_user_email(username, email_value)
                if ok: st.success(msg)
                else: st.error(msg)
            current_pw = st.text_input("Current password", type="password", key="current_pw")
            new_pw = st.text_input("New password", type="password", key="new_pw")
            if st.button("Change password", type="secondary"):
                ok, msg = change_user_password(username, current_pw, new_pw)
                if ok: st.success(msg)
                else: st.error(msg)

        if st.button("Reset my tracking start to now", type="secondary"):
            settings["tracking_started_at"] = datetime.now(timezone.utc).isoformat()
            save_settings(username, settings)
            st.success("Tracking start reset. Future dashboard metrics will start from now.")
            st.rerun()

    with tab_watchlist:
        current = list(load_user_watchlist(username).keys())
        if not current:
            current = list(settings.get("selected_asset_keys") or DEFAULT_ASSETS)

        valid_current = [asset for asset in current if asset in ASSET_UNIVERSE]
        if not valid_current:
            valid_current = DEFAULT_ASSETS.copy()

        grouped = {}
        for key, meta in ASSET_UNIVERSE.items():
            grouped.setdefault(meta["group"], []).append(key)

        st.markdown("<div class='benzino-panel-title'>Edit Watchlist</div>", unsafe_allow_html=True)
        st.caption(
            "Choose the assets this user wants to track. Saving updates Supabase immediately, "
            "refreshes the dashboard filter, and is picked up by Telegram watchlist routing on the next scanner run."
        )

        all_assets_ordered = []
        for group in sorted(grouped.keys()):
            all_assets_ordered.extend(sorted(grouped[group]))

        with st.form("watchlist_edit_form", clear_on_submit=False):
            selected = st.multiselect(
                "Active watchlist",
                options=all_assets_ordered,
                default=valid_current,
                format_func=lambda asset: f"{asset} · {ASSET_UNIVERSE[asset]['group']}",
                help="Select one or more assets, then click Save watchlist.",
            )

            c_save, c_reset = st.columns([1, 1])
            with c_save:
                save_clicked = st.form_submit_button("Save watchlist", type="primary", use_container_width=True)
            with c_reset:
                reset_clicked = st.form_submit_button("Restore default watchlist", use_container_width=True)

        if reset_clicked:
            selected = DEFAULT_ASSETS.copy()
            save_user_watchlist(username, selected)
            settings["selected_asset_keys"] = selected
            save_settings(username, settings)
            st.success("Watchlist restored to the default set.")
            st.rerun()

        if save_clicked:
            selected = [asset for asset in selected if asset in ASSET_UNIVERSE]
            if not selected:
                st.error("Select at least one asset before saving.")
            else:
                save_user_watchlist(username, selected)
                settings["selected_asset_keys"] = selected
                save_settings(username, settings)
                st.success("Watchlist updated successfully.")
                st.rerun()

        current = list(load_user_watchlist(username).keys())
        current_set = set(current or DEFAULT_ASSETS)
        st.caption("Current active watchlist: " + ", ".join(current or DEFAULT_ASSETS))

        st.markdown("<div class='section-gap'></div>", unsafe_allow_html=True)
        wl_system_df = load_all_system_signals(settings)
        if wl_system_df is not None and not wl_system_df.empty:
            wl_system_df = wl_system_df.copy()
            wl_system_df["outcome"] = wl_system_df.apply(outcome_label, axis=1)
            wl_graded = wl_system_df[wl_system_df["grade"].astype(str).isin(VALID_GRADES)].copy()
            wl_resolved_all = wl_graded[wl_graded["outcome"].isin(["WIN", "LOSS", "BREAKEVEN", "CLOSED"])].copy()
            system_win_rate = (wl_resolved_all["outcome"].eq("WIN").sum() / len(wl_resolved_all) * 100) if len(wl_resolved_all) else 0.0

            wl_user_df = wl_graded[wl_graded["asset"].astype(str).isin(current_set)].copy()
            wl_resolved_user = wl_user_df[wl_user_df["outcome"].isin(["WIN", "LOSS", "BREAKEVEN", "CLOSED"])].copy()
            user_win_rate = (wl_resolved_user["outcome"].eq("WIN").sum() / len(wl_resolved_user) * 100) if len(wl_resolved_user) else 0.0

            wl_user_open = wl_user_df[wl_user_df["status"].astype(str).str.upper().eq("OPEN")]
            wl_user_avg_r = pd.to_numeric(wl_resolved_user.get("r_multiple", pd.Series(dtype=float)), errors="coerce").mean() if len(wl_resolved_user) else 0.0

            wm1, wm2, wm3, wm4, wm5 = st.columns(5)
            with wm1:
                metric_card("System win rate", f"{system_win_rate:.2f}%", f"{len(wl_resolved_all):,} closed · all assets")
            with wm2:
                metric_card("Watchlist win rate", f"{user_win_rate:.2f}%", f"{len(wl_resolved_user):,} closed · your {len(current_set)} assets")
            with wm3:
                metric_card("Watchlist open trades", f"{len(wl_user_open):,}", "Currently active")
            with wm4:
                metric_card("Watchlist avg R", f"{wl_user_avg_r:+.2f}", "Closed trades only")
            with wm5:
                metric_card("Watchlist coverage", f"{len(current_set)}/{len(ASSET_UNIVERSE)}", "Assets enabled")
        else:
            st.info("No scanner data yet — win rate metrics will appear once signals have been generated.")

        st.markdown("<div class='section-gap'></div>", unsafe_allow_html=True)
        watchlist_rows = []
        for key, meta in ASSET_UNIVERSE.items():
            watchlist_rows.append({
                "Status": "Enabled" if key in current_set else "Disabled",
                "Asset": key,
                "Ticker": meta.get("ticker"),
                "Group": meta.get("group"),
            })

        render_benzino_aggrid(
            pd.DataFrame(watchlist_rows),
            key="watchlist_editor_table",
            title="Available Assets",
            height=430,
            page_size=12,
            pinned=["Asset"],
            badge_cols={"Status": "status"},
            enable_search=True,
        )

    with tab_telegram:
        st.caption(
            "Activating here registers your chat ID with the scanner directly — every 5-minute scan now reads "
            "this table and routes alerts to you on top of (not instead of) the admin's global Telegram "
            "destination. 'Watchlist only' sends alerts solely for assets in your saved Watchlist tab; "
            "'All signals' sends every A+/A/B/C alert the scanner generates, regardless of your watchlist."
        )
        try:
            tg = read_df("SELECT * FROM user_telegram_settings WHERE scan_owner = %s", (username,))
            row = tg.iloc[0].to_dict() if not tg.empty else {}
            active = bool(row.get("alerts_enabled", False))
            st.markdown(f"**Telegram alerts:** {'Active' if active else 'Inactive'}")

            # Show the confirmation from the PREVIOUS run here, before anything else.
            # st.success() called right before st.rerun() never has a chance to paint
            # in the browser, since the rerun wipes the frame immediately — so the
            # save was always working, it just looked silent. Stashing a flag in
            # session_state across the rerun and showing the message on the next run
            # makes the confirmation actually visible.
            _tg_flash = st.session_state.pop("telegram_settings_flash", None)
            if _tg_flash:
                st.success(_tg_flash)

            chat_id = st.text_input("Telegram chat ID", value=str(row.get("telegram_chat_id") or settings.get("telegram_chat_ids") or ""))
            current_mode = "All signals" if bool(row.get("all_signals_alerts", False)) else "Watchlist only"
            alert_mode = st.selectbox("Alert route", ["Watchlist only", "All signals"], index=0 if current_mode == "Watchlist only" else 1)
            watchlist_alerts = alert_mode == "Watchlist only"
            all_alerts = alert_mode == "All signals"

            col_a, col_b = st.columns(2)
            with col_a:
                activate_clicked = st.button("Activate Settings", type="primary", width="stretch", disabled=active)
            with col_b:
                st.markdown("<div class='danger-button'>", unsafe_allow_html=True)
                deactivate_clicked = st.button("Deactivate alerts", disabled=not active, width="stretch")
                st.markdown("</div>", unsafe_allow_html=True)

            if activate_clicked and not str(chat_id).strip():
                st.error("Enter your Telegram chat ID before activating alerts.")
            elif activate_clicked or deactivate_clicked:
                new_active = True if activate_clicked else False
                execute(
                    """
                    INSERT INTO user_telegram_settings(scan_owner, telegram_chat_id, alerts_enabled, watchlist_alerts, all_signals_alerts, updated_at)
                    VALUES (%s,%s,%s,%s,%s,NOW())
                    ON CONFLICT (scan_owner) DO UPDATE
                    SET telegram_chat_id = EXCLUDED.telegram_chat_id,
                        alerts_enabled = EXCLUDED.alerts_enabled,
                        watchlist_alerts = EXCLUDED.watchlist_alerts,
                        all_signals_alerts = EXCLUDED.all_signals_alerts,
                        updated_at = NOW()
                    """,
                    (username, chat_id, new_active, watchlist_alerts, all_alerts),
                )
                settings["telegram_chat_ids"] = chat_id
                settings["telegram_watchlist_enabled"] = watchlist_alerts
                settings["telegram_all_signals_enabled"] = all_alerts
                settings["telegram_alerts_enabled"] = new_active
                if activate_clicked:
                    settings["telegram_alerts_activated_at"] = datetime.now(timezone.utc).isoformat()
                save_settings(username, settings)
                # Stash the confirmation so it survives the rerun below and actually displays.
                st.session_state["telegram_settings_flash"] = (
                    "Telegram settings activated." if new_active else "Telegram alerts deactivated."
                )
                st.rerun()
            st.caption("Activate Settings saves the chat ID and alert route in one step. Only one route can be active at a time.")
        except Exception as exc:
            st.error(f"Telegram settings error: {exc}")

    with tab_health:
        render_system_health_panel()

    with tab_reset:
        st.warning("Reset tools do not delete your login. They only clear personal settings/watchlist, or admin global scanner data if explicitly selected.")
        if st.button("Clear my watchlist", type="secondary"):
            execute("UPDATE user_watchlists SET enabled = FALSE WHERE scan_owner = %s", (username,))
            st.success("Watchlist cleared.")
        if is_admin():
            st.divider()
            st.subheader("Admin tools")
            confirm = st.text_input("Type DELETE GLOBAL SCANNER DATA to clear scanner_signals and prop ledgers")
            if st.button("Admin clear global scanner data", type="secondary"):
                if confirm == "DELETE GLOBAL SCANNER DATA":
                    execute("DELETE FROM prop_firm_trades")
                    execute("DELETE FROM prop_firm_state")
                    execute("DELETE FROM scanner_signals")
                    execute("DELETE FROM scanner_runtime_log")
                    st.success("Global scanner data cleared.")
                else:
                    st.error("Confirmation text did not match.")

# ═══════════════════════════════════════════════════════════════════════════════
# MAIN
# ═══════════════════════════════════════════════════════════════════════════════

def main() -> None:
    apply_theme()
    try:
        init_tables()
    except Exception as exc:
        st.error(f"Database not ready: {exc}")
        st.stop()

    render_auth_gate()
    username = active_username()
    settings = load_settings(username)
    page = sidebar_controls(username, settings)
    settings = render_user_topbar(username, settings)

    if page == "Dashboard":
        render_opportunity_board(username, settings)
    elif page == "Asset Deep Dive":
        render_asset_deep_dive(username, settings)
    elif page == "Market News":
        render_market_news(username, settings)
    elif page == "Workflow":
        render_workflow(username, settings)
    else:
        render_settings(username, settings)


if __name__ == "__main__":
    main()