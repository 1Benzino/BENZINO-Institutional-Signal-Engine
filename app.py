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

import numpy as np
import pandas as pd
import streamlit as st
import plotly.express as px
import plotly.graph_objects as go

try:
    import psycopg2
    from psycopg2.extras import RealDictCursor
except Exception:  # pragma: no cover
    psycopg2 = None
    RealDictCursor = None

# ═══════════════════════════════════════════════════════════════════════════════
# CONFIG
# ═══════════════════════════════════════════════════════════════════════════════

APP_VERSION = "v4.7-agreement-confidence"
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
        r_multiple NUMERIC
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
    st.markdown("""
    <div style='text-align:center;padding:35px 0 15px;'>
      <div style='font-size:62px;'>📡</div>
      <div style='font-size:44px;font-weight:950;color:#00D4A3;letter-spacing:2px;'>BENZINO</div>
      <div style='color:#7F9BB8;font-weight:700;'>Institutional Signal Engine</div>
    </div>
    """, unsafe_allow_html=True)
    left, mid, right = st.columns([1, 1.25, 1])
    with mid:
        tab_login, tab_create, tab_reset = st.tabs(["Login", "Create User", "Reset Password"])
        with tab_login:
            username = st.text_input("Username", key="login_user")
            password = st.text_input("PIN / password", type="password", key="login_pass")
            if st.button("Login", type="primary", width="stretch"):
                if validate_login(username, password):
                    with st.spinner("Loading your Benzino dashboard…"):
                        st.session_state.auth_user = normalize_username(username)
                    st.rerun()
                else:
                    st.error("Invalid username or password.")
        with tab_create:
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
        with tab_reset:
            lookup = st.text_input("Username or saved email", key="reset_lookup")
            st.caption("A temporary password will be sent to the email saved on the profile.")
            if st.button("Send reset password", type="primary", width="stretch"):
                ok, msg = reset_password_by_email(lookup)
                if ok:
                    st.success(msg)
                else:
                    st.error(msg)
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
    df = numeric_cols(df, ["confidence", "edge_score", "ml_prob", "entry", "sl", "tp", "rr", "rsi", "atr", "exit_price", "r_multiple", "bars_open", "mtf_score"])
    df["created_at"] = pd.to_datetime(df["created_at"], errors="coerce", utc=True)
    df["created_at_eat"] = df["created_at"].apply(fmt_nairobi)
    df["session"] = df["created_at"].apply(session_name)
    return df


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
        losses = closed["pnl_cash"] < 0
        resolved = int((wins | losses).sum())
        out["win_rate"] = float(wins.sum() / resolved * 100) if resolved else 0.0
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
    with c5: metric_card("Win rate", f"{perf['win_rate']:.1f}%", f"{perf['closed_count']} closed")
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
    st.plotly_chart(fig, width="stretch")



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


def decayed_confidence_value(confidence, created_at, timeframe: str = "1h") -> float:
    base = float(pd.to_numeric(confidence, errors="coerce") if confidence is not None else 50)
    ts = to_nairobi(created_at)
    if ts is None:
        return base
    age_hours = max(0.0, (pd.Timestamp.now(tz=NAIROBI_TZ) - ts).total_seconds() / 3600)
    half_life = {"15m": 3, "1h": 8, "4h": 24, "1d": 96}.get(str(timeframe).lower(), 8)
    decay = 0.5 ** (age_hours / half_life)
    return float(50 + (base - 50) * decay)


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
        direction = payload.get("direction", "NEUTRAL")
        strength = payload.get("strength", 0)
        try: strength = float(strength)
        except Exception: strength = 0
        tone = "strong" if strength >= .65 else "moderate" if strength >= .35 else "weak"
        parts.append(f"**{name}** voted **{direction}** with {tone} strength ({strength:.2f}).")
    return " ".join(parts) if parts else "No valid strategy votes were stored."


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
    directional_votes = [v for v in votes.values() if isinstance(v, dict) and str(v.get("direction", "NEUTRAL")).upper() in {"BULLISH", "BEARISH"}]
    total_votes = max(1, len(votes) or 5)
    active_votes = len(directional_votes)
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
        f"System agreement was **{conf:.1f}%**, based on **{active_votes}/{total_votes}** directional strategy vote(s). "
        f"This is different from conviction: a single strategy can be very strong, but if the other systems are neutral, agreement stays low. "
        f"After age decay it currently reads about **{dconf:.1f}%**, because older signals should lose urgency even when the original setup was clean. "
        f"The setup carries an edge score of **{edge:.1f}**, RR of **{rr:.2f}R**, and MTF alignment of **{mtf_score:.0f}%**.\n\n"
        f"**Strategy reasoning:** {format_votes(votes)}\n\n"
        f"**Multi-timeframe context:** {mtf_line or 'No detailed MTF context was stored.'}\n\n"
        f"**Final interpretation:** {reason}"
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
    # Keep the section title outside the card; the card itself contains the explanation.
    st.subheader(title)
    st.markdown("<div class='ai-card'>", unsafe_allow_html=True)
    st.markdown(body)
    st.markdown("</div>", unsafe_allow_html=True)

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
    st.subheader("System Health")
    if runtime_df.empty:
        st.info("No scanner runtime logs yet. Run the scanner once after this update and refresh the dashboard.")
        return

    c1, c2, c3, c4 = st.columns(4)
    with c1: metric_card("Last run", f"{summary['last_seconds']:.1f}s", summary["last_started_at"])
    with c2: metric_card("Fastest run", f"{summary['fastest_seconds']:.1f}s", f"{summary['runs']} logged run(s)")
    with c3: metric_card("Slowest run", f"{summary['slowest_seconds']:.1f}s")
    with c4: metric_card("Average run", f"{summary['avg_seconds']:.1f}s", f"Last TFs: {summary['last_timeframes']}")

    st.markdown("<div class='section-gap'></div>", unsafe_allow_html=True)
    st.markdown("**Recent scanner runs**")
    cols = ["started_at", "total_seconds", "assets_scanned", "signals_saved", "shadow_saved", "open_trades", "alerted", "timeframes_scanned", "fastest_asset_seconds", "slowest_asset_seconds", "avg_asset_seconds"]
    view = runtime_df[[c for c in cols if c in runtime_df.columns]].copy()
    if "started_at" in view.columns:
        view["started_at"] = view["started_at"].apply(fmt_nairobi)
    st.dataframe(view.head(30), width="stretch", hide_index=True)


def explain_signal(row: pd.Series) -> str:
    return rich_signal_explanation(row)


# ═══════════════════════════════════════════════════════════════════════════════
# UI HELPERS
# ═══════════════════════════════════════════════════════════════════════════════

def apply_theme() -> None:
    st.set_page_config(page_title="Benzino ISE", page_icon="📡", layout="wide")
    st.markdown("""
    <style>
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
    .metric-card { background:#0F2235; border:1px solid #1E3050; border-radius:18px; padding:18px; min-height:112px; box-shadow:0 0 0 1px rgba(0,212,163,0.02); }
    .compact-card { background:#0F2235; border:1px solid #1E3050; border-radius:16px; padding:14px 16px; margin:10px 0; }
    .metric-label { color:#8BAAB8; font-size:13px; font-weight:800; text-transform:uppercase; letter-spacing:.5px; }
    .metric-value { color:#E8EDF2; font-size:28px; font-weight:950; margin-top:4px; word-break:break-word; }
    .soft-card { background:#0F2235; border:1px solid #1E3050; border-radius:18px; padding:20px; margin:16px 0; line-height:1.55; }
    .ai-card { background:linear-gradient(180deg,#10283D 0%,#0F2235 100%); border:1px solid #244363; border-radius:18px; padding:22px; margin:16px 0; line-height:1.65; }
    .green { color:#00D4A3; }
    .red { color:#FF5D5D; }
    .muted { color:#8BAAB8; }
    .section-gap { height:22px; }
    .stTabs [data-baseweb="tab-list"] { gap: 8px; border-bottom: 1px solid #1E3050; }
    .stTabs [data-baseweb="tab"] { background:#0F2235; border:1px solid #1E3050; border-radius:12px 12px 0 0; color:#8BAAB8; padding:10px 16px; }
    .stTabs [aria-selected="true"] { color:#00D4A3 !important; border-bottom-color:#00D4A3 !important; }
    div[data-testid="stDataFrame"] { border:1px solid #1E3050; border-radius:14px; overflow:hidden; margin-top:12px; }
    button[kind="primary"] { background:#00A97F !important; border-color:#00D4A3 !important; }
    input, textarea, div[data-baseweb="select"] > div { border-radius:12px !important; }
    .danger-button button { background:#8B1E2D !important; border-color:#FF5D5D !important; color:#fff !important; }
    .grey-note { background:#111A2A; border:1px solid #26364A; border-radius:14px; padding:12px 14px; color:#A9BBC9; }
    </style>
    """, unsafe_allow_html=True)


def metric_card(label: str, value: str, note: str = "") -> None:
    st.markdown(
        f"""
        <div class='metric-card'>
          <div class='metric-label'>{html.escape(label)}</div>
          <div class='metric-value'>{html.escape(str(value))}</div>
          <div class='muted'>{html.escape(note)}</div>
        </div>
        """,
        unsafe_allow_html=True,
    )


def page_header(title: str, subtitle: str) -> None:
    st.markdown(f"<h1 style='color:#E8EDF2;margin-bottom:0'>{html.escape(title)}</h1>", unsafe_allow_html=True)
    st.markdown(f"<div class='muted' style='margin-bottom:18px'>{html.escape(subtitle)}</div>", unsafe_allow_html=True)


def parse_account_size(value: str, fallback: float = 10000.0) -> float:
    try:
        cleaned = re.sub(r"[^0-9.]", "", str(value or ""))
        return float(cleaned) if cleaned else float(fallback)
    except Exception:
        return float(fallback)


def sidebar_controls(username: str, settings: dict) -> dict:
    with st.sidebar:
        st.markdown("""
        <div class='sidebar-logo'>
          <div class='sidebar-dish'>📡</div>
          <div class='sidebar-brand'>BENZINO</div>
          <div class='sidebar-subtitle'>Institutional Signal Engine</div>
        </div>
        <div class='side-divider'></div>
        """, unsafe_allow_html=True)

        if st.button("Refresh dashboard", width="stretch", type="primary"):
            with st.spinner("Refreshing dashboard from Supabase…"):
                st.cache_data.clear()
            st.rerun()

        st.markdown("<div class='side-divider'></div>", unsafe_allow_html=True)
        current_account = float(settings.get("account_size", 10000) or 10000)
        account_text = st.text_input("Account size", value=f"{current_account:,.0f}")
        account = parse_account_size(account_text, current_account)
        leverage = st.number_input("Leverage", min_value=1, max_value=500, value=int(settings.get("leverage", 100)), step=1)
        risk_pct = st.number_input("Risk per trade (%)", min_value=0.1, max_value=10.0, value=float(settings.get("risk_pct", 1.0)), step=0.1)
        preferred_tf = st.selectbox(
            "Preferred timeframe",
            ["15m", "1h", "4h", "1d"],
            index=["15m", "1h", "4h", "1d"].index(str(settings.get("preferred_timeframe", "1h"))) if str(settings.get("preferred_timeframe", "1h")) in ["15m", "1h", "4h", "1d"] else 1,
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

        st.markdown("<div class='side-divider'></div>", unsafe_allow_html=True)
        st.markdown(
            f"""
            <div class='compact-card'>
              <div class='metric-label'>Version</div>
              <div style='font-weight:850;margin-top:6px;'>{html.escape(APP_VERSION)}</div>
              <div class='muted'>{html.escape(username)} · {html.escape(user_role(username).title())}</div>
            </div>
            """, unsafe_allow_html=True
        )
        if st.button("Log out", width="stretch"):
            st.session_state.pop("auth_user", None)
            st.rerun()
    return settings


# ═══════════════════════════════════════════════════════════════════════════════
# PAGES
# ═══════════════════════════════════════════════════════════════════════════════

def render_opportunity_board(username: str, settings: dict) -> None:
    page_header("System Performance & Signal Board", "Live system performance plus the latest saved scanner signals from Supabase.")
    with st.spinner("Loading latest saved Supabase data…"):
        raw_df = enrich_position_sizing(load_signals_for_user(username, settings), settings)
        df = apply_timeframe_view(raw_df, settings)
    if df.empty:
        st.info("No scanner rows yet for your watchlist/timeframe since account activation. Confirm your watchlist is saved, wait for the GitHub cron, then refresh dashboard.")
        return

    trade_df = df[df["grade"].astype(str).isin(VALID_GRADES)].copy()
    no_trade_df = df[df["grade"].astype(str).eq("NO TRADE")].copy()
    open_df = trade_df[trade_df["status"].astype(str).str.upper().eq("OPEN")]
    closed_df = trade_df[trade_df["status"].astype(str).str.upper().str.contains("CLOSED|EXPIRED|TP|SL", na=False)]

    c1, c2, c3, c4, c5 = st.columns(5)
    with c1: metric_card("Total rows", f"{len(df):,}", "Since activation")
    with c2: metric_card("Journaled", f"{len(trade_df):,}", "A+/A/B/C")
    with c3: metric_card("Open", f"{len(open_df):,}", "Active trades")
    with c4: metric_card("Closed", f"{len(closed_df):,}", "Resolved trades")
    with c5: metric_card("NO TRADE", f"{len(no_trade_df):,}", "Shadow-tracked")

    st.subheader("System performance")
    render_performance_strip(df, settings, prop_mode=False)

    st.markdown("<div class='section-gap'></div>", unsafe_allow_html=True)
    st.subheader("Latest scanner signals")
    ranked = df.sort_values(["created_at", "edge_score", "confidence"], ascending=[False, False, False]).copy()
    ranked["generated"] = ranked["created_at"].apply(time_ago)
    ranked["created_at_eat"] = ranked["created_at"].apply(fmt_nairobi)
    ranked["decayed_confidence"] = ranked.apply(lambda r: decayed_confidence_value(r.get("confidence"), r.get("created_at"), r.get("timeframe")), axis=1)
    ranked["decayed_quality"] = np.where(ranked["decayed_confidence"] >= 70, "Fresh/strong", np.where(ranked["decayed_confidence"] >= 55, "Still valid", "Aging/weak"))
    cols = [
        "generated", "created_at_eat", "asset", "timeframe", "signal", "grade", "status", "confidence", "decayed_confidence", "decayed_quality", "edge_score", "ml_prob",
        "entry", "sl", "tp", "rr", "mtf_score", "risk_cash", "position_size", "margin_required", "regime"
    ]
    st.dataframe(ranked[[c for c in cols if c in ranked.columns]].head(100), width="stretch", hide_index=True)

    left, right = st.columns(2)
    with left:
        if not trade_df.empty:
            fig = px.histogram(trade_df, x="grade", title="Grade distribution")
            st.plotly_chart(fig, width="stretch")
    with right:
        if not trade_df.empty:
            by_asset = trade_df.groupby("asset", as_index=False).agg(edge_score=("edge_score", "mean"), trades=("signal_id", "count"))
            fig = px.bar(by_asset.sort_values("edge_score", ascending=False), x="asset", y="edge_score", hover_data=["trades"], title="Average edge by asset")
            st.plotly_chart(fig, width="stretch")


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
    with c2: metric_card("System agreement", f"{float(latest.get('confidence') or 0):.1f}%", f"Age-adjusted {decayed_confidence_value(latest.get('confidence'), latest.get('created_at'), latest.get('timeframe')):.1f}%")
    with c3: metric_card("RR", f"{float(latest.get('rr') or 0):.2f}R", str(latest.get("status", "")))
    with c4: metric_card("Generated", time_ago(latest.get("created_at")), fmt_nairobi(latest.get("created_at")))

    explain_source = adf.head(5).copy()
    options = explain_source.apply(lambda r: f"{r.get('asset')} · {r.get('timeframe')} · {r.get('signal')} · {r.get('grade')} · {time_ago(r.get('created_at'))} · {r.get('signal_id')}", axis=1).tolist()
    choice = st.selectbox("Explain AI: last 5 generated signals", options)
    sid = choice.split(" · ")[-1]
    row = explain_source[explain_source["signal_id"].astype(str).eq(sid)].iloc[0]
    render_ai_card("Explain AI — signal decision", rich_signal_explanation(row))

    mtf_context = parse_jsonish(row.get("mtf_context"))
    if mtf_context:
        st.subheader("Multi-timeframe confirmation")
        rows = []
        for tf, payload in mtf_context.items():
            if isinstance(payload, dict):
                rows.append({"Timeframe": tf, "Direction": payload.get("direction"), "Strength": payload.get("strength")})
        if rows:
            st.dataframe(pd.DataFrame(rows), width="stretch", hide_index=True)
        st.caption(f"MTF score: {float(row.get('mtf_score') or 0):.0f}%")

    votes = parse_jsonish(row.get("strategy_votes"))
    if votes:
        vote_rows = []
        for name, payload in votes.items():
            if isinstance(payload, dict):
                vote_rows.append({"System": name, "Direction": payload.get("direction"), "Strength": payload.get("strength")})
        st.subheader("Strategy confluence")
        st.dataframe(pd.DataFrame(vote_rows), width="stretch", hide_index=True)

    st.subheader("History for selected asset")
    hist = adf.copy()
    hist["created_at_eat"] = hist["created_at"].apply(fmt_nairobi)
    cols = ["created_at_eat", "timeframe", "signal", "grade", "status", "confidence", "edge_score", "mtf_score", "rr", "r_multiple", "exit_reason", "session"]
    st.dataframe(hist[[c for c in cols if c in hist.columns]].head(100), width="stretch", hide_index=True)


def render_workflow(username: str, settings: dict) -> None:
    page_header("Workflow", "Normal journal, prop-firm mode, NO TRADE tracker, Coach AI, and Explain AI.")
    raw_df = enrich_position_sizing(load_signals_for_user(username, settings), settings)
    df = apply_timeframe_view(raw_df, settings)
    if df.empty:
        st.info("No journal data available yet for this timeframe. Try View performance timeframe = All.")
        return
    df["outcome"] = df.apply(outcome_label, axis=1)
    trades = df[df["grade"].astype(str).isin(VALID_GRADES)].copy()
    no_trades = df[df["grade"].astype(str).eq("NO TRADE")].copy()
    open_trades = trades[trades["status"].astype(str).str.upper().eq("OPEN")]
    closed_trades = trades[trades["outcome"].isin(["WIN", "LOSS", "BREAKEVEN", "CLOSED"])]

    t1, t2, t3, t4, t5 = st.tabs(["Normal Journal", "Prop Firm", "NO TRADE Tracker", "Coach AI", "Explain AI"])

    with t1:
        c1, c2, c3, c4 = st.columns(4)
        win_rate = 0.0
        resolved = closed_trades[closed_trades["outcome"].isin(["WIN", "LOSS"])]
        if len(resolved):
            win_rate = (resolved["outcome"].eq("WIN").mean() * 100)
        with c1: metric_card("Total journaled", f"{len(trades):,}")
        with c2: metric_card("Open", f"{len(open_trades):,}")
        with c3: metric_card("Closed", f"{len(closed_trades):,}")
        with c4: metric_card("Win rate", f"{win_rate:.1f}%", "NO TRADE excluded")

        st.subheader("Account performance")
        render_performance_strip(trades, settings, prop_mode=False)
        st.caption("The figures above use the selected View performance timeframe. Use All to see blended performance.")
        tf_perf = performance_by_timeframe(raw_df[raw_df["grade"].astype(str).isin(VALID_GRADES)].copy(), settings, prop_mode=False)
        if not tf_perf.empty:
            st.markdown("**Performance split by timeframe**")
            st.dataframe(tf_perf, width="stretch", hide_index=True)

        st.subheader("Open trades")
        open_view = add_trade_pnl_columns(open_trades, settings)
        open_cols = ["created_at_eat", "asset", "timeframe", "signal", "grade", "entry", "sl", "tp", "rr", "risk_cash", "potential_tp_cash", "potential_sl_cash", "bars_open", "session"]
        st.dataframe(open_view[[c for c in open_cols if c in open_view.columns]].head(200), width="stretch", hide_index=True)
        st.subheader("Closed trades")
        closed_view = add_trade_pnl_columns(closed_trades, settings)
        closed_cols = ["created_at_eat", "asset", "timeframe", "signal", "grade", "status", "outcome", "r_multiple", "pnl_cash", "balance_after", "exit_reason", "session"]
        st.dataframe(closed_view[[c for c in closed_cols if c in closed_view.columns]].head(200), width="stretch", hide_index=True)
        render_balance_curve(trades, settings, title="Normal journal balance curve")

        if len(resolved):
            a, b, c = st.columns(3)
            with a:
                grade_perf = resolved.groupby("grade", as_index=False).agg(win_rate=("outcome", lambda x: (x == "WIN").mean() * 100), trades=("signal_id", "count"))
                st.dataframe(grade_perf, width="stretch", hide_index=True)
            with b:
                asset_perf = resolved.groupby("asset", as_index=False).agg(win_rate=("outcome", lambda x: (x == "WIN").mean() * 100), trades=("signal_id", "count"))
                st.dataframe(asset_perf.sort_values("trades", ascending=False), width="stretch", hide_index=True)
            with c:
                session_perf = resolved.groupby("session", as_index=False).agg(win_rate=("outcome", lambda x: (x == "WIN").mean() * 100), trades=("signal_id", "count"))
                st.dataframe(session_perf, width="stretch", hide_index=True)

    with t2:
        st.caption("Prop-firm mode uses the same journal but applies stricter FTMO-style rules: only A+/A trades count, 10% target, 5% daily loss guard, 10% max loss guard, and minimum 4 trading days.")
        prop_source = trades[trades["grade"].astype(str).isin(["A+", "A"])].copy()
        render_performance_strip(prop_source, settings, prop_mode=True)
        st.caption("Prop-firm metrics use the selected View performance timeframe by default. Choose All only if you want a blended challenge across styles.")
        prop_tf_perf = performance_by_timeframe(raw_df[raw_df["grade"].astype(str).isin(["A+", "A"])].copy(), settings, prop_mode=True)
        if not prop_tf_perf.empty:
            st.markdown("**Prop-firm performance split by timeframe**")
            st.dataframe(prop_tf_perf, width="stretch", hide_index=True)
        st.subheader("Prop-firm eligible trades")
        if prop_source.empty:
            st.info("No A+/A trades yet for prop-firm mode.")
        else:
            prop_view = add_trade_pnl_columns(prop_source, settings)
            cols = ["created_at_eat", "asset", "timeframe", "signal", "grade", "status", "entry", "sl", "tp", "rr", "r_multiple", "pnl_cash", "balance_after", "exit_reason", "session"]
            st.dataframe(prop_view[[c for c in cols if c in prop_view.columns]].head(300), width="stretch", hide_index=True)
            render_balance_curve(prop_source, settings, title="Prop-firm eligible balance curve")

    with t3:
        st.write("These are blocked ideas. They are useful for research, but excluded from the actual journal win rate.")
        st.dataframe(no_trades[["created_at_eat", "asset", "timeframe", "signal", "grade", "confidence", "edge_score", "rr", "reason", "session"]].head(300), width="stretch", hide_index=True)

    with t4:
        st.subheader("Coach AI")
        if len(closed_trades) < 10:
            render_ai_card("Coach AI — building evidence", f"Coach has **{len(closed_trades)}** closed trades. It will avoid declaring a best asset/session until there is enough evidence. Keep collecting data, but watch open exposure and avoid changing the rules too early.")
        else:
            resolved = closed_trades[closed_trades["outcome"].isin(["WIN", "LOSS"])].copy()
            notes = []
            if not resolved.empty:
                asset_perf = resolved.groupby("asset").agg(win_rate=("outcome", lambda x: (x == "WIN").mean()), trades=("signal_id", "count"), avg_r=("r_multiple", "mean")).reset_index()
                asset_perf = asset_perf[asset_perf["trades"] >= 5].sort_values(["win_rate", "avg_r"], ascending=False)
                if not asset_perf.empty:
                    best = asset_perf.iloc[0]
                    notes.append(f"Your strongest supported asset is **{best['asset']}**: {best['trades']} closed trades, {best['win_rate']*100:.1f}% win rate, average {best['avg_r']:+.2f}R. Treat this as the playbook to repeat, not just a lucky asset.")
                weak = resolved.groupby("asset").agg(win_rate=("outcome", lambda x: (x == "WIN").mean()), trades=("signal_id", "count"), avg_r=("r_multiple", "mean")).reset_index()
                weak = weak[weak["trades"] >= 5].sort_values(["win_rate", "avg_r"], ascending=True)
                if not weak.empty:
                    w = weak.iloc[0]
                    notes.append(f"Your weakest supported area is **{w['asset']}**: {w['trades']} closed trades and {w['win_rate']*100:.1f}% win rate. Reduce size or demand stronger MTF confirmation here until the numbers improve.")
                session_perf = resolved.groupby("session").agg(win_rate=("outcome", lambda x: (x == "WIN").mean()), trades=("signal_id", "count"), avg_r=("r_multiple", "mean")).reset_index()
                session_perf = session_perf[session_perf["trades"] >= 5].sort_values(["win_rate", "avg_r"], ascending=False)
                if not session_perf.empty:
                    srow = session_perf.iloc[0]
                    notes.append(f"Best supported session is **{srow['session']}** with {srow['trades']} closed trades and {srow['win_rate']*100:.1f}% win rate. Prioritise this session when similar grades appear.")
            if len(open_trades) >= 3:
                notes.append("Exposure warning: three or more trades are open. The coach would slow down new entries until at least one trade resolves, especially in prop-firm mode.")
            a_count = len(open_trades[open_trades["grade"].isin(["A+", "A"])])
            b_count = len(open_trades[open_trades["grade"].isin(["B", "C"])])
            notes.append(f"Current open quality mix: **{a_count}** A+/A trade(s) and **{b_count}** B/C trade(s). Prop-firm focus should stay on A+/A only; B/C is research/journal learning fuel.")
            body = "\n\n".join([f"- {n}" for n in notes])
            render_ai_card("Coach AI — trade management guidance", body)

    with t5:
        st.subheader("Explain AI")
        closed_latest = closed_trades.sort_values("created_at", ascending=False).head(5).copy()
        if closed_latest.empty:
            st.info("No closed trades yet. Explain AI will focus on closed outcomes once TP, SL, or expiry appears.")
        else:
            options = closed_latest.apply(lambda r: f"{r.get('asset')} · {r.get('timeframe')} · {r.get('outcome')} · {r.get('grade')} · {fmt_nairobi(r.get('created_at'))} · {r.get('signal_id')}", axis=1).tolist()
            choice = st.selectbox("Choose one of the last 5 closed trades", options)
            sid = choice.split(" · ")[-1]
            row = closed_latest[closed_latest["signal_id"].astype(str).eq(sid)].iloc[0]
            render_ai_card("Explain AI — closed trade lesson", rich_closed_trade_explanation(row))



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
        grouped = {}
        for key, meta in ASSET_UNIVERSE.items():
            grouped.setdefault(meta["group"], []).append(key)
        selected = st.multiselect("Select your watchlist", options=list(ASSET_UNIVERSE.keys()), default=current or DEFAULT_ASSETS)
        if st.button("Save watchlist", type="primary"):
            if not selected:
                st.error("Select at least one asset.")
            else:
                save_user_watchlist(username, selected)
                settings["selected_asset_keys"] = selected
                save_settings(username, settings)
                st.success("Watchlist saved. The scanner will use this for user-specific routing on its next run.")
                st.rerun()
        st.caption("Current watchlist: " + ", ".join(current or DEFAULT_ASSETS))

    with tab_telegram:
        try:
            tg = read_df("SELECT * FROM user_telegram_settings WHERE scan_owner = %s", (username,))
            row = tg.iloc[0].to_dict() if not tg.empty else {}
            active = bool(row.get("alerts_enabled", False))
            st.markdown(f"**Telegram alerts:** {'Active' if active else 'Inactive'}")
            chat_id = st.text_input("Telegram chat ID", value=str(row.get("telegram_chat_id") or settings.get("telegram_chat_ids") or ""))
            current_mode = "All signals" if bool(row.get("all_signals_alerts", False)) else "Watchlist only"
            alert_mode = st.radio("Alert route", ["Watchlist only", "All signals"], index=0 if current_mode == "Watchlist only" else 1, horizontal=True)
            watchlist_alerts = alert_mode == "Watchlist only"
            all_alerts = alert_mode == "All signals"

            col_a, col_b = st.columns(2)
            with col_a:
                activate_clicked = st.button("Activate Settings", type="primary", disabled=active or not bool(str(chat_id).strip()), width="stretch")
            with col_b:
                st.markdown("<div class='danger-button'>", unsafe_allow_html=True)
                deactivate_clicked = st.button("Deactivate alerts", disabled=not active, width="stretch")
                st.markdown("</div>", unsafe_allow_html=True)

            if activate_clicked or deactivate_clicked:
                new_active = bool(activate_clicked)
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
                st.success("Telegram settings activated." if new_active else "Telegram alerts deactivated.")
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
    settings = sidebar_controls(username, settings)

    page_header("Navigation", "Move between system performance, deep dive, workflow and settings.")
    tab_board, tab_deep, tab_workflow, tab_settings = st.tabs(["System Performance", "Asset Deep Dive", "Workflow", "Settings"])
    with tab_board:
        render_opportunity_board(username, settings)
    with tab_deep:
        render_asset_deep_dive(username, settings)
    with tab_workflow:
        render_workflow(username, settings)
    with tab_settings:
        render_settings(username, settings)


if __name__ == "__main__":
    main()
