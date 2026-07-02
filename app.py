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

APP_VERSION = "v7.4-polish-no-trade-prop-expiry"
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

# Prop-firm challenge rules used by the Supabase replay simulator.
CHALLENGE_MIN_TRADING_DAYS = 4
CHALLENGE_PHASE1_TARGET_PCT = 0.10
CHALLENGE_PHASE2_TARGET_PCT = 0.05
CHALLENGE_MAX_DAILY_LOSS_PCT = 0.05
CHALLENGE_MAX_TOTAL_LOSS_PCT = 0.10
PROP_MAX_TRADES_PER_DAY = 4
PROP_MIN_SESSION_TRADES = 20

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
    CREATE TABLE IF NOT EXISTS capital_executed_trades (
        id TEXT PRIMARY KEY,
        deal_id TEXT,
        deal_reference TEXT,
        source_type TEXT,
        environment TEXT,
        epic TEXT,
        asset TEXT,
        instrument_name TEXT,
        direction TEXT,
        status TEXT,
        opened_at TIMESTAMPTZ,
        closed_at TIMESTAMPTZ,
        entry_price NUMERIC,
        exit_price NUMERIC,
        size NUMERIC,
        pnl NUMERIC,
        pnl_ftmo_equiv NUMERIC,
        ftmo_leverage NUMERIC DEFAULT 100,
        capital_leverage NUMERIC,
        ftmo_normalization_factor NUMERIC DEFAULT 1,
        currency TEXT,
        raw_json JSONB,
        updated_at TIMESTAMPTZ DEFAULT NOW()
    );
    CREATE TABLE IF NOT EXISTS capital_trade_comparisons (
        id TEXT PRIMARY KEY,
        capital_trade_id TEXT REFERENCES capital_executed_trades(id),
        signal_id TEXT REFERENCES scanner_signals(signal_id),
        asset TEXT,
        direction TEXT,
        simulated_entry NUMERIC,
        actual_entry NUMERIC,
        entry_diff NUMERIC,
        simulated_exit NUMERIC,
        actual_exit NUMERIC,
        exit_diff NUMERIC,
        simulated_r NUMERIC,
        actual_pnl NUMERIC,
        actual_pnl_ftmo_equiv NUMERIC,
        ftmo_leverage NUMERIC DEFAULT 100,
        capital_leverage NUMERIC,
        ftmo_normalization_factor NUMERIC DEFAULT 1,
        simulated_outcome TEXT,
        actual_status TEXT,
        match_quality TEXT,
        opened_at TIMESTAMPTZ,
        updated_at TIMESTAMPTZ DEFAULT NOW()
    );
    CREATE TABLE IF NOT EXISTS prop_challenge_history (
        id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
        scan_owner TEXT,
        challenge_number INTEGER,
        phase_1_passed BOOLEAN,
        phase_2_passed BOOLEAN,
        status TEXT,
        starting_balance NUMERIC,
        ending_balance NUMERIC,
        realised_pnl NUMERIC,
        win_rate NUMERIC,
        trading_days INTEGER,
        started_at TIMESTAMPTZ,
        finished_at TIMESTAMPTZ,
        failure_reason TEXT,
        created_at TIMESTAMPTZ DEFAULT NOW()
    );
    CREATE TABLE IF NOT EXISTS explain_ai_lessons (
        id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
        signal_id TEXT REFERENCES scanner_signals(signal_id),
        scan_owner TEXT,
        lesson_type TEXT,
        lesson_text TEXT,
        created_at TIMESTAMPTZ DEFAULT NOW(),
        updated_at TIMESTAMPTZ DEFAULT NOW()
    );
    CREATE INDEX IF NOT EXISTS idx_explain_ai_lessons_signal_type
        ON explain_ai_lessons(signal_id, lesson_type, updated_at DESC);
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
                cur.execute("ALTER TABLE scanner_signals ADD COLUMN IF NOT EXISTS trade_notes TEXT")
                cur.execute("ALTER TABLE scanner_signals ADD COLUMN IF NOT EXISTS display_id TEXT")
                cur.execute("ALTER TABLE scanner_signals ADD COLUMN IF NOT EXISTS replay_checked_at TIMESTAMPTZ")
                cur.execute("ALTER TABLE capital_executed_trades ADD COLUMN IF NOT EXISTS raw_json JSONB")
                cur.execute("ALTER TABLE capital_executed_trades ADD COLUMN IF NOT EXISTS environment TEXT")
                cur.execute("ALTER TABLE capital_trade_comparisons ADD COLUMN IF NOT EXISTS match_quality TEXT")
                cur.execute("ALTER TABLE capital_trade_comparisons ADD COLUMN IF NOT EXISTS actual_r NUMERIC")
                cur.execute("ALTER TABLE capital_trade_comparisons ADD COLUMN IF NOT EXISTS auto_trade BOOLEAN DEFAULT FALSE")
                cur.execute("ALTER TABLE capital_trade_comparisons ADD COLUMN IF NOT EXISTS actual_pnl_ftmo_equiv NUMERIC")
                cur.execute("ALTER TABLE capital_trade_comparisons ADD COLUMN IF NOT EXISTS ftmo_leverage NUMERIC DEFAULT 100")
                cur.execute("ALTER TABLE capital_trade_comparisons ADD COLUMN IF NOT EXISTS capital_leverage NUMERIC")
                cur.execute("ALTER TABLE capital_trade_comparisons ADD COLUMN IF NOT EXISTS ftmo_normalization_factor NUMERIC DEFAULT 1")
                cur.execute("ALTER TABLE capital_executed_trades ADD COLUMN IF NOT EXISTS pnl_ftmo_equiv NUMERIC")
                cur.execute("ALTER TABLE capital_executed_trades ADD COLUMN IF NOT EXISTS ftmo_leverage NUMERIC DEFAULT 100")
                cur.execute("ALTER TABLE capital_executed_trades ADD COLUMN IF NOT EXISTS capital_leverage NUMERIC")
                cur.execute("ALTER TABLE capital_executed_trades ADD COLUMN IF NOT EXISTS ftmo_normalization_factor NUMERIC DEFAULT 1")
                cur.execute("ALTER TABLE prop_challenge_history ADD COLUMN IF NOT EXISTS failure_reason TEXT")
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


def load_capital_trade_comparisons(limit: int = 500) -> pd.DataFrame:
    """Actual Capital.com executions matched against simulated BENZINO signals."""
    df = read_df(
        """
        SELECT
            c.opened_at, c.asset, c.direction, c.match_quality,
            c.simulated_entry, c.actual_entry,
            c.simulated_exit, c.actual_exit,
            c.simulated_r, c.actual_r, c.actual_pnl, c.actual_pnl_ftmo_equiv, c.ftmo_normalization_factor, c.simulated_outcome, c.actual_status,
            c.signal_id, c.capital_trade_id, COALESCE(c.auto_trade, FALSE) AS auto_trade,
            ce.instrument_name, ce.environment, ce.status AS execution_status,
            ce.size, ce.currency, ce.updated_at
        FROM capital_trade_comparisons c
        LEFT JOIN capital_executed_trades ce ON ce.id = c.capital_trade_id
        ORDER BY c.opened_at DESC NULLS LAST, c.updated_at DESC
        LIMIT %s
        """,
        (limit,),
    )
    if df.empty:
        return df
    return numeric_cols(df, [
        "simulated_entry", "actual_entry", "simulated_exit",
        "actual_exit", "simulated_r", "actual_r", "actual_pnl", "size"
    ])


def load_capital_executed_trades(limit: int = 500) -> pd.DataFrame:
    """Raw Capital.com execution rows imported by the scanner."""
    df = read_df(
        """
        SELECT opened_at, closed_at, asset, direction, status, source_type, environment,
               epic, instrument_name, entry_price, exit_price, size, pnl, currency, updated_at
        FROM capital_executed_trades
        ORDER BY COALESCE(opened_at, updated_at) DESC NULLS LAST
        LIMIT %s
        """,
        (limit,),
    )
    if df.empty:
        return df
    return numeric_cols(df, ["entry_price", "exit_price", "size", "pnl"])




def prop_challenge_scan_owner(username: str, timeframe: str) -> str:
    """Store prop challenge attempts per user and preferred timeframe."""
    return f"{normalize_username(username)}:{str(timeframe or '1h').lower()}"


def load_prop_challenge_history(username: str, timeframe: str, limit: int = 100) -> pd.DataFrame:
    """Read completed prop-firm challenge attempts from Supabase."""
    scope = prop_challenge_scan_owner(username, timeframe)
    df = read_df(
        """
        SELECT challenge_number, status, phase_1_passed, phase_2_passed,
               starting_balance, ending_balance, realised_pnl, win_rate,
               trading_days, started_at, finished_at, failure_reason, created_at
        FROM prop_challenge_history
        WHERE scan_owner = %s
        ORDER BY COALESCE(challenge_number, 0) DESC, created_at DESC
        LIMIT %s
        """,
        (scope, limit),
    )
    return df


def archive_prop_challenge_attempt(
    username: str,
    timeframe: str,
    *,
    status: str,
    phase_1_passed: bool,
    phase_2_passed: bool,
    starting_balance: float,
    ending_balance: float,
    realised_pnl: float,
    win_rate: float,
    trading_days: int,
    started_at: str,
    finished_at: str,
    failure_reason: str = "",
) -> bool:
    """Persist a completed prop challenge once, then return True if inserted."""
    scope = prop_challenge_scan_owner(username, timeframe)
    status = str(status or "").upper()
    finished_ts = pd.to_datetime(finished_at, errors="coerce", utc=True)
    started_ts = pd.to_datetime(started_at, errors="coerce", utc=True)
    if pd.isna(finished_ts):
        finished_ts = pd.Timestamp.now(tz="UTC")
    if pd.isna(started_ts):
        started_ts = finished_ts

    existing = read_df(
        """
        SELECT id
        FROM prop_challenge_history
        WHERE scan_owner = %s
          AND status = %s
          AND finished_at = %s
        LIMIT 1
        """,
        (scope, status, finished_ts.isoformat()),
    )
    if not existing.empty:
        return False

    seq = read_df(
        "SELECT COALESCE(MAX(challenge_number), 0) + 1 AS next_number FROM prop_challenge_history WHERE scan_owner = %s",
        (scope,),
    )
    challenge_number = 1
    if not seq.empty:
        try:
            challenge_number = int(seq.iloc[0].get("next_number") or 1)
        except Exception:
            challenge_number = 1

    execute(
        """
        INSERT INTO prop_challenge_history(
            scan_owner, challenge_number, phase_1_passed, phase_2_passed, status,
            starting_balance, ending_balance, realised_pnl, win_rate, trading_days,
            started_at, finished_at, failure_reason
        ) VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s)
        """,
        (
            scope,
            challenge_number,
            bool(phase_1_passed),
            bool(phase_2_passed),
            status,
            float(starting_balance),
            float(ending_balance),
            float(realised_pnl),
            float(win_rate),
            int(trading_days or 0),
            started_ts.isoformat(),
            finished_ts.isoformat(),
            str(failure_reason or ""),
        ),
    )

    return True


def rebuild_prop_challenge_history_from_trades(username: str, timeframe: str, histories: list[dict]) -> None:
    """Replace this user's simulated prop-firm history for the timeframe with a clean replay."""
    scope = prop_challenge_scan_owner(username, timeframe)
    try:
        execute("DELETE FROM prop_challenge_history WHERE scan_owner = %s", (scope,))
    except Exception:
        return
    for idx, h in enumerate(histories, start=1):
        try:
            execute(
                """
                INSERT INTO prop_challenge_history(
                    scan_owner, challenge_number, phase_1_passed, phase_2_passed, status,
                    starting_balance, ending_balance, realised_pnl, win_rate, trading_days,
                    started_at, finished_at, failure_reason
                ) VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s)
                """,
                (
                    scope,
                    idx,
                    bool(h.get("phase_1_passed", False)),
                    bool(h.get("phase_2_passed", False)),
                    str(h.get("status", "")).upper(),
                    float(h.get("starting_balance", 10000.0)),
                    float(h.get("ending_balance", 10000.0)),
                    float(h.get("realised_pnl", 0.0)),
                    float(h.get("win_rate", 0.0)),
                    int(h.get("trading_days", 0) or 0),
                    pd.to_datetime(h.get("started_at"), errors="coerce", utc=True).isoformat(),
                    pd.to_datetime(h.get("finished_at"), errors="coerce", utc=True).isoformat(),
                    str(h.get("failure_reason", "") or ""),
                ),
            )
        except Exception:
            continue



def prop_session_from_timestamp(ts) -> str:
    """Trading-session label in Nairobi display time.

    This is intentionally simple and stable:
      Asia:     00:00–07:59 EAT
      London:   08:00–15:59 EAT
      New York: 16:00–23:59 EAT
    """
    try:
        hour = pd.to_datetime(ts, utc=True).tz_convert(NAIROBI_TZ).hour
    except Exception:
        return "Unknown"
    if 0 <= hour < 8:
        return "Asia"
    if 8 <= hour < 16:
        return "London"
    return "New York"


def prop_best_session_profile(df: pd.DataFrame, min_trades: int = PROP_MIN_SESSION_TRADES) -> dict:
    """Find the user's dynamic best prop session from closed A/A+ trades only."""
    if df is None or df.empty:
        return {"best_session": "All sessions", "profit_factor": 0.0, "win_rate": 0.0, "trade_count": 0, "sample_ready": False}
    work = df.copy()
    if "prop_event_time" not in work.columns:
        event_time = pd.to_datetime(work.get("exit_at", pd.Series(pd.NaT, index=work.index)), errors="coerce", utc=True)
        created_time = pd.to_datetime(work.get("created_at", pd.Series(pd.NaT, index=work.index)), errors="coerce", utc=True)
        work["prop_event_time"] = event_time.fillna(created_time)
    work = work.dropna(subset=["prop_event_time"]).copy()
    work["r_multiple"] = pd.to_numeric(work.get("r_multiple", 0), errors="coerce").fillna(0.0)
    work["prop_session"] = work["prop_event_time"].apply(prop_session_from_timestamp)
    rows = []
    for session, g in work.groupby("prop_session"):
        if session == "Unknown":
            continue
        wins = g[g["r_multiple"] > 0]
        losses = g[g["r_multiple"] < 0]
        gross_profit = float(wins["r_multiple"].sum()) if not wins.empty else 0.0
        gross_loss = abs(float(losses["r_multiple"].sum())) if not losses.empty else 0.0
        pf = gross_profit / gross_loss if gross_loss > 0 else (gross_profit if gross_profit > 0 else 0.0)
        wr = float((g["r_multiple"] > 0).mean() * 100) if len(g) else 0.0
        net = float(g["r_multiple"].sum())
        rows.append({"best_session": session, "profit_factor": pf, "win_rate": wr, "net_r": net, "trade_count": int(len(g)), "sample_ready": len(g) >= min_trades})
    if not rows:
        return {"best_session": "All sessions", "profit_factor": 0.0, "win_rate": 0.0, "trade_count": 0, "sample_ready": False}
    eligible = [r for r in rows if r["sample_ready"]]
    ranked = sorted(eligible or rows, key=lambda r: (r["profit_factor"], r["win_rate"], r["net_r"], r["trade_count"]), reverse=True)
    out = ranked[0]
    out["all_sessions"] = rows
    return out


def apply_prop_best_session_trade_filter(df: pd.DataFrame, profile: dict) -> tuple[pd.DataFrame, pd.DataFrame]:
    """Apply Prop Firm v2: best session only, max 4 trades/day.

    If no session has the minimum sample yet, the profile is marked not ready
    and we do not restrict by session. We still apply the 4-trades/day cap.
    """
    if df is None or df.empty:
        return pd.DataFrame(), pd.DataFrame()
    work = df.copy().sort_values("prop_event_time").reset_index(drop=True)
    work["prop_session"] = work["prop_event_time"].apply(prop_session_from_timestamp)
    work["prop_day_all"] = work["prop_event_time"].apply(lambda ts: pd.Timestamp(ts).tz_convert(NAIROBI_TZ).date())
    best = str(profile.get("best_session") or "All sessions")
    sample_ready = bool(profile.get("sample_ready"))
    skipped_parts = []
    eligible = work.copy()
    if sample_ready and best not in {"", "All sessions"}:
        outside = eligible[eligible["prop_session"] != best].copy()
        if not outside.empty:
            outside["prop_skip_reason"] = "Skipped — outside best session"
            skipped_parts.append(outside)
        eligible = eligible[eligible["prop_session"] == best].copy()
    eligible["_daily_rank"] = eligible.groupby("prop_day_all").cumcount() + 1
    taken = eligible[eligible["_daily_rank"] <= PROP_MAX_TRADES_PER_DAY].copy()
    capped = eligible[eligible["_daily_rank"] > PROP_MAX_TRADES_PER_DAY].copy()
    if not capped.empty:
        capped["prop_skip_reason"] = "Skipped — daily trade cap reached"
        skipped_parts.append(capped)
    skipped = pd.concat(skipped_parts, ignore_index=True) if skipped_parts else pd.DataFrame()
    return taken.drop(columns=[c for c in ["_daily_rank", "prop_day_all"] if c in taken.columns]), skipped

def simulate_prop_challenge_cycles(prop_closed_all: pd.DataFrame, activated_at: str = "", starting: float = 10000.0) -> dict:
    """Replay scoped A+/A closed trades using the exact FTMO 2-step model.

    Model used:
      • Phase 1 starts from a fresh $10,000 account and passes at $11,000 only
        after at least 4 distinct trading days have been completed.
      • Phase 2 starts from a fresh $10,000 verification account after Phase 1
        passes and passes at $10,500 only after at least 4 distinct trading days.
      • Max total loss is anchored to the original account size: equity must not
        fall below $9,000 in either phase.
      • Max daily loss is anchored to the balance at the start of that trading
        day: equity must not fall below day-open balance minus $500.

    Completed cycles are rebuilt from Supabase every run. The active object is
    the current unfinished phase after all completed passes/fails have been
    consumed. No old prop_firm_state balance is trusted here.
    """
    risk_cash = float(starting) * 0.01
    daily_loss_limit_cash = float(starting) * CHALLENGE_MAX_DAILY_LOSS_PCT
    max_loss_floor = float(starting) * (1.0 - CHALLENGE_MAX_TOTAL_LOSS_PCT)
    targets = {
        1: float(starting) * (1.0 + CHALLENGE_PHASE1_TARGET_PCT),
        2: float(starting) * (1.0 + CHALLENGE_PHASE2_TARGET_PCT),
    }

    empty_active = {
        "phase": "Phase 1 Challenge",
        "phase_number": 1,
        "status": "ACTIVE",
        "start_at": pd.to_datetime(activated_at, errors="coerce", utc=True),
        "equity": float(starting),
        "pnl": 0.0,
        "roi_pct": 0.0,
        "progress": 0.0,
        "trading_days": 0,
        "closed_count": 0,
        "open_count": 0,
        "worst_day_pnl": 0.0,
        "best_day_pnl": 0.0,
        "last_closed_at": "",
        "max_drawdown_cash": 0.0,
        "max_drawdown_pct": 0.0,
        "fail_reason": "",
        "pass_date": "",
        "phase1_passed_at": "",
    }

    if prop_closed_all is None or prop_closed_all.empty:
        return {"history": [], "active": empty_active, "active_curve": pd.DataFrame(), "active_daily": pd.DataFrame(), "all_daily": pd.DataFrame(), "all_trades": pd.DataFrame(), "skipped_trades": pd.DataFrame(), "best_session": {"best_session":"All sessions","profit_factor":0.0,"win_rate":0.0,"trade_count":0,"sample_ready":False}}

    df = prop_closed_all.copy()
    df = numeric_cols(df, ["r_multiple", "entry", "sl", "tp", "rr"])
    event_time = pd.to_datetime(df.get("exit_at", pd.Series(pd.NaT, index=df.index)), errors="coerce", utc=True)
    created_time = pd.to_datetime(df.get("created_at", pd.Series(pd.NaT, index=df.index)), errors="coerce", utc=True)
    df["prop_event_time"] = event_time.fillna(created_time)
    df = df.dropna(subset=["prop_event_time"]).sort_values("prop_event_time").reset_index(drop=True)

    act_ts = pd.to_datetime(activated_at, errors="coerce", utc=True)
    if pd.notna(act_ts):
        df = df[df["prop_event_time"] >= act_ts].copy().reset_index(drop=True)
    if df.empty:
        return {"history": [], "active": empty_active, "active_curve": pd.DataFrame(), "active_daily": pd.DataFrame(), "all_daily": pd.DataFrame(), "all_trades": pd.DataFrame(), "skipped_trades": pd.DataFrame(), "best_session": {"best_session":"All sessions","profit_factor":0.0,"win_rate":0.0,"trade_count":0,"sample_ready":False}}

    df["pnl_cash"] = pd.to_numeric(df["r_multiple"], errors="coerce").fillna(0.0) * risk_cash

    best_session_profile = prop_best_session_profile(df, PROP_MIN_SESSION_TRADES)
    skipped_prop_trades = pd.DataFrame()
    df, skipped_prop_trades = apply_prop_best_session_trade_filter(df, best_session_profile)
    if df.empty:
        return {"history": [], "active": empty_active, "active_curve": pd.DataFrame(), "active_daily": pd.DataFrame(), "all_daily": pd.DataFrame(), "all_trades": pd.DataFrame(), "skipped_trades": skipped_prop_trades, "best_session": best_session_profile}

    histories: list[dict] = []
    all_replay_rows: list[dict] = []
    challenge_no = 1

    phase = 1
    cycle_start_ts = act_ts if pd.notna(act_ts) else df["prop_event_time"].iloc[0]
    phase_start_ts = cycle_start_ts
    phase_balance = float(starting)
    phase_rows: list[dict] = []
    phase_days: set = set()
    phase_day_open: dict = {}
    phase_day_min_equity: dict = {}
    phase_day_pnl: dict = {}
    cycle_rows: list[dict] = []
    phase1_passed_at = ""
    phase1_passed = False

    def _day_from_ts(ts):
        try:
            return pd.Timestamp(ts).tz_convert(NAIROBI_TZ).date()
        except Exception:
            return pd.Timestamp(ts, tz="UTC").tz_convert(NAIROBI_TZ).date()

    def _phase_stats(rows: list[dict]) -> dict:
        if not rows:
            return {
                "days": 0,
                "worst_day_pnl": 0.0,
                "best_day_pnl": 0.0,
                "max_drawdown_cash": 0.0,
                "max_drawdown_pct": 0.0,
                "last_closed_at": "",
            }
        tmp = pd.DataFrame(rows)
        day_pnl = tmp.groupby("prop_day")["pnl_cash"].sum() if "prop_day" in tmp.columns else pd.Series(dtype=float)
        bal = pd.to_numeric(tmp["balance_after"], errors="coerce") if "balance_after" in tmp.columns else pd.Series(dtype=float)
        peak = bal.cummax() if len(bal) else pd.Series(dtype=float)
        dd = bal - peak if len(bal) else pd.Series(dtype=float)
        dd_pct = ((dd / peak.replace(0, np.nan)) * 100).replace([np.inf, -np.inf], np.nan) if len(dd) else pd.Series(dtype=float)
        return {
            "days": int(day_pnl.index.nunique()) if len(day_pnl) else 0,
            "worst_day_pnl": float(day_pnl.min()) if len(day_pnl) else 0.0,
            "best_day_pnl": float(day_pnl.max()) if len(day_pnl) else 0.0,
            "max_drawdown_cash": float(dd.min()) if len(dd) else 0.0,
            "max_drawdown_pct": float(dd_pct.min()) if len(dd_pct.dropna()) else 0.0,
            "last_closed_at": tmp["prop_event_time"].max() if "prop_event_time" in tmp.columns and not tmp.empty else "",
        }

    def _win_rate(rows: list[dict]) -> float:
        if not rows:
            return 0.0
        return win_rate_from_resolved(pd.DataFrame(rows))

    def _archive(status: str, finished_ts, failure_reason: str, terminal_balance: float, terminal_phase: int):
        nonlocal phase, cycle_start_ts, phase_start_ts, phase_balance, phase_rows, phase_days
        nonlocal phase_day_open, phase_day_min_equity, phase_day_pnl, cycle_rows
        nonlocal phase1_passed_at, phase1_passed, challenge_no

        histories.append({
            "challenge_number": int(challenge_no),
            "status": str(status).upper(),
            "phase_1_passed": bool(phase1_passed or str(status).upper() == "PASSED"),
            "phase_2_passed": bool(str(status).upper() == "PASSED"),
            "starting_balance": float(starting),
            "ending_balance": float(terminal_balance),
            "realised_pnl": float(terminal_balance) - float(starting),
            "win_rate": _win_rate(cycle_rows),
            # This is the number of trading days in the terminal phase, because
            # that is the phase whose account/balance is displayed on this row.
            "trading_days": len(set([r.get("prop_day") for r in phase_rows if r.get("prop_day") is not None])),
            "started_at": cycle_start_ts,
            "finished_at": finished_ts,
            "failure_reason": str(failure_reason or ""),
        })

        phase = 1
        phase1_passed = False
        phase1_passed_at = ""
        phase_balance = float(starting)
        phase_rows = []
        phase_days = set()
        phase_day_open = {}
        phase_day_min_equity = {}
        phase_day_pnl = {}
        cycle_rows = []
        challenge_no += 1
        cycle_start_ts = pd.Timestamp(finished_ts) + pd.Timedelta(seconds=1)
        phase_start_ts = cycle_start_ts

    for _, row in df.iterrows():
        ts = row["prop_event_time"]
        if ts < phase_start_ts:
            continue

        day = _day_from_ts(ts)
        if day not in phase_day_open:
            # FTMO daily loss is measured from the balance at the start of the
            # trading day, not from the total account start and not from daily
            # net P/L alone.
            phase_day_open[day] = float(phase_balance)
            phase_day_min_equity[day] = float(phase_balance)
            phase_day_pnl[day] = 0.0

        pnl = float(row.get("pnl_cash") or 0.0)
        phase_balance += pnl
        phase_day_pnl[day] = phase_day_pnl.get(day, 0.0) + pnl
        phase_day_min_equity[day] = min(float(phase_day_min_equity.get(day, phase_balance)), float(phase_balance))
        phase_days.add(day)

        row_dict = row.to_dict()
        row_dict["challenge_number"] = int(challenge_no)
        row_dict["balance_after"] = float(phase_balance)
        row_dict["prop_day"] = day
        row_dict["challenge_phase"] = f"Phase {phase}"
        row_dict["day_open_balance"] = float(phase_day_open[day])
        row_dict["daily_loss_floor"] = float(phase_day_open[day]) - daily_loss_limit_cash
        row_dict["phase_target"] = targets[phase]
        row_dict["prop_session"] = prop_session_from_timestamp(ts)
        row_dict["prop_selection"] = "Taken"
        phase_rows.append(row_dict)
        cycle_rows.append(row_dict)
        all_replay_rows.append(row_dict.copy())

        terminal = ""
        reason = ""
        if phase_balance < max_loss_floor:
            terminal = "FAILED"
            reason = f"Phase {phase}: 10% max total loss breached"
        elif phase_balance < (float(phase_day_open[day]) - daily_loss_limit_cash):
            terminal = "FAILED"
            reason = f"Phase {phase}: 5% max daily loss breached"
        elif phase_balance >= targets[phase] and len(phase_days) >= CHALLENGE_MIN_TRADING_DAYS:
            if phase == 1:
                # Phase 1 is complete. FTMO Verification starts from a fresh
                # $10,000 account on the next eligible trade.
                phase1_passed = True
                phase1_passed_at = ts
                phase = 2
                phase_balance = float(starting)
                phase_rows = []
                phase_days = set()
                phase_day_open = {}
                phase_day_min_equity = {}
                phase_day_pnl = {}
                phase_start_ts = pd.Timestamp(ts) + pd.Timedelta(seconds=1)
                continue
            terminal = "PASSED"

        if terminal:
            _archive(terminal, ts, reason, phase_balance, phase)

    active_curve = pd.DataFrame(phase_rows)
    active_daily = pd.DataFrame()
    if not active_curve.empty:
        active_daily = active_curve.groupby("prop_day").agg(
            **{
                "Daily P/L": ("pnl_cash", "sum"),
                "Trades": ("pnl_cash", "count"),
                "Opening Balance": ("day_open_balance", "first"),
                "Closing Balance": ("balance_after", "last"),
                "Intraday Low": ("balance_after", "min"),
                "Daily Loss Floor": ("daily_loss_floor", "first"),
            }
        ).reset_index().rename(columns={"prop_day": "Day"})
        active_daily = active_daily.sort_values("Day")
        active_daily["Day Result"] = active_daily["Daily P/L"].apply(lambda x: "WIN" if float(x) > 0 else "LOSS" if float(x) < 0 else "BREAKEVEN")
        active_daily["Daily Breach"] = active_daily.apply(lambda r: "YES" if float(r["Intraday Low"]) < float(r["Daily Loss Floor"]) else "NO", axis=1)
        active_daily["Target Hit"] = active_daily["Closing Balance"].apply(lambda x: "YES" if float(x) >= targets[phase] else "NO")

    stats = _phase_stats(phase_rows)
    equity = float(active_curve["balance_after"].iloc[-1]) if not active_curve.empty else float(starting)
    target_profit = targets[phase] - float(starting)
    active = {
        "phase": "Phase 1 Challenge" if phase == 1 else "Phase 2 Verification",
        "phase_number": phase,
        "status": "ACTIVE",
        "start_at": phase_start_ts,
        "equity": equity,
        "pnl": equity - float(starting),
        "roi_pct": ((equity - float(starting)) / float(starting) * 100) if starting else 0.0,
        "progress": max(0.0, min(1.0, (equity - float(starting)) / target_profit)) if target_profit else 0.0,
        "trading_days": len(phase_days),
        "closed_count": len(active_curve),
        "open_count": 0,
        "worst_day_pnl": stats["worst_day_pnl"],
        "best_day_pnl": stats["best_day_pnl"],
        "last_closed_at": stats["last_closed_at"],
        "max_drawdown_cash": stats["max_drawdown_cash"],
        "max_drawdown_pct": stats["max_drawdown_pct"],
        "fail_reason": "",
        "pass_date": "",
        "phase1_passed_at": phase1_passed_at,
    }

    all_trades = pd.DataFrame(all_replay_rows)
    all_daily = pd.DataFrame()
    if not all_trades.empty:
        all_daily = all_trades.groupby(["challenge_number", "challenge_phase", "prop_day"]).agg(
            **{
                "Daily P/L": ("pnl_cash", "sum"),
                "Trades": ("pnl_cash", "count"),
                "Opening Balance": ("day_open_balance", "first"),
                "Closing Balance": ("balance_after", "last"),
                "Intraday Low": ("balance_after", "min"),
                "Daily Loss Floor": ("daily_loss_floor", "first"),
                "Phase Target": ("phase_target", "first"),
            }
        ).reset_index().rename(columns={"challenge_number": "Challenge", "challenge_phase": "Phase", "prop_day": "Day"})
        all_daily["_challenge_order"] = pd.to_numeric(all_daily["Challenge"], errors="coerce").fillna(0).astype(int)
        all_daily["_phase_order"] = all_daily["Phase"].astype(str).str.extract(r"(\d+)")[0].fillna("0").astype(int)
        all_daily["Challenge"] = all_daily["Challenge"].apply(lambda x: f"#{int(x)}" if pd.notna(x) else "—")
        all_daily["Day Result"] = all_daily["Daily P/L"].apply(lambda x: "WIN" if float(x) > 0 else "LOSS" if float(x) < 0 else "BREAKEVEN")
        all_daily["Daily Breach"] = all_daily.apply(lambda r: "YES" if float(r["Intraday Low"]) < float(r["Daily Loss Floor"]) else "NO", axis=1)
        all_daily["Target Hit"] = all_daily.apply(lambda r: "YES" if float(r["Closing Balance"]) >= float(r["Phase Target"]) else "NO", axis=1)
        # Latest challenge first, latest day first, then latest phase first.
        # This keeps Phase 2 above Phase 1 inside the same challenge/day because
        # Phase 2 can only happen after Phase 1 in the replay sequence.
        all_daily = all_daily.sort_values(["_challenge_order", "Day", "_phase_order"], ascending=[False, False, False]).drop(columns=["_challenge_order", "_phase_order"])
    return {"history": histories, "active": active, "active_curve": active_curve, "active_daily": active_daily, "all_daily": all_daily, "all_trades": all_trades, "skipped_trades": skipped_prop_trades, "best_session": best_session_profile}

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
            if trades_today >= PROP_MAX_TRADES_PER_DAY:
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
    """Load the logged-in user's journal rows from Supabase.

    Important: filter by the user's watchlist inside SQL BEFORE applying LIMIT.
    The previous version loaded the latest 5,000 scanner rows from the whole
    system first, then filtered the user watchlist in pandas. As the full
    master scanner universe grew, older user trades could fall outside that
    global 5,000-row window even though they still belonged in the user
    journal. That made totals, wins, balance, and realised PnL appear to move
    backwards.
    """
    tracking_started = settings.get("tracking_started_at") or "1970-01-01T00:00:00Z"
    params: list = [tracking_started]
    where = ["created_at >= %s"]

    if not include_all_admin:
        watchlist_assets = sorted(set(load_user_watchlist(username).keys()))
        if watchlist_assets:
            where.append("asset = ANY(%s)")
            params.append(watchlist_assets)

    # This limit is now applied AFTER the user/watchlist filter, not before it.
    # 50k is intentionally high so journal history remains stable while still
    # preventing accidental unbounded reads on very large databases.
    params.append(50000)
    sql = f"""
        SELECT * FROM scanner_signals
        WHERE {' AND '.join(where)}
        ORDER BY created_at DESC
        LIMIT %s
        """
    df = read_df(sql, tuple(params))
    if df.empty:
        return df
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



def resolved_outcome_masks(df: pd.DataFrame) -> tuple[pd.Series, pd.Series, pd.Series, pd.Series]:
    """Resolved outcome masks for win-rate calculations.

    Win-rate denominator includes:
    CLOSED_TP, CLOSED_SL, EXPIRED_WIN, EXPIRED_LOSS, BREAKEVEN and EXPIRED_BREAKEVEN.
    Generic CLOSED/EXPIRED rows are classified using r_multiple where available.
    """
    if df is None or df.empty:
        empty = pd.Series([], dtype=bool)
        return empty, empty, empty, empty

    status = df.get("status", pd.Series("", index=df.index)).astype(str).str.upper()
    outcome = df.get("outcome", pd.Series("", index=df.index)).astype(str).str.upper()
    r = pd.to_numeric(df.get("r_multiple", pd.Series(np.nan, index=df.index)), errors="coerce")

    wins = (
        status.isin(["CLOSED_TP", "EXPIRED_WIN"])
        | outcome.isin(["WIN", "EXPIRED_WIN"])
        | ((status.str.contains("TP", na=False) | status.str.contains("WIN", na=False)) & ~status.str.contains("SHADOW", na=False))
    )

    losses = (
        status.isin(["CLOSED_SL", "EXPIRED_LOSS"])
        | outcome.isin(["LOSS", "EXPIRED_LOSS"])
        | ((status.str.contains("SL", na=False) | status.str.contains("LOSS", na=False)) & ~status.str.contains("SHADOW", na=False))
    )

    breakevens = (
        status.isin(["BREAKEVEN", "EXPIRED_BREAKEVEN", "CLOSED_BE"])
        | outcome.isin(["BREAKEVEN", "EXPIRED_BREAKEVEN"])
    )

    generic_resolved = (
        (status.str.contains("EXPIRED", na=False) | status.eq("CLOSED"))
        & ~(wins | losses | breakevens)
        & r.notna()
    )
    wins = wins | (generic_resolved & (r > 0))
    losses = losses | (generic_resolved & (r < 0))
    breakevens = breakevens | (generic_resolved & (r == 0))

    resolved = wins | losses | breakevens
    return wins, losses, breakevens, resolved


def win_rate_from_resolved(df: pd.DataFrame) -> float:
    """Win rate = wins / resolved outcomes, including expired wins/losses."""
    if df is None or df.empty:
        return 0.0
    wins, losses, breakevens, resolved = resolved_outcome_masks(df)
    total = int(resolved.sum())
    return float(wins.sum() / total * 100) if total else 0.0


def win_rate_group(group: pd.DataFrame) -> float:
    """Groupby-safe win rate using the same app-wide resolved outcome logic."""
    return win_rate_from_resolved(group)


def closed_resolved_trades(df: pd.DataFrame) -> pd.DataFrame:
    """Return rows that count as resolved for performance/win-rate analysis."""
    if df is None or df.empty:
        return pd.DataFrame()
    wins, losses, breakevens, resolved = resolved_outcome_masks(df)
    return df.loc[resolved].copy()



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
        out["win_rate"] = win_rate_from_resolved(closed)
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

    wins, losses, breakevens, resolved = resolved_outcome_masks(closed)
    out["total_trades"] = int(resolved.sum())
    out["winning_trades"] = int(wins.sum())
    out["losing_trades"] = int(losses.sum())
    out["win_rate"] = win_rate_from_resolved(closed)

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


def render_balance_curve(df: pd.DataFrame, settings: dict, title: str = "Balance curve", split_by_grade: bool = False, include_overall: bool = False) -> None:
    """Render realised balance curve from closed trades when evidence exists.

    When split_by_grade=True, the chart shows separate hypothetical equity
    curves for A+/A, B, and C trades. Each curve starts from the same user
    account size and only compounds the trades in that grade bucket, making it
    clear which quality tier is helping or hurting the journal.
    """
    if df is None or df.empty:
        return
    view = add_trade_pnl_columns(df.copy(), settings)
    status = view.get("status", pd.Series(dtype=str)).astype(str).str.upper()
    closed = view[status.str.contains("CLOSED|EXPIRED|TP|SL", na=False)].copy()
    if closed.empty:
        return
    closed = closed.sort_values("created_at")

    if split_by_grade and "grade" in closed.columns:
        account = float(settings.get("account_size", 10000) or 10000)
        grade = closed["grade"].astype(str).str.upper().str.strip()
        closed["Grade Group"] = np.select(
            [grade.isin(["A+", "A"]), grade.eq("B"), grade.eq("C")],
            ["A+/A only", "B only", "C only"],
            default="Other",
        )
        closed = closed[closed["Grade Group"].isin(["A+/A only", "B only", "C only"])].copy()
        if closed.empty:
            return
        pieces = []
        if include_overall:
            overall = closed.sort_values("created_at").copy()
            overall["Grade Group"] = "All trades"
            overall["grade_balance_after"] = account + pd.to_numeric(overall["pnl_cash"], errors="coerce").fillna(0.0).cumsum()
            pieces.append(overall)
        for group_name, group_df in closed.groupby("Grade Group", sort=False):
            group_df = group_df.sort_values("created_at").copy()
            group_df["grade_balance_after"] = account + pd.to_numeric(group_df["pnl_cash"], errors="coerce").fillna(0.0).cumsum()
            pieces.append(group_df)
        chart_df = pd.concat(pieces, ignore_index=True) if pieces else pd.DataFrame()
        if chart_df.empty:
            return
        fig = px.line(chart_df, x="created_at", y="grade_balance_after", color="Grade Group", title=title)
        fig.update_layout(yaxis_title="Balance after", xaxis_title="created_at", height=380, margin=dict(l=20, r=20, t=20, b=35))
    else:
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
    """Build a proper closed-trade lesson, not a bullet summary.

    This stays deterministic for now: it explains and stores the lesson, but it
    does not fine-tune scanner weights. The adaptive layer will come later.
    """
    asset = str(row.get("asset", "")).upper()
    tf = str(row.get("timeframe", ""))
    signal = str(row.get("signal", "")).upper()
    grade = str(row.get("grade", ""))
    outcome = outcome_label(row)
    r_mult = float(pd.to_numeric(row.get("r_multiple"), errors="coerce") or 0)
    exit_reason = str(row.get("exit_reason", "") or "recorded close")
    reason = str(row.get("reason", "") or "No original reason was stored.")
    regime = str(row.get("regime", "") or "unknown regime")
    rsi = float(pd.to_numeric(row.get("rsi"), errors="coerce") or 0)
    rr = float(pd.to_numeric(row.get("rr"), errors="coerce") or 0)
    ml_prob = float(pd.to_numeric(row.get("ml_prob"), errors="coerce") or 0)
    mtf_score = float(pd.to_numeric(row.get("mtf_score"), errors="coerce") or 0)
    votes = parse_jsonish(row.get("strategy_votes"))
    mtf = parse_jsonish(row.get("mtf_context"))
    trade_note = str(row.get("trade_notes") or "").strip()

    vote_text = format_votes(votes)
    mtf_bits = []
    if isinstance(mtf, dict):
        for k, v in mtf.items():
            if isinstance(v, dict):
                mtf_bits.append(f"{k}: {v.get('direction', 'NEUTRAL')} ({float(v.get('strength') or 0):.2f})")
    mtf_text = "; ".join(mtf_bits) if mtf_bits else "No detailed multi-timeframe breakdown was stored for this trade."

    stretched = rsi >= 75 if signal == "BUY" else rsi <= 25
    exhaustion_sentence = ""
    if stretched:
        exhaustion_sentence = (
            f" One warning sign was the RSI reading of {rsi:.1f}. For a {signal} setup this suggests the move may already have been extended, "
            "so confirmation needed to be balanced against the risk of entering late in the impulse."
        )
    elif rsi:
        exhaustion_sentence = f" The RSI reading of {rsi:.1f} did not, by itself, show an extreme exhaustion condition."

    if outcome == "WIN":
        outcome_lesson = (
            f"The result confirms that the original confluence translated into follow-through. A {r_mult:+.2f}R close means the trade did more than look good at entry; "
            "it also survived live market movement and reached the intended reward side of the plan. The lesson is not simply that this asset won. "
            "The more useful lesson is to identify the conditions that made the win repeatable: the grade quality, the timeframe agreement, the market regime, "
            "and the strategy votes that were present before entry."
        )
        playbook = (
            "For the playbook, this trade should strengthen confidence in similar setups only when the same ingredients are present again. "
            "A future trade should not be upgraded just because the asset name matches; it should be upgraded only if the structure, regime, confirmation, and risk-reward profile resemble this winning case."
        )
    elif outcome == "LOSS":
        outcome_lesson = (
            f"The trade closed as a loss at {r_mult:+.2f}R, so the key lesson is about the difference between a valid setup and a well-timed setup. "
            "The entry may have satisfied the engine's confluence rules, but the market did not give enough continuation before invalidating the idea. "
            "That makes this a timing and filtering lesson rather than a reason to discard the entire strategy."
        )
        playbook = (
            "For the playbook, one loss should not rewrite the strategy. However, if future losses cluster around the same conditions — the same asset, timeframe, regime, extreme RSI area, weak volatility expansion, or similar strategy-vote mix — "
            "then this pattern should become a filter when the adaptive learning layer is built. Until then, this lesson should be treated as evidence to review, not an automatic rule change."
        )
    else:
        outcome_lesson = (
            f"This trade did not produce a clean win-or-loss lesson because it closed through {exit_reason}. The most useful review is therefore about opportunity cost and timing. "
            "When a setup cannot reach either side of the plan within its expected life, the engine should ask whether the signal had enough volatility, urgency, and follow-through potential at entry."
        )
        playbook = (
            "For the playbook, expiry-style outcomes should be used to study slow trades. A setup that repeatedly stalls may still be directionally reasonable, but it may need a better entry trigger, a different timeframe, or a stricter volatility requirement."
        )

    note_section = ""
    if trade_note:
        note_section = (
            f"\n\n**Trader context**\n\nYou added the following note: _{trade_note}_. Explain AI should treat this as important context rather than noise. "
            "If the note points to a news spike, abnormal liquidity event, manual override, or broker-specific price move, then the lesson should not be blamed entirely on the strategy logic. "
            "Those events belong in the execution and risk-management review, especially around whether the trade should have been avoided during high-impact conditions."
        )

    return (
        f"**{asset} · {tf} · {signal} · Grade {grade}**\n\n"
        f"This trade closed via **{exit_reason}** with a final result of **{r_mult:+.2f}R**. At entry, the engine accepted the setup because: {reason} "
        f"The planned reward-to-risk was **{rr:.2f}R**, the stored market regime was **{regime}**, multi-timeframe alignment was **{mtf_score:.0f}%**, and ML probability was **{ml_prob:.2f}**."
        f"{exhaustion_sentence}\n\n"
        f"**Why the trade made sense at the time**\n\n"
        f"The setup was not random. It came from the engine finding enough evidence to justify a {grade} grade: {vote_text}. "
        f"The multi-timeframe picture was: {mtf_text}. That means the lesson should begin from the quality of the decision at entry, not only from the final result.\n\n"
        f"**Why the trade closed the way it did**\n\n"
        f"{outcome_lesson}\n\n"
        f"**What the playbook should learn**\n\n"
        f"{playbook}\n\n"
        f"**What would improve the next version of this setup**\n\n"
        f"A stronger future version would need cleaner confirmation at the moment of entry: less evidence of exhaustion, clearer volatility expansion, stronger higher-timeframe support, or a pullback that improves risk placement before the trade is triggered. "
        f"This is exactly the kind of closed-outcome evidence that will later feed the adaptive learning layer, but for now it is stored as an Explain AI lesson rather than used to change scanner behaviour automatically."
        f"{note_section}"
    )


def save_explain_ai_lesson(signal_id: str, scan_owner: str, lesson_text: str, lesson_type: str = "CLOSED_TRADE") -> None:
    signal_id = str(signal_id or "").strip()
    scan_owner = str(scan_owner or "").strip()
    lesson_text = str(lesson_text or "").strip()
    if not signal_id or not lesson_text:
        return
    existing = read_df(
        """
        SELECT id
        FROM explain_ai_lessons
        WHERE signal_id = %s AND lesson_type = %s
        ORDER BY updated_at DESC NULLS LAST, created_at DESC NULLS LAST
        LIMIT 1
        """,
        (signal_id, lesson_type),
    )
    if existing.empty:
        execute(
            """
            INSERT INTO explain_ai_lessons(signal_id, scan_owner, lesson_type, lesson_text, created_at, updated_at)
            VALUES (%s,%s,%s,%s,NOW(),NOW())
            """,
            (signal_id, scan_owner, lesson_type, lesson_text),
        )
    else:
        execute(
            """
            UPDATE explain_ai_lessons
            SET scan_owner = %s, lesson_text = %s, updated_at = NOW()
            WHERE id = %s
            """,
            (scan_owner, lesson_text, str(existing.iloc[0]["id"])),
        )


def load_explain_ai_lesson(signal_id: str, lesson_type: str = "CLOSED_TRADE") -> str:
    signal_id = str(signal_id or "").strip()
    if not signal_id:
        return ""
    df = read_df(
        """
        SELECT lesson_text
        FROM explain_ai_lessons
        WHERE signal_id = %s AND lesson_type = %s
        ORDER BY updated_at DESC NULLS LAST, created_at DESC NULLS LAST
        LIMIT 1
        """,
        (signal_id, lesson_type),
    )
    if df.empty:
        return ""
    return str(df.iloc[0].get("lesson_text") or "")


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

            if (v.includes('NOT PASSED') || v.includes('FAILED') || v.includes('SL') || v.includes('LOSS')) {
              bg = 'rgba(255,93,93,.18)';
              color = '#FF5D5D';
            } else if (v.includes('PASSED') || v.includes('TP') || v.includes('WIN')) {
              bg = 'rgba(0,212,163,.18)';
              color = '#00D4A3';
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



def price_decimals_for_asset(asset: str | None, value=None) -> int:
    """TradingView-style display precision for Entry, SL and TP.

    The database keeps raw precision, but the app should display the same
    practical quote precision a trader sees on TradingView/broker charts.
    """
    a = str(asset or "").strip().upper().replace("/", "").replace("-", "")

    # Crypto, commodities, indices and equities normally trade visually at 2dp.
    if a in {"BTCUSD", "ETHUSD", "OIL", "BRENT", "NATGAS", "COPPER", "XAUUSD", "XAGUSD", "SP500", "NAS100", "DOW30", "NVDA", "MU"}:
        return 2

    # JPY FX pairs use pipette-style 3dp on TradingView/broker displays.
    if a.endswith("JPY") or "JPY" in a:
        return 3

    # Most non-JPY FX pairs use 5dp.
    known_fx = {
        "EURUSD", "GBPUSD", "USDCHF", "USDCAD", "AUDUSD", "NZDUSD",
        "EURGBP", "EURAUD", "EURNZD", "EURCAD", "EURCHF",
        "GBPAUD", "GBPNZD", "GBPCAD", "GBPCHF",
        "AUDCAD", "AUDNZD", "AUDCHF", "NZDCAD", "NZDCHF",
    }
    if a in known_fx:
        return 5

    # Fallback from price scale when an asset label is unavailable.
    try:
        x = abs(float(str(value).replace(",", "")))
        if x >= 10:
            return 2
        if x >= 1:
            return 5
        return 5
    except Exception:
        return 2


def format_market_price(value, asset: str | None = None):
    """Format Entry, SL and TP using asset-specific TradingView precision."""
    try:
        if value is None or pd.isna(value):
            return ""
        x = float(str(value).replace(",", ""))
        if not np.isfinite(x):
            return ""
        decimals = price_decimals_for_asset(asset, x)
        return f"{x:,.{decimals}f}"
    except Exception:
        return "" if value is None else str(value)


def is_price_display_column(col_name: str) -> bool:
    """Only Entry, SL, and TP are allowed to keep market-price precision."""
    c = str(col_name or "").strip().lower()
    c = c.replace("_", " ").replace("-", " ")
    c = re.sub(r"\s+", " ", c)

    exact = {
        "entry", "sl", "tp",
        "hypothetical entry", "hypothetical sl", "hypothetical tp",
    }
    return c in exact



def benzino_id_number(value) -> float:
    """Extract the numeric part from Benzino-123 style IDs for fallback sorting."""
    try:
        match = re.search(r"(\d+)", str(value or ""))
        return float(match.group(1)) if match else np.nan
    except Exception:
        return np.nan


def _parse_display_created_series(series: pd.Series) -> pd.Series:
    """Parse either raw timestamps or display timestamps like '2026-06-30 15:44 EAT'."""
    try:
        raw = series.astype(str).str.replace(" EAT", "", regex=False).str.strip()
        return pd.to_datetime(raw, errors="coerce", utc=True)
    except Exception:
        return pd.to_datetime(series, errors="coerce", utc=True)


def sort_signal_rows_newest_first(df: pd.DataFrame) -> pd.DataFrame:
    """Default-sort any table with Signal ID/display_id by newest generated signal first.

    Primary sort is the signal creation time. If a table does not expose a
    timestamp, fall back to the Benzino-XXX sequence number, which is generated
    by the scanner at save time.
    """
    if df is None or df.empty:
        return df
    id_candidates = ["Signal ID", "signal_id", "display_id"]
    if not any(c in df.columns for c in id_candidates):
        return df

    out = df.copy()
    created_col = next((c for c in ["created_at", "Created At", "signal_created_at", "closed_at", "Closed At"] if c in out.columns), None)
    id_col = next((c for c in ["Signal ID", "display_id", "signal_id"] if c in out.columns), None)

    if created_col:
        out["_benzino_sort_created"] = _parse_display_created_series(out[created_col])
    else:
        out["_benzino_sort_created"] = pd.NaT

    if id_col:
        out["_benzino_sort_id"] = out[id_col].apply(benzino_id_number)
    else:
        out["_benzino_sort_id"] = np.nan

    out = out.sort_values(
        ["_benzino_sort_created", "_benzino_sort_id"],
        ascending=[False, False],
        na_position="last",
        kind="mergesort",
    )
    return out.drop(columns=["_benzino_sort_created", "_benzino_sort_id"], errors="ignore")


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
    show_status_filter: bool = True,
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

    # Any table with a Signal ID should default to newest generated signal first.
    # This uses created_at/Created At first, then Benzino-XXX number as a fallback.
    view = sort_signal_rows_newest_first(view)

    if column_order:
        ordered = [c for c in column_order if c in view.columns]
        rest = [c for c in view.columns if c not in ordered]
        view = view[ordered + rest]

    # Decimal policy:
    # Only Entry, SL and TP keep market-price precision. Every other numeric
    # decimal is rounded to 2dp so tables do not show noisy precision.
    asset_col_for_precision = next((c for c in ["Asset", "asset", "Instrument", "symbol", "Symbol"] if c in view.columns), None)
    for _col in view.columns:
        if is_price_display_column(_col):
            if asset_col_for_precision:
                view[_col] = view.apply(lambda r, c=_col: format_market_price(r.get(c), r.get(asset_col_for_precision)), axis=1)
            else:
                view[_col] = view[_col].apply(format_market_price)
        elif pd.api.types.is_numeric_dtype(view[_col]):
            def _fmt_numeric(x, _col=_col):
                if pd.isna(x):
                    return ""
                try:
                    v = float(x)
                    if not np.isfinite(v):
                        return ""
                    return f"{v:.2f}"
                except Exception:
                    return str(x) if x is not None else ""
            view[_col] = view[_col].apply(_fmt_numeric)

    search_value = ""
    status_col_name = next((c for c in view.columns if str(c).strip().lower() == "status"), None)
    if title or enable_search or show_filter_button or (status_col_name and show_status_filter):
        if status_col_name and show_status_filter:
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

    # Use the database display_id so the app matches Telegram and Supabase exactly.
    # Do NOT recalculate Benzino IDs in the app, otherwise Signal ID changes with filters/limits.
    if "display_id" in view.columns:
        display = view["display_id"].astype(str).replace({"nan": "", "None": "", "NaT": ""})
        fallback = view["signal_id"].astype(str) if "signal_id" in view.columns else display
        view["signal_id"] = display.where(display.str.strip().ne(""), fallback)

    view = sort_signal_rows_newest_first(view).head(limit)
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
    .section-gap { height:32px; }
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
    button[kind="segmented_controlActive"] p,
    button[kind="segmented_controlActive"] span,
    button[kind="segmented_controlActive"] div,
    [data-testid="stBaseButton-segmented_controlActive"] p,
    [data-testid="stBaseButton-segmented_controlActive"] span,
    [data-testid="stBaseButton-segmented_controlActive"] div {
        color: #FFFFFF !important;
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
        padding: 18px 22px 18px 18px;
        min-height: 136px;
        height: auto;
        position: relative;
        display: flex;
        align-items: center;
        justify-content: flex-start;
        overflow: visible;
    }
    .benzino-stat-card > div:first-child {
        width: calc(100% - 6px);
        transform: translateY(3px);
    }
    .benzino-stat-card-no-icon { padding-right:18px !important; }
    .benzino-stat-card-no-icon .benzino-stat-label { max-width:100% !important; text-transform:uppercase; letter-spacing:.5px; }
    .benzino-stat-label {
        color:#8BAAB8;
        font-size:clamp(11px, .78vw, 14px);
        font-weight:850;
        line-height:1.16;
        white-space:nowrap;
        max-width: 100%;
        overflow: hidden;
        text-overflow: ellipsis;
    }
    .benzino-stat-value {
        color:#E8EDF2;
        font-size:clamp(22px, 1.55vw, 30px);
        font-weight:950;
        margin-top:8px;
        line-height:1.08;
        white-space:normal;
        overflow-wrap:anywhere;
        letter-spacing:-.5px;
    }
    .benzino-stat-note {
        font-size:clamp(10px, .68vw, 12px);
        font-weight:800;
        margin-top:8px;
        line-height:1.2;
        max-width: 100%;
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
        with st.container(border=True):
            st.markdown("<div class='benzino-panel-title'>Balance Curve by Grade</div>", unsafe_allow_html=True)
            render_balance_curve(df, settings, title="", split_by_grade=True, include_overall=True)

    with right:
        with st.container(border=True, height=440):
            st.markdown("<div class='benzino-panel-title'>Performance by Grade</div>", unsafe_allow_html=True)
            # Match Workflow → User split analysis exactly:
            # grade performance is based on CLOSED journal trades only, excluding No Trade.
            grade_order = ["A+", "A", "B", "C"]
            grade_colors = {"A+": "#00D4A3", "A": "#4C8CFF", "B": "#D6A84E", "C": "#FF5D5D"}

            grade_source = df.copy()
            grade_source["outcome"] = grade_source.apply(outcome_label, axis=1)
            grade_source = grade_source[
                grade_source["grade"].astype(str).isin(grade_order)
                & grade_source["outcome"].isin(["WIN", "LOSS", "BREAKEVEN", "CLOSED"])
            ].copy()

            counts = (
                grade_source["grade"]
                .astype(str)
                .value_counts()
                .reindex(grade_order)
                .fillna(0)
                .astype(int)
            )
            counts = counts[counts > 0]

            # The donut slice size still shows trade distribution by grade, but
            # the legend now shows the more useful metric: win rate per grade.
            # This keeps Dashboard consistent with Workflow → User split analysis,
            # where the table already reports A/B/C win_rate + trade count.
            win_rates_by_grade = {}
            for g in counts.index:
                g_rows = grade_source[grade_source["grade"].astype(str).eq(str(g))].copy()
                win_rates_by_grade[g] = win_rate_from_resolved(g_rows)

            if counts.empty:
                st.markdown("<div class='benzino-empty-note'>No closed performance data yet for this watchlist/timeframe.</div>", unsafe_allow_html=True)
            else:
                total = int(counts.sum())
                customdata = [[win_rates_by_grade.get(g, 0.0)] for g in counts.index]
                fig = go.Figure(data=[go.Pie(
                    labels=counts.index.tolist(),
                    values=counts.values.tolist(),
                    customdata=customdata,
                    hole=0.54,
                    marker=dict(colors=[grade_colors.get(g, "#8BAAB8") for g in counts.index]),
                    textinfo="none",
                    hovertemplate="%{label}<br>%{value} trade(s)<br>Win rate: %{customdata[0]:.2f}%<extra></extra>",
                    sort=False,
                )])
                fig.update_layout(
                    paper_bgcolor="rgba(0,0,0,0)", plot_bgcolor="rgba(0,0,0,0)",
                    showlegend=False, margin=dict(l=2, r=2, t=0, b=0), height=288,
                    annotations=[dict(text=f"<b>{total}</b><br><span style='font-size:11px'>Closed Trades</span>", x=0.5, y=0.5, font=dict(size=24, color="#E8EDF2"), showarrow=False)],
                )
                fig.update_traces(domain=dict(x=[0.07, 0.93], y=[0.03, 0.97]))
                st.plotly_chart(fig, use_container_width=True, config={"displayModeBar": False})
                legend_parts = ["<div class='grade-legend-grid'>"]
                for g in counts.index:
                    win_rate = win_rates_by_grade.get(g, 0.0)
                    safe_g = html.escape(str(g))
                    safe_color = grade_colors.get(g, "#8BAAB8")
                    legend_parts.append(
                        f"<div class='grade-legend-item'>"
                        f"<span class='grade-legend-name'><span style='color:{safe_color};font-size:16px;'>■</span>{safe_g}</span>"
                        f"<span class='grade-legend-value'>{win_rate:.2f}% ({int(counts[g])})</span>"
                        f"</div>"
                    )
                legend_parts.append("</div>")
                st.markdown("".join(legend_parts), unsafe_allow_html=True)


    st.markdown("<div class='section-gap'></div>", unsafe_allow_html=True)

    # ---- Generated signals: full Supabase table, ordered and styled for trading readability ----
    with st.container(border=True):
        generated = df.copy()
        # Use database display_id so this table matches Telegram and Supabase exactly.
        # The previous app-side re-numbering produced wrong IDs such as Benzino-365
        # while Telegram/Supabase correctly showed Benzino-258.
        if "display_id" in generated.columns:
            display = generated["display_id"].astype(str).replace({"nan": "", "None": "", "NaT": ""})
            fallback = generated["signal_id"].astype(str) if "signal_id" in generated.columns else display
            generated["signal_id"] = display.where(display.str.strip().ne(""), fallback)
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
            display_df = sort_signal_rows_newest_first(display_df)

            # Search across the final display table.
            if table_search:
                mask = display_df.astype(str).apply(
                    lambda col: col.str.contains(table_search, case=False, na=False)
                ).any(axis=1)
                display_df = display_df[mask].copy()

            def _fmt_entry_sl_tp(x, asset=None):
                if pd.isna(x) or str(x).strip() == "":
                    return "—"
                n = pd.to_numeric(x, errors="coerce")
                if pd.notna(n):
                    return format_market_price(float(n), asset)
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
                    if "Asset" in display_df.columns:
                        display_df[money_col] = display_df.apply(lambda r, c=money_col: _fmt_entry_sl_tp(r.get(c), r.get("Asset")), axis=1)
                    else:
                        display_df[money_col] = display_df[money_col].apply(_fmt_entry_sl_tp)
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
    closed = graded[graded["outcome"].isin(["WIN", "LOSS", "BREAKEVEN", "CLOSED", "EXPIRED_WIN", "EXPIRED_LOSS", "EXPIRED_BREAKEVEN"])].copy()
    resolved = closed_resolved_trades(closed)

    win_rate = win_rate_from_resolved(closed)
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
        grade_perf = closed.groupby("grade").apply(
            lambda g: pd.Series({
                "win_rate": win_rate_group(g),
                "trades": len(closed_resolved_trades(g)),
                "avg_r": pd.to_numeric(g.get("r_multiple", pd.Series(dtype=float)), errors="coerce").mean(),
            }),
            include_groups=False,
        ).reset_index().sort_values("grade")
        st.markdown("**By grade**")
        render_benzino_aggrid(grade_perf, key="system_perf_grade", height=240, page_size=10, pinned=["grade"], badge_cols={"grade":"grade", "Grade":"grade"}, numeric_cols_right=[c for c in grade_perf.columns if c not in ["grade", "Grade"]], enable_search=False, show_footer=False, use_pagination=False)

    with g2:
        session_perf = closed.groupby("session").apply(
            lambda g: pd.Series({
                "win_rate": win_rate_group(g),
                "trades": len(closed_resolved_trades(g)),
                "avg_r": pd.to_numeric(g.get("r_multiple", pd.Series(dtype=float)), errors="coerce").mean(),
            }),
            include_groups=False,
        ).reset_index().sort_values("trades", ascending=False)
        st.markdown("**By session**")
        render_benzino_aggrid(session_perf, key="system_perf_session", height=240, page_size=10, pinned=["session"], numeric_cols_right=[c for c in session_perf.columns if c not in ["session", "Session"]], enable_search=False, show_footer=False, use_pagination=False)

    a1, a2 = st.columns(2)
    with a1:
        timeframe_perf = closed.groupby("timeframe").apply(
            lambda g: pd.Series({
                "win_rate": win_rate_group(g),
                "trades": len(closed_resolved_trades(g)),
                "avg_r": pd.to_numeric(g.get("r_multiple", pd.Series(dtype=float)), errors="coerce").mean(),
            }),
            include_groups=False,
        ).reset_index().sort_values("timeframe")
        st.markdown("**By timeframe**")
        render_benzino_aggrid(timeframe_perf, key="system_perf_timeframe_split", height=240, page_size=10, pinned=["timeframe"], numeric_cols_right=[c for c in timeframe_perf.columns if c != "timeframe"], enable_search=False, show_footer=False, use_pagination=False)

    with a2:
        asset_perf = closed.groupby("asset").apply(
            lambda g: pd.Series({
                "win_rate": win_rate_group(g),
                "trades": len(closed_resolved_trades(g)),
                "avg_r": pd.to_numeric(g.get("r_multiple", pd.Series(dtype=float)), errors="coerce").mean(),
            }),
            include_groups=False,
        ).reset_index().sort_values(["trades", "win_rate"], ascending=[False, False])
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
                    "Description": desc,
                    "Content": item.get("content") or "",
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



def news_why_it_matters(row: dict) -> str:
    """Small deterministic explanation for the Market News detail popup."""
    headline = str(row.get("Headline", "") or "")
    desc = str(row.get("Description", "") or "")
    blob = f"{headline} {desc}".lower()

    reasons = []
    if any(k in blob for k in ["fed", "fomc", "interest rate", "central bank", "cpi", "inflation", "nfp", "payrolls"]):
        reasons.append("macro/rates language appears in the story, so it can affect broad risk sentiment, currencies, gold, indices, and crypto.")
    if any(k in blob for k in ["earnings", "guidance", "revenue", "profit", "forecast"]):
        reasons.append("company earnings or guidance language appears, so it may directly affect equity and index sentiment.")
    if any(k in blob for k in ["war", "conflict", "sanction", "tariff", "geopolitical"]):
        reasons.append("geopolitical risk language appears, which can move safe havens, oil, gold, and risk assets quickly.")
    if any(k in blob for k in ["oil", "opec", "inventory", "crude", "gas"]):
        reasons.append("energy-market language appears, so oil, Brent, natural gas, inflation expectations, and related FX can be sensitive.")
    if any(k in blob for k in ["bitcoin", "btc", "ethereum", "eth", "crypto", "etf", "sec"]):
        reasons.append("crypto-specific language appears, so BTC/ETH sentiment may react more directly.")

    if not reasons:
        reasons.append("the headline is relevant to the selected watchlist asset; check whether price is already reacting before treating it as trade evidence.")

    return " ".join(reasons)


def render_news_detail_popup(row: dict) -> None:
    """Show a compact detail window for one selected Market News headline."""
    if not row:
        return

    title = str(row.get("Headline", "Market News Detail") or "Market News Detail")
    asset = str(row.get("Asset", "") or "")
    source = str(row.get("Source", "") or "")
    published = str(row.get("Published", "") or "")
    impact = str(row.get("Impact", "") or "")
    impact_score = str(row.get("Impact Score", "") or "")
    sentiment = str(row.get("Sentiment", "") or "")
    desc = str(row.get("Description", "") or "")
    content = str(row.get("Content", "") or "")
    url = str(row.get("URL", "") or "")

    def _body():
        st.markdown(f"### {html.escape(title)}")
        st.caption(f"{asset} · {source} · {published}")
        c1, c2, c3 = st.columns(3)
        with c1:
            metric_card("Impact", impact, f"Score {impact_score}/100")
        with c2:
            metric_card("Sentiment", sentiment, "Headline tone")
        with c3:
            metric_card("Asset", asset, "Watchlist match")

        if desc:
            st.markdown("#### Summary")
            st.write(desc)
        elif content:
            st.markdown("#### Summary")
            st.write(content)

        st.markdown("#### Why this matters")
        st.write(news_why_it_matters(row))

        st.markdown("#### Trading note")
        st.write(
            "Treat this as market context, not an entry trigger by itself. Confirm whether the scanner signal, session, volatility, and price reaction support the same direction."
        )

        if url:
            st.link_button("Open full article", url, use_container_width=True)

    if hasattr(st, "dialog"):
        @st.dialog("News Detail")
        def _dialog():
            _body()
        _dialog()
    else:
        with st.expander("News Detail", expanded=True):
            _body()



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

    table_view = view[["Asset", "Headline", "Source", "Published", "Sentiment", "Impact", "Impact Score", "Description", "Content", "URL"]].copy()

    st.markdown("<div class='benzino-panel-title'>Watchlist News</div>", unsafe_allow_html=True)
    st.caption("Select a headline row to open a detail window with summary, impact reasoning, and the full-article link.")

    if AgGrid is not None and GridOptionsBuilder is not None:
        display_view = table_view[["Asset", "Headline", "Source", "Published", "Sentiment", "Impact", "Impact Score"]].copy()
        gb = GridOptionsBuilder.from_dataframe(display_view)
        gb.configure_default_column(sortable=True, filter=True, resizable=True, wrapText=True, autoHeight=True)
        gb.configure_selection(selection_mode="single", use_checkbox=False)
        gb.configure_pagination(paginationAutoPageSize=False, paginationPageSize=12)
        gb.configure_grid_options(
            rowHeight=52,
            headerHeight=44,
            suppressMenuHide=True,
            domLayout="normal",
            animateRows=True,
            quickFilterText=None,
        )
        renderers = aggrid_badge_renderers()
        if "Asset" in display_view.columns:
            gb.configure_column("Asset", pinned="left")
        if "Sentiment" in display_view.columns and "status" in renderers:
            gb.configure_column("Sentiment", cellRenderer=renderers["status"])
        if "Impact" in display_view.columns and "grade" in renderers:
            gb.configure_column("Impact", cellRenderer=renderers["grade"])
        if "Impact Score" in display_view.columns:
            gb.configure_column("Impact Score", cellStyle={"textAlign": "right", "fontWeight": "700"})

        news_response = AgGrid(
            display_view,
            gridOptions=gb.build(),
            height=560,
            fit_columns_on_grid_load=False,
            theme="balham",
            allow_unsafe_jscode=True,
            custom_css=benzino_aggrid_css(),
            key="market_news_table_selectable",
        )

        selected = news_response.get("selected_rows", [])
        if isinstance(selected, pd.DataFrame):
            selected_rows = selected.to_dict("records")
        else:
            selected_rows = selected or []

        if selected_rows:
            selected_headline = str(selected_rows[0].get("Headline", ""))
            detail_rows = table_view[table_view["Headline"].astype(str).eq(selected_headline)].head(1)
            if not detail_rows.empty:
                render_news_detail_popup(detail_rows.iloc[0].to_dict())
    else:
        render_benzino_aggrid(
            table_view[["Asset", "Headline", "Source", "Published", "Sentiment", "Impact", "Impact Score"]],
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
    # No Trade Tracker source: use the same user/watchlist + selected timeframe
    # scope as the rest of the Workflow page. The previous version used raw_df
    # before apply_timeframe_view(), which made this tab show all timeframes even
    # when the user had selected 15m/1h/4h/1d. It also rendered only .head(300)
    # later, so busy days could hide older Supabase shadow history.
    _nt_source = df.copy() if df is not None and not df.empty else pd.DataFrame(columns=raw_df.columns if raw_df is not None else [])
    if not _nt_source.empty and "outcome" not in _nt_source.columns:
        _nt_source["outcome"] = _nt_source.apply(outcome_label, axis=1)
    no_trades = _nt_source[_nt_source["status"].astype(str).str.upper().eq("SHADOW")].copy() if not _nt_source.empty and "status" in _nt_source.columns else pd.DataFrame()
    open_trades = trades[trades["status"].astype(str).str.upper().eq("OPEN")]
    closed_trades = trades[trades["outcome"].isin(["WIN", "LOSS", "BREAKEVEN", "CLOSED"])]

    t1, t2, t3, t4, t5, t6 = st.tabs(["User Journal", "System Performance", "Prop Firm", "No Trade Tracker", "Coach AI", "Explain AI"])

    with t1:
        c1, c2, c3, c4 = st.columns(4)
        resolved = closed_resolved_trades(closed_trades)
        won_trades = int(resolved_outcome_masks(closed_trades)[0].sum()) if not closed_trades.empty else 0
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
                grade_perf = resolved.groupby("grade").apply(lambda g: pd.Series({"win_rate": win_rate_group(g), "trades": len(closed_resolved_trades(g))}), include_groups=False).reset_index()
                st.markdown("**By grade**")
                render_benzino_aggrid(grade_perf, key="journal_grade_perf", height=240, page_size=10, pinned=["grade"], badge_cols={"grade":"grade", "Grade":"grade"}, numeric_cols_right=[c for c in grade_perf.columns if c not in ["grade", "Grade"]], enable_search=False, show_footer=False, use_pagination=False)
            with ug2:
                session_perf = resolved.groupby("session").apply(lambda g: pd.Series({"win_rate": win_rate_group(g), "trades": len(closed_resolved_trades(g))}), include_groups=False).reset_index()
                st.markdown("**By session**")
                render_benzino_aggrid(session_perf, key="journal_session_perf", height=240, page_size=10, pinned=["session"], numeric_cols_right=[c for c in session_perf.columns if c not in ["session", "Session"]], enable_search=False, show_footer=False, use_pagination=False)
            ut1, ut2 = st.columns(2)
            with ut1:
                timeframe_perf = resolved.groupby("timeframe").apply(lambda g: pd.Series({"win_rate": win_rate_group(g), "trades": len(closed_resolved_trades(g))}), include_groups=False).reset_index()
                st.markdown("**By timeframe**")
                render_benzino_aggrid(timeframe_perf, key="journal_timeframe_perf", height=240, page_size=10, pinned=["timeframe"], numeric_cols_right=[c for c in timeframe_perf.columns if c != "timeframe"], enable_search=False, show_footer=False, use_pagination=False)
            with ut2:
                asset_perf = resolved.groupby("asset").apply(lambda g: pd.Series({"win_rate": win_rate_group(g), "trades": len(closed_resolved_trades(g))}), include_groups=False).reset_index()
                st.markdown("**By asset**")
                render_benzino_aggrid(asset_perf.sort_values("trades", ascending=False), key="journal_asset_perf", height=240, page_size=10, pinned=["asset"], numeric_cols_right=[c for c in asset_perf.columns if c != "asset"], enable_search=False, show_footer=False, use_pagination=False)

        def _render_journal_signal_grid(source_df: pd.DataFrame, table_title: str, key_prefix: str, cols: list[str], badge_map: dict, numeric_right: list[str]) -> None:
            prepared = prepare_signal_table(source_df[[c for c in cols if c in source_df.columns]].head(200))
            title_col, sig_col, grade_col, status_col, search_col = st.columns([3.6, 1.0, 1.0, 1.15, 2.25], vertical_alignment="center")
            with title_col:
                st.markdown(f"<div class='benzino-panel-title'>{html.escape(table_title)}</div>", unsafe_allow_html=True)
            with sig_col:
                signal_choice = st.selectbox("Signal", ["All", "BUY", "SELL", "HOLD", "NO TRADE"], label_visibility="collapsed", key=f"{key_prefix}_signal_filter")
            with grade_col:
                grade_choice = st.selectbox("Grade", ["All", "A+", "A", "B", "C", "NO TRADE"], label_visibility="collapsed", key=f"{key_prefix}_grade_filter")
            with status_col:
                status_options = ["All"] + sorted([str(v) for v in prepared.get("Status", pd.Series(dtype=str)).dropna().astype(str).unique() if str(v).strip()]) if "Status" in prepared.columns else ["All"]
                status_choice = st.selectbox("Status", status_options, label_visibility="collapsed", key=f"{key_prefix}_status_filter_inline")
            with search_col:
                search_choice = st.text_input(f"Search {table_title}", placeholder="Search…", label_visibility="collapsed", key=f"{key_prefix}_search")
            if signal_choice != "All" and "Signal" in prepared.columns:
                prepared = prepared[prepared["Signal"].astype(str).str.upper().str.contains(signal_choice, na=False)]
            if grade_choice != "All" and "Grade" in prepared.columns:
                prepared = prepared[prepared["Grade"].astype(str).str.upper().eq(grade_choice.upper())]
            if status_choice != "All" and "Status" in prepared.columns:
                prepared = prepared[prepared["Status"].astype(str).eq(status_choice)]
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

        st.markdown("<div class='section-gap'></div>", unsafe_allow_html=True)
        st.subheader("Capital.com simulated vs actual")
        st.caption("This compares BENZINO's simulated signal outcome against trades BENZINO opened on your Capital.com demo account. Historical signal plans stay locked; the focus here is whether the auto-executed trade matched the simulated result, not manual entry or exit drift.")
        cap_comp = load_capital_trade_comparisons(limit=500)
        cap_raw = load_capital_executed_trades(limit=500)
        if cap_comp.empty and cap_raw.empty:
            st.info("No Capital.com auto-trade executions have been imported yet. Once CAPITAL_AUTO_TRADE_ENABLED is turned on and the scanner opens demo trades, this section will show simulated vs actual results.")
        else:
            auto_count = int(pd.Series(cap_comp.get("auto_trade", pd.Series(dtype=bool))).fillna(False).astype(bool).sum()) if not cap_comp.empty else 0
            matched_count = len(cap_comp)
            total_actual_pnl = float(pd.to_numeric(cap_comp.get("actual_pnl", pd.Series(dtype=float)), errors="coerce").fillna(0).sum()) if not cap_comp.empty else 0.0
            avg_sim_r = float(pd.to_numeric(cap_comp.get("simulated_r", pd.Series(dtype=float)), errors="coerce").dropna().mean()) if not cap_comp.empty else 0.0
            avg_actual_r = float(pd.to_numeric(cap_comp.get("actual_r", pd.Series(dtype=float)), errors="coerce").dropna().mean()) if not cap_comp.empty else 0.0
            ec1, ec2, ec3, ec4 = st.columns(4)
            with ec1: metric_card("Auto executions", f"{auto_count:,}", "Opened by BENZINO on Capital.com")
            with ec2: metric_card("Matched signals", f"{matched_count:,}", "Linked by signal ID")
            with ec3: metric_card("Avg R", f"Sim {avg_sim_r:+.2f}R / Actual {avg_actual_r:+.2f}R", "Simulation vs execution")
            with ec4: metric_card("Actual P/L", f"${total_actual_pnl:+,.2f}", "Capital.com reported P/L")

            if not cap_comp.empty:
                comp = cap_comp.copy()
                comp["Opened"] = pd.to_datetime(comp.get("opened_at"), errors="coerce", utc=True).dt.tz_convert(NAIROBI_TZ).dt.strftime("%Y-%m-%d %H:%M")
                comp_display = comp.rename(columns={
                    "asset": "Asset",
                    "direction": "Direction",
                    "match_quality": "Match",
                    "simulated_entry": "Sim Entry",
                    "actual_entry": "Actual Entry",
                    "simulated_exit": "Sim Exit",
                    "actual_exit": "Actual Exit",
                    "simulated_r": "Sim R",
                    "actual_r": "Actual R",
                    "actual_pnl": "Actual P/L",
                    "simulated_outcome": "Sim Outcome",
                    "actual_status": "Actual Status",
                    "instrument_name": "Instrument",
                    "environment": "Environment",
                    "size": "Size",
                    "currency": "Currency",
                    "auto_trade": "Auto Trade",
                })
                order = ["Opened", "Asset", "Direction", "Match", "Auto Trade", "Sim Entry", "Actual Entry", "Sim Exit", "Actual Exit", "Sim R", "Actual R", "Actual P/L", "Sim Outcome", "Actual Status", "Instrument", "Environment", "Size", "Currency", "signal_id"]
                comp_display = comp_display[[c for c in order if c in comp_display.columns] + [c for c in comp_display.columns if c not in order]]

                cf1, cf2 = st.columns([0.32, 0.68], vertical_alignment="center")
                with cf1:
                    asset_opts = ["All"] + sorted([x for x in comp_display.get("Asset", pd.Series(dtype=str)).dropna().astype(str).unique() if x])
                    cap_asset_filter = st.selectbox("Execution asset", asset_opts, key="capital_exec_asset_filter")
                with cf2:
                    st.markdown("<div class='grey-note' style='margin-top:4px;'>Auto-traded rows are matched by the originating BENZINO signal ID, so entry/exit drift stats are intentionally removed.</div>", unsafe_allow_html=True)
                if cap_asset_filter != "All" and "Asset" in comp_display.columns:
                    comp_display = comp_display[comp_display["Asset"].astype(str).eq(cap_asset_filter)]

                render_benzino_aggrid(
                    comp_display,
                    key="capital_execution_comparison",
                    height=360,
                    page_size=25,
                    pinned=["Opened", "Asset", "Direction", "Match"],
                    badge_cols={"Direction":"signal", "Match":"status", "Sim Outcome":"status", "Actual Status":"status", "Auto Trade":"status"},
                    numeric_cols_right=["Sim Entry", "Actual Entry", "Sim Exit", "Actual Exit", "Sim R", "Actual R", "Actual P/L", "Size"],
                    enable_search=False,
                    show_footer=False,
                )
            elif not cap_raw.empty:
                st.warning("Capital.com executions were imported, but none are linked to BENZINO auto-traded signals yet.")

        st.markdown("<div class='section-gap'></div>", unsafe_allow_html=True)
        st.subheader("Expiry breakdown")
        expiry_rules = {
            "15m": {"bars": 56, "approx": "~14 hours"},
            "1h": {"bars": 56, "approx": "~2.3 days"},
            "4h": {"bars": 42, "approx": "~7 days"},
            "1d": {"bars": 20, "approx": "~1 month"},
        }
        selected_tf = str(settings.get("view_timeframe") or settings.get("preferred_timeframe") or "All").lower()
        if selected_tf not in expiry_rules:
            selected_tf = "All"
        expiry_rows = []
        for tf, meta in expiry_rules.items():
            expiry_rows.append({
                "Timeframe": tf,
                "Expiry Bars": int(meta["bars"]),
                "Approx Window": meta["approx"],
                "Currently Selected": "YES" if selected_tf == tf else "NO",
            })
        expiry_df = pd.DataFrame(expiry_rows)
        selected_note = (
            f"The selected {selected_tf} timeframe expires after {expiry_rules[selected_tf]['bars']} bars "
            f"({expiry_rules[selected_tf]['approx']})."
            if selected_tf in expiry_rules
            else "Select a specific timeframe to see the exact expiry rule applied to that journal view."
        )
        st.caption(selected_note + " TP/SL checks use 1-minute replay where available; otherwise the scanner falls back to the signal timeframe candles.")
        render_benzino_aggrid(
            expiry_df,
            key="journal_expiry_breakdown",
            height=320,
            page_size=4,
            pinned=["Timeframe"],
            badge_cols={"Currently Selected": "status"},
            numeric_cols_right=["Expiry Bars"],
            enable_search=False,
            show_footer=False,
            use_pagination=False,
        )


    with t2:
        # System Performance must use the full Supabase scanner history, not the user's
        # currently selected View Performance timeframe. The user's journal tab is
        # timeframe-scoped; this tab is intentionally global/system-wide.
        render_system_performance(system_raw_df, settings)

    with t3:
        challenge_tf = str(settings.get("preferred_timeframe") or settings.get("view_timeframe") or "1h")

        # Prop Firm is a user-scoped view, not the old global scanner ledger.
        # It uses exactly what the logged-in user can trade: current watchlist,
        # selected timeframe, and A+/A trades only. This prevents a global
        # prop_firm_state row from showing FAILED for a user's 4h account when
        # the visible 4h history did not fail.
        prop_settings = settings.copy()
        prop_settings["account_size"] = 10000.0
        prop_settings["risk_pct"] = 1.0
        prop_settings["leverage"] = 100

        starting = 10000.0
        risk_cash = starting * 0.01
        daily_floor = -starting * 0.05
        max_loss_floor = starting * 0.90
        target_balance = starting * 1.10

        # The prop-firm view now replays every scoped A+/A closed trade from the
        # user's activation timestamp. It does not trust the old incremental
        # prop_firm_state row, because that row can drift when challenges pass,
        # fail, or restart between scanner runs.
        prop_start_map = settings.get("prop_challenge_started_at_by_tf", {})
        if not isinstance(prop_start_map, dict):
            prop_start_map = {}
        prop_started_at_raw = str(settings.get("tracking_started_at", "") or "")

        st.markdown(
            f"""
            <div class='grey-note' style='margin-top:10px;margin-bottom:18px;'>
                This tab recalculates the FTMO-style challenge from your current watchlist and selected timeframe
                <b>({html.escape(str(challenge_tf))})</b>. It uses only <b>A+/A closed trades</b>, a fixed
                <b>&#36;10,000</b> account, <b>1% risk per trade</b>, a <b>&#36;1,000 Phase 1 target</b>,
                a <b>&#36;500 Phase 2 target</b>, a <b>5% max daily loss</b>, and a <b>10% max total loss</b>.
                Phase 2 starts from a fresh <b>&#36;10,000</b> verification account after Phase 1 passes.
                Completed cycles are rebuilt from Supabase on every load.
            </div>
            """,
            unsafe_allow_html=True,
        )

        prop_source = trades[
            trades.get("grade", pd.Series(dtype=str)).astype(str).isin(["A+", "A"])
        ].copy() if trades is not None and not trades.empty else pd.DataFrame()
        # Do not cut the stream at the last restart. The simulator below handles
        # every pass/fail/restart cycle itself and then exposes only the active
        # current cycle for the top cards.
        prop_closed = closed_resolved_trades(prop_source) if not prop_source.empty else pd.DataFrame()

        status = "ACTIVE"
        fail_reason = ""
        breach_date = ""
        pass_date = ""
        challenge_started_at = ""
        last_closed_at = ""
        current = starting
        roi_pct = 0.0
        progress_to_target = 0.0
        trading_days = 0
        closed_count = int(len(prop_closed)) if prop_closed is not None and not prop_closed.empty else 0
        open_count = 0
        worst_day_pnl = 0.0
        best_day_pnl = 0.0
        latest_day_pnl = 0.0
        max_drawdown_cash = 0.0
        max_drawdown_pct = 0.0
        day_summary = pd.DataFrame()
        prop_curve = pd.DataFrame()

        # The challenge start is the user activation/restart timestamp, not the
        # first trade found in the filtered data. This lets each user restart
        # a failed challenge without deleting old scanner history.
        try:
            challenge_started_at = fmt_nairobi(prop_started_at_raw) if prop_started_at_raw else ""
        except Exception:
            challenge_started_at = ""

        if not prop_source.empty:
            try:
                open_count = int(prop_source.get("status", pd.Series("", index=prop_source.index)).astype(str).str.upper().eq("OPEN").sum())
            except Exception:
                open_count = 0

        if not prop_closed.empty:
            prop_curve = prop_closed.copy()
            prop_curve = numeric_cols(prop_curve, ["r_multiple", "entry", "sl", "tp", "rr"])

            if "exit_at" in prop_curve.columns:
                event_time = pd.to_datetime(prop_curve["exit_at"], errors="coerce", utc=True)
            else:
                event_time = pd.Series(pd.NaT, index=prop_curve.index)
            created_time = pd.to_datetime(prop_curve.get("created_at", pd.Series(pd.NaT, index=prop_curve.index)), errors="coerce", utc=True)
            prop_curve["prop_event_time"] = event_time.fillna(created_time)
            prop_curve = prop_curve.dropna(subset=["prop_event_time"]).sort_values("prop_event_time")

            prop_curve["pnl_cash"] = pd.to_numeric(prop_curve["r_multiple"], errors="coerce").fillna(0.0) * risk_cash
            prop_curve["balance_after"] = starting + prop_curve["pnl_cash"].cumsum()
            current = float(prop_curve["balance_after"].iloc[-1]) if not prop_curve.empty else starting
            roi_pct = (current / starting - 1) * 100 if starting else 0.0
            progress_to_target = max(0.0, min(1.0, (current - starting) / (starting * 0.10))) if starting else 0.0
            last_closed_at = fmt_nairobi(prop_curve["prop_event_time"].max()) if not prop_curve.empty else ""

            running_peak = prop_curve["balance_after"].cummax()
            dd = prop_curve["balance_after"] - running_peak
            max_drawdown_cash = float(dd.min()) if len(dd) else 0.0
            peak_for_dd = running_peak.replace(0, np.nan)
            dd_pct = (dd / peak_for_dd * 100).replace([np.inf, -np.inf], np.nan)
            max_drawdown_pct = float(dd_pct.min()) if len(dd_pct.dropna()) else 0.0

            event_eat = prop_curve["prop_event_time"].dt.tz_convert(NAIROBI_TZ)
            prop_curve["prop_day"] = event_eat.dt.date
            day_pnl = prop_curve.groupby("prop_day")["pnl_cash"].sum().sort_index()
            trading_days = int(day_pnl.index.nunique())
            worst_day_pnl = float(day_pnl.min()) if len(day_pnl) else 0.0
            best_day_pnl = float(day_pnl.max()) if len(day_pnl) else 0.0
            latest_day_pnl = float(day_pnl.iloc[-1]) if len(day_pnl) else 0.0

            day_summary = prop_curve.groupby("prop_day").agg(
                daily_pnl=("pnl_cash", "sum"),
                trades=("signal_id", "count") if "signal_id" in prop_curve.columns else ("pnl_cash", "count"),
            ).reset_index().rename(columns={"prop_day": "Day", "daily_pnl": "Daily P/L", "trades": "Trades"})
            day_summary = day_summary.sort_values("Day")
            day_summary["Opening Balance"] = starting + day_summary["Daily P/L"].cumsum().shift(1).fillna(0.0)
            day_summary["Closing Balance"] = starting + day_summary["Daily P/L"].cumsum()
            day_summary["Day Result"] = day_summary["Daily P/L"].apply(lambda x: "WIN" if float(x) > 0 else "LOSS" if float(x) < 0 else "BREAKEVEN")
            day_summary["Daily Breach"] = day_summary["Daily P/L"].apply(lambda x: "YES" if float(x) <= daily_floor else "NO")
            day_summary["Target Hit"] = day_summary["Closing Balance"].apply(lambda x: "YES" if float(x) >= target_balance else "NO")

            total_breach_rows = prop_curve[prop_curve["balance_after"] <= max_loss_floor]
            daily_breach_days = day_pnl[day_pnl <= daily_floor]

            # Pass/fail is evaluated chronologically. A failure before a later target hit remains FAILED.
            for _, drow in day_summary.iterrows():
                day = str(drow["Day"])
                if float(drow["Closing Balance"]) <= max_loss_floor:
                    status = "FAILED"
                    fail_reason = "10% max total loss breached"
                    breach_date = day
                    break
                if float(drow["Daily P/L"]) <= daily_floor:
                    status = "FAILED"
                    fail_reason = "5% max daily loss breached"
                    breach_date = day
                    break
                days_so_far = int(day_summary[day_summary["Day"] <= drow["Day"]]["Day"].nunique())
                if float(drow["Closing Balance"]) >= target_balance and days_so_far >= 4:
                    status = "PASSED"
                    pass_date = day
                    break

            if status == "ACTIVE" and current >= target_balance and trading_days >= 4:
                status = "PASSED"
                pass_date = str(day_summary.iloc[-1]["Day"]) if not day_summary.empty else ""

        # Full FTMO pathway simulation using the same scoped A+/A trade stream.
        # Phase 1: 10% target, 5% max daily loss, 10% max total loss, 4 min trading days.
        # Phase 2: 5% target, same loss rules, 4 min trading days.
        # Funded: no profit target, same loss rules, refund/profit-split metadata only.
        def _evaluate_ftmo_phase(curve: pd.DataFrame, start_pos: int, target_profit: float, phase_name: str, start_label: str = "") -> dict:
            result = {
                "phase": phase_name,
                "status": "LOCKED" if start_pos is None else "ACTIVE",
                "start_pos": start_pos,
                "end_pos": None,
                "start_date": "",
                "pass_date": "",
                "breach_date": "",
                "breach_reason": "",
                "equity": starting,
                "pnl": 0.0,
                "roi_pct": 0.0,
                "trading_days": 0,
                "closed_trades": 0,
                "best_day": 0.0,
                "worst_day": 0.0,
                "max_drawdown_cash": 0.0,
                "max_drawdown_pct": 0.0,
                "progress": 0.0,
                "daily_ledger": pd.DataFrame(),
            }
            if curve is None or curve.empty or start_pos is None or start_pos >= len(curve):
                return result

            phase_curve = curve.iloc[int(start_pos):].copy().reset_index(drop=True)
            if phase_curve.empty:
                return result
            result["start_date"] = start_label or (fmt_nairobi(phase_curve["prop_event_time"].iloc[0]) if "prop_event_time" in phase_curve.columns else "")
            phase_curve["phase_balance_after"] = starting + pd.to_numeric(phase_curve["pnl_cash"], errors="coerce").fillna(0.0).cumsum()
            phase_curve["phase_day"] = phase_curve["prop_event_time"].dt.tz_convert(NAIROBI_TZ).dt.date
            phase_day = phase_curve.groupby("phase_day").agg(
                daily_pnl=("pnl_cash", "sum"),
                trades=("pnl_cash", "count"),
                closing_balance=("phase_balance_after", "last"),
            ).reset_index().rename(columns={"phase_day": "Day", "daily_pnl": "Daily P/L", "trades": "Trades", "closing_balance": "Closing Balance"})
            phase_day["Opening Balance"] = starting + phase_day["Daily P/L"].cumsum().shift(1).fillna(0.0)
            phase_day["Day Result"] = phase_day["Daily P/L"].apply(lambda x: "WIN" if float(x) > 0 else "LOSS" if float(x) < 0 else "BREAKEVEN")
            phase_day["Daily Breach"] = phase_day["Daily P/L"].apply(lambda x: "YES" if float(x) <= daily_floor else "NO")
            phase_day["Target Hit"] = phase_day["Closing Balance"].apply(lambda x: "YES" if float(x) >= starting + target_profit else "NO")
            result["daily_ledger"] = phase_day

            running_peak = phase_curve["phase_balance_after"].cummax()
            dd = phase_curve["phase_balance_after"] - running_peak
            result["max_drawdown_cash"] = float(dd.min()) if len(dd) else 0.0
            dd_pct = (dd / running_peak.replace(0, np.nan) * 100).replace([np.inf, -np.inf], np.nan)
            result["max_drawdown_pct"] = float(dd_pct.min()) if len(dd_pct.dropna()) else 0.0
            result["trading_days"] = int(phase_day["Day"].nunique()) if not phase_day.empty else 0
            result["best_day"] = float(phase_day["Daily P/L"].max()) if not phase_day.empty else 0.0
            result["worst_day"] = float(phase_day["Daily P/L"].min()) if not phase_day.empty else 0.0
            result["closed_trades"] = int(len(phase_curve))
            result["equity"] = float(phase_curve["phase_balance_after"].iloc[-1]) if not phase_curve.empty else starting
            result["pnl"] = result["equity"] - starting
            result["roi_pct"] = (result["pnl"] / starting * 100) if starting else 0.0
            result["progress"] = max(0.0, min(1.0, result["pnl"] / target_profit)) if target_profit else 0.0

            status_local = "ACTIVE"
            pass_day = ""
            pass_pos = None
            for _, drow in phase_day.iterrows():
                day = drow["Day"]
                day_rows = phase_curve[phase_curve["phase_day"].eq(day)]
                day_last_local_pos = int(day_rows.index.max()) if not day_rows.empty else 0
                event_label = ""
                try:
                    event_label = fmt_nairobi(phase_curve.loc[day_last_local_pos, "prop_event_time"])
                except Exception:
                    event_label = str(day)
                if float(drow["Closing Balance"]) <= max_loss_floor:
                    status_local = "FAILED"
                    result["breach_reason"] = "10% max total loss breached"
                    result["breach_date"] = event_label
                    pass_pos = day_last_local_pos
                    break
                if float(drow["Daily P/L"]) <= daily_floor:
                    status_local = "FAILED"
                    result["breach_reason"] = "5% max daily loss breached"
                    result["breach_date"] = event_label
                    pass_pos = day_last_local_pos
                    break
                days_so_far = int(phase_day[phase_day["Day"] <= day]["Day"].nunique())
                if float(drow["Closing Balance"]) >= starting + target_profit and days_so_far >= 4:
                    status_local = "PASSED"
                    pass_day = event_label
                    pass_pos = day_last_local_pos
                    break
            result["status"] = status_local
            result["pass_date"] = pass_day
            if pass_pos is not None:
                result["end_pos"] = int(start_pos) + int(pass_pos)
            return result

        phase1 = _evaluate_ftmo_phase(prop_curve, 0 if not prop_curve.empty else None, starting * 0.10, "Phase 1 Challenge", challenge_started_at)
        if phase1.get("status") == "PASSED" and phase1.get("end_pos") is not None:
            phase2_start = int(phase1["end_pos"]) + 1
            phase2 = _evaluate_ftmo_phase(prop_curve, phase2_start if phase2_start < len(prop_curve) else None, starting * 0.05, "Phase 2 Verification", phase1.get("pass_date", ""))
            if phase2.get("status") == "LOCKED":
                phase2["status"] = "ACTIVE"
                phase2["start_date"] = "Waiting for next eligible trade"
        else:
            phase2 = {"phase": "Phase 2 Verification", "status": "LOCKED", "start_date": "After Phase 1 passes", "pass_date": "", "breach_date": "", "breach_reason": "", "progress": 0.0, "equity": starting, "pnl": 0.0, "roi_pct": 0.0, "trading_days": 0, "closed_trades": 0, "best_day": 0.0, "worst_day": 0.0, "max_drawdown_cash": 0.0, "max_drawdown_pct": 0.0, "daily_ledger": pd.DataFrame()}
        terminal_phase = None
        terminal_result = ""
        if str(phase1.get("status", "")).upper() == "FAILED":
            terminal_phase = phase1
            terminal_result = "FAILED"
        elif str(phase2.get("status", "")).upper() == "FAILED":
            terminal_phase = phase2
            terminal_result = "FAILED"
        elif str(phase2.get("status", "")).upper() == "PASSED":
            terminal_phase = phase2
            terminal_result = "PASSED"

        if False and terminal_phase is not None and terminal_result:
            terminal_pos = terminal_phase.get("end_pos")
            completed_at_raw = ""
            restart_at_raw = datetime.now(timezone.utc).isoformat()
            try:
                if terminal_pos is not None and prop_curve is not None and not prop_curve.empty:
                    terminal_pos = int(terminal_pos)
                    if 0 <= terminal_pos < len(prop_curve):
                        terminal_ts = pd.to_datetime(prop_curve.iloc[terminal_pos]["prop_event_time"], errors="coerce", utc=True)
                        if pd.notna(terminal_ts):
                            completed_at_raw = terminal_ts.isoformat()
                            restart_at_raw = (terminal_ts + pd.Timedelta(seconds=1)).isoformat()
            except Exception:
                completed_at_raw = ""

            finished_raw = completed_at_raw or restart_at_raw
            completed_slice = pd.DataFrame()
            try:
                if terminal_pos is not None and prop_curve is not None and not prop_curve.empty:
                    completed_slice = prop_curve.iloc[: int(terminal_pos) + 1].copy()
            except Exception:
                completed_slice = pd.DataFrame()
            completed_win_rate = win_rate_from_resolved(completed_slice) if completed_slice is not None and not completed_slice.empty else 0.0

            inserted = archive_prop_challenge_attempt(
                username,
                challenge_tf,
                status=terminal_result,
                phase_1_passed=str(phase1.get("status", "")).upper() == "PASSED",
                phase_2_passed=str(phase2.get("status", "")).upper() == "PASSED",
                starting_balance=starting,
                ending_balance=float(terminal_phase.get("equity", starting) or starting),
                realised_pnl=float(terminal_phase.get("pnl", 0.0) or 0.0),
                win_rate=completed_win_rate,
                trading_days=int(terminal_phase.get("trading_days", 0) or 0),
                started_at=prop_started_at_raw or datetime.now(timezone.utc).isoformat(),
                finished_at=finished_raw,
            )
            if inserted:
                prop_start_map[challenge_tf] = restart_at_raw
                settings["prop_challenge_started_at_by_tf"] = prop_start_map
                save_settings(username, settings)
                st.rerun()

        # Authoritative self-resetting replay from all Supabase trade data since activation.
        # This rebuilds challenge history and then replaces the displayed cards with
        # the currently active Phase 1/Phase 2 account, so balances never keep
        # compounding past the $1,000 / $500 targets.
        prop_sim = simulate_prop_challenge_cycles(prop_closed, prop_started_at_raw, starting)
        rebuild_prop_challenge_history_from_trades(username, challenge_tf, prop_sim.get("history", []))
        active_prop = prop_sim.get("active", {})
        prop_curve = prop_sim.get("active_curve", pd.DataFrame())
        prop_all_replay = prop_sim.get("all_trades", pd.DataFrame())
        day_summary = prop_sim.get("all_daily", pd.DataFrame())
        if day_summary is None or day_summary.empty:
            day_summary = prop_sim.get("active_daily", pd.DataFrame())
        current = float(active_prop.get("equity", starting) or starting)
        roi_pct = float(active_prop.get("roi_pct", 0.0) or 0.0)
        progress_to_target = float(active_prop.get("progress", 0.0) or 0.0)
        trading_days = int(active_prop.get("trading_days", 0) or 0)
        closed_count = int(active_prop.get("closed_count", 0) or 0)
        worst_day_pnl = float(active_prop.get("worst_day_pnl", 0.0) or 0.0)
        best_day_pnl = float(active_prop.get("best_day_pnl", 0.0) or 0.0)
        max_drawdown_cash = float(active_prop.get("max_drawdown_cash", 0.0) or 0.0)
        max_drawdown_pct = float(active_prop.get("max_drawdown_pct", 0.0) or 0.0)
        status = "ACTIVE"
        fail_reason = ""
        breach_date = ""
        pass_date = ""
        challenge_started_at = fmt_nairobi(active_prop.get("start_at")) if active_prop.get("start_at") else (fmt_nairobi(prop_started_at_raw) if prop_started_at_raw else "")
        last_closed_at = fmt_nairobi(active_prop.get("last_closed_at")) if active_prop.get("last_closed_at") else ""
        active_phase_name = str(active_prop.get("phase", "Phase 1 Challenge"))
        active_phase_number = int(active_prop.get("phase_number", 1) or 1)
        active_target_label = "+$1,000" if active_phase_number == 1 else "+$500"
        phase1_passed_at = fmt_nairobi(active_prop.get("phase1_passed_at")) if active_prop.get("phase1_passed_at") else ""
        current_phase_status = "Phase 2 active" if active_phase_number == 2 else "Phase 1 active"
        if active_phase_number == 2:
            current_phase_subtitle = "Phase 1 passed; Phase 2 target + 4 trading days required"
        elif current >= (starting + 1000.0):
            current_phase_subtitle = "Phase 1 target reached; continue until 4 trading days are complete"
        else:
            current_phase_subtitle = "Phase 1 target + 4 trading days required"

        # Keep the FTMO coverage cards and phase analytics aligned with the
        # authoritative Supabase replay above. Completed phases are archived in
        # Challenge review history; the top cards always show the currently
        # active unfinished phase.
        phase1 = {
            "phase": "Phase 1 Challenge",
            "status": "PASSED" if active_phase_number == 2 else "ACTIVE",
            "start_date": challenge_started_at,
            "pass_date": phase1_passed_at if active_phase_number == 2 else "",
            "breach_date": "",
            "breach_reason": "",
            "equity": starting if active_phase_number == 2 else current,
            "pnl": 0.0 if active_phase_number == 2 else current - starting,
            "roi_pct": 0.0 if active_phase_number == 2 else roi_pct,
            "progress": 1.0 if active_phase_number == 2 else progress_to_target,
            "trading_days": CHALLENGE_MIN_TRADING_DAYS if active_phase_number == 2 else trading_days,
            "closed_trades": 0 if active_phase_number == 2 else closed_count,
            "best_day": 0.0 if active_phase_number == 2 else best_day_pnl,
            "worst_day": 0.0 if active_phase_number == 2 else worst_day_pnl,
            "max_drawdown_cash": 0.0 if active_phase_number == 2 else max_drawdown_cash,
            "max_drawdown_pct": 0.0 if active_phase_number == 2 else max_drawdown_pct,
        }
        phase2 = {
            "phase": "Phase 2 Verification",
            "status": "ACTIVE" if active_phase_number == 2 else "LOCKED",
            "start_date": challenge_started_at if active_phase_number == 2 else "After Phase 1 passes",
            "pass_date": "",
            "breach_date": "",
            "breach_reason": "",
            "equity": current if active_phase_number == 2 else starting,
            "pnl": current - starting if active_phase_number == 2 else 0.0,
            "roi_pct": roi_pct if active_phase_number == 2 else 0.0,
            "progress": progress_to_target if active_phase_number == 2 else 0.0,
            "trading_days": trading_days if active_phase_number == 2 else 0,
            "closed_trades": closed_count if active_phase_number == 2 else 0,
            "best_day": best_day_pnl if active_phase_number == 2 else 0.0,
            "worst_day": worst_day_pnl if active_phase_number == 2 else 0.0,
            "max_drawdown_cash": max_drawdown_cash if active_phase_number == 2 else 0.0,
            "max_drawdown_pct": max_drawdown_pct if active_phase_number == 2 else 0.0,
        }

        funded_status = "LOCKED"
        funded_note = "Eligible after Phase 2 is passed"
        status_color = "green" if status == "PASSED" else "red" if status == "FAILED" else ""
        mc = prop_firm_monte_carlo(prop_curve, {"starting_balance": starting, "current_equity": current}, runs=2000)
        c1, c2, c3, c4, c5 = st.columns(5)
        with c1: metric_card("Current phase equity", f"${current:,.2f}", f"{active_phase_name} · Start ${starting:,.0f}")
        with c2: metric_card("ROI to target", f"{roi_pct:+.2f}%", f"Target {active_target_label}")
        with c3: metric_card("Worst day P/L", f"${worst_day_pnl:+,.2f}", f"Daily floor -${starting*0.05:,.0f}")
        with c4: metric_card("Trading days", f"{trading_days}", "Current phase only")
        with c5: metric_card("Challenge status", current_phase_status, current_phase_subtitle)

        st.markdown("<div class='section-gap'></div>", unsafe_allow_html=True)
        i1, i2, i3, i4, i5 = st.columns(5)
        with i1: metric_card("Current phase started", challenge_started_at or "—", "Auto-replayed from Supabase")
        with i2:
            if active_phase_number == 2:
                metric_card("Phase 1 passed at", phase1_passed_at or "—", "Phase 2 starts after this time")
            else:
                metric_card("Current phase passed at", "—", "Only shown after the active phase passes")
        with i3: metric_card("Last closed", last_closed_at or "—", "Most recent resolved A+/A trade")
        with i4: metric_card("Closed / Open", f"{closed_count} / {open_count}", "A+/A trades only")
        with i5: metric_card("Max drawdown", f"${max_drawdown_cash:,.2f}", f"{max_drawdown_pct:.2f}% from peak")

        st.markdown("<div class='section-gap'></div>", unsafe_allow_html=True)
        best_session_info = prop_sim.get("best_session", {}) if isinstance(prop_sim, dict) else {}
        bs1, bs2, bs3 = st.columns(3)
        session_label = str(best_session_info.get("best_session", "All sessions"))
        sample_note = f"{int(best_session_info.get('trade_count', 0) or 0)} A/A+ trades"
        if not bool(best_session_info.get("sample_ready", False)):
            sample_note += f" · minimum {PROP_MIN_SESSION_TRADES} required"
        with bs1: metric_card("Best trading session", session_label, sample_note)
        with bs2: metric_card("Session profit factor", f"{float(best_session_info.get('profit_factor', 0.0) or 0.0):.2f}", "A/A+ closed trades only")
        with bs3: metric_card("Session win rate", f"{float(best_session_info.get('win_rate', 0.0) or 0.0):.2f}%", "Used for prop trade filter")

        st.markdown("<div class='section-gap'></div>", unsafe_allow_html=True)
        p1, p2, p3 = st.columns(3)
        with p1: metric_card("Pass probability", f"{mc['pass_pct']:.2f}%", f"From current equity · {mc['sample_size']} closed")
        with p2: metric_card("Breach probability", f"{mc['fail_pct']:.2f}%", "Within next 60 simulated trades")
        with p3: metric_card("Unresolved", f"{mc['unresolved_pct']:.2f}%", "Neither hit in 60 trades")
        if mc["used_placeholder"]:
            st.caption("Fewer than 10 real closed A+/A trades exist, so this uses a conservative placeholder R-distribution until more trade history is available.")

        st.markdown("<div class='section-gap'></div>", unsafe_allow_html=True)
        status_line = f"<b>{html.escape(current_phase_status)}</b> · {html.escape(active_phase_name)} progress to {html.escape(active_target_label)} target: {progress_to_target*100:.0f}%"
        if fail_reason:
            status_line += f" · {html.escape(fail_reason)}"
            if breach_date:
                status_line += f" on {html.escape(breach_date)}"
        st.markdown(f"<div class='compact-card'>{status_line}</div>", unsafe_allow_html=True)
        st.progress(progress_to_target)

        if status == "FAILED":
            st.error("This challenge failed because the selected timeframe/watchlist breached a prop-firm loss rule. The balance can still be above $10,000 and fail if one trading day loses more than $500.")
        elif active_phase_number == 2:
            st.success("Phase 1 has passed. The account is now in Phase 2 verification and will archive as a full challenge pass once the +$500 Phase 2 target is reached.")

        st.markdown("<div class='section-gap'></div>", unsafe_allow_html=True)
        st.subheader("FTMO rule coverage")
        r1, r2, r3 = st.columns(3)
        with r1:
            metric_card("Phase 1 Challenge", phase1.get("status", "ACTIVE"), "Target +$1,000")
        with r2:
            metric_card("Phase 2 Verification", phase2.get("status", "LOCKED"), "Target +$500")
        with r3:
            metric_card("Funded Account", funded_status, "Unlimited target · 90% split")

        st.markdown("<div class='section-gap'></div>", unsafe_allow_html=True)
        rule_rows = [
            {"Rule": "Profit Target", "Phase 1": "$1,000", "Phase 2": "$500", "Funded Account": "Unlimited"},
            {"Rule": "Max Daily Loss", "Phase 1": "$500", "Phase 2": "$500", "Funded Account": "$500"},
            {"Rule": "Max Loss / Max Drawdown", "Phase 1": "$1,000", "Phase 2": "$1,000", "Funded Account": "$1,000"},
            {"Rule": "Min Trading Days", "Phase 1": "4 days", "Phase 2": "4 days", "Funded Account": "Unlimited"},
            {"Rule": "Trading Period", "Phase 1": "Unlimited", "Phase 2": "Unlimited", "Funded Account": "Unlimited"},
            {"Rule": "Refund", "Phase 1": "—", "Phase 2": "—", "Funded Account": "Yes · 100%"},
            {"Rule": "Rewards", "Phase 1": "—", "Phase 2": "—", "Funded Account": "Up to 90% of profit"},
        ]
        render_benzino_aggrid(
            pd.DataFrame(rule_rows),
            key="ftmo_rules_matrix",
            height=300,
            page_size=10,
            pinned=["Rule"],
            enable_search=False,
        )

        st.markdown("<div class='section-gap'></div>", unsafe_allow_html=True)
        st.subheader("Phase analytics")
        st.markdown("<div style='height:12px;'></div>", unsafe_allow_html=True)

        def _money(v) -> str:
            try:
                return f"${float(v):,.2f}"
            except Exception:
                return "$0.00"

        def _pct(v) -> str:
            try:
                return f"{float(v):,.2f}%"
            except Exception:
                return "0.00%"

        phase_rows = []
        for ph in [phase1, phase2]:
            phase_rows.append({
                "Phase": ph.get("phase", ""),
                "Status": ph.get("status", ""),
                "Started": ph.get("start_date", ""),
                "Passed On": ph.get("pass_date", ""),
                "Breach Date": ph.get("breach_date", ""),
                "Breach Reason": ph.get("breach_reason", ""),
                "Equity": _money(ph.get("equity", starting)),
                "P/L": _money(ph.get("pnl", 0.0)),
                "ROI %": _pct(ph.get("roi_pct", 0.0)),
                "Progress %": _pct(float(ph.get("progress", 0.0) or 0.0) * 100),
                "Trading Days": ph.get("trading_days", 0),
                "Closed Trades": ph.get("closed_trades", 0),
                "Best Day": _money(ph.get("best_day", 0.0)),
                "Worst Day": _money(ph.get("worst_day", 0.0)),
                "Max Drawdown": _money(ph.get("max_drawdown_cash", 0.0)),
                "Max DD %": _pct(ph.get("max_drawdown_pct", 0.0)),
            })
        phase_rows.append({
            "Phase": "Funded Account",
            "Status": funded_status,
            "Started": "After Phase 2 passes" if funded_status == "LOCKED" else phase2.get("pass_date", ""),
            "Passed On": "—",
            "Breach Date": "",
            "Breach Reason": funded_note,
            "Equity": _money(phase2.get("equity", starting) if funded_status == "ACTIVE" else starting),
            "P/L": _money(0.0),
            "ROI %": _pct(0.0),
            "Progress %": _pct(0.0),
            "Trading Days": 0,
            "Closed Trades": 0,
            "Best Day": _money(0.0),
            "Worst Day": _money(0.0),
            "Max Drawdown": _money(0.0),
            "Max DD %": _pct(0.0),
        })
        phase_view = pd.DataFrame(phase_rows)
        render_benzino_aggrid(
            phase_view,
            key="ftmo_phase_analytics",
            height=260,
            page_size=10,
            pinned=["Phase", "Status"],
            badge_cols={"Status": "status"},
            numeric_cols_right=["Trading Days", "Closed Trades"],
            enable_search=False,
            show_status_filter=False,
        )

        st.markdown("<div class='section-gap'></div>", unsafe_allow_html=True)
        st.subheader("Closed A+/A trades")
        all_closed_view_source = prop_all_replay if 'prop_all_replay' in locals() and prop_all_replay is not None and not prop_all_replay.empty else prop_closed
        if all_closed_view_source is None or all_closed_view_source.empty:
            st.info("No A+/A trades have closed yet for this user, watchlist, and selected timeframe.")
        else:
            view = all_closed_view_source.copy()
            if "prop_event_time" in view.columns:
                view["closed_at"] = view["prop_event_time"].apply(fmt_nairobi)
            cols = ["closed_at", "asset", "timeframe", "signal", "grade", "status", "outcome", "r_multiple", "pnl_cash", "balance_after", "exit_reason", "entry", "sl", "tp"]

            closed_trade_table = prepare_signal_table(
                view[[c for c in cols if c in view.columns]].sort_values("closed_at", ascending=False).head(300)
            )
            closed_trade_table = closed_trade_table.rename(columns={
                "closed_at": "Closed At",
                "pnl_cash": "P/L Cash",
                "balance_after": "Balance After",
            })

            for money_col in ["P/L Cash", "Balance After"]:
                if money_col in closed_trade_table.columns:
                    closed_trade_table[money_col] = pd.to_numeric(closed_trade_table[money_col], errors="coerce").apply(
                        lambda x: "—" if pd.isna(x) else f"${x:,.2f}"
                    )

            closed_trade_order = [
                "Asset", "Signal", "Grade", "Status", "Outcome", "R Multiple", "Timeframe",
                "Closed At", "P/L Cash", "Balance After", "Exit Reason", "Entry", "SL", "TP"
            ]
            closed_trade_table = closed_trade_table[[c for c in closed_trade_order if c in closed_trade_table.columns] + [c for c in closed_trade_table.columns if c not in closed_trade_order]]

            render_benzino_aggrid(
                closed_trade_table,
                key="challenge_closed_trades",
                height=420,
                page_size=10,
                pinned=["Asset", "Signal", "Grade"],
                badge_cols={"Signal":"signal", "Grade":"grade", "Status":"status", "Outcome":"outcome"},
                numeric_cols_right=["R Multiple", "Entry", "SL", "TP"],
                show_status_filter=False,
            )

            st.markdown("**Challenge outcomes**")
            outcome_source = load_prop_challenge_history(username, challenge_tf, limit=1000)
            if outcome_source is None or outcome_source.empty:
                outcome_source = pd.DataFrame(prop_sim.get("history", []))
            if outcome_source is None or outcome_source.empty:
                st.info("No completed challenges yet. The wins/losses visual will appear once a challenge is passed or failed.")
            else:
                outcome_df = outcome_source.copy()
                outcome_df["Result"] = outcome_df.get("status", pd.Series(dtype=str)).astype(str).str.upper()
                outcome_df = outcome_df[outcome_df["Result"].isin(["PASSED", "FAILED"])]
                if outcome_df.empty:
                    st.info("No completed passed or failed challenges yet.")
                else:
                    counts = (
                        outcome_df["Result"]
                        .value_counts()
                        .reindex(["PASSED", "FAILED"], fill_value=0)
                        .reset_index()
                    )
                    counts.columns = ["Result", "Challenges"]
                    total_challenges = int(counts["Challenges"].sum())
                    counts["Share"] = counts["Challenges"].apply(lambda x: f"{(float(x) / total_challenges * 100):.1f}%" if total_challenges else "0.0%")
                    counts["Label"] = counts.apply(lambda r: f"{int(r['Challenges'])} · {r['Share']}", axis=1)
                    fig = px.bar(
                        counts,
                        x="Result",
                        y="Challenges",
                        text="Label",
                        title=f"Passed vs failed challenges · Total {total_challenges}",
                    )
                    fig.update_traces(textposition="outside", cliponaxis=False)
                    fig.update_layout(
                        height=360,
                        margin=dict(t=60, b=30, l=20, r=20),
                        yaxis_title="Number of challenges",
                        xaxis_title="Challenge result",
                        showlegend=False,
                    )
                    st.plotly_chart(fig, use_container_width=True)

            if not day_summary.empty:
                st.markdown("**Daily challenge ledger · all simulated challenges**")
                daily_view = day_summary.copy()

                # Keep the ledger human-logical: latest challenge first, latest
                # day first, and where Phase 1 and Phase 2 share the same day,
                # show Phase 2 first because it happened later in the replay.
                daily_view["__challenge_no"] = daily_view["Challenge"].astype(str).str.replace("#", "", regex=False)
                daily_view["__challenge_no"] = pd.to_numeric(daily_view["__challenge_no"], errors="coerce").fillna(-1).astype(int)
                daily_view["__phase_order"] = daily_view["Phase"].astype(str).str.extract(r"(\d+)")[0]
                daily_view["__phase_order"] = pd.to_numeric(daily_view["__phase_order"], errors="coerce").fillna(0).astype(int)
                daily_view["__day_sort"] = pd.to_datetime(daily_view["Day"], errors="coerce")

                daily_view = daily_view.sort_values(
                    ["__challenge_no", "__day_sort", "__phase_order"],
                    ascending=[False, False, False],
                    kind="mergesort",
                )

                if "Day" in daily_view.columns:
                    daily_view["Day"] = pd.to_datetime(daily_view["Day"], errors="coerce").dt.strftime("%Y-%m-%d")

                if "Challenge" in daily_view.columns:
                    daily_challenges = sorted(
                        [str(x) for x in daily_view["Challenge"].dropna().unique()],
                        key=lambda x: int(str(x).replace("#", "")) if str(x).replace("#", "").isdigit() else -1,
                        reverse=True,
                    )
                    selected_daily_challenge = st.selectbox(
                        "Filter daily ledger by challenge",
                        ["All"] + daily_challenges,
                        key=f"daily_challenge_filter_{challenge_tf}",
                    )
                    if selected_daily_challenge != "All":
                        daily_view = daily_view[daily_view["Challenge"].astype(str) == selected_daily_challenge].copy()

                daily_view = daily_view.drop(columns=["__challenge_no", "__phase_order", "__day_sort"], errors="ignore")

                # Column order: keep the key result flags immediately after Daily P/L,
                # then show the balances as properly formatted dollar amounts.
                preferred_daily_cols = [
                    "Challenge", "Phase", "Day", "Daily P/L", "Day Result", "Target Hit",
                    "Trades", "Opening Balance", "Closing Balance", "Intraday Low",
                    "Daily Loss Floor", "Phase Target", "Daily Breach",
                ]
                daily_view = daily_view[[c for c in preferred_daily_cols if c in daily_view.columns]]

                currency_cols = ["Daily P/L", "Opening Balance", "Closing Balance", "Intraday Low", "Daily Loss Floor", "Phase Target"]
                for c in currency_cols:
                    if c in daily_view.columns:
                        daily_view[c] = pd.to_numeric(daily_view[c], errors="coerce").apply(
                            lambda x: "—" if pd.isna(x) else f"${x:,.2f}"
                        )
                if "Trades" in daily_view.columns:
                    daily_view["Trades"] = pd.to_numeric(daily_view["Trades"], errors="coerce").apply(
                        lambda x: "—" if pd.isna(x) else f"{int(x):,}"
                    )

                render_benzino_aggrid(
                    daily_view,
                    key="challenge_daily_loss_check",
                    height=300,
                    page_size=10,
                    pinned=["Challenge", "Phase", "Day"],
                    badge_cols={"Daily Breach":"status", "Target Hit":"status", "Day Result":"outcome"},
                    numeric_cols_right=[],
                    enable_search=False,
                    show_status_filter=False,
                )


        st.markdown("**Challenge review history**")
        history_view = load_prop_challenge_history(username, challenge_tf, limit=100)
        if not history_view.empty:
            history_view = history_view.copy()
            history_view["Timeframe"] = challenge_tf
            history_view["Challenge"] = history_view["challenge_number"].apply(lambda x: f"#{int(x)}" if pd.notna(x) else "—")
            def _phase1_label(row):
                if bool(row.get("phase_1_passed", False)):
                    return "PASSED"
                return "FAILED" if str(row.get("status", "")).upper() == "FAILED" else "ACTIVE"

            def _phase2_label(row):
                if bool(row.get("phase_2_passed", False)):
                    return "PASSED"
                if bool(row.get("phase_1_passed", False)) and str(row.get("status", "")).upper() == "FAILED":
                    return "FAILED"
                return "LOCKED"

            history_view["Phase 1"] = history_view.apply(_phase1_label, axis=1)
            history_view["Phase 2"] = history_view.apply(_phase2_label, axis=1)
            history_view["Started"] = history_view["started_at"].apply(fmt_nairobi)
            history_view["Finished"] = history_view["finished_at"].apply(fmt_nairobi)
            def _fmt_usd(value, signed: bool = False) -> str:
                try:
                    if pd.isna(value):
                        return "—"
                    v = float(value)
                    if not np.isfinite(v):
                        return "—"
                    return f"${v:+,.2f}" if signed else f"${v:,.2f}"
                except Exception:
                    return "—"

            history_view["Starting Balance"] = pd.to_numeric(history_view["starting_balance"], errors="coerce").apply(_fmt_usd)
            history_view["Ending Balance"] = pd.to_numeric(history_view["ending_balance"], errors="coerce").apply(_fmt_usd)
            history_view["Realised P/L"] = pd.to_numeric(history_view["realised_pnl"], errors="coerce").apply(lambda x: _fmt_usd(x, signed=True))
            history_view["Win Rate %"] = pd.to_numeric(history_view["win_rate"], errors="coerce")
            history_view["Trading Days"] = pd.to_numeric(history_view["trading_days"], errors="coerce").fillna(0).astype(int)
            history_view["Failure Reason"] = history_view.get("failure_reason", "").fillna("").astype(str) if "failure_reason" in history_view.columns else ""
            display_cols = [
                "Challenge", "Timeframe", "Phase 1", "Phase 2", "Failure Reason", "Trading Days",
                "Started", "Finished", "Starting Balance", "Ending Balance", "Realised P/L", "Win Rate %",
            ]
            history_display = history_view[[c for c in display_cols if c in history_view.columns]].copy()

            history_filter_col1, history_filter_col2 = st.columns([1, 1])
            with history_filter_col1:
                if "Challenge" in history_display.columns:
                    history_challenges = sorted(
                        [str(x) for x in history_display["Challenge"].dropna().unique()],
                        key=lambda x: int(str(x).replace("#", "")) if str(x).replace("#", "").isdigit() else -1,
                        reverse=True,
                    )
                    selected_history_challenge = st.selectbox(
                        "Filter challenge history by challenge",
                        ["All"] + history_challenges,
                        key=f"history_challenge_filter_{challenge_tf}",
                    )
                    if selected_history_challenge != "All":
                        history_display = history_display[history_display["Challenge"].astype(str) == selected_history_challenge].copy()
            with history_filter_col2:
                selected_history_result = st.selectbox(
                    "Filter challenge history by result",
                    ["All", "Passed", "Failed"],
                    key=f"history_result_filter_{challenge_tf}",
                )
                if selected_history_result == "Passed":
                    history_display = history_display[
                        (history_display.get("Phase 1", "").astype(str).str.upper() == "PASSED")
                        & (history_display.get("Phase 2", "").astype(str).str.upper() == "PASSED")
                    ].copy()
                elif selected_history_result == "Failed":
                    history_display = history_display[
                        ~((history_display.get("Phase 1", "").astype(str).str.upper() == "PASSED")
                          & (history_display.get("Phase 2", "").astype(str).str.upper() == "PASSED"))
                    ].copy()
            render_benzino_aggrid(
                history_display,
                key=f"challenge_review_history_{challenge_tf}",
                height=320,
                page_size=10,
                pinned=["Challenge", "Timeframe", "Phase 1", "Phase 2"],
                badge_cols={"Phase 1": "status", "Phase 2": "status"},
                numeric_cols_right=["Starting Balance", "Ending Balance", "Realised P/L", "Win Rate %", "Trading Days"],
                enable_search=False,
                show_status_filter=False,
            )
        else:
            st.info("No completed prop-firm challenges have been archived yet. Passed or failed attempts will appear here automatically.")

    with t4:
        st.caption("All signals the scanner blocked from being journaled as real trades. Includes two types: (1) directional ideas (BUY/SELL) where the grade was too weak or R:R too thin — these are hypothetically tracked against TP/SL/expiry to see if they'd have worked. (2) HOLD rows where the systems genuinely split with no directional consensus — these have no hypothetical outcome since there's no entry thesis, but they're recorded so you can see how often the scanner truly sees no edge.")
        no_trades_directional = no_trades[no_trades["signal"].astype(str).str.upper().isin(["BUY", "SELL"])].copy() if not no_trades.empty else pd.DataFrame()
        no_trades_hold = no_trades[no_trades["signal"].astype(str).str.upper().eq("HOLD")].copy() if not no_trades.empty else pd.DataFrame()
        # Count every resolved shadow row, including legacy HOLD rows that the
        # updated scanner backfills into a research-only BUY/SELL plan. This is
        # the full No Trade research ledger, not just brand-new directional rows.
        no_trades_resolved = (
            no_trades[
                no_trades["shadow_outcome"].notna()
                & no_trades["shadow_outcome"].astype(str).str.strip().ne("")
            ].copy()
            if "shadow_outcome" in no_trades.columns and not no_trades.empty
            else pd.DataFrame()
        )
        # No Trade research dashboard: simulate a separate account that takes
        # every rejected/blocked idea as a hypothetical trade using the user's
        # selected account size and risk settings. Only resolved shadow rows are
        # included in the curve because unresolved ideas have no final R yet.
        shadow_starting_balance = float(settings.get("account_size") or 10000.0)
        shadow_risk_pct = float(settings.get("risk_pct") or 1.0) / 100.0
        shadow_risk_cash = shadow_starting_balance * shadow_risk_pct

        shadow_curve = no_trades_resolved.copy() if not no_trades_resolved.empty else pd.DataFrame()
        if not shadow_curve.empty:
            shadow_curve["shadow_closed_at_sort"] = pd.to_datetime(
                shadow_curve.get("shadow_closed_at", shadow_curve.get("created_at")),
                errors="coerce", utc=True,
            )
            shadow_curve["created_at_sort"] = pd.to_datetime(shadow_curve.get("created_at"), errors="coerce", utc=True)
            shadow_curve["curve_time"] = shadow_curve["shadow_closed_at_sort"].fillna(shadow_curve["created_at_sort"])
            shadow_curve["shadow_r_multiple"] = pd.to_numeric(shadow_curve["shadow_r_multiple"], errors="coerce")
            shadow_curve = shadow_curve.dropna(subset=["curve_time", "shadow_r_multiple"]).sort_values("curve_time")
            shadow_curve["Hypothetical P/L"] = shadow_curve["shadow_r_multiple"] * shadow_risk_cash
            shadow_curve["Balance"] = shadow_starting_balance + shadow_curve["Hypothetical P/L"].cumsum()

        resolved_count = int(len(shadow_curve)) if not shadow_curve.empty else 0
        total_shadow_pnl = float(shadow_curve["Hypothetical P/L"].sum()) if resolved_count else 0.0
        shadow_balance = shadow_starting_balance + total_shadow_pnl
        hyp_win_rate = 0.0
        hyp_avg_r = 0.0
        if resolved_count:
            hyp_win_rate = float((shadow_curve["shadow_r_multiple"] > 0).mean() * 100)
            hyp_avg_r = float(shadow_curve["shadow_r_multiple"].mean())

        h1, h2, h3, h4 = st.columns(4)
        with h1: metric_card("No Trade balance", f"${shadow_balance:,.2f}", f"Start ${shadow_starting_balance:,.0f} · risk {shadow_risk_pct*100:.2f}%")
        with h2: metric_card("No Trade P/L", f"${total_shadow_pnl:+,.2f}", "If every resolved blocked idea was taken")
        with h3: metric_card("Resolved shadow trades", f"{resolved_count:,}", f"From {len(no_trades):,} total shadow rows")
        with h4: metric_card("No Trade win rate", f"{hyp_win_rate:.2f}%", f"Average {hyp_avg_r:+.2f}R")

        st.markdown("<div class='section-gap'></div>", unsafe_allow_html=True)
        st.subheader("No Trade hypothetical balance curve")
        if resolved_count:
            fig = go.Figure()
            fig.add_trace(go.Scatter(
                x=shadow_curve["curve_time"],
                y=shadow_curve["Balance"],
                mode="lines",
                name="No Trade only",
                hovertemplate="%{x|%Y-%m-%d %H:%M}<br>Balance: $%{y:,.2f}<extra></extra>",
            ))
            fig.update_layout(
                height=420,
                margin=dict(t=20, b=45, l=20, r=20),
                paper_bgcolor="#0E1117",
                plot_bgcolor="#0E1117",
                font=dict(color="#E8EDF2"),
                xaxis_title="Resolved at",
                yaxis_title="Hypothetical balance",
                legend_title_text="",
                hovermode="x unified",
            )
            fig.update_xaxes(gridcolor="rgba(255,255,255,0.12)", zerolinecolor="rgba(255,255,255,0.12)")
            fig.update_yaxes(tickprefix="$", tickformat=",.0f", gridcolor="rgba(255,255,255,0.12)", zerolinecolor="rgba(255,255,255,0.12)")
            with st.container(border=True):
                st.plotly_chart(fig, use_container_width=True, config={"displayModeBar": False})
            st.markdown(
                "<div class='grey-note'>This curve is research-only. It uses resolved SHADOW rows from Supabase, "
                "the selected timeframe/watchlist scope, and your selected account/risk settings. It is excluded from "
                "User Journal and Prop Firm performance.</div>",
                unsafe_allow_html=True,
            )
        else:
            st.info("No resolved No Trade shadow outcomes yet. The updated scanner will now backfill and resolve the historical SHADOW / NO TRADE rows from Supabase, including legacy HOLD rows that previously had Entry = SL = TP.")

        st.markdown("<div class='section-gap'></div>", unsafe_allow_html=True)
        no_trade_cols = [
            "created_at", "created_at_eat", "asset", "timeframe", "signal", "grade", "status",
            "entry", "sl", "tp", "rr", "confidence", "edge_score", "shadow_outcome",
            "shadow_r_multiple", "shadow_exit_price", "reason", "session"
        ]
        no_trade_table = no_trades[[c for c in no_trade_cols if c in no_trades.columns]].copy() if not no_trades.empty else pd.DataFrame(columns=[c for c in no_trade_cols if c in no_trades.columns])
        if not no_trade_table.empty and "created_at" in no_trades.columns:
            no_trade_table = no_trade_table.loc[no_trades.sort_values("created_at", ascending=False).index.intersection(no_trade_table.index)]

        no_trade_display = prepare_signal_table(no_trade_table, limit=10000)
        if not no_trade_display.empty:
            # The database status for No Trade rows is intentionally always SHADOW,
            # so the table uses a more useful research status instead: whether the
            # hypothetical trade has been resolved by TP/SL/expiry yet.
            hyp_reason = no_trade_display.get("Hypothetical Outcome", pd.Series("", index=no_trade_display.index)).astype(str).str.upper().str.strip()
            hyp_r = pd.to_numeric(no_trade_display.get("Hypothetical R", pd.Series(np.nan, index=no_trade_display.index)), errors="coerce")

            no_trade_display["Status"] = np.where(hyp_reason.ne("") & hyp_reason.ne("NAN"), "RESOLVED", "OPEN")
            no_trade_display["Outcome"] = np.select(
                [
                    hyp_r > 0,
                    hyp_r < 0,
                    hyp_r.eq(0) & hyp_reason.ne("") & hyp_reason.ne("NAN"),
                    hyp_reason.str.contains("TP", na=False),
                    hyp_reason.str.contains("SL", na=False),
                ],
                ["WIN", "LOSS", "BREAKEVEN", "WIN", "LOSS"],
                default="OPEN",
            )

            # Place Status and Outcome immediately after Grade, matching the User Journal layout.
            no_trade_order = [
                "Asset", "Signal", "Grade", "Status", "Outcome", "Age", "Entry", "SL", "TP",
                "RR", "Confidence", "Decayed Confidence", "Edge Score", "Hypothetical Outcome",
                "Hypothetical R", "Hypothetical Exit", "Session", "Reason", "Ticker", "Timeframe",
                "Created At", "Signal ID", "Scan Owner"
            ]
            no_trade_display = no_trade_display[[c for c in no_trade_order if c in no_trade_display.columns] + [c for c in no_trade_display.columns if c not in no_trade_order]]

            st.markdown("<div class='benzino-panel-title'>Research Queue</div>", unsafe_allow_html=True)
            f1, f2, f3 = st.columns([0.22, 0.22, 0.56], vertical_alignment="center")
            with f1:
                status_options = ["All"] + sorted([v for v in no_trade_display["Status"].dropna().astype(str).unique() if v])
                selected_research_status = st.selectbox("Research status", status_options, key="no_trade_research_status_filter")
            with f2:
                outcome_options = ["All"] + sorted([v for v in no_trade_display["Outcome"].dropna().astype(str).unique() if v])
                selected_research_outcome = st.selectbox("Outcome", outcome_options, key="no_trade_research_outcome_filter")
            with f3:
                st.markdown("<div class='grey-note' style='margin-top:4px;'>Filter No Trade ideas by whether the hypothetical setup is still open or resolved, and by whether the resolved idea won or lost.</div>", unsafe_allow_html=True)

            if selected_research_status != "All":
                no_trade_display = no_trade_display[no_trade_display["Status"].astype(str).eq(selected_research_status)].copy()
            if selected_research_outcome != "All":
                no_trade_display = no_trade_display[no_trade_display["Outcome"].astype(str).eq(selected_research_outcome)].copy()

        render_benzino_aggrid(
            no_trade_display,
            key="no_trade_tracker",
            title=None,
            height=560,
            page_size=100,
            pinned=["Asset", "Signal", "Grade", "Status", "Outcome"],
            badge_cols={"Signal":"signal", "Grade":"grade", "Status":"status", "Outcome":"outcome", "Hypothetical Outcome":"status"},
            numeric_cols_right=["Entry", "SL", "TP", "Confidence", "Decayed Confidence", "RR", "Edge Score", "Hypothetical R", "Hypothetical Exit", "R Multiple"],
            show_status_filter=False,
        )

    with t5:
        st.subheader("Coach AI")
        st.caption("Coach AI reviews your journal patterns and turns trade history into practical behaviour, risk, and execution guidance.")
        prop_state = load_prop_firm_state()
        prop_status = str(prop_state.get("status") or "ACTIVE").upper()

        resolved = closed_resolved_trades(closed_trades) if not closed_trades.empty else pd.DataFrame()
        coach_parts = []
        if prop_status == "FAILED":
            coach_parts.append(
                "The official prop challenge has failed, which changes the coaching priority immediately. The right response is not to look for the next A+ entry to recover the account; it is to pause, review the ledger, and understand whether the failure came from trade quality, overexposure, daily-loss pressure, or taking too many correlated opportunities. Continuing to risk capital after a failed challenge would defeat the purpose of having the grading system in the first place."
            )
        elif prop_status == "PASSED":
            coach_parts.append(
                "The official prop challenge has reached its pass condition. Coach AI would treat this as a capital-preservation moment rather than an invitation to keep pressing. The system has done its job on this ledger, so the better decision is to lock in the result and let the next challenge start with a clean risk profile."
            )
        else:
            try:
                roi_now = (float(prop_state.get("current_equity") or 0) / float(prop_state.get("starting_balance") or 1) - 1) * 100
            except Exception:
                roi_now = 0.0
            coach_parts.append(
                f"The official prop challenge is still active and currently sits at {roi_now:+.2f}% toward the target. That means the system is still in decision-making mode, not recovery mode or celebration mode. The main coaching priority is to protect the ledger from unnecessary drawdown while allowing only the strongest graded opportunities to continue proving themselves."
            )

        if len(closed_trades) < 10 or resolved.empty:
            coach_parts.append(
                f"Coach AI currently has {len(closed_trades)} closed journal trade(s) to study. That is enough to describe individual trades, but not enough to make strong claims about the best asset, best session, or worst recurring mistake. The correct behaviour at this stage is patience: keep collecting outcomes, avoid changing the rules too early, and pay close attention to whether open exposure is growing faster than evidence quality."
            )
        else:
            asset_perf = resolved.groupby("asset").apply(
                lambda g: pd.Series({
                    "win_rate": win_rate_group(g) / 100,
                    "trades": len(closed_resolved_trades(g)),
                    "avg_r": pd.to_numeric(g.get("r_multiple", pd.Series(dtype=float)), errors="coerce").mean(),
                }), include_groups=False
            ).reset_index()
            supported_assets = asset_perf[asset_perf["trades"] >= 5].copy()
            if not supported_assets.empty:
                best = supported_assets.sort_values(["win_rate", "avg_r"], ascending=False).iloc[0]
                worst = supported_assets.sort_values(["win_rate", "avg_r"], ascending=True).iloc[0]
                coach_parts.append(
                    f"The strongest supported asset in the current sample is {best['asset']}. It has {int(best['trades'])} closed trades, a {best['win_rate']*100:.2f}% win rate, and an average result of {best['avg_r']:+.2f}R. Coach AI would not treat this as a lucky label on a chart; it suggests the engine's confirmation model is currently reading that market structure better than others. When similar grades compete for attention, this asset deserves priority until the sample changes."
                )
                coach_parts.append(
                    f"The weakest supported area is {worst['asset']}, with {int(worst['trades'])} closed trades, a {worst['win_rate']*100:.2f}% win rate, and an average result of {worst['avg_r']:+.2f}R. The recommendation is not to ban the asset, but to demand stronger evidence before trusting it: cleaner multi-timeframe alignment, less stretched momentum, and better risk placement. Until performance improves, this area should be treated as research fuel rather than a prop-firm priority."
                )
            if "session" in resolved.columns:
                session_perf = resolved.groupby("session").apply(
                    lambda g: pd.Series({
                        "win_rate": win_rate_group(g) / 100,
                        "trades": len(closed_resolved_trades(g)),
                        "avg_r": pd.to_numeric(g.get("r_multiple", pd.Series(dtype=float)), errors="coerce").mean(),
                    }), include_groups=False
                ).reset_index()
                session_perf = session_perf[session_perf["trades"] >= 5].sort_values(["win_rate", "avg_r"], ascending=False)
                if not session_perf.empty:
                    srow = session_perf.iloc[0]
                    coach_parts.append(
                        f"Session behaviour also matters. The best supported session is {srow['session']}, with {int(srow['trades'])} closed trades and a {srow['win_rate']*100:.2f}% win rate. That suggests the system is finding cleaner follow-through during that window. When two trades have similar grades, Coach AI would prefer the one appearing in the stronger session, because execution environment can be the difference between a good idea and a good fill."
                    )

        if len(open_trades) >= 3:
            coach_parts.append(
                f"Current exposure is elevated because {len(open_trades)} trades are still open. The coaching message here is simple: let some risk resolve before adding more. This matters even more in prop-firm mode, where one good setup can be ruined by stacking too many positions into the same market shock."
            )
        a_count = len(open_trades[open_trades["grade"].isin(["A+", "A"])]) if not open_trades.empty and "grade" in open_trades.columns else 0
        b_count = len(open_trades[open_trades["grade"].isin(["B", "C"])]) if not open_trades.empty and "grade" in open_trades.columns else 0
        coach_parts.append(
            f"The current open-quality mix is {a_count} A+/A trade(s) and {b_count} B/C trade(s). The practical instruction is to keep prop-firm capital reserved for A+/A setups and let B/C trades remain journal-learning data. The goal is not to take every signal; it is to learn which signals deserve capital when the cost of being wrong is highest."
        )
        render_ai_card("Trade Management Guidance", "\n\n".join(coach_parts))

    with t6:
        st.subheader("Explain AI")
        st.caption("Closed outcomes are the main lesson source. Select a trade from the table to open its full Explain AI lesson. Lessons are saved in the explain_ai_lessons table.")

        if closed_trades.empty:
            st.info("No closed trades yet. Explain AI will populate once TP, SL, or expiry outcomes are recorded.")
        else:
            review_queue = closed_trades.sort_values("created_at", ascending=False).head(200).copy()
            review_display = prepare_signal_table(review_queue, limit=200)
            # Preserve the real DB signal_id for row selection; prepare_signal_table may display the public Benzino ID.
            review_display["Raw Signal ID"] = review_queue.reset_index(drop=True)["signal_id"].astype(str).values
            preferred_cols = ["Asset", "Timeframe", "Signal", "Grade", "Status", "Outcome", "R Multiple", "Entry", "SL", "TP", "Session", "Created At", "Raw Signal ID"]
            review_display = review_display[[c for c in preferred_cols if c in review_display.columns] + [c for c in review_display.columns if c not in preferred_cols and c != "Review Case"]]

            title_col, sig_col, grade_col, status_col, search_col = st.columns([4.0, 1.1, 1.1, 1.25, 2.2], vertical_alignment="center")
            with title_col:
                st.markdown("<div class='benzino-panel-title'>Closed Trade Lessons</div>", unsafe_allow_html=True)
            with sig_col:
                explain_signal_filter = st.selectbox("Signal", ["All", "BUY", "SELL"], label_visibility="collapsed", key="explain_review_signal_filter")
            with grade_col:
                explain_grade_filter = st.selectbox("Grade", ["All", "A+", "A", "B", "C"], label_visibility="collapsed", key="explain_review_grade_filter")
            with status_col:
                _status_options = ["All"] + sorted(review_display["Status"].dropna().astype(str).unique().tolist()) if "Status" in review_display.columns else ["All"]
                explain_status_filter = st.selectbox("Status", _status_options, label_visibility="collapsed", key="explain_review_status_filter")
            with search_col:
                explain_review_search = st.text_input("Search closed trade lessons", placeholder="Search…", label_visibility="collapsed", key="explain_review_search")

            if explain_signal_filter != "All" and "Signal" in review_display.columns:
                review_display = review_display[review_display["Signal"].astype(str).str.upper().str.contains(explain_signal_filter, na=False)]
            if explain_grade_filter != "All" and "Grade" in review_display.columns:
                review_display = review_display[review_display["Grade"].astype(str).str.upper().eq(explain_grade_filter.upper())]
            if explain_status_filter != "All" and "Status" in review_display.columns:
                review_display = review_display[review_display["Status"].astype(str).eq(explain_status_filter)]
            if explain_review_search:
                q = str(explain_review_search).lower().strip()
                review_display = review_display[review_display.astype(str).apply(lambda col: col.str.lower().str.contains(q, na=False)).any(axis=1)]

            st.caption("Select a row to open the lesson window. In AgGrid, double-clicking visually selects the row; in Streamlit's fallback table, use the row selector.")
            selected_sid = ""
            event = st.dataframe(
                review_display.drop(columns=["Raw Signal ID"], errors="ignore"),
                width="stretch",
                hide_index=True,
                selection_mode="single-row",
                on_select="rerun",
                key="explain_ai_closed_trade_table",
            )
            try:
                selected_rows = event.selection.rows
            except Exception:
                selected_rows = []
            if selected_rows:
                idx = selected_rows[0]
                if 0 <= idx < len(review_display):
                    selected_sid = str(review_display.iloc[idx].get("Raw Signal ID") or "")

            if selected_sid:
                row_df = review_queue[review_queue["signal_id"].astype(str).eq(selected_sid)]
                if not row_df.empty:
                    selected_row = row_df.iloc[0].copy()
                    generated_lesson = rich_closed_trade_explanation(selected_row)
                    stored_lesson = load_explain_ai_lesson(selected_sid)
                    lesson_text = stored_lesson or generated_lesson
                    if not stored_lesson:
                        try:
                            save_explain_ai_lesson(selected_sid, str(selected_row.get("scan_owner") or active_username()), generated_lesson)
                        except Exception as exc:
                            st.warning(f"Could not save Explain AI lesson: {exc}")

                    @st.dialog("Closed Trade Lesson", width="large")
                    def _show_closed_lesson():
                        render_ai_card("Closed Trade Lesson", lesson_text)
                        if st.button("Regenerate and save latest lesson", type="primary", key=f"regen_lesson_{selected_sid}"):
                            try:
                                save_explain_ai_lesson(selected_sid, str(selected_row.get("scan_owner") or active_username()), generated_lesson)
                                st.success("Lesson regenerated and saved to explain_ai_lessons.")
                            except Exception as exc:
                                st.error(f"Failed to save lesson: {exc}")
                    _show_closed_lesson()





def user_performance_for_admin(username: str, user_settings: dict | None = None) -> dict:
    """Per-user admin metrics using each user's own watchlist, tracking date and preferred timeframe."""
    settings = DEFAULT_SETTINGS.copy()
    if isinstance(user_settings, dict):
        settings.update(user_settings)

    preferred_tf = str(settings.get("preferred_timeframe") or settings.get("view_timeframe") or "1h")
    settings["view_timeframe"] = preferred_tf

    starting_balance = float(settings.get("account_size", 10000) or 10000)

    result = {
        "win_rate": "0.00%",
        "starting_balance": f"${starting_balance:,.2f}",
        "current_balance": f"${starting_balance:,.2f}",
    }

    try:
        df = load_signals_for_user(username, settings)
        df = apply_timeframe_view(df, settings)
        if df is None or df.empty:
            return result

        df["outcome"] = df.apply(outcome_label, axis=1)
        trades = df[df["grade"].astype(str).isin(VALID_GRADES)].copy()
        perf = compute_user_performance(trades, settings, prop_mode=False)

        closed = trades[trades["outcome"].isin(["WIN", "LOSS", "BREAKEVEN", "CLOSED"])].copy()
        result["win_rate"] = f"{win_rate_from_resolved(closed):.2f}%" if len(closed) else "0.00%"
        result["starting_balance"] = f"${float(perf.get('starting_balance', starting_balance)):,.2f}"
        result["current_balance"] = f"${float(perf.get('current_balance', starting_balance)):,.2f}"
        return result
    except Exception:
        return result


def user_win_rate_for_admin(username: str, user_settings: dict | None = None) -> str:
    """Backward-compatible wrapper."""
    return user_performance_for_admin(username, user_settings).get("win_rate", "0.00%")




def prop_firm_win_rate_for_admin(username: str, timeframe: str = "1h") -> str:
    """Return the user's prop-firm challenge win rate for the admin User Management table.

    Full FTMO challenge pass = Phase 2 passed. This reads the replayed
    prop_challenge_history for that user's preferred timeframe only.
    """
    try:
        scope = prop_challenge_scan_owner(username, timeframe)
        df = read_df(
            """
            SELECT phase_2_passed
            FROM prop_challenge_history
            WHERE scan_owner = %s
            """,
            (scope,),
        )
        if df.empty:
            return "0.00%"
        total = len(df)
        passed = int(pd.Series(df["phase_2_passed"]).fillna(False).astype(bool).sum())
        return f"{(passed / total * 100):.2f}%" if total else "0.00%"
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

                admin_perf_map = {
                    str(u): user_performance_for_admin(str(u), settings_map.get(str(u), {}))
                    for u in all_users["username"].astype(str).tolist()
                }
                all_users["win_rate"] = all_users["username"].astype(str).map(lambda u: admin_perf_map.get(u, {}).get("win_rate", "0.00%"))
                all_users["prop_firm_win_rate"] = all_users["username"].astype(str).map(
                    lambda u: prop_firm_win_rate_for_admin(u, settings_map.get(u, {}).get("preferred_timeframe", "1h"))
                )
                all_users["starting_balance"] = all_users["username"].astype(str).map(lambda u: admin_perf_map.get(u, {}).get("starting_balance", "$0.00"))
                all_users["current_balance"] = all_users["username"].astype(str).map(lambda u: admin_perf_map.get(u, {}).get("current_balance", "$0.00"))

                all_users["tracking_started_at"] = all_users["username"].astype(str).map(lambda u: settings_map.get(u, {}).get("tracking_started_at", ""))
                all_users["telegram_activated"] = all_users["username"].astype(str).map(lambda u: "Yes" if telegram_map.get(u) else "No")
                all_users["created_at"] = all_users["created_at"].apply(fmt_nairobi)
                all_users["tracking_started_at"] = all_users["tracking_started_at"].apply(fmt_nairobi)
                user_cols = ["username", "role", "preferred_timeframe", "win_rate", "prop_firm_win_rate", "watchlist_count", "watchlist", "current_balance", "starting_balance", "account_size", "risk_pct", "leverage", "telegram_activated", "email", "created_at", "tracking_started_at"]
                all_users = all_users[[c for c in user_cols if c in all_users.columns]]
                render_benzino_aggrid(all_users, key="admin_user_management", title="User Management", height=420, page_size=10, pinned=["username"], numeric_cols_right=["watchlist_count", "account_size", "risk_pct", "leverage"], badge_cols={"telegram_activated": "status"})


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
            system_win_rate = win_rate_from_resolved(wl_resolved_all)

            wl_user_df = wl_graded[wl_graded["asset"].astype(str).isin(current_set)].copy()
            wl_resolved_user = wl_user_df[wl_user_df["outcome"].isin(["WIN", "LOSS", "BREAKEVEN", "CLOSED"])].copy()
            user_win_rate = win_rate_from_resolved(wl_resolved_user)

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

        asset_perf: dict = {}
        if wl_system_df is not None and not wl_system_df.empty:
            graded = wl_system_df[wl_system_df["grade"].astype(str).isin(VALID_GRADES)].copy()
            graded["outcome"] = graded.apply(outcome_label, axis=1)
            for asset_key, grp in graded.groupby("asset"):
                resolved = grp[grp["outcome"].isin(["WIN", "LOSS"])]
                wins = (resolved["outcome"] == "WIN").sum()
                total_res = len(resolved)
                avg_r = pd.to_numeric(resolved.get("r_multiple", pd.Series(dtype=float)), errors="coerce").mean() if total_res else float("nan")
                open_cnt = (grp["status"].astype(str).str.upper() == "OPEN").sum()
                best_grade = grp["grade"].value_counts().idxmax() if len(grp) else "—"
                asset_perf[str(asset_key)] = {
                    "win_rate": f"{wins / total_res * 100:.1f}%" if total_res else "—",
                    "total_signals": len(grp),
                    "resolved": total_res,
                    "avg_r": f"{avg_r:+.2f}R" if not (avg_r != avg_r) else "—",
                    "open_trades": open_cnt,
                    "top_grade": best_grade,
                }

        for key, meta in ASSET_UNIVERSE.items():
            perf = asset_perf.get(key, {})
            watchlist_rows.append({
                "Status": "Enabled" if key in current_set else "Disabled",
                "Asset": key,
                "Group": meta.get("group"),
                "Signals": perf.get("total_signals", 0),
                "Resolved": perf.get("resolved", 0),
                "Win Rate": perf.get("win_rate", "—"),
                "Avg R": perf.get("avg_r", "—"),
                "Open": perf.get("open_trades", 0),
                "Top Grade": perf.get("top_grade", "—"),
            })

        render_benzino_aggrid(
            pd.DataFrame(watchlist_rows),
            key="watchlist_editor_table",
            title="Available Assets",
            height=480,
            page_size=15,
            pinned=["Status", "Asset"],
            badge_cols={"Status": "status"},
            numeric_cols_right=["Signals", "Resolved", "Open"],
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