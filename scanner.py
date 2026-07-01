"""
scanner.py — Benzino Institutional-Grade Autonomous Signal Engine
═══════════════════════════════════════════════════════════════════════════════
Runs standalone (no Streamlit) on a 15-minute GitHub Actions cron.

STRATEGY ENGINE — four independent, literature-backed systems vote on direction:
  1. Time-Series Momentum      Moskowitz, Ooi & Pedersen (2012) — AQR / JFE
  2. Donchian/Turtle Breakout  Richard Dennis Turtles, ADX-confirmed
  3. RSI-2 Mean Reversion      Larry Connors — trend-filtered, not pure contrarian
  4. ML Ensemble               LR(20%) + RF(35%) + GB(45%)

Signals are graded A+/A/B/C/NO TRADE by strategy CONFLUENCE, not a single metric.

INSTITUTIONAL BEHAVIOUR:
  - Runs every 15 minutes regardless of who is logged into the Streamlit app.
  - Every grade (A+, A, B, C) is auto-journaled. NO TRADE signals are shadow-
    tracked (saved, never alerted) so the research panel can study what was
    filtered out.
  - A separate FTMO-style prop-firm ledger runs concurrently and only ever
    counts A+ and A trades toward its equity, daily-loss, and max-loss limits.
  - Telegram alerts fire at most once per (asset, timeframe, signal, candle
    close) — true duplicate elimination, not a rolling time window.
  - A new alert for a given (asset, timeframe) slot is blocked until the
    previous open trade in that slot has closed via TP, SL, or expiry.

ENV VARS (GitHub Actions secrets):
  DATABASE_URL, TELEGRAM_BOT_TOKEN, SCAN_OWNER,
  ACCOUNT_SIZE, RISK_PER_TRADE, LEVERAGE,
  MIN_ALERT_EDGE_SCORE, MIN_ALERT_CONFIDENCE_DIST
"""

from __future__ import annotations

import os
import html
import uuid
import time
import statistics
import json
import warnings
import traceback
import math
from datetime import datetime, timezone
from dataclasses import dataclass, field
from urllib.parse import urlsplit, urlunsplit, parse_qsl, urlencode

warnings.filterwarnings("ignore")

import numpy as np
import pandas as pd
import yfinance as yf
import requests

from sklearn.ensemble import RandomForestClassifier, GradientBoostingClassifier
from sklearn.linear_model import LogisticRegression
from sklearn.pipeline import Pipeline
from sklearn.preprocessing import StandardScaler
from sklearn.impute import SimpleImputer

try:
    import psycopg2
    from psycopg2.extras import RealDictCursor
except ImportError:
    psycopg2 = None
    RealDictCursor = None

# ═══════════════════════════════════════════════════════════════════════════════
#  CONFIGURATION
# ═══════════════════════════════════════════════════════════════════════════════

MASTER_WATCHLIST = {
    # Commodities — using spot/CFD-equivalent tickers so prices match TradingView XAUUSD/XAGUSD.
    # GC=F (Gold Futures) and SI=F (Silver Futures) trade $20-50 above spot due to contango;
    # switching to the =X forex-pair form gives prices consistent with broker spot charts.
    "XAUUSD": "XAUUSD=X", "XAGUSD": "XAGUSD=X", "OIL": "CL=F", "BRENT": "BZ=F",
    "NATGAS": "NG=F", "COPPER": "HG=F",
    "EURUSD": "EURUSD=X", "GBPUSD": "GBPUSD=X", "USDJPY": "JPY=X",
    "USDCHF": "CHF=X", "USDCAD": "CAD=X", "AUDUSD": "AUDUSD=X", "NZDUSD": "NZDUSD=X",
    "GBPJPY": "GBPJPY=X", "EURJPY": "EURJPY=X", "AUDJPY": "AUDJPY=X",
    "NZDJPY": "NZDJPY=X", "CADJPY": "CADJPY=X", "CHFJPY": "CHFJPY=X",
    "EURGBP": "EURGBP=X", "EURAUD": "EURAUD=X", "EURNZD": "EURNZD=X",
    "EURCAD": "EURCAD=X", "EURCHF": "EURCHF=X", "GBPAUD": "GBPAUD=X",
    "GBPNZD": "GBPNZD=X", "GBPCAD": "GBPCAD=X", "GBPCHF": "GBPCHF=X",
    "AUDCAD": "AUDCAD=X", "AUDNZD": "AUDNZD=X", "AUDCHF": "AUDCHF=X",
    "NZDCAD": "NZDCAD=X", "NZDCHF": "NZDCHF=X",
    "BTCUSD": "BTC-USD", "ETHUSD": "ETH-USD",
    "SP500": "^GSPC", "NAS100": "^NDX", "DOW30": "^DJI",
    "NVDA": "NVDA", "MU": "MU",
}


def load_user_watchlist(username: str) -> dict[str, str]:
    """
    Load one user's enabled watchlist from Supabase.

    Returns:
        {"XAUUSD": "XAUUSD=X", "BTCUSD": "BTC-USD"}

    If the user has no saved watchlist yet, this returns an empty dict.
    The scanner still scans MASTER_WATCHLIST; this helper is for user-specific
    routing, dashboards, and future per-user Telegram delivery.
    """
    username = str(username or "").strip()
    if not username:
        return {}

    try:
        conn = db_connect()
        with conn.cursor() as cur:
            cur.execute(
                """
                SELECT asset, ticker
                FROM user_watchlists
                WHERE scan_owner = %s
                  AND enabled = TRUE
                ORDER BY asset
                """,
                (username,),
            )
            rows = cur.fetchall()
        conn.close()

        watchlist = {}
        for row in rows:
            asset = str(row.get("asset", "")).strip().upper()
            ticker = str(row.get("ticker", "")).strip()
            if asset and ticker and asset in MASTER_WATCHLIST:
                watchlist[asset] = ticker

        return watchlist

    except Exception as exc:
        print(f"[WARN] Could not load watchlist for {username}: {exc}")
        return {}


def get_all_user_watchlists() -> dict[str, dict[str, str]]:
    """
    Load every enabled user watchlist from Supabase.

    Returns:
        {
            "ben": {"XAUUSD": "XAUUSD=X", "BTCUSD": "BTC-USD"},
            "brother": {"EURUSD": "EURUSD=X"}
        }

    The scanner scans MASTER_WATCHLIST once, then these watchlists can be used
    to decide which users should see each signal.
    """
    try:
        conn = db_connect()
        with conn.cursor() as cur:
            cur.execute(
                """
                SELECT scan_owner, asset, ticker
                FROM user_watchlists
                WHERE enabled = TRUE
                ORDER BY scan_owner, asset
                """
            )
            rows = cur.fetchall()
        conn.close()

        watchlists: dict[str, dict[str, str]] = {}
        for row in rows:
            username = str(row.get("scan_owner", "")).strip()
            asset = str(row.get("asset", "")).strip().upper()
            ticker = str(row.get("ticker", "")).strip()

            if not username or not asset or not ticker:
                continue
            if asset not in MASTER_WATCHLIST:
                continue

            watchlists.setdefault(username, {})
            watchlists[username][asset] = ticker

        return watchlists

    except Exception as exc:
        print(f"[WARN] Could not load user watchlists: {exc}")
        return {}


def _normalize_timeframe(value: str | None) -> str:
    tf = str(value or DEFAULT_USER_TIMEFRAME).strip().lower()
    aliases = {"15": "15m", "15min": "15m", "60m": "1h", "1hr": "1h", "hourly": "1h", "4hr": "4h", "daily": "1d", "day": "1d"}
    tf = aliases.get(tf, tf)
    return tf if tf in TIMEFRAME_CONFIGS else DEFAULT_USER_TIMEFRAME


def _extract_timeframes_from_settings(settings: dict) -> list[str]:
    """Read a user's preferred scanner timeframe(s) from settings_json.

    Supports several key names so the scanner remains compatible as the app UI evolves.
    """
    if not isinstance(settings, dict):
        return [DEFAULT_USER_TIMEFRAME]
    raw_multi = (
        settings.get("selected_timeframes")
        or settings.get("scanner_timeframes")
        or settings.get("signal_timeframes")
        or settings.get("enabled_timeframes")
    )
    if isinstance(raw_multi, list):
        out = [_normalize_timeframe(x) for x in raw_multi]
        return sorted(set(out), key=["15m", "1h", "4h", "1d"].index)
    raw = (
        settings.get("preferred_timeframe")
        or settings.get("signal_timeframe")
        or settings.get("timeframe")
        or settings.get("prop_timeframe")
        or DEFAULT_USER_TIMEFRAME
    )
    return [_normalize_timeframe(raw)]


def get_user_scan_preferences() -> dict[str, dict]:
    """Load user settings needed by the fast scanner.

    Returns:
        {
          "ben": {"timeframes": ["1h"], "tracking_started_at": "..."},
          "brother": {"timeframes": ["15m"]}
        }
    """
    try:
        conn = db_connect()
        with conn.cursor() as cur:
            cur.execute("SELECT username, settings_json FROM user_settings ORDER BY username")
            rows = cur.fetchall()
        conn.close()
    except Exception as exc:
        print(f"[WARN] Could not load user scan preferences: {exc}")
        return {}

    prefs: dict[str, dict] = {}
    for row in rows:
        username = str(row.get("username", "")).strip()
        if not username:
            continue
        try:
            settings = json.loads(row.get("settings_json") or "{}")
            if not isinstance(settings, dict):
                settings = {}
        except Exception:
            settings = {}
        prefs[username] = {
            "timeframes": _extract_timeframes_from_settings(settings),
            "tracking_started_at": settings.get("tracking_started_at", ""),
        }
    return prefs


def should_run_full_universe(now: datetime | None = None) -> bool:
    """Backward-compatible helper retained for older code paths.

    Production scanner runs now scan the full MASTER_WATCHLIST every time.
    The GitHub schedule controls which timeframe group is scanned.
    The Streamlit app controls which saved scanner rows each user sees.
    """
    return True


def build_scan_plan(now: datetime | None = None) -> tuple[dict[str, str], list[str], str]:
    """Build the production scan plan.

    Asset universe:
        Always scan the full MASTER_WATCHLIST.

    Timeframe universe:
        Controlled by SCAN_TIMEFRAMES from GitHub Actions:
          - 15m every 15 minutes
          - 1h every hour
          - 4h every 4 hours
          - 1d once daily

    User watchlists:
        Do NOT control scanner coverage. They only filter what each user sees
        in app.py after login, and optionally route per-user Telegram alerts.
    """
    now = now or datetime.now(timezone.utc)

    assets: dict[str, str] = dict(MASTER_WATCHLIST)
    requested_tfs: set[str] = set(SCAN_TIMEFRAMES)

    if not requested_tfs:
        requested_tfs.add(DEFAULT_USER_TIMEFRAME)

    ordered_tfs = [tf for tf in ["15m", "1h", "4h", "1d"] if tf in requested_tfs]
    active_tfs = active_timeframes_for_run(now, ordered_tfs)

    mode = "MASTER_SCHEDULED"
    if FORCE_FULL_SCAN:
        mode = "MASTER_MANUAL_FULL"

    return assets, active_tfs, mode


# Backward-compatible alias for any older helper that still imports WATCHLIST.
# New scanner loops should use MASTER_WATCHLIST directly.
WATCHLIST = MASTER_WATCHLIST

# Multi-timeframe scan universe. Yahoo Finance does not reliably expose native 4h candles,
# so 4h is built by resampling 60m data. The scanner creates a separate signal row for
# each asset + timeframe + signal + candle_close.
TIMEFRAME_CONFIGS = {
    "15m": {"interval": "15m", "period": "60d",  "expiry_bars": 48},
    "1h":  {"interval": "60m", "period": "730d", "expiry_bars": 72},
    "4h":  {"interval": "60m", "period": "730d", "resample": "4h", "expiry_bars": 42},
    "1d":  {"interval": "1d",  "period": "5y",   "expiry_bars": 20},
}
SCAN_TIMEFRAMES = [tf.strip().lower() for tf in os.environ.get("SCAN_TIMEFRAMES", "15m,1h,4h,1d").split(",") if tf.strip().lower() in TIMEFRAME_CONFIGS]
if not SCAN_TIMEFRAMES:
    SCAN_TIMEFRAMES = ["15m", "1h", "4h", "1d"]

SCHEDULE_CRON = os.environ.get("SCHEDULE_CRON", "").strip()
SCHEDULED_TIMEFRAME_CRONS = {
    # Legacy multi-cron workflow labels.
    "2,17,32,47 * * * *": ["15m"],
    "7 * * * *": ["1h"],
    "17 */4 * * *": ["4h"],
    "37 0 * * *": ["1d"],

    # New single-cron workflow labels.
    # The workflow runs every 15 minutes and passes the exact comma-separated
    # SCAN_TIMEFRAMES for that run, for example:
    #   15m
    #   15m,1h
    #   15m,1h,4h
    #   15m,1d
    "every_15m_dynamic": ["15m", "1h", "4h", "1d"],

    # Manual workflow_dispatch should also trust the selected input exactly.
    "manual": ["15m", "1h", "4h", "1d"],
}


def is_schedule_controlled_run() -> bool:
    """True when GitHub Actions has already selected the exact timeframe set.

    In the new workflow, GitHub runs one schedule every 15 minutes and writes
    SCAN_TIMEFRAMES into the environment before scanner.py starts. When that
    happens, scanner.py must trust the workflow and must not apply its old
    runtime optimiser, otherwise a valid 1h scan at minute 17 could be skipped
    because it is not near minute 00.

    This also keeps manual workflow_dispatch runs predictable: if the user
    manually selects 4h, scanner.py scans 4h immediately instead of waiting for
    the next 4-hour candle window.

    "auto_dispatch" is the label the workflow sets when an EXTERNAL trigger
    (e.g. cron-job.org calling workflow_dispatch on a schedule, used because
    GitHub's native schedule: trigger is best-effort and can drift/skip) fires
    with scan_timeframes=auto. In that case the workflow's bash step re-derives
    the same 15m/1h/4h/1d cadence from the current UTC minute/hour that the
    native schedule path would have used — so it is just as trustworthy as
    "every_15m_dynamic" and must be trusted the same way, or 1h/4h/1d get
    silently dropped by the minute-window heuristic below even when the
    workflow correctly included them in SCAN_TIMEFRAMES.
    """
    label = str(SCHEDULE_CRON or "").strip()
    return bool(label) and (
        label in SCHEDULED_TIMEFRAME_CRONS
        or label.startswith("every_15m")
        or label == "auto_dispatch"
    )


# Production scan policy: every run scans the full MASTER_WATCHLIST.
# GitHub Actions controls the timeframe group through SCAN_TIMEFRAMES.
# User watchlists only filter the Streamlit dashboard and per-user Telegram routing.
# The legacy flags below are retained so existing secrets/workflows do not break.
FORCE_FULL_SCAN = os.environ.get("FORCE_FULL_SCAN", "false").strip().lower() in {"1", "true", "yes", "y"}
SCAN_MASTER_WATCHLIST_FALLBACK = os.environ.get("SCAN_MASTER_WATCHLIST_FALLBACK", "false").strip().lower() in {"1", "true", "yes", "y"}
FULL_UNIVERSE_SCAN_EVERY_HOURS = int(os.environ.get("FULL_UNIVERSE_SCAN_EVERY_HOURS", "0"))
DEFAULT_USER_TIMEFRAME = os.environ.get("DEFAULT_USER_TIMEFRAME", "1h").strip().lower()
if DEFAULT_USER_TIMEFRAME not in TIMEFRAME_CONFIGS:
    DEFAULT_USER_TIMEFRAME = "1h"

# Runtime optimisation:
# - 15m and 1h are scanned every run.
# - 4h and 1d are scanned only near their candle windows unless explicitly forced.
# Set SCAN_ALL_TIMEFRAMES_EVERY_RUN=true if you want the old slower behaviour.
SCAN_ALL_TIMEFRAMES_EVERY_RUN = os.environ.get("SCAN_ALL_TIMEFRAMES_EVERY_RUN", "false").strip().lower() in {"1", "true", "yes", "y"}
SLOW_TIMEFRAME_WINDOW_MINUTES = int(os.environ.get("SLOW_TIMEFRAME_WINDOW_MINUTES", "15"))
MTF_CONFIRMATION_TIMEFRAMES = ["15m", "1h", "4h"]
_TF_CACHE: dict[tuple[str, str], pd.DataFrame | None] = {}


def active_timeframes_for_run(now: datetime | None = None, requested_timeframes: list[str] | None = None) -> list[str]:
    """Return the timeframes this scanner run should actively generate.

    requested_timeframes comes from user settings. The 5-minute cron should not
    scan higher timeframes unless a fresh candle window is due, because 4h/1d
    data does not change every five minutes.
    """
    configured = [tf for tf in (requested_timeframes or SCAN_TIMEFRAMES) if tf in TIMEFRAME_CONFIGS]
    if not configured:
        configured = [DEFAULT_USER_TIMEFRAME]

    if SCAN_ALL_TIMEFRAMES_EVERY_RUN or is_schedule_controlled_run():
        # GitHub Actions or a manual dispatch has already selected the intended
        # timeframe list through SCAN_TIMEFRAMES. Return it exactly as received.
        return configured

    now = now or datetime.now(timezone.utc)
    minute_window = max(5, int(SLOW_TIMEFRAME_WINDOW_MINUTES))
    active: list[str] = []

    for tf in configured:
        if tf == "15m":
            active.append(tf)
        elif tf == "1h":
            # Scan 1h only near the top of the hour unless it is the only selected timeframe.
            if now.minute < minute_window or configured == ["1h"]:
                active.append(tf)
        elif tf == "4h":
            if now.hour % 4 == 0 and now.minute < minute_window:
                active.append(tf)
        elif tf == "1d":
            if now.hour == 0 and now.minute < minute_window:
                active.append(tf)

    # No scheduled scans. If no configured timeframe is due, skip scanner work.
    return active

# Legacy aliases retained for older helper code and Telegram text.
ENTRY_INTERVAL, ENTRY_PERIOD = "15m", "60d"
REGIME_INTERVAL, REGIME_PERIOD = "60m", "730d"

LOOKAHEAD = 8   # bars-ahead label for ML training

ACCOUNT_SIZE   = float(os.environ.get("ACCOUNT_SIZE",   "10000"))
RISK_PER_TRADE = float(os.environ.get("RISK_PER_TRADE", "0.01"))
LEVERAGE       = float(os.environ.get("LEVERAGE",       "100"))
SCAN_OWNER     = str(os.environ.get("SCAN_OWNER",       "benzino_system"))

MIN_ALERT_EDGE_SCORE      = float(os.environ.get("MIN_ALERT_EDGE_SCORE",      "35"))
MIN_ALERT_CONFIDENCE_DIST = float(os.environ.get("MIN_ALERT_CONFIDENCE_DIST", "12"))

ATR_SL_MULT = 1.5
ATR_TP_MULT = 3.0
EXPIRY_BARS = 48          # auto-expire an open trade after 48 entry-timeframe bars (~12h on 15m)

# FTMO-style challenge rules — mirrors app.py's Challenge Mode panel
CHALLENGE_PROFIT_TARGET    = 0.10
CHALLENGE_MAX_DAILY_LOSS   = 0.05
CHALLENGE_MAX_TOTAL_LOSS   = 0.10
CHALLENGE_MIN_TRADING_DAYS = 4

GRADE_RANK = {"A+": 4, "A": 3, "B": 2, "C": 1, "NO TRADE": 0}


# ═══════════════════════════════════════════════════════════════════════════════
#  RESULT DATACLASS
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class ScanResult:
    asset        : str
    ticker       : str
    timeframe    : str
    signal       : str
    grade        : str
    confidence   : float
    edge_score   : float
    ml_prob      : float
    entry        : float
    sl           : float
    tp           : float
    rr           : float
    regime       : str
    rsi          : float
    atr          : float
    trend_1h     : str
    trend_15m    : str
    reason       : str
    candle_close : str
    mtf_score    : float = 0.0
    mtf_context  : dict = field(default_factory=dict)
    strategy_votes: dict = field(default_factory=dict)
    signal_id    : str = field(default_factory=lambda: uuid.uuid4().hex)
    created_at   : str = field(default_factory=lambda: datetime.now(timezone.utc).isoformat())
    alert_sent   : bool = False


# ═══════════════════════════════════════════════════════════════════════════════
#  DATABASE
# ═══════════════════════════════════════════════════════════════════════════════

def _clean_db_url(url: str) -> str:
    url = str(url or "").strip()
    if not url:
        return ""
    if url.startswith("postgres://"):
        url = "postgresql://" + url[len("postgres://"):]
    try:
        parts = urlsplit(url)
        allowed = {"sslmode", "connect_timeout", "application_name", "target_session_attrs", "keepalives"}
        cleaned = urlencode([(k, v) for k, v in parse_qsl(parts.query, keep_blank_values=True) if k in allowed])
        return urlunsplit((parts.scheme, parts.netloc, parts.path, cleaned, parts.fragment))
    except Exception:
        return url


def db_connect():
    url = os.environ.get("DATABASE_URL", "").strip()
    if not url:
        raise RuntimeError("DATABASE_URL is not set.")
    if psycopg2 is None:
        raise RuntimeError("psycopg2 is not installed — add psycopg2-binary to requirements_scanner.txt.")
    return psycopg2.connect(_clean_db_url(url), cursor_factory=RealDictCursor)


def init_tables() -> None:
    ddl = """
    CREATE TABLE IF NOT EXISTS scanner_signals (
        signal_id      TEXT PRIMARY KEY,
        created_at     TIMESTAMPTZ NOT NULL DEFAULT NOW(),
        scan_owner     TEXT,
        asset          TEXT,
        ticker         TEXT,
        timeframe      TEXT,
        signal         TEXT,
        grade          TEXT,
        confidence     NUMERIC,
        edge_score     NUMERIC,
        ml_prob        NUMERIC,
        entry          NUMERIC,
        sl             NUMERIC,
        tp             NUMERIC,
        rr             NUMERIC,
        regime         TEXT,
        rsi            NUMERIC,
        atr            NUMERIC,
        trend_1h       TEXT,
        trend_15m      TEXT,
        reason         TEXT,
        candle_close   TIMESTAMPTZ,
        strategy_votes JSONB,
        mtf_score      NUMERIC,
        mtf_context    JSONB,
        alert_sent     BOOLEAN DEFAULT FALSE,
        status         TEXT DEFAULT 'SHADOW',
        bars_open      INTEGER DEFAULT 0,
        exit_price     NUMERIC,
        exit_reason    TEXT,
        exit_at        TIMESTAMPTZ,
        r_multiple     NUMERIC,
        shadow_outcome     TEXT,
        shadow_r_multiple  NUMERIC,
        shadow_exit_price  NUMERIC,
        shadow_closed_at   TIMESTAMPTZ
    );
    CREATE INDEX IF NOT EXISTS idx_scanner_asset_tf_signal_candle
        ON scanner_signals (asset, timeframe, signal, candle_close);
    CREATE INDEX IF NOT EXISTS idx_scanner_open_slot
        ON scanner_signals (asset, timeframe, status);

    CREATE TABLE IF NOT EXISTS user_watchlists (
        id BIGSERIAL PRIMARY KEY,
        scan_owner TEXT NOT NULL,
        asset TEXT NOT NULL,
        ticker TEXT NOT NULL,
        enabled BOOLEAN DEFAULT TRUE,
        created_at TIMESTAMPTZ DEFAULT NOW(),
        UNIQUE(scan_owner, asset)
    );

    CREATE TABLE IF NOT EXISTS user_telegram_settings (
        scan_owner TEXT PRIMARY KEY,
        telegram_chat_id TEXT,
        watchlist_alerts BOOLEAN DEFAULT TRUE,
        all_signals_alerts BOOLEAN DEFAULT FALSE,
        updated_at TIMESTAMPTZ DEFAULT NOW()
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
        scan_owner          TEXT PRIMARY KEY,
        starting_balance    NUMERIC,
        current_equity      NUMERIC,
        daily_pnl           NUMERIC DEFAULT 0,
        daily_reset_date    DATE,
        trading_days        INTEGER DEFAULT 0,
        status              TEXT DEFAULT 'ACTIVE',
        updated_at           TIMESTAMPTZ DEFAULT NOW()
    );

    CREATE TABLE IF NOT EXISTS prop_firm_trades (
        trade_id    TEXT PRIMARY KEY,
        signal_id   TEXT REFERENCES scanner_signals(signal_id),
        scan_owner  TEXT,
        asset       TEXT,
        grade       TEXT,
        r_multiple  NUMERIC,
        pnl_cash    NUMERIC,
        closed_at   TIMESTAMPTZ DEFAULT NOW()
    );
    CREATE UNIQUE INDEX IF NOT EXISTS idx_prop_firm_trades_signal_id
        ON prop_firm_trades (signal_id);

    CREATE TABLE IF NOT EXISTS benzino_signal_counter (
        id      INTEGER PRIMARY KEY DEFAULT 1,
        counter BIGINT NOT NULL DEFAULT 0,
        CONSTRAINT single_row CHECK (id = 1)
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
    try:
        conn = db_connect()
        with conn:
            with conn.cursor() as cur:
                cur.execute(ddl)
                cur.execute("ALTER TABLE scanner_signals ADD COLUMN IF NOT EXISTS mtf_score NUMERIC")
                cur.execute("ALTER TABLE scanner_signals ADD COLUMN IF NOT EXISTS mtf_context JSONB")
                cur.execute("ALTER TABLE scanner_signals ADD COLUMN IF NOT EXISTS shadow_outcome TEXT")
                cur.execute("ALTER TABLE scanner_signals ADD COLUMN IF NOT EXISTS shadow_r_multiple NUMERIC")
                cur.execute("ALTER TABLE scanner_signals ADD COLUMN IF NOT EXISTS shadow_exit_price NUMERIC")
                cur.execute("ALTER TABLE scanner_signals ADD COLUMN IF NOT EXISTS shadow_closed_at TIMESTAMPTZ")
                cur.execute("ALTER TABLE scanner_signals ADD COLUMN IF NOT EXISTS display_id TEXT")
                # Dashboard uses this table when replaying simulated FTMO challenge cycles.
                cur.execute("""
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
                    )
                """)
                cur.execute("ALTER TABLE prop_challenge_history ADD COLUMN IF NOT EXISTS failure_reason TEXT")
                cur.execute("ALTER TABLE user_telegram_settings ADD COLUMN IF NOT EXISTS alerts_enabled BOOLEAN DEFAULT FALSE")
                cur.execute("ALTER TABLE user_telegram_settings ADD COLUMN IF NOT EXISTS updated_at TIMESTAMPTZ DEFAULT NOW()")
                cur.execute("ALTER TABLE scanner_runtime_log ADD COLUMN IF NOT EXISTS open_trades INTEGER DEFAULT 0")
                cur.execute("ALTER TABLE scanner_runtime_log ADD COLUMN IF NOT EXISTS alerted INTEGER DEFAULT 0")
                cur.execute("INSERT INTO benzino_signal_counter (id, counter) VALUES (1, 0) ON CONFLICT (id) DO NOTHING")
                # Migration/fix: a journaled A+/A/B/C BUY/SELL setup must be OPEN even when Telegram is disabled.
                # Older runs incorrectly left graded setups as SHADOW when no alert was sent.
                cur.execute(
                    """
                    UPDATE scanner_signals
                    SET status = 'OPEN'
                    WHERE UPPER(TRIM(COALESCE(grade, ''))) IN ('A+', 'A', 'B', 'C')
                      AND UPPER(TRIM(COALESCE(signal, ''))) IN ('BUY', 'SELL')
                      AND UPPER(TRIM(COALESCE(status, 'SHADOW'))) = 'SHADOW'
                      AND exit_at IS NULL
                    """
                )
        conn.close()
        print("[DB] Tables ready. Graded BUY/SELL setups are auto-opened; NO TRADE remains SHADOW.")
    except Exception as e:
        print(f"[DB] init_tables failed: {e}")


def safe_number(value, default: float = 0.0) -> float:
    """Return a finite float. Converts NaN/inf/None to default."""
    try:
        x = float(value)
        if math.isnan(x) or math.isinf(x):
            return float(default)
        return x
    except Exception:
        return float(default)


def sanitize_for_json(value):
    """Recursively convert NaN/inf/numpy values into JSONB-safe values."""
    if value is None:
        return None
    if isinstance(value, dict):
        return {str(k): sanitize_for_json(v) for k, v in value.items()}
    if isinstance(value, (list, tuple, set)):
        return [sanitize_for_json(v) for v in value]
    if isinstance(value, (np.integer,)):
        return int(value)
    if isinstance(value, (np.floating, float)):
        x = float(value)
        if math.isnan(x) or math.isinf(x):
            return None
        return x
    if isinstance(value, (np.bool_, bool)):
        return bool(value)
    return value


def save_signal(sig: ScanResult) -> bool:
    sql = """
    INSERT INTO scanner_signals
        (signal_id, display_id, created_at, scan_owner, asset, ticker, timeframe, signal, grade,
         confidence, edge_score, ml_prob, entry, sl, tp, rr, regime, rsi, atr,
         trend_1h, trend_15m, reason, candle_close, strategy_votes, mtf_score, mtf_context, alert_sent, status)
    VALUES
        (%s,%s,%s,%s,%s,%s,%s,%s,%s, %s,%s,%s,%s,%s,%s,%s,%s,%s,%s, %s,%s,%s,%s,%s,%s,%s,%s,%s)
    ON CONFLICT (signal_id) DO NOTHING;
    """
    import json
    grade_norm = str(sig.grade or "").strip().upper()
    signal_norm = str(sig.signal or "").strip().upper()
    status = "OPEN" if (grade_norm in ("A+", "A", "B", "C") and signal_norm in ("BUY", "SELL")) else "SHADOW"
    if not getattr(sig, "display_id", None):
        sig.display_id = next_benzino_display_id()
    try:
        conn = db_connect()
        with conn:
            with conn.cursor() as cur:
                cur.execute(sql, (
                    sig.signal_id, sig.display_id, sig.created_at, SCAN_OWNER, sig.asset, sig.ticker,
                    sig.timeframe, sig.signal, sig.grade,
                    round(safe_number(sig.confidence), 2), round(safe_number(sig.edge_score), 2), round(safe_number(sig.ml_prob, 0.5), 2),
                    round(safe_number(sig.entry), 8), round(safe_number(sig.sl), 8), round(safe_number(sig.tp), 8), round(safe_number(sig.rr), 2),
                    sig.regime, round(safe_number(sig.rsi, 50.0), 2), round(safe_number(sig.atr), 2),
                    sig.trend_1h, sig.trend_15m, sig.reason, sig.candle_close,
                    json.dumps(sanitize_for_json(sig.strategy_votes), allow_nan=False), round(safe_number(sig.mtf_score), 2),
                    json.dumps(sanitize_for_json(sig.mtf_context or {}), allow_nan=False), sig.alert_sent, status,
                ))
        conn.close()
        return True
    except Exception as e:
        print(f"[DB] save_signal failed for {sig.asset}: {e}")
        return False


def force_open_graded_setups() -> int:
    """Safety migration: every A+/A/B/C BUY/SELL row must be OPEN unless already closed."""
    sql = """
    UPDATE scanner_signals
    SET status = 'OPEN'
    WHERE UPPER(TRIM(COALESCE(grade, ''))) IN ('A+', 'A', 'B', 'C')
      AND UPPER(TRIM(COALESCE(signal, ''))) IN ('BUY', 'SELL')
      AND UPPER(TRIM(COALESCE(status, 'SHADOW'))) = 'SHADOW'
      AND exit_at IS NULL
    RETURNING signal_id;
    """
    try:
        conn = db_connect()
        with conn:
            with conn.cursor() as cur:
                cur.execute(sql)
                rows = cur.fetchall()
        conn.close()
        count = len(rows or [])
        if count:
            print(f"[DB] Auto-open migration fixed {count} graded shadow row(s).")
        return count
    except Exception as e:
        print(f"[DB] force_open_graded_setups failed: {e}")
        return 0


def mark_alert_sent(signal_id: str) -> None:
    try:
        conn = db_connect()
        with conn:
            with conn.cursor() as cur:
                cur.execute(
                    "UPDATE scanner_signals SET alert_sent = TRUE WHERE signal_id = %s",
                    (signal_id,))
        conn.close()
    except Exception as e:
        print(f"[DB] mark_alert_sent failed: {e}")


def duplicate_alert_exists(asset: str, timeframe: str, signal: str, candle_close: str) -> bool:
    """
    True duplicate definition: same asset + timeframe + signal + candle close
    has already been alerted. This is exact-match, not a rolling time window.
    """
    sql = """
    SELECT 1 FROM scanner_signals
    WHERE asset = %s AND timeframe = %s AND signal = %s
      AND candle_close = %s AND alert_sent = TRUE
    LIMIT 1;
    """
    try:
        conn = db_connect()
        with conn.cursor() as cur:
            cur.execute(sql, (asset, timeframe, signal, candle_close))
            row = cur.fetchone()
        conn.close()
        return row is not None
    except Exception as e:
        print(f"[DB] duplicate_alert_exists check failed: {e}")
        return False




def duplicate_setup_exists(asset: str, timeframe: str, signal: str, candle_close: str) -> bool:
    """
    True setup duplicate definition: same asset + timeframe + signal + candle close
    already exists in Supabase. This is independent of Telegram.

    This prevents the scheduled scanner from opening/saving the same 15-minute
    candle setup multiple times when Telegram is disabled or optional.
    """
    sql = """
    SELECT 1 FROM scanner_signals
    WHERE asset = %s AND timeframe = %s AND signal = %s
      AND candle_close = %s
    LIMIT 1;
    """
    try:
        conn = db_connect()
        with conn.cursor() as cur:
            cur.execute(sql, (asset, timeframe, signal, candle_close))
            row = cur.fetchone()
        conn.close()
        return row is not None
    except Exception as e:
        print(f"[DB] duplicate_setup_exists check failed: {e}")
        return False


def open_trade_for_slot(asset: str, timeframe: str) -> dict | None:
    """
    A new alert cannot fire for (asset, timeframe) while a previous trade in
    that exact slot is still OPEN. Returns the open row, or None if the slot
    is free.
    """
    sql = """
    SELECT * FROM scanner_signals
    WHERE asset = %s AND timeframe = %s AND status = 'OPEN'
    ORDER BY created_at DESC LIMIT 1;
    """
    try:
        conn = db_connect()
        with conn.cursor() as cur:
            cur.execute(sql, (asset, timeframe))
            row = cur.fetchone()
        conn.close()
        return dict(row) if row else None
    except Exception as e:
        print(f"[DB] open_trade_for_slot check failed: {e}")
        return None  # fail open — better to risk a rare dup than to block all alerts


def close_trade(signal_id: str, exit_price: float, exit_reason: str, r_multiple: float) -> None:
    """Close an OPEN trade exactly once.

    Historical outcomes must be immutable. The old update matched only signal_id,
    which was safe in normal flow because evaluate_open_trades() fetches OPEN
    rows, but adding the status guard prevents any future accidental rerun or
    helper call from rewriting an already-closed TP/SL/expiry result.
    """
    sql = """
    UPDATE scanner_signals
    SET status = %s, exit_price = %s, exit_reason = %s, exit_at = NOW(), r_multiple = %s
    WHERE signal_id = %s
      AND UPPER(TRIM(COALESCE(status, ''))) = 'OPEN'
      AND exit_at IS NULL;
    """
    status = {"TP": "CLOSED_TP", "SL": "CLOSED_SL", "EXPIRY": "EXPIRED"}.get(exit_reason, "CLOSED")
    try:
        conn = db_connect()
        with conn:
            with conn.cursor() as cur:
                cur.execute(sql, (status, exit_price, exit_reason, r_multiple, signal_id))
                if cur.rowcount == 0:
                    print(f"[DB] close_trade skipped for {signal_id}: trade is no longer OPEN or already has exit_at.")
        conn.close()
    except Exception as e:
        print(f"[DB] close_trade failed: {e}")


def bump_bars_open(signal_id: str, bars: int) -> None:
    try:
        conn = db_connect()
        with conn:
            with conn.cursor() as cur:
                cur.execute("UPDATE scanner_signals SET bars_open = %s WHERE signal_id = %s", (bars, signal_id))
        conn.close()
    except Exception:
        pass


def fetch_open_trades(assets: set[str] | None = None, timeframes: set[str] | None = None) -> list[dict]:
    try:
        conn = db_connect()
        with conn.cursor() as cur:
            sql = "SELECT * FROM scanner_signals WHERE status = 'OPEN'"
            params: list = []
            if assets:
                sql += " AND asset = ANY(%s)"
                params.append(list(assets))
            if timeframes:
                sql += " AND timeframe = ANY(%s)"
                params.append(list(timeframes))
            sql += " ORDER BY created_at ASC"
            cur.execute(sql, tuple(params))
            rows = [dict(r) for r in cur.fetchall()]
        conn.close()
        return rows
    except Exception as e:
        print(f"[DB] fetch_open_trades failed: {e}")
        return []


def fetch_unresolved_shadow_trades(assets: set[str] | None = None, timeframes: set[str] | None = None,
                                   max_age_days: int = 14) -> list[dict]:
    """
    NO TRADE signals are never alerted and never touch the prop ledger, but they
    ARE still worth tracking hypothetically: "if a trader had taken this blocked
    idea anyway, would it have won?" This is shadow research only — it must never
    influence the real journal win rate.
    """
    try:
        conn = db_connect()
        with conn.cursor() as cur:
            sql = """
                SELECT * FROM scanner_signals
                WHERE status = 'SHADOW'
                  AND shadow_outcome IS NULL
                  AND created_at >= NOW() - INTERVAL '%s days'
            """
            params: list = [max_age_days]
            if assets:
                sql += " AND asset = ANY(%s)"
                params.append(list(assets))
            if timeframes:
                sql += " AND timeframe = ANY(%s)"
                params.append(list(timeframes))
            sql += " ORDER BY created_at ASC LIMIT 500"
            cur.execute(sql, tuple(params))
            rows = [dict(r) for r in cur.fetchall()]
        conn.close()
        return rows
    except Exception as e:
        print(f"[DB] fetch_unresolved_shadow_trades failed: {e}")
        return []


def close_shadow_trade(signal_id: str, exit_price: float, outcome: str, r_multiple: float) -> None:
    """
    Resolve a NO TRADE shadow row's hypothetical outcome. This NEVER changes
    `status` (it stays 'SHADOW' forever — it was never a real trade) and NEVER
    touches the prop-firm ledger. It only fills in shadow_* research columns.
    """
    sql = """
    UPDATE scanner_signals
    SET shadow_outcome = %s, shadow_r_multiple = %s, shadow_exit_price = %s, shadow_closed_at = NOW()
    WHERE signal_id = %s;
    """
    try:
        conn = db_connect()
        with conn:
            with conn.cursor() as cur:
                cur.execute(sql, (outcome, r_multiple, exit_price, signal_id))
        conn.close()
    except Exception as e:
        print(f"[DB] close_shadow_trade failed: {e}")


# ── Prop firm ledger — A+/A trades only ───────────────────────────────────────

def load_prop_firm_state() -> dict:
    sql_select = "SELECT * FROM prop_firm_state WHERE scan_owner = %s"
    sql_insert = """
    INSERT INTO prop_firm_state (scan_owner, starting_balance, current_equity, daily_reset_date)
    VALUES (%s, %s, %s, %s) RETURNING *;
    """
    try:
        conn = db_connect()
        with conn.cursor() as cur:
            cur.execute(sql_select, (SCAN_OWNER,))
            row = cur.fetchone()
            if row is None:
                cur.execute(sql_insert, (SCAN_OWNER, ACCOUNT_SIZE, ACCOUNT_SIZE,
                                         datetime.now(timezone.utc).date()))
                conn.commit()
                row = cur.fetchone()
        conn.close()
        return dict(row)
    except Exception as e:
        print(f"[DB] load_prop_firm_state failed: {e}")
        return {
            "scan_owner": SCAN_OWNER, "starting_balance": ACCOUNT_SIZE,
            "current_equity": ACCOUNT_SIZE, "daily_pnl": 0,
            "daily_reset_date": datetime.now(timezone.utc).date(),
            "trading_days": 0, "status": "ACTIVE",
        }


def prop_firm_trade_already_recorded(signal_id: str) -> bool:
    """Return True when this closed signal has already been applied to the prop ledger."""
    try:
        conn = db_connect()
        with conn.cursor() as cur:
            cur.execute("SELECT 1 FROM prop_firm_trades WHERE signal_id = %s LIMIT 1", (signal_id,))
            row = cur.fetchone()
        conn.close()
        return row is not None
    except Exception as e:
        print(f"[DB] prop_firm_trade_already_recorded failed: {e}")
        return False


def update_prop_firm(signal_id: str, asset: str, grade: str, r_multiple: float) -> None:
    """Apply closed A+/A trades to the prop-firm ledger exactly once.

    Normal account performance is computed in app.py from scanner_signals.
    The prop-firm ledger is stricter: only A+ and A closed trades are posted.
    This function is called immediately when an OPEN trade closes via TP, SL,
    or expiry, so prop equity updates as soon as the scanner resolves the trade.
    """
    if grade not in ("A+", "A"):
        return

    # Idempotency guard: never double-count a closed trade if the scanner is rerun
    # or if a previous run closed the signal but crashed later.
    if prop_firm_trade_already_recorded(signal_id):
        print(f"[PropFirm] {asset} {grade} already posted to ledger — skipping duplicate.")
        return

    force_open_graded_setups()
    state = load_prop_firm_state()
    if state.get("status") != "ACTIVE":
        print(f"[PropFirm] Challenge already {state.get('status')} — ignoring new trade.")
        return

    starting = float(state["starting_balance"])
    risk_cash = starting * RISK_PER_TRADE
    pnl_cash = float(r_multiple) * risk_cash

    today = datetime.now(timezone.utc).date()
    daily_pnl = float(state.get("daily_pnl") or 0)
    reset_date = state.get("daily_reset_date")
    if reset_date != today:
        daily_pnl = 0.0

    new_equity = float(state["current_equity"]) + pnl_cash
    daily_pnl += pnl_cash

    # Count the first posted trade of a new day as a trading day. If this is the
    # first ever trade and reset_date is today, keep at least one trading day.
    trading_days = int(state.get("trading_days") or 0)
    if reset_date != today or trading_days == 0:
        trading_days += 1

    status = "ACTIVE"
    if new_equity <= starting * (1 - CHALLENGE_MAX_TOTAL_LOSS):
        status = "FAILED"
    elif daily_pnl <= -starting * CHALLENGE_MAX_DAILY_LOSS:
        status = "FAILED"
    elif (new_equity >= starting * (1 + CHALLENGE_PROFIT_TARGET)
          and trading_days >= CHALLENGE_MIN_TRADING_DAYS):
        status = "PASSED"

    try:
        conn = db_connect()
        with conn:
            with conn.cursor() as cur:
                cur.execute("""
                    UPDATE prop_firm_state
                    SET current_equity = %s, daily_pnl = %s, daily_reset_date = %s,
                        trading_days = %s, status = %s, updated_at = NOW()
                    WHERE scan_owner = %s
                """, (new_equity, daily_pnl, today, trading_days, status, SCAN_OWNER))
                cur.execute("""
                    INSERT INTO prop_firm_trades (trade_id, signal_id, scan_owner, asset, grade, r_multiple, pnl_cash)
                    VALUES (%s,%s,%s,%s,%s,%s,%s)
                    ON CONFLICT (signal_id) DO NOTHING
                """, (uuid.uuid4().hex, signal_id, SCAN_OWNER, asset, grade, r_multiple, pnl_cash))
        conn.close()
        print(f"[PropFirm] {asset} {grade} closed {r_multiple:+.2f}R (${pnl_cash:+,.2f}) "
              f"→ equity ${new_equity:,.2f} · status {status} · trading days {trading_days}")
    except Exception as e:
        print(f"[DB] update_prop_firm failed: {e}")



def log_runtime(run_id: str, started_at: datetime, finished_at: datetime, total_seconds: float,
                assets_scanned: int, signals_saved: int, shadow_saved: int, open_trades: int,
                alerted: int, timeframes_scanned: list[str], asset_seconds: list[float]) -> None:
    """Persist scanner runtime statistics for the Streamlit System Health panel."""
    fastest = min(asset_seconds) if asset_seconds else 0.0
    slowest = max(asset_seconds) if asset_seconds else 0.0
    avg = float(np.mean(asset_seconds)) if asset_seconds else 0.0
    try:
        conn = db_connect()
        with conn:
            with conn.cursor() as cur:
                cur.execute(
                    """
                    INSERT INTO scanner_runtime_log
                        (run_id, started_at, finished_at, total_seconds, assets_scanned,
                         signals_saved, shadow_saved, open_trades, alerted, timeframes_scanned,
                         fastest_asset_seconds, slowest_asset_seconds, avg_asset_seconds)
                    VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s)
                    ON CONFLICT (run_id) DO NOTHING
                    """,
                    (
                        run_id, started_at.isoformat(), finished_at.isoformat(), float(total_seconds),
                        int(assets_scanned), int(signals_saved), int(shadow_saved), int(open_trades),
                        int(alerted), ",".join(timeframes_scanned), float(fastest), float(slowest), float(avg),
                    ),
                )
        conn.close()
        print(f"[Runtime] Logged run {run_id[:8]}: {total_seconds:.1f}s · TFs {','.join(timeframes_scanned)}")
    except Exception as e:
        print(f"[Runtime] Failed to log scanner runtime: {e}")

# ═══════════════════════════════════════════════════════════════════════════════
#  DATA DOWNLOAD
# ═══════════════════════════════════════════════════════════════════════════════

def download(ticker: str, interval: str, period: str) -> pd.DataFrame | None:
    try:
        df = yf.download(ticker, interval=interval, period=period, auto_adjust=True, progress=False)
        if df is None or df.empty:
            return None
        if isinstance(df.columns, pd.MultiIndex):
            df.columns = df.columns.get_level_values(0)
        df = df.reset_index()
        df.columns = [str(c) for c in df.columns]
        date_col = df.columns[0]
        df[date_col] = pd.to_datetime(df[date_col], utc=True).dt.tz_localize(None)
        df = df.rename(columns={date_col: "Date"})
        return df if len(df) >= 50 else None
    except Exception as e:
        print(f"[data] {ticker} ({interval}): {e}")
        return None


def resample_ohlcv(df: pd.DataFrame, rule: str) -> pd.DataFrame | None:
    """Resample Date/Open/High/Low/Close/Volume data into a higher timeframe."""
    try:
        if df is None or df.empty:
            return None
        work = df.copy()
        work["Date"] = pd.to_datetime(work["Date"], utc=True, errors="coerce")
        work = work.dropna(subset=["Date"]).set_index("Date").sort_index()
        agg = {"Open": "first", "High": "max", "Low": "min", "Close": "last"}
        if "Volume" in work.columns:
            agg["Volume"] = "sum"
        out = work.resample(rule).agg(agg).dropna(subset=["Open", "High", "Low", "Close"]).reset_index()
        out["Date"] = pd.to_datetime(out["Date"], utc=True).dt.tz_localize(None)
        return out if len(out) >= 50 else None
    except Exception as exc:
        print(f"[data] resample {rule} failed: {exc}")
        return None


def get_timeframe_df(ticker: str, timeframe: str) -> pd.DataFrame | None:
    """Download/cache the requested scanner timeframe, including synthetic 4h candles."""
    timeframe = str(timeframe or "15m").lower()
    if timeframe not in TIMEFRAME_CONFIGS:
        timeframe = "15m"
    key = (ticker, timeframe)
    if key in _TF_CACHE:
        cached = _TF_CACHE[key]
        return cached.copy() if cached is not None else None
    cfg = TIMEFRAME_CONFIGS[timeframe]
    base = download(ticker, cfg["interval"], cfg["period"])
    if base is not None and cfg.get("resample"):
        base = resample_ohlcv(base, cfg["resample"])
    _TF_CACHE[key] = base.copy() if base is not None else None
    return base.copy() if base is not None else None


def trend_direction_from_df(df: pd.DataFrame | None) -> tuple[str, float]:
    """Return BULLISH/BEARISH/NEUTRAL plus a 0-1 trend strength estimate."""
    if df is None or df.empty:
        return "NEUTRAL", 0.0
    try:
        work = add_indicators(df)
        l = work.iloc[-1]
        price = float(l.get("Close", np.nan))
        ema20 = float(l.get("ema20", np.nan))
        ema50 = float(l.get("ema50", np.nan))
        ema200 = float(l.get("ema200", np.nan))
        adx = float(l.get("ADX", 0) or 0)
        if any(np.isnan(x) for x in [price, ema20, ema50, ema200]):
            return "NEUTRAL", 0.0
        if price > ema20 > ema50 and price > ema200:
            return "BULLISH", float(np.clip((adx if not np.isnan(adx) else 20) / 40, 0.25, 1.0))
        if price < ema20 < ema50 and price < ema200:
            return "BEARISH", float(np.clip((adx if not np.isnan(adx) else 20) / 40, 0.25, 1.0))
        if price > ema50:
            return "BULLISH", 0.35
        if price < ema50:
            return "BEARISH", 0.35
        return "NEUTRAL", 0.0
    except Exception:
        return "NEUTRAL", 0.0


def mtf_confirmation(ticker: str, dominant_direction: str) -> tuple[dict, float, str, float]:
    """Score 15m/1h/4h alignment as a fifth strategy vote."""
    dominant_direction = str(dominant_direction or "NEUTRAL").upper()
    context = {}
    aligned = 0
    checked = 0
    for tf in MTF_CONFIRMATION_TIMEFRAMES:
        df_tf = get_timeframe_df(ticker, tf)
        direction, strength = trend_direction_from_df(df_tf)
        context[tf] = {"direction": direction, "strength": round(float(strength), 2)}
        if direction in ("BULLISH", "BEARISH"):
            checked += 1
            if direction == dominant_direction:
                aligned += 1
    score = float(aligned / checked * 100) if checked else 0.0
    if dominant_direction in ("BULLISH", "BEARISH") and score >= 67:
        vote_dir = dominant_direction
    elif dominant_direction in ("BULLISH", "BEARISH") and score <= 33 and checked:
        vote_dir = "BEARISH" if dominant_direction == "BULLISH" else "BULLISH"
    else:
        vote_dir = "NEUTRAL"
    vote_strength = float(np.clip(score / 100, 0, 1)) if vote_dir == dominant_direction else 0.0
    context["score"] = round(score, 2)
    context["aligned"] = aligned
    context["checked"] = checked
    return context, score, vote_dir, vote_strength


# ═══════════════════════════════════════════════════════════════════════════════
#  INDICATORS
# ═══════════════════════════════════════════════════════════════════════════════

def add_indicators(df: pd.DataFrame) -> pd.DataFrame:
    df = df.copy()
    c = df["Close"]

    df["ema9"]   = c.ewm(span=9,   adjust=False).mean()
    df["ema20"]  = c.ewm(span=20,  adjust=False).mean()
    df["ema50"]  = c.ewm(span=50,  adjust=False).mean()
    df["ema200"] = c.ewm(span=200, adjust=False).mean()

    delta = c.diff()
    gain  = delta.clip(lower=0).rolling(14).mean()
    loss  = (-delta.clip(upper=0)).rolling(14).mean()
    df["RSI"] = 100 - (100 / (1 + gain / (loss + 1e-9)))

    # 2-period RSI for Connors mean reversion
    g2 = delta.clip(lower=0).rolling(2).mean()
    l2 = (-delta.clip(upper=0)).rolling(2).mean()
    df["RSI2"] = 100 - (100 / (1 + g2 / (l2 + 1e-9)))

    macd_line = c.ewm(span=12, adjust=False).mean() - c.ewm(span=26, adjust=False).mean()
    df["MACD"] = macd_line
    df["MACD_sig"] = macd_line.ewm(span=9, adjust=False).mean()
    df["MACD_hist"] = macd_line - df["MACD_sig"]

    lo14 = df["Low"].rolling(14).min()
    hi14 = df["High"].rolling(14).max()
    df["stoch_k"] = 100 * (c - lo14) / (hi14 - lo14 + 1e-9)
    df["stoch_d"] = df["stoch_k"].rolling(3).mean()

    sma20 = c.rolling(20).mean()
    std20 = c.rolling(20).std()
    df["bb_upper"] = sma20 + 2 * std20
    df["bb_lower"] = sma20 - 2 * std20
    df["bb_pct"] = (c - df["bb_lower"]) / (df["bb_upper"] - df["bb_lower"] + 1e-9)

    hl = df["High"] - df["Low"]
    hc = (df["High"] - c.shift()).abs()
    lc = (df["Low"] - c.shift()).abs()
    tr = pd.concat([hl, hc, lc], axis=1).max(axis=1)
    df["ATR"] = tr.rolling(14).mean()

    # Wilder's ADX — trend-strength confirmation for the Donchian breakout
    up_move   = df["High"].diff()
    down_move = -df["Low"].diff()
    plus_dm  = np.where((up_move > down_move) & (up_move > 0), up_move, 0.0)
    minus_dm = np.where((down_move > up_move) & (down_move > 0), down_move, 0.0)
    atr14 = tr.rolling(14).mean() + 1e-9
    plus_di  = 100 * pd.Series(plus_dm, index=df.index).rolling(14).mean() / atr14
    minus_di = 100 * pd.Series(minus_dm, index=df.index).rolling(14).mean() / atr14
    dx = 100 * (plus_di - minus_di).abs() / (plus_di + minus_di + 1e-9)
    df["ADX"] = dx.rolling(14).mean()

    df["returns"] = c.pct_change()
    df["vol20"] = df["returns"].rolling(20).std()
    df["momentum"] = c - c.shift(10)
    df["roc10"] = c.pct_change(10) * 100

    # Donchian channels — 20-bar Turtle entry channel
    df["donchian_high20"] = df["High"].rolling(20).max()
    df["donchian_low20"]  = df["Low"].rolling(20).min()

    df["higher_high"] = (df["High"] > df["High"].rolling(5).max().shift(1)).astype(int)
    df["higher_low"]  = (df["Low"]  > df["Low"].rolling(5).min().shift(1)).astype(int)
    df["ema_bull"]    = (df["ema20"] > df["ema50"]).astype(int)
    df["above_200"]   = (c > df["ema200"]).astype(int)

    if "Volume" in df.columns and df["Volume"].sum() > 0:
        df["vol_sma"] = df["Volume"].rolling(20).mean()
        df["vol_ratio"] = df["Volume"] / (df["vol_sma"] + 1e-9)
    else:
        df["vol_ratio"] = 1.0

    return df


def classify_regime(df: pd.DataFrame) -> tuple[str, float]:
    l = df.iloc[-1]
    def sf(k):
        v = l.get(k, 0)
        return float(v) if not (isinstance(v, float) and np.isnan(v)) else 0.0
    price, ema20, ema50, ema200 = sf("Close"), sf("ema20"), sf("ema50"), sf("ema200")
    vol = sf("vol20")
    vol_mean = float(df["vol20"].mean()) if "vol20" in df.columns else vol
    trend_pct = abs(ema20 - ema50) / (price + 1e-9) * 100
    above_50, above_200 = price > ema50, price > ema200
    high_vol = vol > vol_mean * 1.2
    if above_50 and above_200 and trend_pct > 1.5: return "Strong Bull", 9.0
    if above_50 and trend_pct > 0.5: return "Weak Bull", 6.5
    if not above_50 and not above_200 and trend_pct > 1.5: return "Strong Bear", 8.5
    if not above_50 and trend_pct > 0.5: return "Weak Bear", 5.5
    if high_vol: return "Volatile Range", 3.0
    return "Quiet Range", 2.0


def trend_label(df: pd.DataFrame | None) -> str:
    if df is None or df.empty:
        return "Unavailable"
    df = add_indicators(df)
    l = df.iloc[-1]
    def sf(k):
        v = l.get(k, np.nan)
        return float(v) if pd.notna(v) else np.nan
    ema20, ema50, price = sf("ema20"), sf("ema50"), sf("Close")
    if any(np.isnan(x) for x in [ema20, ema50, price]):
        return "Unavailable"
    if price > ema20 > ema50: return "Bullish (price > EMA20 > EMA50)"
    if price < ema20 < ema50: return "Bearish (price < EMA20 < EMA50)"
    return "Neutral-Bullish" if price > ema50 else "Neutral-Bearish"


# ═══════════════════════════════════════════════════════════════════════════════
#  STRATEGY 1 — TIME-SERIES MOMENTUM (Moskowitz, Ooi & Pedersen, 2012)
# ═══════════════════════════════════════════════════════════════════════════════

def strategy_tsmom(df: pd.DataFrame, lookback: int = 40) -> tuple[str, float]:
    """
    Time-series momentum: the sign of an asset's own past return predicts its
    near-term continuation (Moskowitz, Ooi & Pedersen, 2012 — tested across 58
    futures markets, 1985-2009). We scale conviction by the volatility-adjusted
    magnitude of the move, mirroring the paper's risk-parity sizing approach.
    """
    if len(df) < lookback + 5:
        return "NEUTRAL", 0.0
    past_ret = df["Close"].iloc[-1] / df["Close"].iloc[-lookback] - 1
    vol = df["returns"].rolling(lookback).std().iloc[-1]
    if pd.isna(vol) or vol == 0:
        return "NEUTRAL", 0.0
    risk_adj_momentum = past_ret / vol
    direction = "BULLISH" if past_ret > 0 else "BEARISH" if past_ret < 0 else "NEUTRAL"
    strength = safe_number(np.clip(abs(risk_adj_momentum) / 3.0, 0, 1), 0.0)
    return direction, strength


# ═══════════════════════════════════════════════════════════════════════════════
#  STRATEGY 2 — DONCHIAN / TURTLE BREAKOUT (ADX-confirmed)
# ═══════════════════════════════════════════════════════════════════════════════

def strategy_donchian_breakout(df: pd.DataFrame) -> tuple[str, float]:
    """
    Classic Turtle Trading entry: close breaks the 20-bar Donchian high/low.
    One of the few public systems with a verified multi-decade track record.
    Modern markets fade raw breakouts more than in the 1980s, so we require
    ADX > 20 (Wilder) to confirm a real trend is underway, not noise.
    """
    if len(df) < 25 or "donchian_high20" not in df.columns:
        return "NEUTRAL", 0.0
    l = df.iloc[-1]
    close, hi20, lo20, adx = l["Close"], l["donchian_high20"], l["donchian_low20"], l.get("ADX", 0)
    if pd.isna(adx):
        adx = 0
    breakout_up   = close >= hi20
    breakout_down = close <= lo20
    if breakout_up:
        direction = "BULLISH"
    elif breakout_down:
        direction = "BEARISH"
    else:
        direction = "NEUTRAL"
    adx_strength = safe_number(np.clip((safe_number(adx) - 15) / 25, 0, 1), 0.0)  # 0 at ADX 15, 1 at ADX 40+
    strength = adx_strength if direction != "NEUTRAL" else 0.0
    return direction, strength


# ═══════════════════════════════════════════════════════════════════════════════
#  STRATEGY 3 — RSI-2 MEAN REVERSION (Larry Connors)
# ═══════════════════════════════════════════════════════════════════════════════

def strategy_rsi2_meanreversion(df: pd.DataFrame) -> tuple[str, float]:
    """
    Connors' RSI(2): buy oversold panic, sell overbought euphoria — but only
    WITH the dominant trend (price vs 200-period EMA). This trend filter is
    the part most copycat versions omit, and it's what separates Connors'
    published, extensively-backtested results from pure contrarian gambling.
    """
    if len(df) < 205 or "RSI2" not in df.columns:
        return "NEUTRAL", 0.0
    l = df.iloc[-1]
    rsi2, price, ema200 = l["RSI2"], l["Close"], l["ema200"]
    if pd.isna(rsi2) or pd.isna(ema200):
        return "NEUTRAL", 0.0
    above_trend = price > ema200
    if above_trend and rsi2 < 10:
        return "BULLISH", safe_number(np.clip((10 - rsi2) / 10, 0, 1), 0.0)
    if (not above_trend) and rsi2 > 90:
        return "BEARISH", safe_number(np.clip((rsi2 - 90) / 10, 0, 1), 0.0)
    return "NEUTRAL", 0.0


# ═══════════════════════════════════════════════════════════════════════════════
#  STRATEGY 4 — ML ENSEMBLE (LR + RF + GB)
# ═══════════════════════════════════════════════════════════════════════════════

FEATURES = [
    "ema_bull", "above_200", "RSI", "MACD", "MACD_hist", "stoch_k", "stoch_d",
    "bb_pct", "momentum", "returns", "vol20", "roc10", "higher_high", "higher_low",
    "vol_ratio", "ATR", "ADX",
]

def train_ensemble(df: pd.DataFrame) -> pd.DataFrame:
    """Fit the LR/RF/GB ensemble and attach an out-of-sample-safe signal_prob.

    Two bugs this fixes versus the original version:

    1. LABEL CORRUPTION: `target = (Close.shift(-LOOKAHEAD) > Close)` produces
       NaN for the most recent LOOKAHEAD rows, since there is no future close
       yet to compare against. `NaN > x` evaluates to False in pandas, and
       `.astype(int)` then silently turns that False into a real 0 — so the
       most recent LOOKAHEAD rows were being labelled "price did not rise"
       even though the true outcome is genuinely unknown. Those fabricated
       labels were being fed into training as if they were real history.
       Fixed by building the target as a nullable boolean and dropping rows
       where the future close does not exist, instead of comparing against NaN.

    2. TRAIN/PREDICT LEAKAGE: the original code called model.fit(X, y) and then
       model.predict_proba(X) on the IDENTICAL rows — including the most
       recent row, which is the only one strategy_confluence() actually uses
       live (via .iloc[-1]). Every live signal_prob was therefore an in-sample
       prediction with no demonstrated out-of-sample skill; it could not be
       distinguished from memorized noise. Fixed by fitting only on rows whose
       LOOKAHEAD-bars-forward outcome is already known and fully in the past,
       then predicting the live row using a model that never saw it.

    A held-out validation slice (most recent ~20% of the resolved rows, before
    the final live-fit) is also scored honestly and stored in
    df.attrs["ml_oos_accuracy"] so callers can see whether the ensemble shows
    real out-of-sample skill (e.g. ~52-58% on noisy financial data is a
    plausible genuine edge) versus ~50% (no edge) or implausibly high accuracy
    (usually a sign of leakage or overfitting on a short history) before
    trusting it in compute_edge_score().
    """
    df = df.copy()

    future_close = df["Close"].shift(-LOOKAHEAD)
    has_future = future_close.notna()
    df["target"] = pd.Series(np.nan, index=df.index)
    df.loc[has_future, "target"] = (future_close[has_future] > df.loc[has_future, "Close"]).astype(int)

    feats = [f for f in FEATURES if f in df.columns]
    # Only rows with a real, resolved target (i.e. LOOKAHEAD bars already
    # happened) are eligible for training. The most recent LOOKAHEAD rows
    # (including the live row used for the actual trading decision) are
    # excluded here on purpose — their true outcome has not happened yet.
    resolved = df[feats + ["target"]].replace([np.inf, -np.inf], np.nan).dropna()

    df["signal_prob"] = 0.5
    df.attrs["ml_oos_accuracy"] = None
    df.attrs["ml_oos_n"] = 0

    if len(resolved) < 150 or not feats:
        return df

    # Honest out-of-sample check: hold back the most recent 20% of RESOLVED
    # rows (still strictly before the live row) purely to measure accuracy.
    # These rows are never used to fit the model that produces the live
    # signal_prob below — they only answer "does this ensemble show real
    # skill", reported separately from the live prediction itself.
    split_idx = int(len(resolved) * 0.8)
    train_part = resolved.iloc[:split_idx]
    holdout_part = resolved.iloc[split_idx:]

    weights = {"lr": 0.20, "rf": 0.35, "gb": 0.45}

    def _fresh_models():
        return {
            "lr": Pipeline([("imp", SimpleImputer()), ("sc", StandardScaler()),
                            ("m", LogisticRegression(C=0.5, max_iter=1000, random_state=42))]),
            "rf": Pipeline([("imp", SimpleImputer()),
                            ("m", RandomForestClassifier(n_estimators=150, max_depth=5,
                                                         min_samples_leaf=10, random_state=42))]),
            "gb": Pipeline([("imp", SimpleImputer()),
                            ("m", GradientBoostingClassifier(n_estimators=120, learning_rate=0.05,
                                                              max_depth=4, min_samples_leaf=10, random_state=42))]),
        }

    if len(holdout_part) >= 20 and len(train_part) >= 100:
        try:
            oos_models = _fresh_models()
            oos_proba = {}
            for name, model in oos_models.items():
                model.fit(train_part[feats], train_part["target"])
                oos_proba[name] = model.predict_proba(holdout_part[feats])[:, 1]
            oos_ens = sum(weights[n] * oos_proba[n] for n in oos_proba)
            oos_pred = (oos_ens > 0.5).astype(int)
            df.attrs["ml_oos_accuracy"] = float((oos_pred == holdout_part["target"].values).mean())
            df.attrs["ml_oos_n"] = int(len(holdout_part))
        except Exception:
            df.attrs["ml_oos_accuracy"] = None
            df.attrs["ml_oos_n"] = 0

    # Final live fit: train on EVERY resolved row (train_part + holdout_part —
    # both are still strictly in the past relative to the live row), then
    # predict only the live row, which this fit has never seen in any form.
    live_models = _fresh_models()
    live_proba = {}
    for name, model in live_models.items():
        try:
            model.fit(resolved[feats], resolved["target"])
            live_proba[name] = model
        except Exception:
            live_proba[name] = None

    live_row = df[feats].iloc[[-1]].replace([np.inf, -np.inf], np.nan)
    if live_row.isna().any(axis=1).iloc[0]:
        # Live row has a missing feature (e.g. not enough bars for a rolling
        # indicator yet) — leave signal_prob at the neutral 0.5 default.
        return df

    ens_prob = 0.0
    any_ok = False
    for name, model in live_proba.items():
        if model is None:
            continue
        try:
            ens_prob += weights[name] * model.predict_proba(live_row)[:, 1][0]
            any_ok = True
        except Exception:
            continue

    if any_ok:
        df.loc[df.index[-1], "signal_prob"] = ens_prob

    return df




# ═══════════════════════════════════════════════════════════════════════════════
#  STRATEGY CONFLUENCE — combines all four votes into a grade
# ═══════════════════════════════════════════════════════════════════════════════

def strategy_confluence(df: pd.DataFrame, mtf_vote: tuple[str, float] | None = None) -> dict:
    """Run four core strategies plus optional multi-timeframe confirmation."""
    ml_prob = float(df["signal_prob"].iloc[-1]) if "signal_prob" in df.columns else 0.5
    ml_dir = "BULLISH" if ml_prob > 0.55 else "BEARISH" if ml_prob < 0.45 else "NEUTRAL"
    ml_strength = safe_number(np.clip(abs(ml_prob - 0.5) * 2, 0, 1), 0.0)

    tsmom_dir, tsmom_str = strategy_tsmom(df)
    donch_dir, donch_str = strategy_donchian_breakout(df)
    rsi2_dir,  rsi2_str  = strategy_rsi2_meanreversion(df)

    votes = {
        "TSMOM"      : {"direction": tsmom_dir, "strength": round(tsmom_str, 2)},
        "Donchian"   : {"direction": donch_dir, "strength": round(donch_str, 2)},
        "RSI2"       : {"direction": rsi2_dir,  "strength": round(rsi2_str, 2)},
        "MLEnsemble" : {"direction": ml_dir,    "strength": round(ml_strength, 2)},
    }
    if mtf_vote is not None:
        mtf_dir, mtf_strength = mtf_vote
        votes["MTFConfirmation"] = {"direction": mtf_dir, "strength": round(float(mtf_strength), 2)}

    bull_votes = [v for v in votes.values() if v["direction"] == "BULLISH"]
    bear_votes = [v for v in votes.values() if v["direction"] == "BEARISH"]
    n_bull, n_bear = len(bull_votes), len(bear_votes)
    if n_bull > n_bear:
        dominant = "BULLISH"
        agree_count = n_bull
        avg_strength = safe_number(np.mean([safe_number(v.get("strength")) for v in bull_votes]), 0.0) if bull_votes else 0.0
    elif n_bear > n_bull:
        dominant = "BEARISH"
        agree_count = n_bear
        avg_strength = safe_number(np.mean([safe_number(v.get("strength")) for v in bear_votes]), 0.0) if bear_votes else 0.0
    else:
        dominant = "SPLIT"
        agree_count = max(n_bull, n_bear)
        avg_strength = 0.0

    return {
        "votes": votes,
        "dominant": dominant,
        "agree_count": agree_count,
        "total_systems": len(votes),
        "avg_strength": round(avg_strength, 2),
        "ml_prob": ml_prob,
    }


def grade_signal(confluence: dict, rr: float) -> tuple[str, str]:
    """Grade by confluence across all active systems, including MTF when present."""
    dominant = confluence["dominant"]
    agree = int(confluence["agree_count"])
    total = int(confluence.get("total_systems", 5) or 5)
    strength = float(confluence["avg_strength"])
    if dominant == "SPLIT":
        return "NO TRADE", "Systems split — no directional confluence."
    if rr < 1.2:
        return "NO TRADE", f"RR too thin ({rr:.2f}R) regardless of confluence."
    if agree >= max(4, total - 1) and rr >= 2.5 and strength >= 0.50:
        return "A+", f"{agree}/{total} systems agree {dominant.lower()}, strong conviction ({strength:.2f}), RR {rr:.2f}R."
    if agree >= 3 and rr >= 2.0 and strength >= 0.35:
        return "A", f"{agree}/{total} systems agree {dominant.lower()}, RR {rr:.2f}R."
    if agree >= 2 and rr >= 1.5:
        return "B", f"{agree}/{total} systems agree {dominant.lower()}, moderate RR {rr:.2f}R."
    if agree >= 1 and rr >= 1.2:
        return "C", f"Only {agree}/{total} systems agree {dominant.lower()} — weak edge."
    return "NO TRADE", "Confluence and risk/reward both too weak."


# ═══════════════════════════════════════════════════════════════════════════════
#  TRADE PLAN & EDGE SCORE
# ═══════════════════════════════════════════════════════════════════════════════

def build_trade_plan(price: float, atr: float, signal: str) -> dict:
    atr = safe_number(atr)
    price = safe_number(price)
    signal = str(signal or "").upper()
    if atr <= 0 or signal not in ("BUY", "SELL"):
        return {"sl": price, "tp": price, "size": 0, "rr": 0}
    sl = price - atr * ATR_SL_MULT if signal == "BUY" else price + atr * ATR_SL_MULT
    tp = price + atr * ATR_TP_MULT if signal == "BUY" else price - atr * ATR_TP_MULT
    dist = abs(price - sl)
    size = (ACCOUNT_SIZE * RISK_PER_TRADE) / dist if dist > 0 else 0
    rr = abs(tp - price) / dist if dist > 0 else 0
    return {"sl": sl, "tp": tp, "size": size, "rr": rr}


def choose_shadow_research_direction(confluence: dict) -> str:
    """Choose a hypothetical BUY/SELL direction for NO TRADE research rows.

    A NO TRADE row still needs a trade plan if we want to test whether the
    system was too strict. For normal weak-direction setups, this returns the
    dominant side. For split/no-consensus setups, it uses the strongest
    non-neutral strategy vote, then ML probability as a deterministic tie-break.
    This direction is research-only: the row remains SHADOW and is never alerted,
    journaled, or posted to the prop ledger.
    """
    try:
        dominant = str(confluence.get("dominant", "")).upper()
        if dominant == "BULLISH":
            return "BUY"
        if dominant == "BEARISH":
            return "SELL"

        votes = confluence.get("votes") or {}
        scored = []
        for name, payload in votes.items():
            direction = str((payload or {}).get("direction", "")).upper()
            if direction not in ("BULLISH", "BEARISH"):
                continue
            strength = safe_number((payload or {}).get("strength"), 0.0)
            scored.append((strength, direction, str(name)))
        if scored:
            scored.sort(reverse=True)
            return "BUY" if scored[0][1] == "BULLISH" else "SELL"

        ml_prob = safe_number(confluence.get("ml_prob"), 0.5)
        return "BUY" if ml_prob >= 0.5 else "SELL"
    except Exception:
        return "BUY"


def compute_edge_score(signal: str, confidence: float, ml_prob: float, rr: float,
                        ml_oos_accuracy: float | None = None) -> float:
    """Composite edge score.

    `confidence` now means system agreement across all active systems, not
    confidence among only the non-neutral voters. Therefore a 1/5 C setup is
    about 20%, while a 5/5 A+ setup is 100%. The ML component remains
    directional: BUY uses ML probability, SELL uses inverse ML probability.

    ml_oos_accuracy comes from train_ensemble()'s honest held-out validation
    (df.attrs["ml_oos_accuracy"]) — accuracy on rows the final live model
    never trained on. The ML component's weight is scaled by how far that
    accuracy sits above a 50% coin flip, clipped to [0, 1]:
      - None / 50% or below  -> ML contributes ~0 (no demonstrated edge yet,
        e.g. too little history, or genuinely no skill on this asset/timeframe)
      - ~58%+                -> ML contributes close to its full normal weight
      - linearly in between
    This stops an unvalidated or genuinely unskilled ML ensemble from quietly
    carrying 30% of every edge score just because a number happened to come
    out of a model — the weight now has to be earned by out-of-sample accuracy,
    re-measured fresh on every scan.
    """
    agreement_component = safe_number(confidence, 0.0)
    if signal == "BUY":
        ml_component = safe_number(ml_prob, 0.5) * 100
    elif signal == "SELL":
        ml_component = (1 - safe_number(ml_prob, 0.5)) * 100
    else:
        ml_component = max(0, 50 - abs(safe_number(ml_prob, 0.5) - 0.5) * 100)
    rr_component = min(max(safe_number(rr, 0.0), 0.0) * 10, 35)

    if ml_oos_accuracy is None:
        ml_trust = 0.0
    else:
        ml_trust = float(np.clip((safe_number(ml_oos_accuracy, 0.5) - 0.50) / 0.08, 0.0, 1.0))

    ml_weight = 0.30 * ml_trust
    # Redistribute the ML weight it didn't earn back onto the two strategies
    # that don't carry this leakage risk, so the total still sums to 1.0
    # instead of silently shrinking the overall edge score for everyone.
    freed_weight = 0.30 - ml_weight
    agreement_weight = 0.45 + freed_weight * 0.6
    rr_weight = 0.25 + freed_weight * 0.4

    return float(round(agreement_component * agreement_weight + ml_component * ml_weight + rr_component * rr_weight, 2))


# ═══════════════════════════════════════════════════════════════════════════════
#  SCAN ONE ASSET
# ═══════════════════════════════════════════════════════════════════════════════

def scan_asset(asset: str, ticker: str, timeframe: str = "15m") -> ScanResult | None:
    try:
        timeframe = str(timeframe or "15m").lower()
        if timeframe not in TIMEFRAME_CONFIGS:
            timeframe = "15m"

        df_regime = get_timeframe_df(ticker, "1h")
        if df_regime is None:
            print(f"  [{asset} {timeframe}] No 1H regime data.")
            return None
        df_regime = add_indicators(df_regime)
        regime, _ = classify_regime(df_regime)
        t1h = trend_label(df_regime)

        df_15m_for_label = get_timeframe_df(ticker, "15m")
        t15m = trend_label(df_15m_for_label) if df_15m_for_label is not None else "Unavailable"

        df_entry = get_timeframe_df(ticker, timeframe)
        if df_entry is None:
            print(f"  [{asset} {timeframe}] No entry data.")
            return None
        df_entry = add_indicators(df_entry)
        df_entry = train_ensemble(df_entry)

        prelim = strategy_confluence(df_entry)
        mtf_context, mtf_score, mtf_dir, mtf_strength = mtf_confirmation(ticker, prelim["dominant"])
        confluence = strategy_confluence(df_entry, mtf_vote=(mtf_dir, mtf_strength))

        dominant = confluence["dominant"]
        # Even when the final grade is NO TRADE, build a research-only
        # hypothetical BUY/SELL plan so the No Trade Tracker can test what
        # would have happened if the blocked idea had been taken anyway.
        signal = "BUY" if dominant == "BULLISH" else "SELL" if dominant == "BEARISH" else choose_shadow_research_direction(confluence)
        price = safe_number(df_entry["Close"].iloc[-1])
        atr = safe_number(df_entry["ATR"].iloc[-1], 0.0) if "ATR" in df_entry.columns else 0.0
        rsi = safe_number(df_entry["RSI"].iloc[-1], 50.0) if "RSI" in df_entry.columns else 50.0
        plan = build_trade_plan(price, atr, signal)
        # Confidence is system agreement across ALL active systems.
        # Example: 1/5 agreement = 20%, 3/5 = 60%, 5/5 = 100%.
        confidence = safe_number(
            np.clip((safe_number(confluence.get("agree_count"), 0.0) / max(1, safe_number(confluence.get("total_systems"), 5.0))) * 100, 0, 100),
            0.0,
        )
        grade, grade_reason = grade_signal(confluence, plan["rr"])
        ml_oos_accuracy = df_entry.attrs.get("ml_oos_accuracy")
        ml_oos_n = df_entry.attrs.get("ml_oos_n", 0)
        edge_score = compute_edge_score(signal, confidence, confluence["ml_prob"], plan["rr"], ml_oos_accuracy)
        candle_close = str(df_entry["Date"].iloc[-1])

        vote_summary = ", ".join(f"{name}:{v['direction'][:4]}({v['strength']:.2f})" for name, v in confluence["votes"].items())
        mtf_summary = "/".join(f"{tf}:{payload.get('direction','NEUT')[:4]}" for tf, payload in mtf_context.items() if isinstance(payload, dict))
        ml_oos_label = f"{ml_oos_accuracy:.1%} (n={ml_oos_n})" if ml_oos_accuracy is not None else "unvalidated"
        reason = f"{grade_reason} | {vote_summary} | MTF score {mtf_score:.0f}% ({mtf_summary}) | Regime: {regime} | RSI {rsi:.1f} | ML OOS acc: {ml_oos_label}"

        result = ScanResult(
            asset=asset, ticker=ticker, timeframe=timeframe, signal=signal, grade=grade,
            confidence=confidence, edge_score=edge_score, ml_prob=confluence["ml_prob"],
            entry=price, sl=plan["sl"], tp=plan["tp"], rr=plan["rr"], regime=regime,
            rsi=safe_number(rsi, 50.0), atr=safe_number(atr),
            trend_1h=t1h, trend_15m=t15m, reason=reason, candle_close=candle_close,
            mtf_score=mtf_score, mtf_context=mtf_context, strategy_votes=confluence["votes"],
        )
        tag = "✅" if grade != "NO TRADE" else "👻"
        print(f"  [{asset} {timeframe}] {tag} {signal} | Grade {grade} | Agreement {confidence:.1f}% | Edge {edge_score:.1f} | RR {plan['rr']:.2f} | MTF {mtf_score:.2f}% | {confluence['agree_count']}/{confluence['total_systems']} agree")
        return result
    except Exception as e:
        print(f"  [{asset} {timeframe}] ERROR: {e}")
        traceback.print_exc()
        return None


# ═══════════════════════════════════════════════════════════════════════════════
#  TELEGRAM
# ═══════════════════════════════════════════════════════════════════════════════

def next_benzino_display_id() -> str:
    """Atomically increment the persistent sequential display counter.
    Returns strings like 'Benzino-01', 'Benzino-02', ... 'Benzino-137', etc.
    Backed by a single counter row — survives admin resets that delete scanner_signals.
    """
    try:
        conn = db_connect()
        with conn:
            with conn.cursor() as cur:
                cur.execute(
                    "UPDATE benzino_signal_counter SET counter = counter + 1 WHERE id = 1 RETURNING counter"
                )
                row = cur.fetchone()
                n = int(row["counter"]) if row else 1
        conn.close()
        return f"Benzino-{n:02d}"
    except Exception as e:
        print(f"[DB] next_benzino_display_id failed: {e}")
        return "Benzino-00"


def build_telegram_message(sig: ScanResult, display_id: str | None = None) -> str:
    def clean(v):
        return html.escape(str(v if v is not None else ""))

    def price_decimals_for_asset(asset: str) -> int:
        """TradingView-style display precision for Entry, Stop Loss, and Take Profit."""
        asset = str(asset or "").upper().strip()

        if asset.endswith("JPY"):
            return 3

        if asset in {"OIL", "BRENT", "NATGAS"}:
            return 3

        if asset in {
            "BTCUSD", "ETHUSD",
            "XAUUSD", "XAGUSD",
            "COPPER",
            "SP500", "NAS100", "DOW30",
            "NVDA", "MU",
        }:
            return 2

        # Non-JPY FX pairs normally display 5 decimals on TradingView/broker charts.
        if len(asset) == 6 and asset.isalpha():
            return 5

        return 2

    def fmt_price(x):
        """Format Entry, Stop Loss, and Take Profit using TradingView-style asset precision."""
        try:
            x = float(x)
            decimals = price_decimals_for_asset(sig.asset)
            return f"{x:,.{decimals}f}"
        except Exception:
            return str(x)

    def fmt_metric(x, decimals: int = 2):
        try:
            return f"{float(x):.{decimals}f}"
        except Exception:
            return str(x)

    def compact_trend(label: str) -> str:
        label = str(label or "Unavailable").strip()
        label = label.split("(", 1)[0].strip()
        return label or "Unavailable"

    def mtf_trend(tf: str) -> str:
        """Return the stored MTF trend direction for a timeframe, including 4H."""
        ctx = sig.mtf_context or {}
        row = ctx.get(tf) or ctx.get(tf.lower()) or ctx.get(tf.upper()) or {}
        direction = str(row.get("direction", "Unavailable")).strip()
        if not direction or direction.upper() == "NEUTRAL":
            return "Neutral"
        if direction.upper() == "BULLISH":
            return "Bullish"
        if direction.upper() == "BEARISH":
            return "Bearish"
        return direction.title()

    def grade_stars(grade: str) -> str:
        return {"A+": "⭐⭐⭐⭐⭐", "A": "⭐⭐⭐⭐", "B": "⭐⭐⭐", "C": "⭐⭐"}.get(str(grade or "").upper(), "")

    def vote_icon(direction: str) -> str:
        direction = str(direction or "").upper()
        if direction == "BULLISH":
            return "🟩"
        if direction == "BEARISH":
            return "🟥"
        return "⬜"

    def vote_line(name: str, payload: dict) -> str:
        direction = str(payload.get("direction", "NEUTRAL")).upper()
        strength = fmt_metric(safe_number(payload.get("strength"), 0.0))
        # Dotted spacing is fixed-width enough for Telegram while staying readable.
        short_name = str(name or "").replace("MTFConfirmation", "MTFConfirm")
        dots = "." * max(2, 14 - len(short_name))
        return f"{vote_icon(direction)} {clean(short_name)} {dots} {clean(direction)} ({strength})"

    emoji = "🟢" if sig.signal == "BUY" else "🔴" if sig.signal == "SELL" else "⚪"
    tf_label = str(sig.timeframe or "").upper()
    stars = grade_stars(sig.grade)
    separator = "━━━━━━━━━━━━━━━━━━"

    # Use the exact display_id saved with the scanner row, so Telegram matches Supabase and the app.
    shown_id = str(display_id or getattr(sig, "display_id", "") or "").strip() or "Benzino-00"

    votes_lines = "\n".join(
        vote_line(name, v)
        for name, v in (sig.strategy_votes or {}).items()
        if isinstance(v, dict)
    )
    if not votes_lines:
        votes_lines = "No strategy votes available"

    return f"""
{emoji} <b>BENZINO {clean(sig.signal)} SIGNAL</b>
{stars} Grade {clean(sig.grade)} • {clean(sig.asset)} • {clean(tf_label)}

{separator}

📊 <b>Setup Quality</b>
Agreement: {fmt_metric(sig.confidence)}%
Edge Score: {fmt_metric(sig.edge_score)}
ML Probability: {fmt_metric(float(sig.ml_prob) * 100 if safe_number(sig.ml_prob, 0.5) <= 1 else sig.ml_prob)}%
MTF Score: {fmt_metric(sig.mtf_score)}%

💰 <b>Trade Plan</b>
Entry: <code>{fmt_price(sig.entry)}</code>
Stop Loss: <code>{fmt_price(sig.sl)}</code>
Take Profit: <code>{fmt_price(sig.tp)}</code>
Risk/Reward: <code>{fmt_metric(sig.rr)}R</code>

⚙️ <b>Strategy Confluence</b>
{votes_lines}

🌍 <b>Market Context</b>
1H Trend: {clean(compact_trend(sig.trend_1h))}
15M Trend: {clean(compact_trend(sig.trend_15m))}
4H Trend: {clean(mtf_trend("4h"))}
Regime: {clean(sig.regime)}
RSI: {fmt_metric(sig.rsi)}

{separator}
🆔 <code>{clean(shown_id)}</code>
""".strip()

def send_telegram_to(message: str, chat_ids: list[str]) -> tuple[bool, str]:
    """Send one message to an explicit list of chat IDs."""
    token = os.environ.get("TELEGRAM_BOT_TOKEN", "").strip()
    chat_ids = [str(c).strip() for c in chat_ids if str(c).strip()]
    if not token or not chat_ids:
        return False, "No bot token or no recipients."
    url = f"https://api.telegram.org/bot{token}/sendMessage"
    sent, errors = 0, []
    for chat_id in chat_ids:
        try:
            resp = requests.post(url, json={"chat_id": chat_id, "text": message, "parse_mode": "HTML"}, timeout=10)
            if resp.status_code == 200: sent += 1
            else: errors.append(f"{chat_id}: HTTP {resp.status_code}")
        except Exception as e:
            errors.append(f"{chat_id}: {e}")
    return (True, f"Sent to {sent}/{len(chat_ids)} recipient(s).") if sent else (False, "; ".join(errors))


def get_activated_telegram_recipients(asset: str, timeframe: str = "") -> list[str]:
    """
    Read user_telegram_settings (configured from the Settings page in app.py) and
    return every chat_id that should receive this asset+timeframe's alert.

    A user receives the alert if alerts_enabled = TRUE AND their selected
    timeframe(s) (from user_settings.settings_json, e.g. preferred_timeframe)
    include this signal's timeframe, AND either:
      - all_signals_alerts = TRUE (wants every signal), or
      - watchlist_alerts = TRUE AND this asset is in their saved user_watchlists.

    Without the timeframe check, a user who selected "1h" would also receive
    15m/4h/1d alerts for any watchlist asset, since the original version only
    ever matched on asset and ignored timeframe entirely. If a user has no
    timeframe preference saved, _extract_timeframes_from_settings() already
    falls back to DEFAULT_USER_TIMEFRAME, so this filter degrades safely.
    """
    sql = """
    SELECT uts.scan_owner, uts.telegram_chat_id, uts.watchlist_alerts, uts.all_signals_alerts
    FROM user_telegram_settings uts
    WHERE uts.alerts_enabled = TRUE
      AND COALESCE(uts.telegram_chat_id, '') <> ''
    """
    try:
        conn = db_connect()
        with conn.cursor() as cur:
            cur.execute(sql)
            rows = [dict(r) for r in cur.fetchall()]
        conn.close()
    except Exception as e:
        print(f"[DB] get_activated_telegram_recipients failed: {e}")
        return []

    tf_norm = _normalize_timeframe(timeframe) if timeframe else ""
    user_prefs = get_user_scan_preferences() if tf_norm else {}

    recipients = []
    for row in rows:
        owner = str(row.get("scan_owner", ""))

        if tf_norm:
            owner_timeframes = user_prefs.get(owner, {}).get("timeframes") or [DEFAULT_USER_TIMEFRAME]
            if tf_norm not in owner_timeframes:
                continue

        if row.get("all_signals_alerts"):
            recipients.append(str(row["telegram_chat_id"]))
            continue
        if row.get("watchlist_alerts"):
            owner_watchlist = load_user_watchlist(owner)
            if asset in owner_watchlist:
                recipients.append(str(row["telegram_chat_id"]))
    return list(dict.fromkeys(recipients))  # de-duplicated, order-preserving


def send_telegram(message: str, asset: str = "", timeframe: str = "") -> tuple[bool, str]:
    """
    Send an alert to BOTH:
      1. The global TELEGRAM_CHAT_IDS env var (the owner/admin default — always
         receives everything, unchanged from earlier versions, and is NOT
         filtered by timeframe since it has no per-user preference attached), and
      2. Every per-user chat_id activated in Settings whose routing rules match
         this asset AND timeframe (see get_activated_telegram_recipients).

    Recipients are merged and de-duplicated so nobody gets the same alert twice.
    """
    token = os.environ.get("TELEGRAM_BOT_TOKEN", "").strip()
    global_ids = [c.strip() for c in os.environ.get("TELEGRAM_CHAT_IDS", "").split(",") if c.strip()]
    user_ids = get_activated_telegram_recipients(asset, timeframe) if asset else []
    all_ids = list(dict.fromkeys(global_ids + user_ids))

    if not token or not all_ids:
        return False, "TELEGRAM_BOT_TOKEN not set or no recipients (global + per-user) configured."
    return send_telegram_to(message, all_ids)


def telegram_configured() -> bool:
    """Return True only when Telegram credentials exist.

    Telegram is optional. Missing credentials must never affect whether a
    qualified A+/A/B/C BUY/SELL setup is opened, journaled, evaluated, or
    shown in the dashboard.
    """
    token = os.environ.get("TELEGRAM_BOT_TOKEN", "").strip()
    ids = os.environ.get("TELEGRAM_CHAT_IDS", "").strip()
    if token and ids:
        return True
    # Telegram can also be "configured" purely through per-user activation in
    # Settings, with no global TELEGRAM_CHAT_IDS secret set at all.
    if token:
        try:
            conn = db_connect()
            with conn.cursor() as cur:
                cur.execute("SELECT 1 FROM user_telegram_settings WHERE alerts_enabled = TRUE LIMIT 1")
                row = cur.fetchone()
            conn.close()
            return row is not None
        except Exception:
            return False
    return False


# ═══════════════════════════════════════════════════════════════════════════════
#  EVALUATE OPEN TRADES — TP / SL / EXPIRY + prop-firm ledger update
# ═══════════════════════════════════════════════════════════════════════════════

def evaluate_open_trades(assets: set[str] | None = None, timeframes: set[str] | None = None) -> None:
    open_trades = fetch_open_trades(assets=assets, timeframes=timeframes)
    if not open_trades:
        print("[Evaluate] No open trades.")
        return

    print(f"[Evaluate] Checking {len(open_trades)} open trade(s)...")
    for t in open_trades:
        asset, ticker, timeframe = t["asset"], t["ticker"], t["timeframe"]
        signal, entry, sl, tp = str(t["signal"]).upper(), float(t["entry"]), float(t["sl"]), float(t["tp"])
        signal_id = t["signal_id"]
        grade = t["grade"]

        df = get_timeframe_df(ticker, timeframe)
        if df is None:
            continue

        created = pd.to_datetime(t["created_at"], utc=True)
        df["Date"] = pd.to_datetime(df["Date"], utc=True)
        new_bars = df[df["Date"] > created]
        if new_bars.empty:
            continue

        bars_open = int(t.get("bars_open") or 0)
        closed = False

        for _, bar in new_bars.iterrows():
            bars_open += 1
            high, low = float(bar["High"]), float(bar["Low"])

            if signal == "BUY":
                hit_sl, hit_tp = low <= sl, high >= tp
            else:
                hit_sl, hit_tp = high >= sl, low <= tp

            if hit_sl and hit_tp:
                # Conservative: ambiguous same-candle hit treated as SL
                r_mult = -1.0
                close_trade(signal_id, sl, "SL", r_mult)
                update_prop_firm(signal_id, asset, grade, r_mult)
                print(f"  [{asset}] AMBIGUOUS same-candle TP+SL → conservatively marked SL.")
                closed = True
                break
            if hit_sl:
                r_mult = -1.0
                close_trade(signal_id, sl, "SL", r_mult)
                update_prop_firm(signal_id, asset, grade, r_mult)
                print(f"  [{asset}] Closed: SL hit ({r_mult:+.2f}R)")
                closed = True
                break
            if hit_tp:
                r_mult = abs(tp - entry) / abs(entry - sl) if abs(entry - sl) > 0 else 0
                close_trade(signal_id, tp, "TP", r_mult)
                update_prop_firm(signal_id, asset, grade, r_mult)
                print(f"  [{asset}] Closed: TP hit ({r_mult:+.2f}R)")
                closed = True
                break

        if closed:
            continue

        expiry_bars = int(TIMEFRAME_CONFIGS.get(str(timeframe).lower(), {}).get("expiry_bars", EXPIRY_BARS))
        if bars_open >= expiry_bars:
            last_price = float(df["Close"].iloc[-1])
            risk_dist = abs(entry - sl)
            r_mult = ((last_price - entry) / risk_dist if signal == "BUY"
                      else (entry - last_price) / risk_dist) if risk_dist > 0 else 0
            close_trade(signal_id, last_price, "EXPIRY", r_mult)
            update_prop_firm(signal_id, asset, grade, r_mult)
            print(f"  [{asset}] Closed: EXPIRED after {bars_open} bars ({r_mult:+.2f}R)")
        else:
            bump_bars_open(signal_id, bars_open)


def backfill_shadow_trade_plans(assets: set[str] | None = None, timeframes: set[str] | None = None, max_age_days: int = 60) -> int:
    """Repair legacy NO TRADE rows that were saved with Entry = SL = TP.

    Older builds stored split/HOLD rows without a usable hypothetical trade
    plan, so the app could not evaluate them. This backfills a research-only
    BUY/SELL direction and 1:2 ATR-based plan using the row's saved entry/ATR.
    The row stays SHADOW and remains excluded from real journal/prop metrics.
    """
    try:
        conn = db_connect()
        with conn.cursor() as cur:
            sql = """
                SELECT signal_id, asset, timeframe, signal, entry, sl, tp, atr, ml_prob, strategy_votes
                FROM scanner_signals
                WHERE status = 'SHADOW'
                  AND shadow_outcome IS NULL
                  AND created_at >= NOW() - INTERVAL '%s days'
                  AND (
                        UPPER(TRIM(COALESCE(signal,''))) = 'HOLD'
                     OR ABS(COALESCE(entry,0) - COALESCE(sl,0)) <= 0.00000001
                     OR ABS(COALESCE(sl,0) - COALESCE(tp,0)) <= 0.00000001
                  )
            """
            params: list = [max_age_days]
            if assets:
                sql += " AND asset = ANY(%s)"
                params.append(list(assets))
            if timeframes:
                sql += " AND timeframe = ANY(%s)"
                params.append(list(timeframes))
            sql += " ORDER BY created_at ASC LIMIT 1000"
            cur.execute(sql, tuple(params))
            rows = [dict(r) for r in cur.fetchall()]
        conn.close()
    except Exception as exc:
        print(f"[Shadow] Backfill fetch failed: {exc}")
        return 0

    updated = 0
    for row in rows:
        try:
            entry = safe_number(row.get("entry"), 0.0)
            atr = safe_number(row.get("atr"), 0.0)
            if entry <= 0 or atr <= 0:
                continue
            votes = row.get("strategy_votes") or {}
            if isinstance(votes, str):
                try:
                    votes = json.loads(votes)
                except Exception:
                    votes = {}
            confluence = {"dominant": "SPLIT", "votes": votes, "ml_prob": safe_number(row.get("ml_prob"), 0.5)}
            direction = choose_shadow_research_direction(confluence)
            plan = build_trade_plan(entry, atr, direction)
            if abs(plan["sl"] - entry) <= 0 or abs(plan["tp"] - plan["sl"]) <= 0:
                continue
            conn = db_connect()
            with conn:
                with conn.cursor() as cur:
                    cur.execute(
                        """
                        UPDATE scanner_signals
                        SET signal = %s, sl = %s, tp = %s, rr = %s,
                            reason = COALESCE(reason, '') || ' | Shadow research plan backfilled: hypothetical ' || %s || ' using ATR 1:2 RR.'
                        WHERE signal_id = %s
                          AND status = 'SHADOW'
                          AND shadow_outcome IS NULL
                        """,
                        (direction, round(plan["sl"], 8), round(plan["tp"], 8), round(plan["rr"], 2), direction, row["signal_id"]),
                    )
                    updated += cur.rowcount
            conn.close()
        except Exception as exc:
            print(f"[Shadow] Backfill skipped row {row.get('signal_id')}: {exc}")
    if updated:
        print(f"[Shadow] Backfilled {updated} legacy NO TRADE hypothetical plan(s).")
    return updated


def evaluate_shadow_trades(assets: set[str] | None = None, timeframes: set[str] | None = None) -> int:
    """
    Hypothetically resolve NO TRADE (shadow) signals using the exact same
    TP/SL/expiry logic as real trades, but writing only to shadow_* columns.
    Returns the number of shadow rows resolved this run.

    This is what lets the dashboard show "if you had taken every blocked idea,
    your hypothetical win rate would have been X%" — clearly separate from the
    real journal win rate, which only ever counts A+/A/B/C trades.
    """
    backfill_shadow_trade_plans(assets=assets, timeframes=timeframes)
    shadow_trades = fetch_unresolved_shadow_trades(assets=assets, timeframes=timeframes)
    if not shadow_trades:
        print("[Shadow] No unresolved NO TRADE rows to evaluate.")
        return 0

    print(f"[Shadow] Checking {len(shadow_trades)} unresolved NO TRADE row(s)...")
    resolved = 0
    for t in shadow_trades:
        asset, ticker, timeframe = t["asset"], t["ticker"], t["timeframe"]
        signal, entry, sl, tp = str(t["signal"]).upper(), float(t["entry"]), float(t["sl"]), float(t["tp"])
        signal_id = t["signal_id"]

        if abs(entry - sl) <= 0 or sl == tp:
            continue  # no usable hypothetical trade plan was ever built for this row

        df = get_timeframe_df(ticker, timeframe)
        if df is None:
            continue

        created = pd.to_datetime(t["created_at"], utc=True)
        df["Date"] = pd.to_datetime(df["Date"], utc=True)
        new_bars = df[df["Date"] > created]
        if new_bars.empty:
            continue

        bars_open = int(t.get("bars_open") or 0)
        expiry_bars = int(TIMEFRAME_CONFIGS.get(str(timeframe).lower(), {}).get("expiry_bars", EXPIRY_BARS))
        closed = False

        for _, bar in new_bars.iterrows():
            bars_open += 1
            high, low = float(bar["High"]), float(bar["Low"])
            if signal == "BUY":
                hit_sl, hit_tp = low <= sl, high >= tp
            else:
                hit_sl, hit_tp = high >= sl, low <= tp

            if hit_sl and hit_tp:
                # Same conservative rule as real trades: ambiguous same-candle
                # TP+SL is treated as SL.
                close_shadow_trade(signal_id, sl, "SHADOW_SL", -1.0)
                closed = True
                break
            if hit_sl:
                close_shadow_trade(signal_id, sl, "SHADOW_SL", -1.0)
                closed = True
                break
            if hit_tp:
                r_mult = abs(tp - entry) / abs(entry - sl)
                close_shadow_trade(signal_id, tp, "SHADOW_TP", r_mult)
                closed = True
                break

        if closed:
            resolved += 1
            continue

        if bars_open >= expiry_bars:
            last_price = float(df["Close"].iloc[-1])
            risk_dist = abs(entry - sl)
            r_mult = ((last_price - entry) / risk_dist if signal == "BUY"
                      else (entry - last_price) / risk_dist) if risk_dist > 0 else 0
            close_shadow_trade(signal_id, last_price, "SHADOW_EXPIRY", r_mult)
            resolved += 1
        else:
            bump_bars_open(signal_id, bars_open)

    print(f"[Shadow] Resolved {resolved} NO TRADE hypothetical outcome(s) this run.")
    return resolved


# ═══════════════════════════════════════════════════════════════════════════════
#  MAIN SCAN LOOP
# ═══════════════════════════════════════════════════════════════════════════════

def run_scan() -> None:
    run_id = uuid.uuid4().hex
    started = datetime.now(timezone.utc)
    scan_assets, active_tfs, scan_mode = build_scan_plan(started)
    print(f"\n{'='*70}")
    print(f"  BENZINO INSTITUTIONAL SCANNER — {started.strftime('%Y-%m-%d %H:%M UTC')}")
    print(f"  Mode: {scan_mode} | Assets: {len(scan_assets)} | Active TFs: {', '.join(active_tfs)} | Configured TFs: {', '.join(SCAN_TIMEFRAMES)}")
    print(f"  Account: ${ACCOUNT_SIZE:,.0f} | Risk: {RISK_PER_TRADE*100:.2f}% | Leverage: 1:{LEVERAGE:g}")
    if set(active_tfs) != set(SCAN_TIMEFRAMES):
        skipped = [tf for tf in SCAN_TIMEFRAMES if tf not in active_tfs]
        print(f"  Runtime optimiser: skipped TFs this run: {', '.join(skipped) if skipped else 'None'}")
    if scan_mode == "MASTER_SCHEDULED":
        print("  Asset universe: full MASTER_WATCHLIST. User watchlists only filter dashboard visibility.")
    if scan_mode == "MASTER_MANUAL_FULL":
        print("  Manual full scan requested — scanning full MASTER_WATCHLIST.")
    print(f"{'='*70}\n")

    _TF_CACHE.clear()
    init_tables()
    force_open_graded_setups()

    # 1. Resolve outcomes for everything already open BEFORE scanning for new setups.
    evaluate_open_trades(assets=set(scan_assets.keys()), timeframes=set(active_tfs))
    evaluate_shadow_trades(assets=set(scan_assets.keys()), timeframes=set(active_tfs))

    journaled, alerted, shadowed = 0, 0, 0
    assets_scanned = 0
    asset_seconds: list[float] = []

    for asset, ticker in scan_assets.items():
        asset_start = time.perf_counter()
        asset_attempted = False
        print(f"Scanning {asset} ({ticker}) across {len(active_tfs)} active timeframe(s)...")
        for tf in active_tfs:
            asset_attempted = True
            result = scan_asset(asset, ticker, timeframe=tf)
            if result is None:
                continue
            if duplicate_setup_exists(asset, result.timeframe, result.signal, result.candle_close):
                # Existing rows may have been created by an older build. Fix their
                # status before skipping so graded BUY/SELL rows cannot remain SHADOW.
                force_open_graded_setups()
                print(f"  [{asset} {tf}] Setup already stored for this candle — skipping duplicate.")
                continue

            grade_norm = str(result.grade or "").strip().upper()
            signal_norm = str(result.signal or "").strip().upper()

            if grade_norm == "NO TRADE" or signal_norm == "HOLD":
                save_signal(result)
                shadowed += 1
                print(f"  [{asset} {tf}] Stored as SHADOW research row. Telegram not used for NO TRADE.")
                continue

            # Critical rule: journaling/opening is independent of Telegram.
            # A+/A/B/C BUY/SELL setups are saved as OPEN inside save_signal().
            saved = save_signal(result)
            journaled += 1
            if saved:
                print(f"  [{asset} {tf}] Stored as OPEN journal trade. Telegram is optional only.")

            if not telegram_configured():
                print(f"  [{asset} {tf}] Telegram not configured — optional alert skipped.")
                continue

            can_alert = True
            block_reason = ""
            if duplicate_alert_exists(asset, result.timeframe, result.signal, result.candle_close):
                can_alert, block_reason = False, "duplicate candle/signal already alerted"

            # Telegram duplicate/open-slot checks only control notifications.
            # They must never close, shadow, or prevent an already-open journal row.
            if can_alert:
                open_slot = open_trade_for_slot(asset, result.timeframe)
                if open_slot is not None and open_slot.get("signal_id") != result.signal_id:
                    can_alert = False
                    block_reason = f"slot still open (signal {open_slot['signal_id'][:8]})"

            if can_alert:
                message = build_telegram_message(result, getattr(result, "display_id", None))
                ok, info = send_telegram(message, asset, result.timeframe)
                if ok:
                    result.alert_sent = True
                    alerted += 1
                    mark_alert_sent(result.signal_id)
                    print(f"  [{asset} {tf}] 📲 {info}")
                else:
                    print(f"  [{asset} {tf}] Telegram optional alert failed: {info}")
            else:
                print(f"  [{asset} {tf}] Telegram alert suppressed — {block_reason}")

        if asset_attempted:
            assets_scanned += 1
            asset_seconds.append(time.perf_counter() - asset_start)

    force_open_graded_setups()
    state = load_prop_firm_state()
    finished = datetime.now(timezone.utc)
    elapsed = (finished - started).total_seconds()
    print(f"\n{'='*70}")
    print(f"  Scan complete in {elapsed:.1f}s")
    open_count = len(fetch_open_trades(assets=set(scan_assets.keys()), timeframes=set(active_tfs)))
    print(f"  Journaled (A+/A/B/C): {journaled} | Open trades: {open_count} | Alerted: {alerted} | Shadowed (NO TRADE): {shadowed}")
    print(f"  Runtime: fastest asset {min(asset_seconds) if asset_seconds else 0:.1f}s | slowest {max(asset_seconds) if asset_seconds else 0:.1f}s | avg {float(np.mean(asset_seconds)) if asset_seconds else 0:.1f}s")
    print(f"  Prop firm: equity ${float(state['current_equity']):,.2f} "
          f"({(float(state['current_equity'])/float(state['starting_balance'])-1)*100:+.2f}%) "
          f"| status {state['status']} | trading days {state['trading_days']}")
    print(f"{'='*70}\n")

    log_runtime(
        run_id=run_id,
        started_at=started,
        finished_at=finished,
        total_seconds=elapsed,
        assets_scanned=assets_scanned,
        signals_saved=journaled,
        shadow_saved=shadowed,
        open_trades=open_count,
        alerted=alerted,
        timeframes_scanned=active_tfs,
        asset_seconds=asset_seconds,
    )


if __name__ == "__main__":
    run_scan()