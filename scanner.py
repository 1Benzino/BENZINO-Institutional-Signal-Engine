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
import re
from decimal import Decimal
from datetime import datetime, timezone
from zoneinfo import ZoneInfo
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


def load_local_env_file() -> None:
    """Load local .env values before scanner configuration is read.

    GitHub Actions already provides environment variables from secrets, so this
    only fills missing values when running `python3 scanner.py` locally. It first
    tries python-dotenv, then falls back to a small built-in .env parser so the
    scanner still works even if python-dotenv is not installed.
    """
    env_paths = []
    try:
        env_paths.append(os.path.join(os.getcwd(), ".env"))
    except Exception:
        pass
    try:
        env_paths.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".env"))
    except Exception:
        pass

    # De-duplicate while preserving order.
    seen = set()
    env_paths = [p for p in env_paths if p and not (p in seen or seen.add(p))]

    loaded_any = False
    try:
        from dotenv import load_dotenv  # type: ignore
        for env_path in env_paths:
            if os.path.exists(env_path):
                load_dotenv(env_path, override=False)
                loaded_any = True
    except Exception:
        for env_path in env_paths:
            if not os.path.exists(env_path):
                continue
            try:
                with open(env_path, "r", encoding="utf-8") as f:
                    for raw_line in f:
                        line = raw_line.strip()
                        if not line or line.startswith("#") or "=" not in line:
                            continue
                        key, value = line.split("=", 1)
                        key = key.strip()
                        value = value.strip().strip('"').strip("'")
                        if key and key not in os.environ:
                            os.environ[key] = value
                loaded_any = True
            except Exception:
                continue

    if loaded_any:
        print("[ENV] Loaded local .env values for scanner run.")


load_local_env_file()


# Safety guard: no legacy CAPITAL:* symbol should ever reach yfinance.
_ORIGINAL_YF_DOWNLOAD = yf.download
def _benzino_safe_yf_download(tickers, *args, **kwargs):
    def _clean_one(t):
        s = str(t or "").strip()
        if s.upper().startswith("CAPITAL:"):
            asset = s.split(":", 1)[1].strip().upper()
            mapped = YAHOO_FALLBACK_TICKERS.get(asset, "")
            if mapped:
                return mapped
            # Return a harmless impossible symbol rather than CAPITAL:* to avoid long Yahoo errors.
            return "__BENZINO_SKIP__"
        return s
    if isinstance(tickers, (list, tuple, set)):
        tickers = [_clean_one(t) for t in tickers]
    else:
        tickers = _clean_one(tickers)
    return _ORIGINAL_YF_DOWNLOAD(tickers, *args, **kwargs)
yf.download = _benzino_safe_yf_download

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
    # Signal market data uses Yahoo/yfinance-compatible symbols.
    # Capital.com epics are used only for broker execution, broker constraints,
    # actual execution sync, and 1-minute Capital replay.
    "XAUUSD": "GC=F", "XAGUSD": "SI=F", "OIL": "CL=F", "BRENT": "BZ=F",
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

YAHOO_FALLBACK_TICKERS = {
    "XAUUSD": "GC=F", "XAGUSD": "SI=F", "OIL": "CL=F", "BRENT": "BZ=F",
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
        {"XAUUSD": "GC=F", "BTCUSD": "BTC-USD"}

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
            "ben": {"XAUUSD": "GC=F", "BTCUSD": "BTC-USD"},
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

    # Capital.com is now the scanner pricing source of truth.
    # Keep MASTER_WATCHLIST as Yahoo fallback metadata, but pass CAPITAL:<asset>
    # through the scan loop so signal candles, trade plans, replay, and execution
    # all resolve from the same Capital.com feed.
    assets: dict[str, str] = {asset: f"CAPITAL:{asset}" for asset in MASTER_WATCHLIST}
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
    "15m": {"interval": "15m", "period": "60d",  "expiry_bars": 56},
    "1h":  {"interval": "60m", "period": "730d", "expiry_bars": 56},
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
_CAPITAL_PRICE_CACHE: dict[tuple[str, str, int], pd.DataFrame | None] = {}
_CAPITAL_RANGE_PRICE_CACHE: dict[tuple[str, str, str, str], pd.DataFrame | None] = {}
_RUNTIME_BREAKDOWN: dict[str, float] = {}


def _runtime_add(name: str, seconds: float) -> None:
    try:
        _RUNTIME_BREAKDOWN[name] = float(_RUNTIME_BREAKDOWN.get(name, 0.0)) + float(seconds)
    except Exception:
        pass


def _runtime_start() -> float:
    return time.perf_counter()


def _runtime_stop(name: str, start: float) -> None:
    _runtime_add(name, time.perf_counter() - float(start))



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
EXPIRY_BARS = 56          # fallback auto-expiry if a timeframe has no explicit expiry_bars

# FTMO-style challenge rules — mirrors app.py's Challenge Mode panel
CHALLENGE_PROFIT_TARGET    = 0.10
CHALLENGE_MAX_DAILY_LOSS   = 0.05
CHALLENGE_MAX_TOTAL_LOSS   = 0.10
CHALLENGE_MIN_TRADING_DAYS = 4
# Legacy global prop ledger is no longer used for user-facing prop analytics.
# User prop challenges are rebuilt/simulated per logged-in user in app.py.
# Keep this off unless you explicitly need the old SCAN_OWNER aggregate ledger for debugging.
ENABLE_LEGACY_GLOBAL_PROP_LEDGER = os.environ.get("ENABLE_LEGACY_GLOBAL_PROP_LEDGER", "false").strip().lower() in {"1", "true", "yes", "y"}

GRADE_RANK = {"A+": 4, "A": 3, "B": 2, "C": 1, "NO TRADE": 0}

# Shadow research backlog controls. Supabase pooler can time out if thousands of
# rows are resolved one-by-one in a single scanner run, so backlog resolution is
# intentionally chunked and committed in batches. Increase carefully only if the
# database comfortably handles the load.
# Shadow research is intentionally lightweight. It must never slow down the live scanner.
# These are NO TRADE research rows, so the real journal/prop/alerts are unaffected.
SHADOW_EVAL_LIMIT = int(os.environ.get("SHADOW_EVAL_LIMIT", "25"))
SHADOW_MAX_AGE_DAYS = int(os.environ.get("SHADOW_MAX_AGE_DAYS", "7"))
SHADOW_DB_UPDATE_BATCH_SIZE = int(os.environ.get("SHADOW_DB_UPDATE_BATCH_SIZE", "100"))
SHADOW_BACKFILL_LIMIT = int(os.environ.get("SHADOW_BACKFILL_LIMIT", "800"))

# One-off / safety replay controls. Default is OFF after historical cleanup.
# When true, the scanner replays existing resolved Supabase outcomes using the
# Capital.com 1-minute replay engine only. If Capital 1-minute data is not
# available, the row stays open/unchecked for a later run; timeframe candle
# fallback is intentionally disabled for clean Capital-only audit data.
REPLAY_EXISTING_OUTCOMES = os.environ.get("REPLAY_EXISTING_OUTCOMES", "false").strip().lower() in {"1", "true", "yes", "y"}
REPLAY_EXISTING_OUTCOMES_DAYS = int(os.environ.get("REPLAY_EXISTING_OUTCOMES_DAYS", "30"))
REPLAY_EXISTING_OUTCOMES_LIMIT = int(os.environ.get("REPLAY_EXISTING_OUTCOMES_LIMIT", "300"))

# Capital.com actual execution + auto-trading controls. Auto-trading is opt-in.
# Keep this disabled for live accounts unless you have explicitly tested on demo.
CAPITAL_SYNC_EXECUTIONS = os.environ.get("CAPITAL_SYNC_EXECUTIONS", "true").strip().lower() in {"1", "true", "yes", "y"}
CAPITAL_ACTIVITY_LOOKBACK_SECONDS = int(os.environ.get("CAPITAL_ACTIVITY_LOOKBACK_SECONDS", str(7 * 24 * 60 * 60)))
CAPITAL_MATCH_WINDOW_HOURS = int(os.environ.get("CAPITAL_MATCH_WINDOW_HOURS", "2"))
CAPITAL_AUTO_TRADE_ENABLED = os.environ.get("CAPITAL_AUTO_TRADE_ENABLED", "true").strip().lower() in {"1", "true", "yes", "y"}  # platform kill-switch; per-user toggle is in Supabase
CAPITAL_AUTO_TRADE_REQUIRE_DEMO = os.environ.get("CAPITAL_AUTO_TRADE_REQUIRE_DEMO", "true").strip().lower() in {"1", "true", "yes", "y"}
CAPITAL_AUTO_TRADE_GRADES = {g.strip().upper() for g in os.environ.get("CAPITAL_AUTO_TRADE_GRADES", "A+,A,B,C").split(",") if g.strip()}
# Platform ceiling only. The actual grades tested on demo are chosen per user in user_capital_connections.auto_trade_grades.
CAPITAL_AUTO_TRADE_GRADES = CAPITAL_AUTO_TRADE_GRADES.intersection({"A+", "A", "B", "C"}) or {"A+", "A", "B", "C"}
CAPITAL_AUTO_TRADE_TIMEFRAMES = {t.strip().lower() for t in os.environ.get("CAPITAL_AUTO_TRADE_TIMEFRAMES", "15m,1h,4h,1d").split(",") if t.strip()}
CAPITAL_AUTO_TRADE_OWNER = os.environ.get("CAPITAL_AUTO_TRADE_OWNER", "").strip()
CAPITAL_AUTO_TRADE_MIN_SIZE = float(os.environ.get("CAPITAL_AUTO_TRADE_MIN_SIZE", "0.01"))
CAPITAL_AUTO_TRADE_MAX_SIZE = float(os.environ.get("CAPITAL_AUTO_TRADE_MAX_SIZE", "0"))  # 0 means no cap
CAPITAL_AUTO_TRADE_USE_STOPS = os.environ.get("CAPITAL_AUTO_TRADE_USE_STOPS", "true").strip().lower() in {"1", "true", "yes", "y"}
CAPITAL_AUTO_TRADE_SIZE_RETRY = os.environ.get("CAPITAL_AUTO_TRADE_SIZE_RETRY", "true").strip().lower() in {"1", "true", "yes", "y"}
CAPITAL_STRICT_1M_REPLAY_ONLY = os.environ.get("CAPITAL_STRICT_1M_REPLAY_ONLY", "true").strip().lower() in {"1", "true", "yes", "y"}
CAPITAL_MARGIN_BUFFER_PCT = float(os.environ.get("CAPITAL_MARGIN_BUFFER_PCT", "0.95"))
CAPITAL_FTMO_NORMALIZE_PNL = os.environ.get("CAPITAL_FTMO_NORMALIZE_PNL", "true").strip().lower() in {"1", "true", "yes", "y"}
FTMO_COMPARISON_LEVERAGE = float(os.environ.get("FTMO_COMPARISON_LEVERAGE", "100"))
CAPITAL_AUTO_TRADE_MAX_PER_DAY = int(os.environ.get("CAPITAL_AUTO_TRADE_MAX_PER_DAY", "10"))
CAPITAL_AUTO_TRADE_MIN_SESSION_TRADES = int(os.environ.get("CAPITAL_AUTO_TRADE_MIN_SESSION_TRADES", "20"))
NAIROBI_TZ = ZoneInfo("Africa/Nairobi")

# Capital.com execution leverage is broker-limited by asset class. BENZINO keeps
# FTMO simulation at 1:100, then stores an FTMO-equivalent normalized P/L for
# fair simulated-vs-actual comparison.
CAPITAL_ASSET_CLASS = {
    "BTCUSD": "crypto", "ETHUSD": "crypto",
    "NVDA": "shares", "MU": "shares",
    "SP500": "indices", "NAS100": "indices", "DOW30": "indices",
    "XAUUSD": "commodities", "XAGUSD": "commodities", "OIL": "commodities", "BRENT": "commodities", "NATGAS": "commodities", "COPPER": "commodities",
}
CAPITAL_LEVERAGE_CAPS = {
    "currencies": 100.0, "indices": 100.0, "commodities": 100.0,
    "crypto": 20.0, "shares": 20.0, "bonds": 200.0, "interest_rates": 200.0,
}
_CAPITAL_LAST_ERROR = {"text": ""}

# Schema migrations are intentionally OFF during normal scanner runs.
# Running ALTER TABLE / CREATE INDEX every 15 minutes can deadlock with another
# local/GitHub scanner. Apply the SQL migration once in Supabase, then keep this
# false. Set SCANNER_RUN_SCHEMA_MIGRATIONS=true only for a one-off controlled run.
SCANNER_RUN_SCHEMA_MIGRATIONS = os.environ.get("SCANNER_RUN_SCHEMA_MIGRATIONS", "false").strip().lower() in {"1", "true", "yes", "y"}

# Capital history endpoints are optional. Open positions are enough for demo
# auto-trade matching. The history endpoints reject some lastPeriod values on
# some Capital accounts, so they are disabled unless explicitly enabled.
CAPITAL_FETCH_ACTIVITY_HISTORY = os.environ.get("CAPITAL_FETCH_ACTIVITY_HISTORY", "false").strip().lower() in {"1", "true", "yes", "y"}
CAPITAL_CONSTRAINT_REFRESH_HOURS = int(os.environ.get("CAPITAL_CONSTRAINT_REFRESH_HOURS", "24"))

# Audit guard: historical replay must never rewrite the original trade plan.
# Existing rows keep their original entry/sl/tp/rr. Replay is allowed to update
# only outcome fields such as status, exit_price, exit_reason, exit_at,
# r_multiple, bars_open, replay_checked_at, and shadow_* research columns.
LOCK_HISTORICAL_SIGNAL_PLANS = os.environ.get("LOCK_HISTORICAL_SIGNAL_PLANS", "true").strip().lower() in {"1", "true", "yes", "y"}
FORBIDDEN_HISTORICAL_PLAN_KEYS = {"entry", "sl", "tp", "rr"}




def load_enabled_user_capital_connection_for_sync() -> dict:
    """Load one enabled user-owned Capital connection for actual execution sync.

    CapitalSync should no longer require platform-wide CAPITAL_API_KEY /
    CAPITAL_IDENTIFIER / CAPITAL_PASSWORD env values. The dashboard saves user
    credentials in user_capital_connections, and the scanner reads them here.
    """
    try:
        conn = db_connect()
        with conn.cursor() as cur:
            cur.execute(
                """
                SELECT username, api_key, identifier, password, account_type, enabled
                FROM user_capital_connections
                WHERE COALESCE(enabled, FALSE) = TRUE
                  AND COALESCE(api_key, '') <> ''
                  AND COALESCE(identifier, '') <> ''
                  AND COALESCE(password, '') <> ''
                ORDER BY updated_at DESC NULLS LAST, created_at DESC NULLS LAST
                LIMIT 1
                """
            )
            row = cur.fetchone()
        conn.close()
        return dict(row) if row else {}
    except Exception as exc:
        print(f"[CapitalSync] Could not load user Capital connection: {exc}")
        return {}


# User-owned Capital connection bootstrap is deferred until after db_connect exists.
_USER_CAPITAL_SYNC_CONN = {}

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



def hydrate_capital_env_from_user_connection_if_missing() -> dict:
    """Use latest enabled user Capital connection when platform env creds are absent."""
    if os.environ.get("CAPITAL_API_KEY") and os.environ.get("CAPITAL_IDENTIFIER") and os.environ.get("CAPITAL_PASSWORD"):
        return {}
    try:
        conn = db_connect()
        with conn.cursor() as cur:
            cur.execute("""
                SELECT *
                FROM user_capital_connections
                WHERE COALESCE(enabled, FALSE) = TRUE
                  AND COALESCE(api_key, '') <> ''
                  AND COALESCE(identifier, '') <> ''
                  AND COALESCE(password, '') <> ''
                ORDER BY updated_at DESC NULLS LAST, created_at DESC NULLS LAST
                LIMIT 1
            """)
            row = cur.fetchone()
        conn.close()
        if not row:
            return {}
        row = dict(row)
        os.environ["CAPITAL_API_KEY"] = str(row.get("api_key") or "")
        os.environ["CAPITAL_IDENTIFIER"] = str(row.get("identifier") or "")
        os.environ["CAPITAL_PASSWORD"] = str(row.get("password") or "")
        acct = str(row.get("account_type") or "DEMO").strip().upper()
        os.environ.setdefault("CAPITAL_API_URL", "https://demo-api-capital.backend-capital.com" if acct == "DEMO" else "https://api-capital.backend-capital.com")
        print(f"[CapitalSync] Loaded user Capital connection for {row.get('username')} ({acct}).")
        return row
    except Exception as exc:
        print(f"[CapitalSync] Could not hydrate user Capital connection: {exc}")
        return {}


def init_tables() -> None:
    if not SCANNER_RUN_SCHEMA_MIGRATIONS:
        print("[DB] Schema migrations skipped for normal scanner run. Supabase tables are assumed ready.")
        return

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

    CREATE TABLE IF NOT EXISTS user_capital_connections (
        username TEXT PRIMARY KEY,
        api_key TEXT,
        identifier TEXT,
        password TEXT,
        account_type TEXT DEFAULT 'DEMO',
        enabled BOOLEAN DEFAULT FALSE,
        auto_trade_enabled BOOLEAN DEFAULT FALSE,
        auto_trade_grades TEXT DEFAULT 'A+,A',
        use_benzino_settings BOOLEAN DEFAULT TRUE,
        created_at TIMESTAMPTZ DEFAULT NOW(),
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
        currency TEXT,
        raw_json JSONB,
        updated_at TIMESTAMPTZ DEFAULT NOW()
    );
    CREATE INDEX IF NOT EXISTS idx_capital_exec_asset_time
        ON capital_executed_trades (asset, opened_at DESC);
    CREATE INDEX IF NOT EXISTS idx_capital_exec_status
        ON capital_executed_trades (status);

    CREATE TABLE IF NOT EXISTS capital_auto_orders (
        signal_id TEXT PRIMARY KEY REFERENCES scanner_signals(signal_id),
        deal_reference TEXT,
        deal_id TEXT,
        scan_owner TEXT,
        environment TEXT,
        asset TEXT,
        timeframe TEXT,
        direction TEXT,
        grade TEXT,
        epic TEXT,
        size NUMERIC,
        entry NUMERIC,
        sl NUMERIC,
        tp NUMERIC,
        status TEXT,
        error TEXT,
        raw_json JSONB,
        ftmo_leverage NUMERIC DEFAULT 100,
        capital_leverage NUMERIC,
        ftmo_normalization_factor NUMERIC DEFAULT 1,
        created_at TIMESTAMPTZ DEFAULT NOW(),
        updated_at TIMESTAMPTZ DEFAULT NOW()
    );
    CREATE INDEX IF NOT EXISTS idx_capital_auto_asset_time
        ON capital_auto_orders (asset, created_at DESC);

    CREATE TABLE IF NOT EXISTS capital_auto_trade_diagnostics (
        id TEXT PRIMARY KEY,
        username TEXT,
        signal_id TEXT REFERENCES scanner_signals(signal_id),
        display_id TEXT,
        asset TEXT,
        timeframe TEXT,
        direction TEXT,
        grade TEXT,
        eligible BOOLEAN DEFAULT FALSE,
        order_sent BOOLEAN DEFAULT FALSE,
        status TEXT,
        skip_reason TEXT,
        deal_reference TEXT,
        deal_id TEXT,
        prop_selected BOOLEAN DEFAULT FALSE,
        capital_executed BOOLEAN DEFAULT FALSE,
        api_response JSONB,
        checked_at TIMESTAMPTZ DEFAULT NOW(),
        created_at TIMESTAMPTZ DEFAULT NOW(),
        updated_at TIMESTAMPTZ DEFAULT NOW()
    );
    CREATE INDEX IF NOT EXISTS idx_capital_auto_diag_user_time
        ON capital_auto_trade_diagnostics (username, checked_at DESC);
    CREATE INDEX IF NOT EXISTS idx_capital_auto_diag_signal
        ON capital_auto_trade_diagnostics (signal_id);

    CREATE TABLE IF NOT EXISTS capital_auto_daily_state (
        id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
        username TEXT NOT NULL,
        trading_day DATE NOT NULL,
        timeframe TEXT NOT NULL,
        session_order JSONB NOT NULL,
        daily_trade_cap INTEGER DEFAULT 10,
        trades_taken INTEGER DEFAULT 0,
        locked_at TIMESTAMPTZ DEFAULT NOW(),
        completed BOOLEAN DEFAULT FALSE,
        created_at TIMESTAMPTZ DEFAULT NOW(),
        updated_at TIMESTAMPTZ DEFAULT NOW(),
        UNIQUE(username, trading_day, timeframe)
    );
    CREATE INDEX IF NOT EXISTS idx_capital_auto_daily_state_user_day
        ON capital_auto_daily_state (username, trading_day DESC, timeframe);

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
        simulated_outcome TEXT,
        actual_status TEXT,
        match_quality TEXT,
        opened_at TIMESTAMPTZ,
        updated_at TIMESTAMPTZ DEFAULT NOW()
    );
    CREATE INDEX IF NOT EXISTS idx_capital_comparison_asset
        ON capital_trade_comparisons (asset, opened_at DESC);

    CREATE TABLE IF NOT EXISTS capital_execution_audit (
        id TEXT PRIMARY KEY,
        capital_trade_id TEXT REFERENCES capital_executed_trades(id),
        signal_id TEXT REFERENCES scanner_signals(signal_id),
        scan_owner TEXT,
        asset TEXT,
        timeframe TEXT,
        direction TEXT,
        grade TEXT,
        auto_trade BOOLEAN DEFAULT TRUE,
        planned_entry NUMERIC,
        executed_entry NUMERIC,
        entry_slippage NUMERIC,
        planned_sl NUMERIC,
        planned_tp NUMERIC,
        planned_exit NUMERIC,
        actual_exit NUMERIC,
        exit_slippage NUMERIC,
        planned_r NUMERIC,
        actual_r NUMERIC,
        broker_pnl NUMERIC,
        broker_pnl_ftmo_equiv NUMERIC,
        ftmo_leverage NUMERIC DEFAULT 100,
        capital_leverage NUMERIC,
        ftmo_normalization_factor NUMERIC DEFAULT 1,
        replay_outcome TEXT,
        broker_status TEXT,
        size NUMERIC,
        currency TEXT,
        environment TEXT,
        epic TEXT,
        deal_reference TEXT,
        deal_id TEXT,
        opened_at TIMESTAMPTZ,
        closed_at TIMESTAMPTZ,
        updated_at TIMESTAMPTZ DEFAULT NOW()
    );
    CREATE INDEX IF NOT EXISTS idx_capital_execution_audit_owner_time
        ON capital_execution_audit (scan_owner, opened_at DESC);
    CREATE INDEX IF NOT EXISTS idx_capital_execution_audit_signal
        ON capital_execution_audit (signal_id);

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
                cur.execute("ALTER TABLE scanner_signals ADD COLUMN IF NOT EXISTS replay_checked_at TIMESTAMPTZ")
                cur.execute("ALTER TABLE capital_executed_trades ADD COLUMN IF NOT EXISTS raw_json JSONB")
                cur.execute("ALTER TABLE capital_executed_trades ADD COLUMN IF NOT EXISTS environment TEXT")
                cur.execute("ALTER TABLE capital_trade_comparisons ADD COLUMN IF NOT EXISTS match_quality TEXT")
                cur.execute("ALTER TABLE capital_trade_comparisons ADD COLUMN IF NOT EXISTS actual_r NUMERIC")
                cur.execute("ALTER TABLE capital_trade_comparisons ADD COLUMN IF NOT EXISTS auto_trade BOOLEAN DEFAULT FALSE")
                cur.execute("ALTER TABLE capital_auto_orders ADD COLUMN IF NOT EXISTS deal_id TEXT")
                cur.execute("ALTER TABLE capital_auto_orders ADD COLUMN IF NOT EXISTS raw_json JSONB")
                cur.execute("ALTER TABLE capital_auto_orders ADD COLUMN IF NOT EXISTS ftmo_leverage NUMERIC DEFAULT 100")
                cur.execute("ALTER TABLE capital_auto_orders ADD COLUMN IF NOT EXISTS capital_leverage NUMERIC")
                cur.execute("ALTER TABLE capital_auto_orders ADD COLUMN IF NOT EXISTS ftmo_normalization_factor NUMERIC DEFAULT 1")
                cur.execute("ALTER TABLE capital_executed_trades ADD COLUMN IF NOT EXISTS pnl_ftmo_equiv NUMERIC")
                cur.execute("ALTER TABLE capital_executed_trades ADD COLUMN IF NOT EXISTS ftmo_leverage NUMERIC DEFAULT 100")
                cur.execute("ALTER TABLE capital_executed_trades ADD COLUMN IF NOT EXISTS capital_leverage NUMERIC")
                cur.execute("ALTER TABLE capital_executed_trades ADD COLUMN IF NOT EXISTS ftmo_normalization_factor NUMERIC DEFAULT 1")
                cur.execute("ALTER TABLE capital_trade_comparisons ADD COLUMN IF NOT EXISTS actual_pnl_ftmo_equiv NUMERIC")
                cur.execute("ALTER TABLE capital_trade_comparisons ADD COLUMN IF NOT EXISTS ftmo_leverage NUMERIC DEFAULT 100")
                cur.execute("ALTER TABLE capital_trade_comparisons ADD COLUMN IF NOT EXISTS capital_leverage NUMERIC")
                cur.execute("ALTER TABLE capital_trade_comparisons ADD COLUMN IF NOT EXISTS ftmo_normalization_factor NUMERIC DEFAULT 1")
                cur.execute("""
                    CREATE TABLE IF NOT EXISTS user_capital_connections (
                        username TEXT PRIMARY KEY,
                        api_key TEXT,
                        identifier TEXT,
                        password TEXT,
                        account_type TEXT DEFAULT 'DEMO',
                        enabled BOOLEAN DEFAULT FALSE,
                        auto_trade_enabled BOOLEAN DEFAULT FALSE,
                        use_benzino_settings BOOLEAN DEFAULT TRUE,
                        created_at TIMESTAMPTZ DEFAULT NOW(),
                        updated_at TIMESTAMPTZ DEFAULT NOW()
                    )
                """)
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
    if isinstance(value, Decimal):
        try:
            return float(value)
        except Exception:
            return None
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


def jsonb_dumps(value) -> str:
    """JSONB-safe dumps for Capital payloads containing Decimal/numpy/pandas objects."""
    def fallback(obj):
        if isinstance(obj, Decimal):
            return float(obj)
        if isinstance(obj, (np.integer,)):
            return int(obj)
        if isinstance(obj, (np.floating, float)):
            x = float(obj)
            return None if math.isnan(x) or math.isinf(x) else x
        if isinstance(obj, (np.bool_, bool)):
            return bool(obj)
        try:
            if pd.isna(obj):
                return None
        except Exception:
            pass
        return str(obj)
    return json.dumps(sanitize_for_json(value), allow_nan=False, default=fallback)


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
    ;
    """
    try:
        conn = db_connect()
        with conn:
            with conn.cursor() as cur:
                cur.execute(sql)
                # UPDATE without RETURNING has no result set. rowcount is the
                # correct value here; calling fetchall() causes "no results to fetch".
                count = int(cur.rowcount or 0)
        conn.close()
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


def _to_db_timestamp(value):
    """Convert pandas/python timestamps to an ISO string acceptable by Postgres."""
    if value is None:
        return None
    try:
        ts = pd.to_datetime(value, errors="coerce", utc=True)
        if pd.isna(ts):
            return None
        return ts.isoformat()
    except Exception:
        return None


def mark_replay_checked(signal_id: str, bars: int | None = None) -> None:
    """Record that an open trade was checked by the 1-minute replay engine."""
    try:
        conn = db_connect()
        with conn:
            with conn.cursor() as cur:
                if bars is None:
                    cur.execute("UPDATE scanner_signals SET replay_checked_at = NOW() WHERE signal_id = %s", (signal_id,))
                else:
                    cur.execute("UPDATE scanner_signals SET bars_open = %s, replay_checked_at = NOW() WHERE signal_id = %s", (int(bars), signal_id))
        conn.close()
    except Exception as e:
        print(f"[DB] mark_replay_checked failed: {e}")


def close_trade(signal_id: str, exit_price: float, exit_reason: str, r_multiple: float, exit_time=None) -> bool:
    """Close an OPEN trade exactly once.

    Historical outcomes must be immutable. The old update matched only signal_id,
    which was safe in normal flow because evaluate_open_trades() fetches OPEN
    rows, but adding the status guard prevents any future accidental rerun or
    helper call from rewriting an already-closed TP/SL/expiry result.
    """
    sql = """
    UPDATE scanner_signals
    SET status = %s, exit_price = %s, exit_reason = %s, exit_at = COALESCE(%s::timestamptz, NOW()), r_multiple = %s, replay_checked_at = NOW()
    WHERE signal_id = %s
      AND UPPER(TRIM(COALESCE(status, ''))) = 'OPEN'
      AND exit_at IS NULL;
    """
    status = {"TP": "CLOSED_TP", "SL": "CLOSED_SL", "EXPIRY": "EXPIRED"}.get(exit_reason, "CLOSED")
    try:
        conn = db_connect()
        with conn:
            with conn.cursor() as cur:
                cur.execute(sql, (status, exit_price, exit_reason, _to_db_timestamp(exit_time), r_multiple, signal_id))
                changed = int(cur.rowcount or 0) > 0
        conn.close()
        return changed
    except Exception as e:
        print(f"[DB] close_trade failed: {e}")
        return False


def bump_bars_open(signal_id: str, bars: int) -> None:
    try:
        conn = db_connect()
        with conn:
            with conn.cursor() as cur:
                cur.execute("UPDATE scanner_signals SET bars_open = %s, replay_checked_at = NOW() WHERE signal_id = %s", (bars, signal_id))
        conn.close()
    except Exception:
        pass


def fetch_open_trades(assets: set[str] | None = None, timeframes: set[str] | None = None, due_only: bool = False) -> list[dict]:
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
            if due_only:
                sql += """
                    AND (
                        replay_checked_at IS NULL
                        OR replay_checked_at <= NOW() - CASE LOWER(COALESCE(timeframe, '15m'))
                            WHEN '15m' THEN INTERVAL '15 minutes'
                            WHEN '1h' THEN INTERVAL '1 hour'
                            WHEN '4h' THEN INTERVAL '4 hours'
                            WHEN '1d' THEN INTERVAL '1 day'
                            ELSE INTERVAL '15 minutes'
                        END
                    )
                """
            sql += " ORDER BY created_at ASC"
            cur.execute(sql, tuple(params))
            rows = [dict(r) for r in cur.fetchall()]
        conn.close()
        return rows
    except Exception as e:
        print(f"[DB] fetch_open_trades failed: {e}")
        return []


def fetch_unresolved_shadow_trades(assets: set[str] | None = None, timeframes: set[str] | None = None,
                                   max_age_days: int = 3650, limit: int | None = None, due_only: bool = False) -> list[dict]:
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
                  AND created_at >= NOW() - (%s::int * INTERVAL '1 day')
            """
            params: list = [max_age_days]
            if assets:
                sql += " AND asset = ANY(%s)"
                params.append(list(assets))
            if timeframes:
                sql += " AND timeframe = ANY(%s)"
                params.append(list(timeframes))
            if due_only:
                sql += """
                  AND (
                        replay_checked_at IS NULL
                        OR replay_checked_at <= NOW() - CASE LOWER(COALESCE(timeframe, '15m'))
                            WHEN '15m' THEN INTERVAL '15 minutes'
                            WHEN '1h' THEN INTERVAL '1 hour'
                            WHEN '4h' THEN INTERVAL '4 hours'
                            WHEN '1d' THEN INTERVAL '1 day'
                            ELSE INTERVAL '15 minutes'
                        END
                  )
                """
            sql += " ORDER BY created_at ASC LIMIT %s"
            params.append(int(limit or SHADOW_EVAL_LIMIT))
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



def close_shadow_trades_batch(updates: list[tuple[str, float, str, float]]) -> int:
    """Resolve NO TRADE shadow rows in one database transaction.

    `updates` tuples are (signal_id, exit_price, outcome, r_multiple). Batching
    avoids opening thousands of Supabase connections and prevents the pooler
    from timing out during historical backlog repair.
    """
    if not updates:
        return 0
    sql = """
    UPDATE scanner_signals
    SET shadow_outcome = %s,
        shadow_r_multiple = %s,
        shadow_exit_price = %s,
        shadow_closed_at = NOW()
    WHERE signal_id = %s
      AND status = 'SHADOW'
      AND shadow_outcome IS NULL;
    """
    params = [(outcome, float(r_multiple), float(exit_price), signal_id)
              for signal_id, exit_price, outcome, r_multiple in updates]
    try:
        conn = db_connect()
        with conn:
            with conn.cursor() as cur:
                cur.executemany(sql, params)
                count = int(cur.rowcount or 0)
        conn.close()
        return count
    except Exception as e:
        print(f"[DB] close_shadow_trades_batch failed for {len(updates)} row(s): {e}")
        saved = 0
        for signal_id, exit_price, outcome, r_multiple in updates[:10]:
            try:
                close_shadow_trade(signal_id, exit_price, outcome, r_multiple)
                saved += 1
            except Exception:
                pass
        return saved


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
    if not ENABLE_LEGACY_GLOBAL_PROP_LEDGER:
        return
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
#  CAPITAL.COM DATA SOURCE
# ═══════════════════════════════════════════════════════════════════════════════

CAPITAL_API_KEY = os.environ.get("CAPITAL_API_KEY", "").strip()
CAPITAL_IDENTIFIER = os.environ.get("CAPITAL_IDENTIFIER", "").strip()
CAPITAL_PASSWORD = os.environ.get("CAPITAL_PASSWORD", "").strip()
CAPITAL_DEMO = os.environ.get("CAPITAL_DEMO", "true").strip().lower() in {"1", "true", "yes", "y"}
CAPITAL_ENABLED = os.environ.get("CAPITAL_ENABLED", "true").strip().lower() in {"1", "true", "yes", "y"}
CAPITAL_PRIMARY_ALL_ASSETS = os.environ.get("CAPITAL_PRIMARY_ALL_ASSETS", "true").strip().lower() in {"1", "true", "yes", "y"}
# Strict mode: after the Capital.com migration, BENZINO should not silently use Yahoo
# for signal generation or TP/SL replay. If Capital.com cannot provide the data,
# the row is skipped for that run instead of being evaluated against the wrong feed.
CAPITAL_STRICT_ALL_ASSETS = os.environ.get("CAPITAL_STRICT_ALL_ASSETS", "true").strip().lower() in {"1", "true", "yes", "y"}
CAPITAL_PRICE_FIELD = os.environ.get("CAPITAL_PRICE_FIELD", "mid").strip().lower()  # mid, bid, ask
CAPITAL_API_URL_RAW = os.environ.get("CAPITAL_API_URL", "").strip().rstrip("/")
if CAPITAL_API_URL_RAW:
    CAPITAL_BASE_URL = CAPITAL_API_URL_RAW if CAPITAL_API_URL_RAW.endswith("/api/v1") else f"{CAPITAL_API_URL_RAW}/api/v1"
else:
    CAPITAL_BASE_URL = (
        "https://demo-api-capital.backend-capital.com/api/v1"
        if CAPITAL_DEMO else
        "https://api-capital.backend-capital.com/api/v1"
    )
CAPITAL_RESOLUTION_MAP = {
    "1m": "MINUTE",
    "15m": "MINUTE_15",
    "1h": "HOUR",
    "4h": "HOUR_4",
    "1d": "DAY",
}
_CAPITAL_SESSION: dict = {"cst": "", "security_token": "", "ts": 0.0}
_CAPITAL_EPIC_CACHE: dict[str, str | None] = {}
_CAPITAL_MARKET_CACHE: dict[str, dict] = {}

_CAPITAL_UNRESOLVED_EPIC_CACHE: set[str] = set()
_CAPITAL_EPIC_VALIDATION_CACHE: dict[str, bool] = {}
_CAPITAL_MAPPING_REFRESHED_THIS_RUN: set[str] = set()

def capital_saved_epic_needs_refresh(symbol: str, epic: str | None) -> bool:
    """Return True when a saved mapping does not pass a live /prices probe.

    Capital.com epics differ by account/market. Some environments expose dotted
    epics, while others expose shorter epics. The only safe test is not whether
    the value contains a dot; it is whether `/prices/{epic}` returns candles.
    This keeps capital_epic_map useful as the persistent broker-epic resolver
    while rejecting placeholder labels that do not price.
    """
    symbol = str(symbol or "").strip().upper()
    epic = str(epic or "").strip()
    if not symbol or not epic:
        return True
    return not capital_price_epic_works(epic, "15m")


def capital_price_epic_works(epic: str, timeframe: str = "15m") -> bool:
    """Validate an epic with a tiny latest-candle /prices probe."""
    epic = str(epic or "").strip()
    if not epic:
        return False
    key = (epic, timeframe)
    if key in _CAPITAL_EPIC_VALIDATION_CACHE:
        return bool(_CAPITAL_EPIC_VALIDATION_CACHE[key])
    resolution = CAPITAL_RESOLUTION_MAP.get(str(timeframe).lower(), "MINUTE_15")
    data = capital_request("GET", f"/prices/{epic}", params={"resolution": resolution, "max": 5}, retries=1)
    ok = bool(isinstance(data, dict) and isinstance(data.get("prices"), list) and len(data.get("prices") or []) > 0)
    _CAPITAL_EPIC_VALIDATION_CACHE[key] = ok
    return ok

# If platform env credentials are missing, hydrate them from the latest enabled user connection.
try:
    _hydrated_capital_user = hydrate_capital_env_from_user_connection_if_missing()
    if _hydrated_capital_user:
        CAPITAL_API_KEY = os.environ.get("CAPITAL_API_KEY", "").strip()
        CAPITAL_IDENTIFIER = os.environ.get("CAPITAL_IDENTIFIER", "").strip()
        CAPITAL_PASSWORD = os.environ.get("CAPITAL_PASSWORD", "").strip()
        CAPITAL_API_URL_RAW = os.environ.get("CAPITAL_API_URL", "").strip().rstrip("/")
        if CAPITAL_API_URL_RAW:
            CAPITAL_BASE_URL = CAPITAL_API_URL_RAW if CAPITAL_API_URL_RAW.endswith("/api/v1") else f"{CAPITAL_API_URL_RAW}/api/v1"
except Exception as _hydrate_exc:
    print(f"[CapitalSync] User Capital hydration skipped: {_hydrate_exc}")




def refresh_capital_credentials_from_env() -> None:
    """Refresh module-level Capital credential constants after env hydration."""
    global CAPITAL_API_KEY, CAPITAL_IDENTIFIER, CAPITAL_PASSWORD, CAPITAL_API_URL_RAW, CAPITAL_BASE_URL
    CAPITAL_API_KEY = os.environ.get("CAPITAL_API_KEY", "").strip()
    CAPITAL_IDENTIFIER = os.environ.get("CAPITAL_IDENTIFIER", "").strip()
    CAPITAL_PASSWORD = os.environ.get("CAPITAL_PASSWORD", "").strip()
    CAPITAL_API_URL_RAW = os.environ.get("CAPITAL_API_URL", "").strip().rstrip("/")
    if CAPITAL_API_URL_RAW:
        CAPITAL_BASE_URL = CAPITAL_API_URL_RAW if CAPITAL_API_URL_RAW.endswith("/api/v1") else f"{CAPITAL_API_URL_RAW}/api/v1"

def ensure_capital_credentials_loaded() -> bool:
    """Ensure Capital credentials are available from env or user_capital_connections."""
    if capital_configured():
        return True
    row = hydrate_capital_env_from_user_connection_if_missing()
    if row:
        refresh_capital_credentials_from_env()
    return capital_configured()

def capital_configured() -> bool:
    return bool(CAPITAL_ENABLED and CAPITAL_API_KEY and CAPITAL_IDENTIFIER and CAPITAL_PASSWORD)


def is_capital_ticker(ticker: str) -> bool:
    return str(ticker or "").strip().upper().startswith("CAPITAL:")


def capital_symbol_from_ticker(ticker: str) -> str:
    ticker = str(ticker or "").strip()
    return ticker.split(":", 1)[1].strip().upper() if ":" in ticker else ticker.strip().upper()


def yahoo_fallback_for_symbol(symbol: str, ticker: str = "") -> str:
    """Return a safe non-CAPITAL fallback ticker.

    Legacy Supabase rows can contain ticker='CAPITAL:ASSET'. Those must never be
    sent into yfinance. If Capital 1m/history is unavailable for that legacy row,
    either return the known fallback ticker or blank so the row is skipped cleanly.
    """
    symbol = str(symbol or "").strip().upper()
    ticker = str(ticker or "").strip()

    if is_capital_ticker(ticker):
        symbol = capital_symbol_from_ticker(ticker)

    if symbol in YAHOO_FALLBACK_TICKERS:
        return YAHOO_FALLBACK_TICKERS[symbol]

    if is_capital_ticker(ticker):
        return ""

    return ticker



def safe_yfinance_ticker(asset: str, ticker: str = "") -> str:
    """Never allow CAPITAL:* symbols to reach yfinance."""
    asset_norm = str(asset or "").strip().upper()
    ticker_norm = str(ticker or "").strip()
    if is_capital_ticker(ticker_norm):
        asset_norm = capital_symbol_from_ticker(ticker_norm)
        return YAHOO_FALLBACK_TICKERS.get(asset_norm, "")
    return ticker_norm or YAHOO_FALLBACK_TICKERS.get(asset_norm, "")

def preferred_data_ticker(asset: str, current_ticker: str = "") -> str:
    """Return the intended scanner data ticker for an asset.

    Capital.com is the source of truth for BENZINO pricing. New scans and
    historical replay use CAPITAL:<asset> whenever credentials are available.
    Yahoo symbols are retained only as metadata/fallback and are not used when
    CAPITAL_STRICT_ALL_ASSETS is true.
    """
    asset = str(asset or "").strip().upper()
    current_ticker = str(current_ticker or "").strip()
    if is_capital_ticker(current_ticker):
        return current_ticker
    if capital_configured() and CAPITAL_PRIMARY_ALL_ASSETS and asset in MASTER_WATCHLIST:
        return f"CAPITAL:{asset}"
    return current_ticker or MASTER_WATCHLIST.get(asset, "")


def capital_headers(authenticated: bool = True) -> dict:
    headers = {
        "X-CAP-API-KEY": CAPITAL_API_KEY,
        "Content-Type": "application/json",
        "Accept": "application/json",
    }
    if authenticated:
        if not _CAPITAL_SESSION.get("cst") or time.time() - float(_CAPITAL_SESSION.get("ts") or 0) > 3300:
            capital_start_session()
        headers["CST"] = str(_CAPITAL_SESSION.get("cst") or "")
        headers["X-SECURITY-TOKEN"] = str(_CAPITAL_SESSION.get("security_token") or "")
    return headers


def capital_start_session() -> bool:
    if not (CAPITAL_API_KEY and CAPITAL_IDENTIFIER and CAPITAL_PASSWORD):
        return False
    try:
        url = f"{CAPITAL_BASE_URL}/session"
        payload = {
            "identifier": CAPITAL_IDENTIFIER,
            "password": CAPITAL_PASSWORD,
            "encryptedPassword": False,
        }
        resp = requests.post(url, headers=capital_headers(authenticated=False), json=payload, timeout=20)
        if resp.status_code >= 400:
            print(f"[Capital] Session failed: HTTP {resp.status_code} {resp.text[:180]}")
            return False
        _CAPITAL_SESSION["cst"] = resp.headers.get("CST", "")
        _CAPITAL_SESSION["security_token"] = resp.headers.get("X-SECURITY-TOKEN", "")
        _CAPITAL_SESSION["ts"] = time.time()
        ok = bool(_CAPITAL_SESSION["cst"] and _CAPITAL_SESSION["security_token"])
        if ok:
            if not _CAPITAL_SESSION.get("printed_active"):
                print(f"[Capital] Session active ({'demo' if CAPITAL_DEMO else 'live'}).")
                _CAPITAL_SESSION["printed_active"] = True
        else:
            print("[Capital] Session response did not include CST / X-SECURITY-TOKEN.")
        return ok
    except Exception as exc:
        print(f"[Capital] Session failed: {exc}")
        return False


def capital_request(method: str, path: str, *, params: dict | None = None, json_body: dict | None = None, retries: int = 2) -> dict | None:
    """Authenticated Capital.com API request with runtime accounting.

    A previous edit accidentally returned None before the HTTP request ran.
    That broke Capital 1H/1m candles and made the scanner skip valid signals.
    """
    _t0 = _runtime_start()
    try:
        _RUNTIME_BREAKDOWN["capital_api_calls"] = float(_RUNTIME_BREAKDOWN.get("capital_api_calls", 0.0)) + 1.0
    except Exception:
        pass

    if not capital_configured():
        _runtime_stop("capital_api", _t0)
        return None

    for attempt in range(1, int(retries) + 1):
        try:
            url = f"{CAPITAL_BASE_URL}{path}"
            resp = requests.request(
                method.upper(),
                url,
                headers=capital_headers(authenticated=True),
                params=params or {},
                json=json_body,
                timeout=20,
            )
            if resp.status_code in (401, 403):
                _CAPITAL_SESSION["cst"] = ""
                _CAPITAL_SESSION["security_token"] = ""
                resp = requests.request(
                    method.upper(),
                    url,
                    headers=capital_headers(authenticated=True),
                    params=params or {},
                    json=json_body,
                    timeout=20,
                )
            if resp.status_code == 429:
                time.sleep(0.75 + attempt)
                continue
            if resp.status_code >= 400:
                _CAPITAL_LAST_ERROR["text"] = resp.text[:500]
                if attempt == int(retries):
                    print(f"[Capital] {method} {path} failed: HTTP {resp.status_code} {resp.text[:160]}")
                time.sleep(0.25)
                continue
            _runtime_stop("capital_api", _t0)
            return resp.json()
        except Exception as exc:
            _CAPITAL_LAST_ERROR["text"] = str(exc)
            if attempt == int(retries):
                print(f"[Capital] {method} {path} failed: {exc}")
            time.sleep(0.25)

    _runtime_stop("capital_api", _t0)
    return None


CAPITAL_EPIC_HINTS = {
    # Common Capital.com epics seen in public examples / platform naming.
    "XAUUSD": ["GOLD", "XAUUSD"],
    "XAGUSD": ["SILVER", "XAGUSD"],
    "OIL": ["OIL_CRUDE", "CRUDE", "USOIL", "OIL"],
    "BRENT": ["OIL_BRENT", "BRENT"],
    "NATGAS": ["NATURALGAS", "NATGAS", "NATURAL_GAS"],
    "COPPER": ["COPPER"],
    "SP500": ["US500", "SPX500", "SP500", "US500_CASH"],
    "NAS100": ["US100", "NAS100", "NASDAQ100"],
    "DOW30": ["US30", "DOW30", "WALLSTREET"],
    "BTCUSD": ["BTCUSD", "BITCOIN"],
    "ETHUSD": ["ETHUSD", "ETHEREUM"],
}


def _capital_market_score(symbol: str, market: dict) -> int:
    symbol = str(symbol or "").upper()
    epic = str(market.get("epic") or "").upper()
    name = str(market.get("instrumentName") or market.get("name") or market.get("symbol") or "").upper()
    compact_name = name.replace("/", "").replace(" ", "").replace("-", "")
    score = 0
    # Dotted epics are often broker-specific, but not every Capital account uses
    # the same format. Score them slightly higher, but never reject plain epics
    # purely because they lack dots; live /prices validation decides validity.
    if "." in epic:
        score += 25
    if symbol == epic:
        score += 35
    elif symbol in epic:
        score += 60
    if symbol in compact_name:
        score += 55
    # FX pair names are often displayed as EUR/USD rather than EURUSD.
    if len(symbol) == 6 and f"{symbol[:3]}/{symbol[3:]}" in name:
        score += 80
    itype = str(market.get("instrumentType") or market.get("type") or "").upper()
    if "CFD" in itype:
        score += 5
    if market.get("streamingPricesAvailable") is True:
        score += 3
    return score




def _as_float(value, default=None):
    """Convert Capital API numeric values safely, including rule objects like {'value': 1}."""
    try:
        if value is None or value == "":
            return default
        if isinstance(value, dict):
            for key in ("value", "min", "max", "amount", "size", "distance"):
                if key in value:
                    out = _as_float(value.get(key), None)
                    if out is not None:
                        return out
            return default
        if isinstance(value, str):
            m = re.search(r"[-+]?\d+(?:\.\d+)?", value)
            return float(m.group(0)) if m else default
        return float(value)
    except Exception:
        return default


def _deep_find_number(obj, key_fragments: list[str], default=None):
    """Best-effort recursive extraction of Capital instrument constraints.

    Capital often returns dealing rules as nested objects, for example:
        {'dealingRules': {'minDealSize': {'value': 1, 'unit': 'POINTS'}}}

    Older extraction only handled direct numeric values, which is why the
    Supabase columns were being saved as 0/null even though the rule existed.
    """
    try:
        if isinstance(obj, dict):
            for k, v in obj.items():
                kl = str(k).lower()
                if all(f.lower() in kl for f in key_fragments):
                    out = _as_float(v, None)
                    if out is not None:
                        return out
            for v in obj.values():
                found = _deep_find_number(v, key_fragments, None)
                if found is not None:
                    return found
        elif isinstance(obj, list):
            for v in obj:
                found = _deep_find_number(v, key_fragments, None)
                if found is not None:
                    return found
    except Exception:
        pass
    return default


def _rule_value(rules: dict, *names: str, default: float = 0.0) -> float:
    """Return the first numeric dealing-rule value from a Capital rules dict."""
    if not isinstance(rules, dict):
        return float(default)
    lower_map = {str(k).lower(): v for k, v in rules.items()}
    for name in names:
        key = str(name).lower()
        if key in lower_map:
            val = _as_float(lower_map[key], None)
            if val is not None:
                return float(val)
    # Loose matching fallback for small schema differences.
    for name in names:
        wanted = re.sub(r"[^a-z0-9]", "", str(name).lower())
        for k, v in lower_map.items():
            kk = re.sub(r"[^a-z0-9]", "", k)
            if wanted and wanted in kk:
                val = _as_float(v, None)
                if val is not None:
                    return float(val)
    return float(default)


def _capital_dealing_rules(market: dict | None) -> dict:
    market = market or {}
    for candidate in (
        market.get("dealingRules"),
        (market.get("instrument") or {}).get("dealingRules") if isinstance(market.get("instrument"), dict) else None,
        (market.get("market") or {}).get("dealingRules") if isinstance(market.get("market"), dict) else None,
    ):
        if isinstance(candidate, dict) and candidate:
            return candidate
    return {}


def capital_extract_constraints(market: dict | None) -> dict:
    market = market or {}
    rules = _capital_dealing_rules(market)

    # Prefer explicit Capital dealingRules. Fall back to recursive extraction
    # because some endpoint responses flatten or rename these fields.
    min_size = (_rule_value(rules, "minDealSize") or
                _deep_find_number(market, ["min", "deal", "size"]) or
                _deep_find_number(market, ["min", "size"]) or 0.0)
    max_size = (_rule_value(rules, "maxDealSize") or
                _deep_find_number(market, ["max", "deal", "size"]) or
                _deep_find_number(market, ["max", "size"]) or 0.0)
    step_size = (_rule_value(rules, "minStepDistance", "stepDistance", "minStepSize") or
                 _deep_find_number(market, ["step", "size"]) or
                 _deep_find_number(market, ["step", "distance"]) or
                 _deep_find_number(market, ["min", "step"]) or 0.0)

    # Capital's normal stop/limit rule is the practical minimum distance for
    # non-guaranteed SL/TP orders. maxStopOrLimitDistance is the practical max.
    min_stop = (_rule_value(rules, "minNormalStopOrLimitDistance", "minStopOrLimitDistance", "minStopDistance") or
                _deep_find_number(market, ["min", "normal", "stop", "limit", "distance"]) or
                _deep_find_number(market, ["min", "stop", "limit", "distance"]) or
                _deep_find_number(market, ["min", "stop", "distance"]) or 0.0)
    max_stop = (_rule_value(rules, "maxStopOrLimitDistance", "maxStopDistance") or
                _deep_find_number(market, ["max", "stop", "limit", "distance"]) or
                _deep_find_number(market, ["max", "stop", "distance"]) or 0.0)
    min_limit = (_rule_value(rules, "minNormalStopOrLimitDistance", "minStopOrLimitDistance", "minLimitDistance") or
                 _deep_find_number(market, ["min", "limit", "distance"]) or min_stop or 0.0)
    max_limit = (_rule_value(rules, "maxStopOrLimitDistance", "maxLimitDistance") or
                 _deep_find_number(market, ["max", "limit", "distance"]) or max_stop or 0.0)

    # If Capital omits a step but gives a minimum deal size, using min_size as
    # the step is safer than sending arbitrary decimals that may be rejected.
    if not step_size and min_size:
        step_size = min_size

    return {
        "min_size": float(min_size or 0),
        "max_size": float(max_size or 0),
        "step_size": float(step_size or 0),
        "min_stop_distance": float(min_stop or 0),
        "max_stop_distance": float(max_stop or 0),
        "min_limit_distance": float(min_limit or 0),
        "max_limit_distance": float(max_limit or 0),
    }

def round_to_broker_step(size: float, step: float, *, direction: str = "nearest") -> float:
    try:
        size = float(size)
        step = float(step or 0)
        if step <= 0:
            return round(size, 6)
        if direction == "up":
            return round(math.ceil(size / step) * step, 6)
        if direction == "down":
            return round(math.floor(size / step) * step, 6)
        return round(round(size / step) * step, 6)
    except Exception:
        return float(size or 0)


def capital_load_market_info(symbol: str) -> dict:
    symbol = str(symbol or "").strip().upper()
    try:
        conn = db_connect()
        with conn.cursor() as cur:
            cur.execute("""
                SELECT epic, market_info, min_size, max_size, step_size,
                       min_stop_distance, max_stop_distance, min_limit_distance, max_limit_distance
                FROM capital_epic_map WHERE asset = %s LIMIT 1
            """, (symbol,))
            row = cur.fetchone()
        conn.close()
        if not row:
            return {}
        row = dict(row)
        out = dict(row.get("market_info") or {}) if isinstance(row.get("market_info"), dict) else {}
        for k in ["epic","min_size","max_size","step_size","min_stop_distance","max_stop_distance","min_limit_distance","max_limit_distance"]:
            if row.get(k) not in (None, ""):
                out[k] = row.get(k)
        # If the mapping exists but constraints are empty, refresh once from Capital.
        numeric_keys = ["min_size","max_size","step_size","min_stop_distance","max_stop_distance","min_limit_distance","max_limit_distance"]
        if not any(float(out.get(k) or 0) > 0 for k in numeric_keys):
            refreshed = capital_refresh_market_constraints(symbol, out.get("epic"))
            if refreshed:
                out.update(refreshed)
        return out
    except Exception:
        return {}


def capital_available_margin() -> float | None:
    """Best-effort available funds/margin check. Returns None if endpoint shape differs."""
    data = capital_request("GET", "/accounts", retries=1)
    try:
        accounts = data.get("accounts") if isinstance(data, dict) else None
        if isinstance(accounts, list) and accounts:
            acc = accounts[0]
            bal = acc.get("balance") or acc.get("accountBalance") or {}
            for key in ("available", "availableToDeal", "deposit", "cash", "balance"):
                val = bal.get(key) if isinstance(bal, dict) else acc.get(key)
                if val not in (None, ""):
                    return float(val)
    except Exception:
        return None
    return None


def estimate_margin_required(sig, size: float, leverage: float) -> float:
    try:
        return abs(float(size) * float(sig.entry)) / max(1.0, float(leverage or 1))
    except Exception:
        return 0.0


def capital_asset_class(asset: str) -> str:
    asset = str(asset or "").upper().strip()
    if asset in CAPITAL_ASSET_CLASS:
        return CAPITAL_ASSET_CLASS[asset]
    # Most remaining 6-letter symbols in the master universe are FX pairs.
    if len(asset) == 6 and asset.isalpha():
        return "currencies"
    return "commodities"


def capital_effective_leverage_for_asset(asset: str, market_info: dict | None = None) -> float:
    """Return broker execution leverage used for margin/normalization.

    Capital may expose margin/leverage in different shapes per endpoint, so the
    asset-class cap is the reliable default. This does not change BENZINO/FTMO
    simulation; it only describes the actual Capital execution environment.
    """
    cls = capital_asset_class(asset)
    cap = float(CAPITAL_LEVERAGE_CAPS.get(cls, 100.0))
    try:
        market_info = market_info or {}
        lev = _deep_find_number(market_info, ["leverage"], None)
        if lev and lev > 0:
            cap = min(cap, float(lev))
    except Exception:
        pass
    return max(1.0, cap)


def ftmo_normalization_factor(asset: str, market_info: dict | None = None) -> float:
    if not CAPITAL_FTMO_NORMALIZE_PNL:
        return 1.0
    actual_lev = capital_effective_leverage_for_asset(asset, market_info)
    return max(1.0, float(FTMO_COMPARISON_LEVERAGE) / max(1.0, actual_lev))

def capital_load_saved_epic(symbol: str) -> str | None:
    """Read a previously resolved Capital.com epic from Supabase.

    This avoids calling /markets for every asset on every scanner run. The
    table is intentionally managed as a normal data table, not through scanner
    schema migrations, to avoid lock/deadlock issues during scheduled runs.
    """
    symbol = str(symbol or "").strip().upper()
    if not symbol:
        return None
    try:
        conn = db_connect()
        with conn.cursor() as cur:
            cur.execute(
                "SELECT epic, market_info FROM capital_epic_map WHERE asset = %s LIMIT 1",
                (symbol,),
            )
            row = cur.fetchone()
        conn.close()
        if row:
            epic = str(row.get("epic") or "").strip()
            if isinstance(row.get("market_info"), dict):
                _CAPITAL_MARKET_CACHE[symbol] = row.get("market_info") or {}
            return epic or None
    except Exception as exc:
        # Non-fatal: if the table is absent/unavailable, fall back to live resolve.
        print(f"[Capital] Saved epic lookup skipped for {symbol}: {exc}")
    return None


def capital_save_epic(symbol: str, epic: str, market: dict | None = None) -> None:
    """Persist an asset -> Capital epic mapping and broker constraints for future scanner runs."""
    symbol = str(symbol or "").strip().upper()
    epic = str(epic or "").strip()
    if not symbol or not epic:
        return
    try:
        market = market or _CAPITAL_MARKET_CACHE.get(symbol, {}) or {}
        cons = capital_extract_constraints(market)
        conn = db_connect()
        with conn:
            with conn.cursor() as cur:
                cur.execute(
                    """
                    INSERT INTO capital_epic_map(
                        asset, epic, source, instrument_name, market_info,
                        min_size, max_size, step_size, min_stop_distance, max_stop_distance,
                        min_limit_distance, max_limit_distance, updated_at, last_refreshed_at
                    ) VALUES (%s,%s,'CAPITAL',%s,%s,%s,%s,%s,%s,%s,%s,%s,NOW(),NOW())
                    ON CONFLICT (asset) DO UPDATE
                    SET epic = EXCLUDED.epic, source = EXCLUDED.source,
                        instrument_name = EXCLUDED.instrument_name, market_info = EXCLUDED.market_info,
                        min_size = EXCLUDED.min_size, max_size = EXCLUDED.max_size, step_size = EXCLUDED.step_size,
                        min_stop_distance = EXCLUDED.min_stop_distance, max_stop_distance = EXCLUDED.max_stop_distance,
                        min_limit_distance = EXCLUDED.min_limit_distance, max_limit_distance = EXCLUDED.max_limit_distance,
                        updated_at = NOW(), last_refreshed_at = NOW()
                    """,
                    (symbol, epic, str(market.get("instrumentName") or market.get("name") or symbol),
                     json.dumps(sanitize_for_json(market), allow_nan=False),
                     cons["min_size"], cons["max_size"], cons["step_size"], cons["min_stop_distance"], cons["max_stop_distance"], cons["min_limit_distance"], cons["max_limit_distance"]),
                )
        conn.close()
    except Exception as exc:
        # Non-fatal: mapping can still be used in-memory for this run.
        print(f"[Capital] Could not save epic map for {symbol}->{epic}: {exc}")


def capital_refresh_market_constraints(symbol: str, epic: str | None = None) -> dict:
    """Refresh/sync broker constraints into capital_epic_map when saved columns are empty.

    This fixes rows that were created before constraint columns existed.
    """
    symbol = str(symbol or "").upper().strip()
    epic = str(epic or "").strip() or capital_load_saved_epic(symbol) or symbol
    if not symbol or not capital_configured():
        return {}
    market = None
    # Try direct endpoint first, then search fallback.
    for path, params in ((f"/markets/{epic}", None), ("/markets", {"searchTerm": epic}), ("/markets", {"searchTerm": symbol})):
        data = capital_request("GET", path, params=params, retries=1)
        if isinstance(data, dict):
            if isinstance(data.get("instrument"), dict) or isinstance(data.get("dealingRules"), dict):
                market = data
                break
            markets = data.get("markets") or data.get("items") or []
            if isinstance(markets, dict):
                markets = [markets]
            if markets:
                ranked = sorted(markets, key=lambda m: _capital_market_score(symbol, m), reverse=True)
                market = ranked[0]
                epic = str(market.get("epic") or epic)
                break
    if isinstance(market, dict) and market:
        _CAPITAL_MARKET_CACHE[symbol] = market
        capital_save_epic(symbol, epic, market)
        return capital_extract_constraints(market) | {"epic": epic, "market_info": market}
    return {}


def capital_find_epic(symbol: str) -> str | None:
    """Resolve a BENZINO asset key to a validated Capital.com price epic.

    capital_epic_map is the persistent resolver. A saved value is trusted only
    after a small `/prices/{epic}?max=5` probe succeeds. If the saved row is a
    placeholder such as EURUSD/US500/GOLD, the scanner searches `/markets`, tests
    each candidate with `/prices`, saves the first working epic, and caches the
    result for the rest of the run.
    """
    symbol = str(symbol or "").strip().upper()
    if not symbol or not capital_configured():
        return None
    if symbol in _CAPITAL_EPIC_CACHE:
        return _CAPITAL_EPIC_CACHE[symbol]
    if symbol in _CAPITAL_UNRESOLVED_EPIC_CACHE:
        return None

    saved_epic = capital_load_saved_epic(symbol)
    if saved_epic and not capital_saved_epic_needs_refresh(symbol, saved_epic):
        _CAPITAL_EPIC_CACHE[symbol] = saved_epic
        return saved_epic

    if saved_epic and symbol not in _CAPITAL_MAPPING_REFRESHED_THIS_RUN:
        print(f"[CapitalMapping] {symbol}: saved epic {saved_epic} did not pass /prices validation; refreshing via /markets.")
        _CAPITAL_MAPPING_REFRESHED_THIS_RUN.add(symbol)

    candidates: list[str] = []
    if len(symbol) == 6 and symbol.isalpha():
        candidates.extend([f"{symbol[:3]}/{symbol[3:]}", symbol])
    candidates.extend(CAPITAL_EPIC_HINTS.get(symbol, []))
    if saved_epic:
        candidates.append(saved_epic)
    candidates.append(symbol)

    seen_terms = set()
    candidates = [c for c in candidates if c and not (str(c).upper() in seen_terms or seen_terms.add(str(c).upper()))]

    markets_by_epic: dict[str, dict] = {}
    for candidate in candidates:
        data = capital_request("GET", "/markets", params={"searchTerm": candidate}, retries=1)
        markets = []
        if isinstance(data, dict):
            markets = data.get("markets") or data.get("items") or data.get("market") or []
        if isinstance(markets, dict):
            markets = [markets]
        for market in markets or []:
            if not isinstance(market, dict):
                continue
            epic = str(market.get("epic") or "").strip()
            if epic:
                # Keep the highest-scoring version if duplicates appear.
                if epic not in markets_by_epic or _capital_market_score(symbol, market) > _capital_market_score(symbol, markets_by_epic[epic]):
                    markets_by_epic[epic] = market

    ranked = sorted(markets_by_epic.items(), key=lambda kv: _capital_market_score(symbol, kv[1]), reverse=True)
    for epic, market in ranked:
        if capital_price_epic_works(epic, "15m"):
            _CAPITAL_EPIC_CACHE[symbol] = epic
            _CAPITAL_MARKET_CACHE[symbol] = market or {}
            capital_save_epic(symbol, epic, market or {})
            if epic != saved_epic:
                print(f"[CapitalMapping] {symbol}: mapped to broker epic {epic} and saved.")
            return epic

    _CAPITAL_UNRESOLVED_EPIC_CACHE.add(symbol)
    _CAPITAL_EPIC_CACHE[symbol] = None
    print(f"[CapitalMapping] {symbol}: no Capital.com /prices-valid epic found; skipped until capital_epic_map is corrected.")
    return None

# Backward-compatible alias used by the auto-trade layer.
# The strict Capital feed resolver is capital_find_epic().
def capital_resolve_epic(symbol: str) -> str | None:
    return capital_find_epic(symbol)


def _capital_price_value(block: dict | None) -> float | None:
    if not isinstance(block, dict):
        return None
    bid = block.get("bid")
    ask = block.get("ask")
    try:
        if CAPITAL_PRICE_FIELD == "bid" and bid is not None:
            return float(bid)
        if CAPITAL_PRICE_FIELD == "ask" and ask is not None:
            return float(ask)
        if bid is not None and ask is not None:
            return (float(bid) + float(ask)) / 2.0
        if bid is not None:
            return float(bid)
        if ask is not None:
            return float(ask)
    except Exception:
        return None
    return None


def capital_prices_to_df(data: dict) -> pd.DataFrame | None:
    prices = data.get("prices") if isinstance(data, dict) else None
    if not isinstance(prices, list) or not prices:
        return None
    rows = []
    for p in prices:
        try:
            ts = p.get("snapshotTimeUTC") or p.get("snapshotTime")
            row = {
                "Date": pd.to_datetime(ts, utc=True, errors="coerce"),
                "Open": _capital_price_value(p.get("openPrice")),
                "High": _capital_price_value(p.get("highPrice")),
                "Low": _capital_price_value(p.get("lowPrice")),
                "Close": _capital_price_value(p.get("closePrice")),
                "Volume": float(p.get("lastTradedVolume") or 0),
            }
            if pd.isna(row["Date"]) or any(row[k] is None for k in ["Open", "High", "Low", "Close"]):
                continue
            rows.append(row)
        except Exception:
            continue
    if not rows:
        return None
    df = pd.DataFrame(rows).sort_values("Date").drop_duplicates("Date")
    df["Date"] = pd.to_datetime(df["Date"], utc=True, errors="coerce").dt.tz_localize(None)
    return df.reset_index(drop=True)


def capital_download(symbol: str, timeframe: str, max_rows: int = 1000) -> pd.DataFrame | None:
    """Download/cache OHLCV from Capital.com for a BENZINO asset key."""
    if not capital_configured():
        return None
    symbol = str(symbol or "").strip().upper()
    timeframe = str(timeframe or "15m").strip().lower()
    max_rows_i = int(min(max_rows, 1000))
    cache_key = (symbol, timeframe, max_rows_i)
    if cache_key in _CAPITAL_PRICE_CACHE:
        cached = _CAPITAL_PRICE_CACHE[cache_key]
        return cached.copy() if cached is not None else None
    _t0 = _runtime_start()
    resolution = CAPITAL_RESOLUTION_MAP.get(timeframe, "MINUTE_15")
    epic = capital_find_epic(symbol)
    if not epic:
        _CAPITAL_PRICE_CACHE[cache_key] = None
        _runtime_stop("capital_candle_fetch", _t0)
        return None
    params = {"resolution": resolution, "max": max_rows_i}
    data = capital_request("GET", f"/prices/{epic}", params=params, retries=1)
    df = capital_prices_to_df(data or {})
    ok = False
    if df is not None and len(df) >= 50:
        ok = True
    if df is not None and timeframe == "1m" and len(df) >= 5:
        ok = True
    _CAPITAL_PRICE_CACHE[cache_key] = df.copy() if ok else None
    _runtime_stop("capital_candle_fetch", _t0)
    return df.copy() if ok else None




def _capital_time_param(ts) -> str:
    """Format a UTC timestamp for Capital.com's /prices from/to parameters."""
    try:
        t = pd.to_datetime(ts, utc=True, errors="coerce")
        if pd.isna(t):
            return ""
        # Capital API examples use ISO timestamps without timezone suffix.
        return t.strftime("%Y-%m-%dT%H:%M:%S")
    except Exception:
        return ""


def capital_download_range(symbol: str, timeframe: str, start_ts, end_ts, max_rows: int = 1000) -> pd.DataFrame | None:
    """Download/cache a bounded Capital.com candle window.

    This is critical for TP/SL replay. A plain `max=1000` 1-minute request only
    returns the latest ~16 hours, so older open trades were being marked as
    pending even when Capital.com could provide the historical minute range via
    from/to parameters.
    """
    if not capital_configured():
        return None

    symbol = str(symbol or "").strip().upper()
    timeframe = str(timeframe or "1m").strip().lower()
    start = pd.to_datetime(start_ts, utc=True, errors="coerce")
    end = pd.to_datetime(end_ts, utc=True, errors="coerce")
    if pd.isna(start) or pd.isna(end) or end <= start:
        return None

    # Small safety padding around the replay window.
    start = start.floor("min") - pd.Timedelta(minutes=2)
    end = end.ceil("min") + pd.Timedelta(minutes=2)

    # Cache by rounded bounds to make multiple trades in the same asset/window reuse data.
    cache_key = (
        symbol,
        timeframe,
        start.strftime("%Y-%m-%dT%H:%M"),
        end.strftime("%Y-%m-%dT%H:%M"),
    )
    if cache_key in _CAPITAL_RANGE_PRICE_CACHE:
        cached = _CAPITAL_RANGE_PRICE_CACHE[cache_key]
        return cached.copy() if cached is not None else None

    _t0 = _runtime_start()
    resolution = CAPITAL_RESOLUTION_MAP.get(timeframe, "MINUTE")
    epic = capital_find_epic(symbol)
    if not epic:
        _CAPITAL_RANGE_PRICE_CACHE[cache_key] = None
        _runtime_stop("capital_candle_fetch", _t0)
        return None

    # Capital.com caps response size. Chunk long replay windows so a multi-day
    # 1m replay can still be reconstructed without Yahoo fallback.
    step_minutes = 900 if timeframe == "1m" else 900 * 15
    frames: list[pd.DataFrame] = []
    cur = start
    while cur < end:
        chunk_end = min(cur + pd.Timedelta(minutes=step_minutes), end)
        params = {
            "resolution": resolution,
            "from": _capital_time_param(cur),
            "to": _capital_time_param(chunk_end),
            "max": int(min(max_rows, 1000)),
        }
        data = capital_request("GET", f"/prices/{epic}", params=params, retries=1)
        df = capital_prices_to_df(data or {})
        if df is not None and not df.empty:
            frames.append(df)
        cur = chunk_end

    if frames:
        out = pd.concat(frames, ignore_index=True)
        out["Date"] = pd.to_datetime(out["Date"], utc=True, errors="coerce")
        out = out.dropna(subset=["Date"]).sort_values("Date").drop_duplicates("Date").reset_index(drop=True)
        # Keep only the requested padded window.
        out = out[(out["Date"] >= start) & (out["Date"] <= end)].copy()
        if not out.empty:
            _CAPITAL_RANGE_PRICE_CACHE[cache_key] = out.copy()
            _runtime_stop("capital_candle_fetch", _t0)
            return out.copy()

    _CAPITAL_RANGE_PRICE_CACHE[cache_key] = None
    _runtime_stop("capital_candle_fetch", _t0)
    return None


def get_minute_replay_df_for_window(ticker: str, entry_ts, expiry_ts) -> pd.DataFrame | None:
    """Return Capital.com 1-minute candles covering one trade's replay window.

    Runtime-safe design: fetch recent 1-minute candles once per asset per run,
    then reuse that cached dataframe for every trade on the same asset. Older
    trades whose replay window is outside Capital.com's recent 1-minute cache
    are left pending instead of generating hundreds of rejected from/to requests.
    """
    ticker = str(ticker or "").strip()
    if not ticker:
        return None
    start = pd.to_datetime(entry_ts, utc=True, errors="coerce")
    end = pd.to_datetime(expiry_ts, utc=True, errors="coerce")
    if pd.isna(start) or pd.isna(end) or end <= start:
        return None

    recent = get_minute_replay_df(ticker)
    if recent is None or recent.empty:
        return None
    recent = recent.copy()
    recent["Date"] = pd.to_datetime(recent["Date"], utc=True, errors="coerce")
    recent = recent.dropna(subset=["Date"]).sort_values("Date")
    if recent.empty:
        return None

    # The cached recent dataframe must actually cover the replay interval.
    # If it does not, keep the trade pending for now; do not fall back to Yahoo
    # and do not hammer Capital with invalid historical ranges.
    if recent["Date"].min() > start or recent["Date"].max() < min(end, pd.Timestamp.now(tz="UTC")):
        return None
    window = recent[(recent["Date"] >= (start - pd.Timedelta(minutes=2))) & (recent["Date"] <= (end + pd.Timedelta(minutes=2)))].copy()
    return window if not window.empty else None

def should_use_capital_for_ticker(ticker: str) -> bool:
    return capital_configured() and (is_capital_ticker(ticker) or CAPITAL_PRIMARY_ALL_ASSETS)


def asset_symbol_from_any_ticker(ticker: str) -> str:
    """Resolve BENZINO asset key from CAPITAL:<asset>, direct asset, or legacy Yahoo ticker."""
    ticker = str(ticker or "").strip()
    if is_capital_ticker(ticker):
        return capital_symbol_from_ticker(ticker)
    upper = ticker.upper()
    if upper in MASTER_WATCHLIST:
        return upper
    for asset, yahoo in MASTER_WATCHLIST.items():
        if str(yahoo).strip().upper() == upper:
            return asset
    return upper.replace("=X", "").replace("-USD", "USD").replace("^", "")


# ═══════════════════════════════════════════════════════════════════════════════
#  DATA DOWNLOAD
# ═══════════════════════════════════════════════════════════════════════════════

def download(ticker: str, interval: str, period: str, retries: int = 3, pause_seconds: float = 2.0) -> pd.DataFrame | None:
    """Download OHLCV data from Capital.com first.

    When CAPITAL_STRICT_ALL_ASSETS is true, Yahoo is never used for scanner
    candles. This prevents signal prices, TP/SL levels, replay outcomes, and
    Capital.com execution comparisons from being built on different feeds.
    """
    ticker = str(ticker or "").strip()
    symbol = asset_symbol_from_any_ticker(ticker)
    interval_to_tf = {"1m": "1m", "15m": "15m", "30m": "30m", "60m": "1h", "1h": "1h", "1d": "1d"}
    tf = interval_to_tf.get(str(interval).lower(), "15m")

    if capital_configured() and CAPITAL_PRIMARY_ALL_ASSETS and symbol in MASTER_WATCHLIST:
        df = capital_download(symbol, tf, max_rows=1000)

        # Capital.com sometimes rejects/omits native HOUR/HOUR_4 candles for an
        # epic even when 15-minute candles are available. In strict Capital mode
        # we still must not use Yahoo, so build higher timeframes from Capital
        # 15-minute candles instead. This restores 1H regime + MTF confirmation
        # while keeping Capital.com as the only pricing source.
        if (df is None or df.empty) and tf in {"1h", "4h"}:
            base15 = capital_download(symbol, "15m", max_rows=1000)
            if base15 is not None and not base15.empty:
                df = resample_ohlcv(base15, "1h" if tf == "1h" else "4h")

        if df is not None and not df.empty:
            return df
        if CAPITAL_STRICT_ALL_ASSETS:
            print(f"[Capital] {symbol}: unavailable for {tf}; strict Capital.com pricing active — skipped.")
            return None
        fallback = yahoo_fallback_for_symbol(symbol, ticker)
        if fallback:
            print(f"[Capital] {symbol}: unavailable for {tf}; fallback allowed, using Yahoo {fallback}.")
            ticker = fallback
        else:
            return None

    if CAPITAL_STRICT_ALL_ASSETS:
        print(f"[data] {ticker} ({interval}) skipped: Capital.com strict mode is enabled and no Capital mapping was available.")
        return None

    last_error = None
    safe_ticker = safe_yfinance_ticker(symbol, ticker)
    for attempt in range(1, int(retries) + 1):
        try:
            df = yf.download(safe_ticker, interval=interval, period=period, auto_adjust=True, progress=False, threads=False)
            if df is None or df.empty:
                last_error = "empty response"
            else:
                if isinstance(df.columns, pd.MultiIndex):
                    df.columns = df.columns.get_level_values(0)
                df = df.reset_index()
                df.columns = [str(c) for c in df.columns]
                date_col = df.columns[0]
                df[date_col] = pd.to_datetime(df[date_col], utc=True, errors="coerce").dt.tz_localize(None)
                df = df.dropna(subset=[date_col]).rename(columns={date_col: "Date"})
                if len(df) >= 50:
                    return df
                last_error = f"too few rows ({len(df)})"
        except Exception as e:
            last_error = e
        if attempt < int(retries):
            time.sleep(float(pause_seconds))
    print(f"[data] {safe_ticker} ({interval}) skipped after {retries} attempt(s): {last_error}")
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
    # Use Capital.com's native 4H candles when available instead of building
    # 4H from Yahoo/1H data. This keeps every scanner timeframe on Capital.com.
    if capital_configured() and CAPITAL_PRIMARY_ALL_ASSETS and timeframe == "4h":
        symbol = asset_symbol_from_any_ticker(ticker)
        base = capital_download(symbol, "4h", max_rows=1000)
        if base is None:
            base15 = capital_download(symbol, "15m", max_rows=1000)
            base = resample_ohlcv(base15, "4h") if base15 is not None else None
        if base is None and not CAPITAL_STRICT_ALL_ASSETS:
            base = download(ticker, cfg["interval"], cfg["period"])
            if base is not None and cfg.get("resample"):
                base = resample_ohlcv(base, cfg["resample"])
    else:
        base = download(ticker, cfg["interval"], cfg["period"])
        if base is not None and cfg.get("resample"):
            base = resample_ohlcv(base, cfg["resample"])
    _TF_CACHE[key] = base.copy() if base is not None else None
    return base.copy() if base is not None else None




# ═══════════════════════════════════════════════════════════════════════════════
#  1-MINUTE TRADE REPLAY ENGINE
# ═══════════════════════════════════════════════════════════════════════════════

_TIMEFRAME_MINUTES = {"15m": 15, "1h": 60, "4h": 240, "1d": 1440}
_MINUTE_REPLAY_CACHE: dict[str, pd.DataFrame | None] = {}
_REPLAY_UNAVAILABLE_ASSETS: set[str] = set()


def get_minute_replay_df(ticker: str) -> pd.DataFrame | None:
    """Download/cache recent 1-minute candles for execution replay.

    Capital.com is preferred for CAPITAL:<asset> tickers. In strict mode, Yahoo
    is not used as fallback, so old rows are replayed only against the Capital
    feed that matches TradingView.
    """
    ticker = str(ticker or "").strip()
    if not ticker:
        return None
    cache_key = capital_symbol_from_ticker(ticker) if should_use_capital_for_ticker(ticker) else ticker
    if cache_key in _MINUTE_REPLAY_CACHE:
        cached = _MINUTE_REPLAY_CACHE[cache_key]
        return cached.copy() if cached is not None else None

    # Capital.com 1-minute path.
    if should_use_capital_for_ticker(ticker):
        symbol = capital_symbol_from_ticker(ticker)
        if symbol in _REPLAY_UNAVAILABLE_ASSETS:
            _MINUTE_REPLAY_CACHE[cache_key] = None
            return None
        df = capital_download(symbol, "1m", max_rows=1000)
        if df is not None and not df.empty:
            df = df.copy()
            df["Date"] = pd.to_datetime(df["Date"], utc=True, errors="coerce")
            df = df.dropna(subset=["Date"]).sort_values("Date").reset_index(drop=True)
            _MINUTE_REPLAY_CACHE[cache_key] = df.copy()
            return df.copy()
        if CAPITAL_STRICT_ALL_ASSETS:
            print(f"[Replay1m] {symbol}: Capital.com minute data unavailable or epic unresolved — no Yahoo fallback.")
            _REPLAY_UNAVAILABLE_ASSETS.add(symbol)
            _MINUTE_REPLAY_CACHE[cache_key] = None
            return None
        fallback = yahoo_fallback_for_symbol(symbol, ticker)
        if fallback:
            print(f"[Replay1m] {symbol}: Capital.com minute data unavailable; fallback allowed, using Yahoo {fallback}.")
            ticker_yahoo = fallback
        else:
            _MINUTE_REPLAY_CACHE[cache_key] = None
            return None
    else:
        if CAPITAL_STRICT_ALL_ASSETS:
            symbol = asset_symbol_from_any_ticker(ticker)
            if capital_configured() and symbol in MASTER_WATCHLIST:
                capital_ticker = f"CAPITAL:{symbol}"
                _MINUTE_REPLAY_CACHE[ticker] = get_minute_replay_df(capital_ticker)
                return _MINUTE_REPLAY_CACHE[ticker].copy() if _MINUTE_REPLAY_CACHE[ticker] is not None else None
            print(f"[Replay1m] {ticker}: skipped because strict Capital.com pricing is enabled.")
            _MINUTE_REPLAY_CACHE[cache_key] = None
            return None
        ticker_yahoo = ticker

    # Yahoo fallback path. Used only when strict Capital mode is disabled.
    try:
        df = yf.download(ticker_yahoo, interval="1m", period="7d", auto_adjust=True, progress=False, threads=False)
        if df is None or df.empty:
            _MINUTE_REPLAY_CACHE[cache_key] = None
            return None
        if isinstance(df.columns, pd.MultiIndex):
            df.columns = df.columns.get_level_values(0)
        df = df.reset_index()
        df.columns = [str(c) for c in df.columns]
        date_col = df.columns[0]
        df[date_col] = pd.to_datetime(df[date_col], utc=True, errors="coerce")
        df = df.dropna(subset=[date_col]).rename(columns={date_col: "Date"})
        needed = {"Date", "Open", "High", "Low", "Close"}
        if not needed.issubset(set(df.columns)):
            _MINUTE_REPLAY_CACHE[cache_key] = None
            return None
        df = df.sort_values("Date").reset_index(drop=True)
        _MINUTE_REPLAY_CACHE[cache_key] = df.copy()
        return df.copy()
    except Exception as exc:
        print(f"[Replay1m] {ticker_yahoo}: 1-minute download failed: {exc}")
        _MINUTE_REPLAY_CACHE[cache_key] = None
        return None


def _row_time(row: dict, key: str):
    try:
        ts = pd.to_datetime(row.get(key), errors="coerce", utc=True)
        return None if pd.isna(ts) else ts
    except Exception:
        return None


def trade_entry_time(row: dict):
    """Use candle_close as the trade start when available; otherwise created_at."""
    return _row_time(row, "candle_close") or _row_time(row, "created_at") or pd.Timestamp.now(tz="UTC")


def replay_hit_from_bar(signal: str, high: float, low: float, sl: float, tp: float) -> tuple[bool, bool]:
    signal = str(signal or "").upper()
    if signal == "BUY":
        return bool(low <= sl), bool(high >= tp)
    return bool(high >= sl), bool(low <= tp)


def r_multiple_for_exit(signal: str, entry: float, sl: float, exit_price: float, outcome: str) -> float:
    risk = abs(float(entry) - float(sl))
    if risk <= 0:
        return 0.0
    if str(outcome).upper().endswith("SL") or str(outcome).upper() == "SL":
        return -1.0
    if str(signal).upper() == "BUY":
        return (float(exit_price) - float(entry)) / risk
    return (float(entry) - float(exit_price)) / risk


def replay_trade_outcome(row: dict, *, use_minute: bool = True) -> dict | None:
    """Return the first TP/SL/expiry result for one trade row.

    Result format:
        {"reason": "TP"|"SL"|"EXPIRY", "price": float, "r": float,
         "bars_open": int, "method": "1m"|"timeframe"}

    1-minute replay is preferred because it greatly reduces ambiguous TP+SL
    ordering inside a 15m/1h/4h candle. For rows older than Yahoo's 1-minute
    retention window, the function falls back to the signal timeframe candles.
    """
    try:
        ticker = preferred_data_ticker(str(row.get("asset") or ""), str(row.get("ticker") or "").strip())
        timeframe = str(row.get("timeframe") or "15m").strip().lower()
        signal = str(row.get("signal") or "").strip().upper()
        entry = float(row.get("entry"))
        sl = float(row.get("sl"))
        tp = float(row.get("tp"))
        if signal not in ("BUY", "SELL") or entry <= 0 or abs(entry - sl) <= 0 or sl == tp:
            return None
    except Exception:
        return None

    entry_ts = trade_entry_time(row)
    tf_minutes = int(_TIMEFRAME_MINUTES.get(timeframe, 15))
    expiry_bars = int(TIMEFRAME_CONFIGS.get(timeframe, {}).get("expiry_bars", EXPIRY_BARS))
    expiry_ts = entry_ts + pd.Timedelta(minutes=tf_minutes * expiry_bars)

    # Preferred path: replay each 1-minute candle after entry until expiry.
    if use_minute:
        # Use a bounded Capital.com 1m window, not only the latest 1000 minutes.
        # This keeps historical TP/SL detection accurate for older open trades.
        mdf = get_minute_replay_df_for_window(ticker, entry_ts, expiry_ts)
        if mdf is not None and not mdf.empty:
            mdf = mdf.copy()
            mdf["Date"] = pd.to_datetime(mdf["Date"], utc=True, errors="coerce")
            mdf = mdf.dropna(subset=["Date"]).sort_values("Date")
            replay = mdf[(mdf["Date"] > entry_ts) & (mdf["Date"] <= expiry_ts)]
            for _, bar in replay.iterrows():
                high, low = float(bar["High"]), float(bar["Low"])
                hit_sl, hit_tp = replay_hit_from_bar(signal, high, low, sl, tp)
                if hit_sl and hit_tp:
                    return {"reason": "SL", "price": sl, "r": -1.0, "bars_open": max(1, int(math.ceil((bar["Date"] - entry_ts).total_seconds() / 60 / tf_minutes))), "method": "1m_ambiguous", "exit_time": bar["Date"]}
                if hit_sl:
                    return {"reason": "SL", "price": sl, "r": -1.0, "bars_open": max(1, int(math.ceil((bar["Date"] - entry_ts).total_seconds() / 60 / tf_minutes))), "method": "1m", "exit_time": bar["Date"]}
                if hit_tp:
                    r_mult = abs(tp - entry) / abs(entry - sl) if abs(entry - sl) > 0 else 0.0
                    return {"reason": "TP", "price": tp, "r": r_mult, "bars_open": max(1, int(math.ceil((bar["Date"] - entry_ts).total_seconds() / 60 / tf_minutes))), "method": "1m", "exit_time": bar["Date"]}

            latest_minute_time = mdf["Date"].max()
            if pd.notna(latest_minute_time) and latest_minute_time >= expiry_ts:
                expiry_bars_df = mdf[(mdf["Date"] > entry_ts) & (mdf["Date"] <= expiry_ts)]
                last_price = float(expiry_bars_df["Close"].iloc[-1]) if not expiry_bars_df.empty else float(mdf["Close"].iloc[-1])
                r_mult = r_multiple_for_exit(signal, entry, sl, last_price, "EXPIRY")
                return {"reason": "EXPIRY", "price": last_price, "r": r_mult, "bars_open": expiry_bars, "method": "1m", "exit_time": expiry_ts}

    # Strict execution replay: do not use wider timeframe candles as a fallback.
    # If Capital.com 1-minute data is unavailable, leave the trade open and retry
    # on the next scanner run. This prevents wrong TP/SL ordering and keeps the
    # system aligned with the Capital.com feed used on TradingView.
    if CAPITAL_STRICT_1M_REPLAY_ONLY:
        return None

    return None

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
    """Resolve due OPEN trades with Capital 1-minute replay, grouped by asset.

    Grouping is important: the scanner should fetch at most one recent 1-minute
    dataframe per asset per run, then replay all due trades for that asset from
    the same cached dataframe. This keeps TP/SL timing accurate without turning
    one scanner run into hundreds of duplicate Capital API calls.
    """
    _t_eval = _runtime_start()
    force_open_graded_setups()
    trades = fetch_open_trades(assets=assets, timeframes=timeframes, due_only=True)
    if not trades:
        print("[Evaluate] No due open trades to check.")
        _runtime_stop("open_trade_replay", _t_eval)
        return

    print(f"[Evaluate] Checking {len(trades)} due open trade(s) with cached Capital.com 1-minute replay...")
    closed = 0
    pending = 0

    grouped: dict[str, list[dict]] = {}
    for t in trades:
        asset = str(t.get("asset") or asset_symbol_from_any_ticker(str(t.get("ticker") or ""))).strip().upper()
        grouped.setdefault(asset, []).append(t)

    for asset, rows in grouped.items():
        # Prime cache once. If there is no valid epic or no minute data, mark all
        # rows as checked for their cadence and move on. They remain OPEN.
        ticker = preferred_data_ticker(asset, f"CAPITAL:{asset}")
        mdf = get_minute_replay_df(ticker)
        if mdf is None or mdf.empty:
            pending += len(rows)
            for t in rows:
                mark_replay_checked(str(t.get("signal_id")), int(t.get("bars_open") or 0))
            continue

        for t in rows:
            result = replay_trade_outcome(t, use_minute=True)
            if result is None:
                pending += 1
                mark_replay_checked(str(t.get("signal_id")), int(t.get("bars_open") or 0))
                continue
            reason = str(result.get("reason") or "").upper()
            price = float(result.get("price") or 0.0)
            r = float(result.get("r") or 0.0)
            bars = int(result.get("bars_open") or 0)
            exit_time = result.get("exit_time")
            if reason in {"TP", "SL", "EXPIRY"}:
                if close_trade(str(t.get("signal_id")), price, reason, r, exit_time=exit_time):
                    closed += 1
                    print(f"  [{asset}] Closed: {reason} via {result.get('method','1m')} replay after {bars} bar(s) ({r:+.2f}R)")
                    update_prop_firm(str(t.get("signal_id")), asset, str(t.get("grade") or ""), r)
            else:
                mark_replay_checked(str(t.get("signal_id")), bars)

    if pending:
        print(f"[Evaluate] Pending Capital.com 1-minute data: {pending} trade(s); rows were cadence-stamped and will not be hammered this run.")
    if closed:
        print(f"[Evaluate] Closed {closed} trade(s) this run.")
    _runtime_stop("open_trade_replay", _t_eval)




def backfill_shadow_trade_plans(assets: set[str] | None = None, timeframes: set[str] | None = None, due_only: bool = True) -> int:
    """Compatibility no-op for older shadow replay flow.

    Earlier builds used a separate helper to repair missing entry/SL/TP on
    shadow rows. Current scanner rows are saved with their trade plan at signal
    creation, and historical plan rewriting is locked. Keep this no-op so the
    shadow evaluator does not crash when called by older code paths.
    """
    return 0


def validate_capital_epic_map_for_assets(assets: set[str] | list[str] | tuple[str, ...]) -> tuple[int, int]:
    """Resolve and validate broker epics once at startup.

    Returns (valid_count, total_count). This makes mapping health explicit in
    logs and prevents every replay loop from trying to rediscover the same bad
    placeholder values repeatedly.
    """
    asset_list = sorted({str(a or "").strip().upper() for a in assets if str(a or "").strip()})
    if not asset_list or not capital_configured():
        return (0, len(asset_list))
    valid = 0
    unresolved: list[str] = []
    for asset in asset_list:
        epic = capital_find_epic(asset)
        if epic:
            valid += 1
        else:
            unresolved.append(asset)
    if unresolved:
        preview = ", ".join(unresolved[:12]) + ("..." if len(unresolved) > 12 else "")
        print(f"[CapitalMapping] {valid}/{len(asset_list)} broker epics validated. Unresolved: {preview}")
    else:
        print(f"[CapitalMapping] {valid}/{len(asset_list)} broker epics validated.")
    return valid, len(asset_list)

def evaluate_shadow_trades(assets: set[str] | None = None, timeframes: set[str] | None = None) -> int:
    """
    Hypothetically resolve NO TRADE (shadow) signals using 1-minute replay where
    available, writing only to shadow_* columns. The historical backlog is
    chunked per run so Supabase is not hit with thousands of individual updates.
    """
    backfilled = backfill_shadow_trade_plans(assets=assets, timeframes=timeframes, due_only=True)
    shadow_trades = fetch_unresolved_shadow_trades(
        assets=assets,
        timeframes=timeframes,
        max_age_days=SHADOW_MAX_AGE_DAYS,
        limit=SHADOW_EVAL_LIMIT,
        due_only=True,
    )
    if not shadow_trades:
        print("[Shadow] No unresolved NO TRADE rows to evaluate.")
        return 0

    print(
        f"[Shadow] Checking {len(shadow_trades)} recent unresolved NO TRADE row(s) "
        f"with 1-minute replay where available. Limit: {SHADOW_EVAL_LIMIT}; age cap: {SHADOW_MAX_AGE_DAYS}d."
    )
    if backfilled:
        print(f"[Shadow] Backfill was capped at {SHADOW_BACKFILL_LIMIT} row(s) this run.")

    resolved = 0
    pending_capital_data = 0
    pending_updates: list[tuple[str, float, str, float]] = []
    bars_updates: list[tuple[str, int]] = []

    def _flush_pending() -> int:
        nonlocal pending_updates
        if not pending_updates:
            return 0
        saved = close_shadow_trades_batch(pending_updates)
        pending_updates = []
        return saved

    grouped_shadow: dict[str, list[dict]] = {}
    for t in shadow_trades:
        asset = str(t.get("asset") or asset_symbol_from_any_ticker(str(t.get("ticker") or ""))).strip().upper()
        grouped_shadow.setdefault(asset, []).append(t)

    for asset, rows in grouped_shadow.items():
        # Prime the per-run minute cache once per asset. If Capital minute data is
        # unavailable for that asset, cadence-stamp the whole group and move on.
        ticker = preferred_data_ticker(asset, f"CAPITAL:{asset}")
        mdf = get_minute_replay_df(ticker)
        if mdf is None or mdf.empty:
            pending_capital_data += len(rows)
            for t in rows:
                signal_id = t.get("signal_id")
                if signal_id:
                    mark_replay_checked(signal_id)
            continue

        for t in rows:
            signal_id = t.get("signal_id")
            result = replay_trade_outcome(t, use_minute=True)
            if not result:
                # Capital.com 1-minute data may be temporarily unavailable. Mark this
                # row as checked so it is retried on its timeframe cadence instead of
                # hammering the replay endpoint every scanner run.
                pending_capital_data += 1
                if signal_id:
                    mark_replay_checked(signal_id)
                continue
            reason = result.get("reason")
            bars_open = int(result.get("bars_open") or 0)
            if reason == "OPEN":
                if bars_open:
                    bars_updates.append((signal_id, bars_open))
                continue

            outcome = {"TP": "SHADOW_TP", "SL": "SHADOW_SL", "EXPIRY": "SHADOW_EXPIRY"}.get(str(reason), "SHADOW_EXPIRY")
            pending_updates.append((
                signal_id,
                float(result.get("price") or 0.0),
                outcome,
                float(result.get("r") or 0.0),
            ))
            if len(pending_updates) >= max(1, SHADOW_DB_UPDATE_BATCH_SIZE):
                resolved += _flush_pending()

    resolved += _flush_pending()

    for signal_id, bars_open in bars_updates[:100]:
        bump_bars_open(signal_id, bars_open)

    remaining_note = ""
    if len(shadow_trades) >= SHADOW_EVAL_LIMIT:
        remaining_note = " More unresolved rows likely remain and will be processed on later runs."
    pending_note = f" Pending Capital.com 1-minute data: {pending_capital_data}." if pending_capital_data else ""
    print(f"[Shadow] Resolved {resolved} NO TRADE hypothetical outcome(s) this run.{pending_note}{remaining_note}")
    return resolved



def get_replay_backfill_progress(max_age_days: int | None = None) -> dict:
    """Return Capital replay backlog/progress stats for user-visible logs."""
    days = int(max_age_days if max_age_days is not None else REPLAY_EXISTING_OUTCOMES_DAYS)
    sql = """
        SELECT
            COUNT(*) FILTER (WHERE replay_checked_at IS NULL) AS remaining,
            COUNT(*) FILTER (WHERE replay_checked_at IS NOT NULL) AS checked,
            COUNT(*) AS total
        FROM scanner_signals
        WHERE created_at >= NOW() - (%s::int * INTERVAL '1 day')
          AND UPPER(TRIM(COALESCE(signal, ''))) IN ('BUY', 'SELL')
          AND COALESCE(entry, 0) > 0
          AND ABS(COALESCE(entry,0) - COALESCE(sl,0)) > 0.00000001
          AND ABS(COALESCE(sl,0) - COALESCE(tp,0)) > 0.00000001
          AND (
                UPPER(TRIM(COALESCE(status,''))) IN ('CLOSED_TP','CLOSED_SL','EXPIRED','CLOSED')
             OR shadow_outcome IS NOT NULL
          )
    """
    try:
        conn = db_connect()
        with conn.cursor() as cur:
            cur.execute(sql, (days,))
            row = cur.fetchone() or {}
        conn.close()
        remaining = int(row.get("remaining") or 0)
        checked = int(row.get("checked") or 0)
        total = int(row.get("total") or 0)
        pct = (checked / total * 100.0) if total else 100.0
        runs_left = math.ceil(remaining / max(1, int(REPLAY_EXISTING_OUTCOMES_LIMIT))) if remaining else 0
        return {"remaining": remaining, "checked": checked, "total": total, "pct": pct, "runs_left": runs_left}
    except Exception as exc:
        print(f"[Replay1mBackfill] Progress query failed: {exc}")
        return {"remaining": 0, "checked": 0, "total": 0, "pct": 0.0, "runs_left": 0}

def fetch_existing_outcomes_for_replay(max_age_days: int = 30, limit: int = 5000) -> list[dict]:
    """Fetch already-resolved rows that can be improved with 1-minute replay.

    This includes real journal trades with CLOSED/EXPIRED status and shadow
    research rows that already have a shadow outcome. It intentionally excludes
    rows with unusable plans (Entry=SL=TP); those are handled by the shadow
    plan backfill before unresolved shadow evaluation.
    """
    sql = """
        SELECT *
        FROM scanner_signals
        WHERE created_at >= NOW() - (%s::int * INTERVAL '1 day')
          AND UPPER(TRIM(COALESCE(signal, ''))) IN ('BUY', 'SELL')
          AND COALESCE(entry, 0) > 0
          AND ABS(COALESCE(entry,0) - COALESCE(sl,0)) > 0.00000001
          AND ABS(COALESCE(sl,0) - COALESCE(tp,0)) > 0.00000001
          AND (
                UPPER(TRIM(COALESCE(status,''))) IN ('CLOSED_TP','CLOSED_SL','EXPIRED','CLOSED')
             OR shadow_outcome IS NOT NULL
          )
          AND replay_checked_at IS NULL
        ORDER BY created_at ASC
        LIMIT %s
    """
    try:
        conn = db_connect()
        with conn.cursor() as cur:
            cur.execute(sql, (int(max_age_days), int(limit)))
            rows = [dict(r) for r in cur.fetchall()]
        conn.close()
        return rows
    except Exception as exc:
        print(f"[Replay1mBackfill] Fetch failed: {exc}")
        return []


def enforce_historical_plan_lock(updates: list[dict]) -> list[dict]:
    """Remove/guard any accidental plan-field mutations during replay.

    This keeps Supabase audit-clean: replay can correct outcomes, but it cannot
    rewrite the original signal plan. New signals get Capital.com-based
    entry/sl/tp at creation time; old signals keep whatever plan they originally
    had.
    """
    if not LOCK_HISTORICAL_SIGNAL_PLANS:
        return updates
    clean: list[dict] = []
    for update in updates or []:
        if not isinstance(update, dict):
            continue
        blocked = FORBIDDEN_HISTORICAL_PLAN_KEYS.intersection(update.keys())
        if blocked:
            print(f"[Replay1mBackfill] Historical plan lock removed forbidden keys {sorted(blocked)} for {update.get('signal_id')}")
            update = {k: v for k, v in update.items() if k not in FORBIDDEN_HISTORICAL_PLAN_KEYS}
        clean.append(update)
    return clean


def update_existing_outcomes_batch(updates: list[dict]) -> int:
    """Apply replayed journal/shadow outcomes in one controlled DB transaction.

    Important: this function intentionally does NOT update entry, sl, tp, or rr
    for historical rows. It only corrects realised outcome fields after replay.
    """
    updates = enforce_historical_plan_lock(updates)
    if not updates:
        return 0
    try:
        conn = db_connect()
        applied = 0
        with conn:
            with conn.cursor() as cur:
                for u in updates:
                    signal_id = u.get("signal_id")
                    if not signal_id:
                        continue
                    if u.get("is_shadow"):
                        cur.execute(
                            """
                            UPDATE scanner_signals
                            SET shadow_outcome = %s,
                                shadow_r_multiple = %s,
                                shadow_exit_price = %s,
                                shadow_closed_at = %s,
                                replay_checked_at = NOW()
                            WHERE signal_id = %s
                            """,
                            (u["outcome"], u["r_multiple"], u["exit_price"], u["exit_at"], signal_id),
                        )
                    else:
                        cur.execute(
                            """
                            UPDATE scanner_signals
                            SET status = %s,
                                exit_price = %s,
                                exit_reason = %s,
                                exit_at = %s,
                                r_multiple = %s,
                                replay_checked_at = NOW()
                            WHERE signal_id = %s
                            """,
                            (u["status"], u["exit_price"], u["exit_reason"], u["exit_at"], u["r_multiple"], signal_id),
                        )
                        if u.get("prop_grade") in {"A+", "A"}:
                            pnl_cash = float(ACCOUNT_SIZE) * float(RISK_PER_TRADE) * float(u["r_multiple"])
                            cur.execute(
                                """
                                UPDATE prop_firm_trades
                                SET r_multiple = %s, pnl_cash = %s, closed_at = %s
                                WHERE signal_id = %s
                                """,
                                (u["r_multiple"], pnl_cash, u["exit_at"], signal_id),
                            )
                    applied += int(cur.rowcount >= 0)
        conn.close()
        return applied
    except Exception as exc:
        print(f"[Replay1mBackfill] Batch update failed for {len(updates)} row(s): {exc}")
        return 0


def mark_existing_replay_checked(signal_ids: list[str]) -> int:
    """Mark rows as checked even when replay cannot improve them, so each run advances."""
    signal_ids = [str(x) for x in signal_ids if x]
    if not signal_ids:
        return 0
    try:
        conn = db_connect()
        with conn:
            with conn.cursor() as cur:
                cur.execute(
                    "UPDATE scanner_signals SET replay_checked_at = NOW() WHERE signal_id = ANY(%s)",
                    (signal_ids,),
                )
                count = cur.rowcount or 0
        conn.close()
        return int(count)
    except Exception as exc:
        print(f"[Replay1mBackfill] Could not mark checked rows: {exc}")
        return 0


def replay_existing_resolved_outcomes(max_age_days: int | None = None, limit: int | None = None) -> int:
    """Recalculate existing Supabase outcomes with 1-minute replay in safe batches.

    This deliberately processes only a limited number per scanner run. That means
    old SL/TP/expiry data is improved gradually without overloading Supabase.
    Rows are marked with replay_checked_at so the next run moves to the next
    batch instead of hammering the same records repeatedly.
    """
    days = int(max_age_days if max_age_days is not None else REPLAY_EXISTING_OUTCOMES_DAYS)
    lim = int(limit if limit is not None else REPLAY_EXISTING_OUTCOMES_LIMIT)
    progress = get_replay_backfill_progress(days)
    if progress.get("total", 0):
        print(
            f"[Replay1mBackfill] Progress: {progress['checked']:,}/{progress['total']:,} checked "
            f"({progress['pct']:.1f}%). Remaining: {progress['remaining']:,}. "
            f"Estimated runs left at {lim:,}/run: {progress['runs_left']:,}."
        )
    rows = fetch_existing_outcomes_for_replay(days, lim)
    if not rows:
        print("[Replay1mBackfill] No existing resolved outcomes to replay.")
        return 0

    updates: list[dict] = []
    checked_without_update: list[str] = []
    minute_updates = 0
    fallback_updates = 0

    for row in rows:
        signal_id = row.get("signal_id")
        result = replay_trade_outcome(row, use_minute=True)
        if not result or str(result.get("reason") or "").upper() == "OPEN":
            if signal_id:
                checked_without_update.append(str(signal_id))
            continue

        reason = str(result.get("reason") or "").upper()
        if reason not in {"TP", "SL", "EXPIRY"}:
            if signal_id:
                checked_without_update.append(str(signal_id))
            continue

        exit_time = pd.to_datetime(result.get("exit_time"), errors="coerce", utc=True)
        if pd.isna(exit_time):
            exit_time = pd.Timestamp.now(tz="UTC")
        exit_at = exit_time.isoformat()
        exit_price = float(result.get("price") or 0.0)
        r_mult = float(result.get("r") or 0.0)
        is_shadow = str(row.get("status") or "").upper() == "SHADOW" or row.get("shadow_outcome") is not None

        method = str(result.get("method") or "")
        if method.startswith("1m"):
            minute_updates += 1
        else:
            fallback_updates += 1

        if is_shadow:
            outcome = {"TP": "SHADOW_TP", "SL": "SHADOW_SL", "EXPIRY": "SHADOW_EXPIRY"}.get(reason, "SHADOW_EXPIRY")
            updates.append({
                "signal_id": signal_id,
                "is_shadow": True,
                "outcome": outcome,
                "r_multiple": r_mult,
                "exit_price": exit_price,
                "exit_at": exit_at,
            })
        else:
            status = {"TP": "CLOSED_TP", "SL": "CLOSED_SL", "EXPIRY": "EXPIRED"}.get(reason, "CLOSED")
            updates.append({
                "signal_id": signal_id,
                "is_shadow": False,
                "status": status,
                "exit_reason": reason,
                "r_multiple": r_mult,
                "exit_price": exit_price,
                "exit_at": exit_at,
                "prop_grade": str(row.get("grade") or "").upper(),
            })

    updated = update_existing_outcomes_batch(updates)
    marked = mark_existing_replay_checked(checked_without_update)
    remaining_note = " More rows may remain and will be processed on later runs." if len(rows) >= lim else ""
    print(
        f"[Replay1mBackfill] Checked {len(rows)} existing outcome(s); updated {updated}, "
        f"marked {marked} unchanged/open. {minute_updates} used 1-minute data, "
        f"{fallback_updates} used timeframe fallback.{remaining_note}"
    )
    return updated



# ═══════════════════════════════════════════════════════════════════════════════
#  CAPITAL.COM ACTUAL EXECUTION SYNC / SIMULATION COMPARISON
# ═══════════════════════════════════════════════════════════════════════════════

def _first_value(obj: dict, keys: list[str], default=None):
    if not isinstance(obj, dict):
        return default
    for key in keys:
        if key in obj and obj.get(key) not in (None, ""):
            return obj.get(key)
    return default


def _nested_first_value(obj: dict, paths: list[list[str]], default=None):
    for path in paths:
        current = obj
        ok = True
        for key in path:
            if not isinstance(current, dict) or key not in current:
                ok = False
                break
            current = current.get(key)
        if ok and current not in (None, ""):
            return current
    return default


def _parse_capital_time(value):
    try:
        ts = pd.to_datetime(value, errors="coerce", utc=True)
        return None if pd.isna(ts) else ts.to_pydatetime()
    except Exception:
        return None


def _parse_float_or_none(value):
    try:
        if value is None or value == "":
            return None
        x = float(value)
        return x if math.isfinite(x) else None
    except Exception:
        return None

def _json_dict(value) -> dict:
    """Return a dict from psycopg2 JSONB/text values without throwing."""
    if isinstance(value, dict):
        return value
    if isinstance(value, str) and value.strip():
        try:
            parsed = json.loads(value)
            return parsed if isinstance(parsed, dict) else {}
        except Exception:
            return {}
    return {}


def _capital_level_from_raw(raw: dict, kind: str):
    """Extract broker-confirmed levels from Capital.com raw order/position JSON.

    kind: entry | stop | limit | exit
    Capital.com responses are not perfectly consistent across endpoints, so this
    checks confirm, response, payload and open-position raw JSON before falling
    back to None. This prevents the audit from pretending that planned and broker
    prices are identical when Capital did not return the fill in the main row.
    """
    raw = _json_dict(raw)
    position = raw.get("position") if isinstance(raw.get("position"), dict) else raw
    market = raw.get("market") if isinstance(raw.get("market"), dict) else {}
    payload = _json_dict(raw.get("payload"))
    confirm = _json_dict(raw.get("confirm"))
    response = _json_dict(raw.get("response"))
    details = _json_dict(raw.get("details"))

    if kind == "entry":
        keys = ["level", "openLevel", "entryPrice", "price", "executedLevel", "dealLevel"]
        paths = [["affectedDeals", 0, "level"], ["deal", "level"], ["position", "level"]]
    elif kind == "exit":
        keys = ["closeLevel", "exitPrice", "closePrice"]
        paths = [["affectedDeals", 0, "closeLevel"], ["deal", "closeLevel"], ["position", "closeLevel"]]
    elif kind == "stop":
        keys = ["stopLevel", "stopLossLevel", "sl", "stopPrice"]
        paths = [["position", "stopLevel"], ["deal", "stopLevel"], ["affectedDeals", 0, "stopLevel"]]
    else:  # limit / take profit
        keys = ["profitLevel", "limitLevel", "takeProfitLevel", "tp", "limitPrice"]
        paths = [["position", "profitLevel"], ["position", "limitLevel"], ["deal", "limitLevel"], ["affectedDeals", 0, "limitLevel"]]

    # direct dict checks first
    for obj in (position, confirm, response, details, payload, market):
        if isinstance(obj, dict):
            val = _first_value(obj, keys, None)
            parsed = _parse_float_or_none(val)
            if parsed is not None:
                return parsed

    # nested/list paths
    for root in (raw, confirm, response):
        for path in paths:
            cur = root
            ok = True
            for key in path:
                if isinstance(key, int):
                    if isinstance(cur, list) and len(cur) > key:
                        cur = cur[key]
                    else:
                        ok = False
                        break
                else:
                    if isinstance(cur, dict) and key in cur:
                        cur = cur.get(key)
                    else:
                        ok = False
                        break
            if ok:
                parsed = _parse_float_or_none(cur)
                if parsed is not None:
                    return parsed
    return None


def deterministic_uuid_text(seed: str) -> str:
    """Return a UUID string for comparison rows even when Supabase id is UUID.

    Earlier comparison code used readable ids like AUTO::<signal_id>. That fails
    when the table was created with id UUID PRIMARY KEY. Using uuid5 keeps the
    row deterministic and still works if the column is TEXT.
    """
    return str(uuid.uuid5(uuid.NAMESPACE_URL, str(seed or uuid.uuid4().hex)))


def capital_asset_from_epic(epic: str, name: str = "") -> str:
    epic_u = str(epic or "").upper()
    name_u = str(name or "").upper()
    for asset, cached_epic in list(_CAPITAL_EPIC_CACHE.items()):
        if str(cached_epic or "").upper() == epic_u:
            return asset
    checks = {
        "XAUUSD": ["XAU", "GOLD"],
        "XAGUSD": ["XAG", "SILVER"],
        "OIL": ["OIL_CRUDE", "USOIL", "CRUDE"],
        "BRENT": ["OIL_BRENT", "BRENT"],
        "NATGAS": ["NATURAL", "NATGAS", "GAS"],
        "COPPER": ["COPPER"],
        "SP500": ["US500", "SPX", "S&P"],
        "NAS100": ["US100", "NASDAQ", "NAS100"],
        "DOW30": ["US30", "DOW", "WALL"],
        "BTCUSD": ["BTC", "BITCOIN"],
        "ETHUSD": ["ETH", "ETHEREUM"],
    }
    for asset, needles in checks.items():
        if any(n in epic_u or n in name_u for n in needles):
            return asset
    compact = (epic_u + " " + name_u).replace("/", "").replace(" ", "")
    for asset in MASTER_WATCHLIST:
        if asset in compact:
            return asset
    return epic_u or "UNKNOWN"


def capital_fetch_open_positions() -> list[dict]:
    data = capital_request("GET", "/positions", retries=2)
    if not isinstance(data, dict):
        return []
    rows = data.get("positions") or data.get("items") or []
    return rows if isinstance(rows, list) else []


def capital_fetch_activity_history() -> list[dict]:
    """Optional Capital.com history fetch.

    For the current auto-trade demo test, open positions are enough because
    BENZINO stores every API-created order in capital_auto_orders with signal_id.
    Some Capital.com accounts reject numeric lastPeriod values with
    error.invalid.lastPeriod, so history sync stays disabled unless explicitly
    enabled. This prevents noisy failures during every scanner run.
    """
    if not CAPITAL_FETCH_ACTIVITY_HISTORY:
        return []

    rows: list[dict] = []
    # Try conservative string periods first, then a short numeric fallback.
    candidate_params = [
        {"lastPeriod": "DAY", "detailed": "true"},
        {"lastPeriod": "WEEK", "detailed": "true"},
        {"lastPeriod": "LAST_DAY", "detailed": "true"},
    ]
    for params in candidate_params:
        for path in ("/history/activity", "/history/transactions"):
            data = capital_request("GET", path, params=params, retries=1)
            if not isinstance(data, dict):
                continue
            candidate = data.get("activities") or data.get("transactions") or data.get("items") or data.get("history") or []
            if isinstance(candidate, list) and candidate:
                rows.extend(candidate)
                return rows
    return rows


def normalise_capital_position(row: dict) -> dict | None:
    position = row.get("position") if isinstance(row.get("position"), dict) else row
    market = row.get("market") if isinstance(row.get("market"), dict) else {}
    deal_id = str(_first_value(position, ["dealId", "dealID", "id", "positionId"], "") or "")
    deal_ref = str(_first_value(position, ["dealReference", "dealRef", "reference"], "") or "")
    epic = str(_first_value(market, ["epic"], "") or _first_value(position, ["epic", "marketId"], "") or "")
    name = str(_first_value(market, ["instrumentName", "name"], "") or _first_value(position, ["instrumentName", "marketName", "name"], "") or "")
    direction = str(_first_value(position, ["direction", "side"], "") or "").upper()
    opened_at = _parse_capital_time(_first_value(position, ["createdDateUTC", "createdDate", "openDate", "openedAt", "date"], None))
    entry = _parse_float_or_none(_first_value(position, ["level", "openLevel", "entryPrice", "price"], None))
    size = _parse_float_or_none(_first_value(position, ["size", "dealSize", "quantity"], None))
    pnl = _parse_float_or_none(_first_value(position, ["profit", "pnl", "upl", "realizedProfit"], None))
    if not (deal_id or deal_ref or epic):
        return None
    raw_id = deal_id or deal_ref or f"{epic}:{opened_at or datetime.now(timezone.utc).isoformat()}"
    return {
        "id": f"CAPITAL_OPEN:{raw_id}",
        "deal_id": deal_id,
        "deal_reference": deal_ref,
        "source_type": "OPEN_POSITION",
        "environment": "demo" if CAPITAL_DEMO else "live",
        "epic": epic,
        "asset": capital_asset_from_epic(epic, name),
        "instrument_name": name,
        "direction": "BUY" if direction in {"BUY", "LONG"} else "SELL" if direction in {"SELL", "SHORT"} else direction,
        "status": "OPEN",
        "opened_at": opened_at,
        "closed_at": None,
        "entry_price": entry,
        "exit_price": None,
        "size": size,
        "pnl": pnl,
        "currency": str(_first_value(position, ["currency", "profitCurrency"], "") or ""),
        "raw_json": row,
    }


def normalise_capital_activity(row: dict) -> dict | None:
    market = row.get("market") if isinstance(row.get("market"), dict) else {}
    details = row.get("details") if isinstance(row.get("details"), dict) else {}
    deal_id = str(_first_value(row, ["dealId", "dealID", "id", "positionId"], "") or _first_value(details, ["dealId", "positionId"], "") or "")
    deal_ref = str(_first_value(row, ["dealReference", "dealRef", "reference"], "") or _first_value(details, ["dealReference", "dealRef"], "") or "")
    epic = str(_first_value(row, ["epic", "marketId"], "") or _first_value(market, ["epic"], "") or _first_value(details, ["epic", "marketId"], "") or "")
    name = str(_first_value(row, ["instrumentName", "marketName", "name"], "") or _first_value(market, ["instrumentName", "name"], "") or _first_value(details, ["instrumentName", "marketName"], "") or "")
    activity_type = str(_first_value(row, ["type", "activityType"], "") or "").upper()
    raw_status = str(_first_value(row, ["status", "dealStatus"], "") or _first_value(details, ["status"], "") or "").upper()
    direction = str(_first_value(row, ["direction", "side"], "") or _first_value(details, ["direction", "side"], "") or "").upper()
    opened_at = _parse_capital_time(_first_value(row, ["createdDateUTC", "createdDate", "date", "openDate", "openedAt"], None))
    closed_at = _parse_capital_time(_first_value(row, ["closeDate", "closedAt", "date"], None)) if ("CLOSE" in activity_type or "CLOSE" in raw_status) else None
    entry = _parse_float_or_none(_first_value(row, ["level", "openLevel", "entryPrice", "price"], None) or _first_value(details, ["level", "openLevel", "entryPrice", "price"], None))
    exit_price = _parse_float_or_none(_first_value(row, ["closeLevel", "exitPrice"], None) or _first_value(details, ["closeLevel", "exitPrice"], None))
    size = _parse_float_or_none(_first_value(row, ["size", "dealSize", "quantity"], None) or _first_value(details, ["size", "dealSize", "quantity"], None))
    pnl = _parse_float_or_none(_first_value(row, ["profit", "pnl", "realizedProfit", "amount"], None) or _first_value(details, ["profit", "pnl", "realizedProfit", "amount"], None))
    if not (deal_id or deal_ref or epic):
        return None
    if "REJECT" in raw_status:
        return None
    status = "CLOSED" if (closed_at or "CLOSE" in activity_type or "CLOSE" in raw_status) else "ACTIVITY"
    raw_id = deal_id or deal_ref or f"{epic}:{opened_at or datetime.now(timezone.utc).isoformat()}:{activity_type}"
    return {
        "id": f"CAPITAL_ACTIVITY:{raw_id}:{status}",
        "deal_id": deal_id,
        "deal_reference": deal_ref,
        "source_type": activity_type or "ACTIVITY",
        "environment": "demo" if CAPITAL_DEMO else "live",
        "epic": epic,
        "asset": capital_asset_from_epic(epic, name),
        "instrument_name": name,
        "direction": "BUY" if direction in {"BUY", "LONG"} else "SELL" if direction in {"SELL", "SHORT"} else direction,
        "status": status,
        "opened_at": opened_at,
        "closed_at": closed_at,
        "entry_price": entry,
        "exit_price": exit_price,
        "size": size,
        "pnl": pnl,
        "currency": str(_first_value(row, ["currency", "profitCurrency"], "") or _first_value(details, ["currency", "profitCurrency"], "") or ""),
        "raw_json": row,
    }


def upsert_capital_executed_trades(rows: list[dict]) -> int:
    rows = [r for r in rows if isinstance(r, dict) and r.get("id")]
    if not rows:
        return 0
    sql = """
    INSERT INTO capital_executed_trades (
        id, deal_id, deal_reference, source_type, environment, epic, asset,
        instrument_name, direction, status, opened_at, closed_at, entry_price,
        exit_price, size, pnl, currency, raw_json, updated_at
    ) VALUES (
        %s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,NOW()
    )
    ON CONFLICT (id) DO UPDATE SET
        deal_id = EXCLUDED.deal_id,
        deal_reference = EXCLUDED.deal_reference,
        source_type = EXCLUDED.source_type,
        environment = EXCLUDED.environment,
        epic = EXCLUDED.epic,
        asset = EXCLUDED.asset,
        instrument_name = EXCLUDED.instrument_name,
        direction = EXCLUDED.direction,
        status = EXCLUDED.status,
        opened_at = EXCLUDED.opened_at,
        closed_at = EXCLUDED.closed_at,
        entry_price = EXCLUDED.entry_price,
        exit_price = EXCLUDED.exit_price,
        size = EXCLUDED.size,
        pnl = EXCLUDED.pnl,
        currency = EXCLUDED.currency,
        raw_json = EXCLUDED.raw_json,
        updated_at = NOW()
    """
    params = []
    for r in rows:
        params.append((
            r.get("id"), r.get("deal_id"), r.get("deal_reference"), r.get("source_type"),
            r.get("environment"), r.get("epic"), r.get("asset"), r.get("instrument_name"),
            r.get("direction"), r.get("status"), r.get("opened_at"), r.get("closed_at"),
            r.get("entry_price"), r.get("exit_price"), r.get("size"), r.get("pnl"),
            r.get("currency"), json.dumps(sanitize_for_json(r.get("raw_json") or {}), allow_nan=False),
        ))
    try:
        conn = db_connect()
        with conn:
            with conn.cursor() as cur:
                cur.executemany(sql, params)
        conn.close()
        return len(rows)
    except Exception as exc:
        print(f"[CapitalSync] Upsert failed for {len(rows)} row(s): {exc}")
        return 0


def rebuild_capital_trade_comparisons(limit: int = 500) -> int:
    """Match actual Capital.com executions to nearest BENZINO simulated signal.

    Matching is intentionally conservative: same asset, same BUY/SELL direction,
    and nearest signal created before/around the actual open time. The user can
    then inspect entry/exit drift in the app.
    """
    try:
        conn = db_connect()
        with conn:
            with conn.cursor() as cur:
                cur.execute("DELETE FROM capital_trade_comparisons WHERE COALESCE(auto_trade, FALSE) = FALSE")
                cur.execute(
                    """
                    SELECT *
                    FROM capital_executed_trades
                    WHERE opened_at IS NOT NULL
                      AND UPPER(TRIM(COALESCE(direction,''))) IN ('BUY','SELL')
                    ORDER BY opened_at DESC
                    LIMIT %s
                    """,
                    (int(limit),),
                )
                actual_rows = [dict(r) for r in cur.fetchall()]
                inserted = 0
                for actual in actual_rows:
                    cur.execute(
                        """
                        SELECT signal_id, asset, signal, entry, exit_price, r_multiple,
                               status, exit_reason, created_at, candle_close
                        FROM scanner_signals
                        WHERE asset = %s
                          AND UPPER(TRIM(COALESCE(signal,''))) = %s
                          AND UPPER(TRIM(COALESCE(grade,''))) IN ('A+','A','B','C')
                          AND created_at BETWEEN %s::timestamptz - (%s::int * INTERVAL '1 hour')
                                             AND %s::timestamptz + (%s::int * INTERVAL '1 hour')
                        ORDER BY ABS(EXTRACT(EPOCH FROM (created_at - %s::timestamptz))) ASC
                        LIMIT 1
                        """,
                        (
                            actual.get("asset"), actual.get("direction"), actual.get("opened_at"), CAPITAL_MATCH_WINDOW_HOURS,
                            actual.get("opened_at"), CAPITAL_MATCH_WINDOW_HOURS, actual.get("opened_at"),
                        ),
                    )
                    sim = cur.fetchone()
                    if not sim:
                        continue
                    sim = dict(sim)
                    actual_entry = _parse_float_or_none(actual.get("entry_price"))
                    simulated_entry = _parse_float_or_none(sim.get("entry"))
                    actual_exit = _parse_float_or_none(actual.get("exit_price"))
                    simulated_exit = _parse_float_or_none(sim.get("exit_price"))
                    entry_diff = (actual_entry - simulated_entry) if actual_entry is not None and simulated_entry is not None else None
                    exit_diff = (actual_exit - simulated_exit) if actual_exit is not None and simulated_exit is not None else None
                    if entry_diff is None:
                        quality = "MATCHED_NO_ENTRY"
                    else:
                        basis = max(abs(simulated_entry or 0), 1.0)
                        drift_pct = abs(entry_diff) / basis * 100
                        quality = "TIGHT" if drift_pct <= 0.05 else "OK" if drift_pct <= 0.25 else "WIDE"
                    comp_id = deterministic_uuid_text(f"CAPITAL::{actual.get('id')}::{sim.get('signal_id')}")
                    cur.execute(
                        """
                        INSERT INTO capital_trade_comparisons (
                            id, capital_trade_id, signal_id, asset, direction,
                            simulated_entry, actual_entry, entry_diff,
                            simulated_exit, actual_exit, exit_diff,
                            simulated_r, actual_pnl, simulated_outcome, actual_status,
                            match_quality, opened_at, updated_at
                        ) VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,NOW())
                        ON CONFLICT (id) DO NOTHING
                        """,
                        (
                            comp_id, actual.get("id"), sim.get("signal_id"), actual.get("asset"), actual.get("direction"),
                            simulated_entry, actual_entry, entry_diff, simulated_exit, actual_exit, exit_diff,
                            _parse_float_or_none(sim.get("r_multiple")), _parse_float_or_none(actual.get("pnl")),
                            sim.get("status") or sim.get("exit_reason"), actual.get("status"), quality, actual.get("opened_at"),
                        ),
                    )
                    inserted += 1
        conn.close()
        if inserted:
            print(f"[CapitalCompare] Matched {inserted} actual execution(s) to simulated BENZINO signal(s).")
        return inserted
    except Exception as exc:
        print(f"[CapitalCompare] Rebuild failed: {exc}")
        return 0


def capital_auto_order_exists(signal_id: str) -> bool:
    try:
        conn = db_connect()
        with conn.cursor() as cur:
            cur.execute("SELECT 1 FROM capital_auto_orders WHERE signal_id = %s LIMIT 1", (signal_id,))
            row = cur.fetchone()
        conn.close()
        return row is not None
    except Exception as exc:
        print(f"[CapitalAuto] order existence check failed: {exc}")
        return True



def _safe_float_setting(settings: dict, keys: list[str], default: float) -> float:
    for key in keys:
        try:
            value = settings.get(key, None)
            if value not in (None, ""):
                return float(value)
        except Exception:
            continue
    return float(default)



def capital_session_windows_scanner() -> dict[str, tuple[int, int]]:
    """Capital auto-trade session windows in EAT hours.

    The execution engine ranks these sessions daily, then only trades a session
    from one hour after its open until that session closes. The daily cap is a
    maximum, not a quota.
    """
    return {
        "Asia": (0, 8),
        "London AM": (8, 16),
        "London/NY Overlap": (16, 20),
        "New York PM": (20, 24),
    }


def prop_session_from_timestamp_scanner(ts) -> str:
    try:
        dt = pd.to_datetime(ts, utc=True).tz_convert(NAIROBI_TZ)
        hour = int(dt.hour)
    except Exception:
        return "Unknown"
    for name, (start_hour, end_hour) in capital_session_windows_scanner().items():
        if start_hour <= hour < end_hour:
            return name
    return "Unknown"


def prop_session_open_hour_scanner(session: str) -> int | None:
    session_norm = str(session or "").strip().lower()
    aliases = {
        "asia": "Asia",
        "london": "London AM",
        "london am": "London AM",
        "london/ny": "London/NY Overlap",
        "london/ny overlap": "London/NY Overlap",
        "new york": "New York PM",
        "new york pm": "New York PM",
        "ny": "New York PM",
        "ny pm": "New York PM",
    }
    session_name = aliases.get(session_norm, str(session or "").strip())
    window = capital_session_windows_scanner().get(session_name)
    return int(window[0]) if window else None


def capital_session_end_hour_scanner(session: str) -> int | None:
    session_norm = str(session or "").strip().lower()
    aliases = {
        "asia": "Asia",
        "london": "London AM",
        "london am": "London AM",
        "london/ny": "London/NY Overlap",
        "london/ny overlap": "London/NY Overlap",
        "new york": "New York PM",
        "new york pm": "New York PM",
        "ny": "New York PM",
        "ny pm": "New York PM",
    }
    session_name = aliases.get(session_norm, str(session or "").strip())
    window = capital_session_windows_scanner().get(session_name)
    return int(window[1]) if window else None


def prop_is_one_hour_after_session_open_scanner(ts, session: str) -> bool:
    open_hour = prop_session_open_hour_scanner(session)
    end_hour = capital_session_end_hour_scanner(session)
    if open_hour is None or end_hour is None:
        return True
    try:
        dt = pd.to_datetime(ts, utc=True).tz_convert(NAIROBI_TZ)
    except Exception:
        return False
    return int(dt.hour) >= open_hour + 1 and int(dt.hour) < end_hour


def capital_session_has_ended_scanner(dt_eat: pd.Timestamp, session: str) -> bool:
    end_hour = capital_session_end_hour_scanner(session)
    if end_hour is None:
        return False
    return int(dt_eat.hour) >= end_hour


def capital_session_entry_open_scanner(dt_eat: pd.Timestamp, session: str) -> bool:
    open_hour = prop_session_open_hour_scanner(session)
    end_hour = capital_session_end_hour_scanner(session)
    if open_hour is None or end_hour is None:
        return False
    return (int(dt_eat.hour) >= open_hour + 1) and (int(dt_eat.hour) < end_hour)


def capital_session_order_for_user(username: str, timeframe: str, assets: set[str]) -> dict:
    """Rank all execution sessions from closed A/A+ user-journal outcomes.

    Session is classified from the original signal generation time (`created_at`),
    never from the trade close time. Sessions with at least the configured sample
    threshold are ranked first; below-sample sessions are still retained as lower
    priority fallbacks so the engine can use later remaining sessions without
    forcing trades.
    """
    username = str(username or "").strip().lower()
    timeframe = _normalize_timeframe(timeframe)
    if not assets:
        return {"session_order": [], "sample_ready": False, "reason": "empty_watchlist"}
    try:
        conn = db_connect()
        with conn.cursor() as cur:
            cur.execute(
                """
                SELECT asset, timeframe, created_at, r_multiple, grade
                FROM scanner_signals
                WHERE asset = ANY(%s)
                  AND timeframe = %s
                  AND signal IN ('BUY','SELL')
                  AND grade IN ('A+','A')
                  AND exit_at IS NOT NULL
                  AND r_multiple IS NOT NULL
                """,
                (list(sorted(assets)), timeframe),
            )
            rows = [dict(r) for r in cur.fetchall()]
        conn.close()
    except Exception as exc:
        print(f"[CapitalAuto] Session ranking lookup failed for {username}: {exc}")
        return {"session_order": [], "sample_ready": False, "reason": "lookup_failed"}

    buckets: dict[str, list[float]] = {name: [] for name in capital_session_windows_scanner().keys()}
    for r in rows:
        sess = prop_session_from_timestamp_scanner(r.get("created_at"))
        if sess == "Unknown":
            continue
        try:
            rr = float(r.get("r_multiple") or 0)
        except Exception:
            rr = 0.0
        buckets.setdefault(sess, []).append(rr)

    ranked = []
    for sess, vals in buckets.items():
        gross_profit = sum(v for v in vals if v > 0)
        gross_loss = abs(sum(v for v in vals if v < 0))
        pf = gross_profit / gross_loss if gross_loss > 0 else (gross_profit if gross_profit > 0 else 0.0)
        wr = 100.0 * (sum(1 for v in vals if v > 0) / len(vals)) if vals else 0.0
        net = sum(vals)
        ranked.append({
            "session": sess,
            "profit_factor": pf,
            "win_rate": wr,
            "net_r": net,
            "trade_count": len(vals),
            "sample_ready": len(vals) >= CAPITAL_AUTO_TRADE_MIN_SESSION_TRADES,
        })
    # Reliable samples rank above provisional sessions, then by quality.
    ranked = sorted(ranked, key=lambda x: (bool(x["sample_ready"]), x["profit_factor"], x["win_rate"], x["net_r"], x["trade_count"]), reverse=True)
    return {
        "session_order": ranked,
        "best_session": ranked[0]["session"] if ranked else "",
        "sample_ready": bool(ranked and ranked[0].get("sample_ready")),
        "trade_count": int(ranked[0].get("trade_count", 0)) if ranked else 0,
        "reason": "" if ranked else "no_closed_A_trades",
    }


def capital_best_session_profile_for_user(username: str, timeframe: str, assets: set[str]) -> dict:
    ranked = capital_session_order_for_user(username, timeframe, assets)
    order = ranked.get("session_order") or []
    if not order:
        return {"best_session": "", "sample_ready": False, "trade_count": 0, "reason": ranked.get("reason") or "no_closed_A_trades"}
    best = dict(order[0])
    best["best_session"] = best.get("session", "")
    if not best.get("sample_ready"):
        best["reason"] = f"best_session_sample_below_{CAPITAL_AUTO_TRADE_MIN_SESSION_TRADES}"
    best["session_order"] = order
    return best


def capital_auto_trading_day_eat(ts=None):
    try:
        dt = pd.to_datetime(ts or datetime.now(timezone.utc), utc=True).tz_convert(NAIROBI_TZ)
    except Exception:
        dt = pd.Timestamp.now(tz=NAIROBI_TZ)
    return dt.date(), dt


def load_or_create_capital_auto_daily_state(username: str, timeframe: str, assets: set[str], ts=None) -> dict:
    """Freeze the user's session ranking for one EAT trading day.

    The state makes auto-trading restart-safe. It does not force 10 trades; the
    cap is a maximum. If the app/scanner restarts, the same session order is
    reused for the rest of the day.
    """
    username = str(username or "").strip().lower()
    timeframe = _normalize_timeframe(timeframe)
    trading_day, dt_eat = capital_auto_trading_day_eat(ts)
    try:
        conn = db_connect()
        with conn:
            with conn.cursor() as cur:
                cur.execute(
                    """
                    CREATE TABLE IF NOT EXISTS capital_auto_daily_state (
                        id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
                        username TEXT NOT NULL,
                        trading_day DATE NOT NULL,
                        timeframe TEXT NOT NULL,
                        session_order JSONB NOT NULL,
                        daily_trade_cap INTEGER DEFAULT 10,
                        trades_taken INTEGER DEFAULT 0,
                        locked_at TIMESTAMPTZ DEFAULT NOW(),
                        completed BOOLEAN DEFAULT FALSE,
                        created_at TIMESTAMPTZ DEFAULT NOW(),
                        updated_at TIMESTAMPTZ DEFAULT NOW(),
                        UNIQUE(username, trading_day, timeframe)
                    )
                    """
                )
                cur.execute(
                    """
                    SELECT *
                    FROM capital_auto_daily_state
                    WHERE LOWER(username) = %s AND trading_day = %s AND timeframe = %s
                    LIMIT 1
                    """,
                    (username, trading_day, timeframe),
                )
                row = cur.fetchone()
                if row:
                    state = dict(row)
                    so = state.get("session_order") or []
                    if isinstance(so, str):
                        try: so = json.loads(so)
                        except Exception: so = []
                    state["session_order"] = so
                    conn.close()
                    return state
                ranking = capital_session_order_for_user(username, timeframe, assets)
                session_order = ranking.get("session_order") or []
                if not session_order:
                    session_order = [{"session": name, "profit_factor": 0, "win_rate": 0, "net_r": 0, "trade_count": 0, "sample_ready": False} for name in capital_session_windows_scanner().keys()]
                cur.execute(
                    """
                    INSERT INTO capital_auto_daily_state(username, trading_day, timeframe, session_order, daily_trade_cap, trades_taken, completed, updated_at)
                    VALUES (%s,%s,%s,%s::jsonb,%s,0,FALSE,NOW())
                    ON CONFLICT (username, trading_day, timeframe) DO UPDATE SET
                        updated_at = NOW()
                    RETURNING *
                    """,
                    (username, trading_day, timeframe, json.dumps(session_order), int(CAPITAL_AUTO_TRADE_MAX_PER_DAY)),
                )
                row = cur.fetchone() or {}
        conn.close()
        state = dict(row)
        so = state.get("session_order") or []
        if isinstance(so, str):
            try: so = json.loads(so)
            except Exception: so = []
        state["session_order"] = so
        return state
    except Exception as exc:
        print(f"[CapitalAuto] Daily state failed for {username}: {exc}")
        ranking = capital_session_order_for_user(username, timeframe, assets)
        return {"username": username, "trading_day": trading_day, "timeframe": timeframe, "session_order": ranking.get("session_order") or [], "daily_trade_cap": int(CAPITAL_AUTO_TRADE_MAX_PER_DAY), "trades_taken": 0, "fallback_state": True}


def capital_auto_session_gate_for_signal(sig: ScanResult, username: str, timeframe: str, assets: set[str]) -> dict:
    """Capital.com daily session gate.

    Important rule: EVERY ranked session has the same +1 hour delay. If the
    engine moves from the best session to the next remaining session, it still
    cannot accept signals from that next session until that session's own
    open + 1 hour. The gate is evaluated from the signal generation time
    (created_at) first, not the candle close, so the scanner never backfills
    trades from the first hour of a session just because it switched sessions
    later in the day.
    """
    signal_ts = getattr(sig, "created_at", "") or getattr(sig, "candle_close", "") or datetime.now(timezone.utc)
    try:
        dt_eat = pd.to_datetime(signal_ts, utc=True).tz_convert(NAIROBI_TZ)
    except Exception:
        return {"allowed": False, "reason": "invalid_signal_time"}

    state = load_or_create_capital_auto_daily_state(username, timeframe, assets, signal_ts)
    order = state.get("session_order") or []
    ordered_sessions = [
        str(x.get("session") or x.get("best_session") or "").strip()
        for x in order
        if str(x.get("session") or x.get("best_session") or "").strip()
    ]
    if not ordered_sessions:
        return {"allowed": False, "reason": "no_session_order", "daily_state": state}

    current_session = prop_session_from_timestamp_scanner(signal_ts)
    if current_session not in ordered_sessions:
        return {"allowed": False, "reason": f"session_not_ranked:{current_session}", "current_session": current_session, "daily_state": state}

    # Only the highest-ranked session that is currently tradable is active.
    # Higher-ranked sessions that have already ended are skipped. Higher-ranked
    # sessions that are still upcoming or still in their +1h warm-up window block
    # lower-ranked sessions.
    for sess in ordered_sessions:
        if capital_session_has_ended_scanner(dt_eat, sess):
            continue

        if sess != current_session:
            return {
                "allowed": False,
                "reason": f"waiting_for_higher_ranked_session:{sess}",
                "current_session": current_session,
                "active_session": sess,
                "daily_state": state,
            }

        if not capital_session_entry_open_scanner(dt_eat, sess):
            return {
                "allowed": False,
                "reason": f"before_session_plus_1h_entry_window:{sess}",
                "current_session": current_session,
                "active_session": sess,
                "daily_state": state,
            }

        return {"allowed": True, "reason": "", "current_session": current_session, "active_session": sess, "daily_state": state}

    return {"allowed": False, "reason": "session_order_exhausted", "current_session": current_session, "daily_state": state}


def capital_auto_trades_taken_today(username: str) -> int:
    """Count accepted Capital.com auto-orders for the current EAT day.

    This is the hard concurrency guard. It counts all selected execution grades,
    not only A/A+, because the user may choose A only, A+/A, or wider demo sets.
    """
    try:
        conn = db_connect()
        with conn.cursor() as cur:
            cur.execute(
                """
                SELECT COUNT(*) AS n
                FROM capital_auto_orders
                WHERE LOWER(COALESCE(scan_owner,'')) = %s
                  AND status IN ('OPENED','ACCEPTED','CONFIRMED','OPEN','EXECUTED')
                  AND (created_at AT TIME ZONE 'Africa/Nairobi')::date = (NOW() AT TIME ZONE 'Africa/Nairobi')::date
                """,
                (str(username or "").lower(),),
            )
            row = cur.fetchone() or {}
        conn.close()
        return int(row.get("n") or 0)
    except Exception as exc:
        print(f"[CapitalAuto] daily cap lookup failed for {username}: {exc}")
        return CAPITAL_AUTO_TRADE_MAX_PER_DAY


def update_capital_auto_daily_state_count(username: str, timeframe: str, increment: int = 1) -> None:
    try:
        trading_day, _ = capital_auto_trading_day_eat()
        execute(
            """
            UPDATE capital_auto_daily_state
            SET trades_taken = GREATEST(0, COALESCE(trades_taken,0) + %s),
                completed = CASE WHEN GREATEST(0, COALESCE(trades_taken,0) + %s) >= COALESCE(daily_trade_cap, %s) THEN TRUE ELSE completed END,
                updated_at = NOW()
            WHERE LOWER(username) = %s AND trading_day = %s AND timeframe = %s
            """,
            (int(increment), int(increment), int(CAPITAL_AUTO_TRADE_MAX_PER_DAY), str(username or "").lower(), trading_day, _normalize_timeframe(timeframe)),
        )
    except Exception as exc:
        print(f"[CapitalAuto] daily state count update failed: {exc}")

def load_auto_trade_user_settings_for_signal(sig: ScanResult) -> dict:
    """Resolve the user settings that should size this auto-trade.

    Auto-trading is stricter than simulation:
      • only the user's watchlist
      • only the user's selected timeframe
      • only the grades the user selected for demo testing
      • daily session ranking is frozen per user/timeframe in EAT
      • trades begin one hour after the active ranked session opens
      • max accepted auto-orders per Nairobi day is a hard cap, not a quota
    """
    asset = str(getattr(sig, "asset", "") or "").strip().upper()
    grade = str(getattr(sig, "grade", "") or "").strip().upper()
    timeframe = _normalize_timeframe(getattr(sig, "timeframe", "") or DEFAULT_USER_TIMEFRAME)
    owner_filter = str(CAPITAL_AUTO_TRADE_OWNER or "").strip().lower()
    fallback = {
        "username": owner_filter or SCAN_OWNER,
        "account_size": float(ACCOUNT_SIZE),
        "risk_pct": float(RISK_PER_TRADE) * 100.0,
        "leverage": float(LEVERAGE),
        "source": "scanner_fallback",
        "auto_trade_allowed": False,
        "skip_reason": "no_user_match",
    }
    try:
        conn = db_connect()
        with conn.cursor() as cur:
            if owner_filter:
                cur.execute(
                    """
                    SELECT us.username, us.settings_json,
                           COALESCE(ucc.enabled, TRUE) AS capital_connected,
                           COALESCE(ucc.auto_trade_enabled, TRUE) AS user_auto_enabled,
                           COALESCE(NULLIF(ucc.auto_trade_grades,''), 'A+,A') AS auto_trade_grades,
                           COALESCE(ucc.use_benzino_settings, TRUE) AS use_benzino_settings
                    FROM user_settings us
                    JOIN user_watchlists uw
                      ON uw.scan_owner = us.username
                     AND uw.enabled = TRUE
                     AND UPPER(uw.asset) = %s
                    LEFT JOIN user_capital_connections ucc
                      ON LOWER(ucc.username) = LOWER(us.username)
                    WHERE LOWER(us.username) = %s
                    LIMIT 1
                    """,
                    (asset, owner_filter),
                )
            else:
                cur.execute(
                    """
                    SELECT us.username, us.settings_json,
                           COALESCE(ucc.enabled, TRUE) AS capital_connected,
                           COALESCE(ucc.auto_trade_enabled, TRUE) AS user_auto_enabled,
                           COALESCE(NULLIF(ucc.auto_trade_grades,''), 'A+,A') AS auto_trade_grades,
                           COALESCE(ucc.use_benzino_settings, TRUE) AS use_benzino_settings
                    FROM user_settings us
                    JOIN user_watchlists uw
                      ON uw.scan_owner = us.username
                     AND uw.enabled = TRUE
                     AND UPPER(uw.asset) = %s
                    JOIN user_capital_connections ucc
                      ON LOWER(ucc.username) = LOWER(us.username)
                    WHERE COALESCE(ucc.enabled, FALSE) = TRUE
                      AND COALESCE(ucc.auto_trade_enabled, FALSE) = TRUE
                    ORDER BY us.updated_at DESC NULLS LAST, us.username ASC
                    """,
                    (asset,),
                )
            rows = [dict(r) for r in cur.fetchall()]
        conn.close()
    except Exception as exc:
        print(f"[CapitalAuto] Could not load user sizing settings; using fallback: {exc}")
        return fallback

    for row in rows:
        try:
            settings = json.loads(row.get("settings_json") or "{}")
            if not isinstance(settings, dict):
                settings = {}
        except Exception:
            settings = {}
        allowed_tfs = _extract_timeframes_from_settings(settings)
        if timeframe not in allowed_tfs:
            continue
        username = str(row.get("username") or fallback["username"]).strip().lower()
        if row.get("capital_connected") is False or row.get("user_auto_enabled") is False:
            return {**fallback, "username": username, "skip_reason": "user_capital_autotrading_disabled"}
        raw_grades = str(row.get("auto_trade_grades") or "A+,A")
        user_grades = {g.strip().upper() for g in raw_grades.split(",") if g.strip()}
        # Environment is only a platform safety ceiling; the user setting is the actual selector.
        allowed_user_grades = user_grades & set(CAPITAL_AUTO_TRADE_GRADES)
        if grade not in allowed_user_grades:
            return {**fallback, "username": username, "auto_trade_allowed": False, "skip_reason": f"grade_not_selected:{grade}", "selected_grades": sorted(allowed_user_grades)}
        # Watchlist used for daily session ranking and execution state.
        watch = load_user_watchlist(username)
        watch_assets = {a.upper() for a in watch.keys()} or {asset}
        signal_time_for_session = getattr(sig, "created_at", "") or getattr(sig, "candle_close", "")
        session_gate = capital_auto_session_gate_for_signal(sig, username, timeframe, watch_assets)
        session_profile = capital_best_session_profile_for_user(username, timeframe, watch_assets)
        current_session = str(session_gate.get("current_session") or prop_session_from_timestamp_scanner(signal_time_for_session))
        if not bool(session_gate.get("allowed")):
            return {**fallback, "username": username, "auto_trade_allowed": False, "skip_reason": str(session_gate.get("reason") or "session_gate_blocked"), "session_profile": session_profile, "session_gate": session_gate, "current_session": current_session}
        taken_today = capital_auto_trades_taken_today(username)
        if taken_today >= CAPITAL_AUTO_TRADE_MAX_PER_DAY:
            return {**fallback, "username": username, "auto_trade_allowed": False, "skip_reason": "daily_auto_trade_cap_reached", "session_profile": session_profile, "session_gate": session_gate}
        account_size = _safe_float_setting(settings, ["account_size", "account_balance", "starting_balance"], ACCOUNT_SIZE)
        risk_pct = _safe_float_setting(settings, ["risk_pct", "risk_per_trade_pct"], float(RISK_PER_TRADE) * 100.0)
        leverage = _safe_float_setting(settings, ["leverage"], LEVERAGE)
        return {
            "username": username,
            "account_size": max(0.0, float(account_size)),
            "risk_pct": max(0.0, float(risk_pct)),
            "leverage": max(1.0, float(leverage)),
            "source": "user_settings",
            "auto_trade_allowed": True,
            "skip_reason": "",
            "session_profile": session_profile,
            "current_session": current_session,
            "active_session": str(session_gate.get("active_session") or current_session),
            "daily_state": session_gate.get("daily_state") or {},
            "auto_trades_taken_today": taken_today,
            "selected_grades": sorted(allowed_user_grades),
        }
    return fallback

def calculate_capital_position_size(sig: ScanResult, sizing: dict) -> float:
    """Calculate Capital.com order size from the user's risk settings.

    Position size is derived from the same risk model used by the simulator:
      risk_cash = user account size × user risk %
      size      = risk_cash / absolute entry-to-stop distance

    Capital.com instruments have their own min/max increments, so optional env
    caps are applied defensively. If a broker rejects the size, the order is
    logged as rejected and the simulator remains untouched.
    """
    try:
        entry = float(sig.entry)
        sl = float(sig.sl)
        stop_distance = abs(entry - sl)
        if stop_distance <= 0:
            return 0.0
        account_size = float(sizing.get("account_size") or ACCOUNT_SIZE)
        risk_pct = float(sizing.get("risk_pct") or (RISK_PER_TRADE * 100.0))
        risk_cash = account_size * (risk_pct / 100.0)
        size = risk_cash / stop_distance
        market = capital_load_market_info(str(getattr(sig, "asset", "")))
        min_size = float(market.get("min_size") or CAPITAL_AUTO_TRADE_MIN_SIZE or 0)
        max_size = float(market.get("max_size") or CAPITAL_AUTO_TRADE_MAX_SIZE or 0)
        step_size = float(market.get("step_size") or 0)
        size = max(min_size, float(CAPITAL_AUTO_TRADE_MIN_SIZE), float(size))
        if max_size and max_size > 0:
            size = min(max_size, size)
        size = round_to_broker_step(size, step_size, direction="nearest")
        if min_size and size < min_size:
            size = round_to_broker_step(min_size, step_size, direction="up")
        return round(float(size), 6)
    except Exception:
        return 0.0


def record_capital_auto_order(sig: ScanResult, *, status: str, deal_reference: str = "", deal_id: str = "", epic: str = "", size: float = 0.0, error: str = "", raw: dict | None = None) -> None:
    sql = """
    INSERT INTO capital_auto_orders(
        signal_id, deal_reference, deal_id, scan_owner, environment, asset, timeframe,
        direction, grade, epic, size, entry, sl, tp, status, error, raw_json,
        ftmo_leverage, capital_leverage, ftmo_normalization_factor, updated_at
    ) VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,NOW())
    ON CONFLICT (signal_id) DO UPDATE SET
        deal_reference = COALESCE(NULLIF(EXCLUDED.deal_reference,''), capital_auto_orders.deal_reference),
        deal_id = COALESCE(NULLIF(EXCLUDED.deal_id,''), capital_auto_orders.deal_id),
        status = EXCLUDED.status,
        error = EXCLUDED.error,
        raw_json = EXCLUDED.raw_json,
        updated_at = NOW()
    """
    try:
        conn = db_connect()
        with conn:
            with conn.cursor() as cur:
                cur.execute(sql, (
                    sig.signal_id, deal_reference, deal_id, str(((raw or {}).get("sizing") or {}).get("username") or SCAN_OWNER), "demo" if CAPITAL_DEMO else "live",
                    sig.asset, sig.timeframe, sig.signal, sig.grade, epic, float(size or 0),
                    float(sig.entry), float(sig.sl), float(sig.tp), status, error,
                    jsonb_dumps(raw or {}),
                    float((raw or {}).get("ftmo_leverage") or FTMO_COMPARISON_LEVERAGE),
                    float((raw or {}).get("capital_leverage") or capital_effective_leverage_for_asset(sig.asset, (raw or {}).get("broker_constraints") or {})),
                    float((raw or {}).get("ftmo_normalization_factor") or ftmo_normalization_factor(sig.asset, (raw or {}).get("broker_constraints") or {})),
                ))
        conn.close()
    except Exception as exc:
        print(f"[CapitalAuto] failed to record order for {sig.asset}: {exc}")




def record_capital_auto_trade_diagnostic(
    sig: ScanResult,
    *,
    username: str = "",
    eligible: bool = False,
    order_sent: bool = False,
    status: str = "CHECKED",
    skip_reason: str = "",
    deal_reference: str = "",
    deal_id: str = "",
    prop_selected: bool | None = None,
    capital_executed: bool | None = None,
    api_response: dict | None = None,
) -> None:
    """Persist every auto-trade decision so the app can explain why orders did/didn't go to Capital.com."""
    user = str(username or SCAN_OWNER or "").strip().lower()
    if not user:
        user = "unknown"
    display_id = str(getattr(sig, "display_id", "") or "").strip()
    if not display_id:
        display_id = str(getattr(sig, "signal_id", "") or "")[:12]
    if prop_selected is None:
        prop_selected = bool(eligible)
    if capital_executed is None:
        capital_executed = bool(order_sent)
    diag_id = str(uuid.uuid5(uuid.NAMESPACE_DNS, f"CAPITAL_AUTO_DIAG::{user}::{getattr(sig, 'signal_id', '')}"))
    sql = """
        INSERT INTO capital_auto_trade_diagnostics(
            id, username, signal_id, display_id, asset, timeframe, direction, grade,
            eligible, order_sent, status, skip_reason, deal_reference, deal_id,
            prop_selected, capital_executed, api_response, checked_at, updated_at
        ) VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,NOW(),NOW())
        ON CONFLICT (id) DO UPDATE SET
            display_id = EXCLUDED.display_id,
            asset = EXCLUDED.asset,
            timeframe = EXCLUDED.timeframe,
            direction = EXCLUDED.direction,
            grade = EXCLUDED.grade,
            eligible = EXCLUDED.eligible,
            order_sent = EXCLUDED.order_sent,
            status = EXCLUDED.status,
            skip_reason = EXCLUDED.skip_reason,
            deal_reference = COALESCE(NULLIF(EXCLUDED.deal_reference,''), capital_auto_trade_diagnostics.deal_reference),
            deal_id = COALESCE(NULLIF(EXCLUDED.deal_id,''), capital_auto_trade_diagnostics.deal_id),
            prop_selected = EXCLUDED.prop_selected,
            capital_executed = EXCLUDED.capital_executed,
            api_response = EXCLUDED.api_response,
            checked_at = NOW(),
            updated_at = NOW()
    """
    try:
        conn = db_connect()
        with conn:
            with conn.cursor() as cur:
                cur.execute(sql, (
                    diag_id, user, getattr(sig, "signal_id", ""), display_id,
                    getattr(sig, "asset", ""), getattr(sig, "timeframe", ""), getattr(sig, "signal", ""), getattr(sig, "grade", ""),
                    bool(eligible), bool(order_sent), str(status or ""), str(skip_reason or ""),
                    str(deal_reference or ""), str(deal_id or ""), bool(prop_selected), bool(capital_executed),
                    jsonb_dumps(api_response or {}),
                ))
        conn.close()
    except Exception as exc:
        print(f"[CapitalAutoDiag] failed to record diagnostic for {getattr(sig, 'asset', '')}: {exc}")

def capital_confirm_deal(deal_reference: str) -> dict | None:
    deal_reference = str(deal_reference or "").strip()
    if not deal_reference:
        return None
    return capital_request("GET", f"/confirms/{deal_reference}", retries=3)



def adjust_levels_for_capital_constraints(sig: ScanResult, market_info: dict, *, error_text: str = "") -> tuple[float, float]:
    """Return broker-valid SL/TP while preserving the 1:2 direction.

    Guarantees after adjustment:
      BUY  -> SL < entry < TP
      SELL -> TP < entry < SL
    """
    entry = float(sig.entry)
    sl = float(sig.sl)
    direction = str(sig.signal or "").upper()
    text = str(error_text or "")
    nums = re.findall(r"[-+]?\d+(?:\.\d+)?", text)
    boundary = float(nums[-1]) if nums else None
    min_stop = float(market_info.get("min_stop_distance") or market_info.get("min_limit_distance") or 0)
    max_stop = float(market_info.get("max_stop_distance") or market_info.get("max_limit_distance") or 0)
    if min_stop <= 0:
        min_stop = max(abs(entry) * 0.00005, 1e-8)

    # Use broker-provided boundary when Capital tells us the exact valid level.
    if "invalid.stoploss.maxvalue" in text and boundary is not None:
        sl = min(sl, boundary)
    elif "invalid.stoploss.minvalue" in text and boundary is not None:
        sl = max(sl, boundary)

    dist = abs(entry - sl)
    if dist <= 0:
        dist = min_stop
    if min_stop and dist < min_stop:
        dist = min_stop
    if max_stop and max_stop > 0 and dist > max_stop:
        dist = max_stop

    if direction == "BUY":
        sl = min(entry - dist, entry - min_stop)
        risk = abs(entry - sl)
        tp = entry + (2.0 * risk)
        if min_stop and (tp - entry) < min_stop:
            tp = entry + min_stop
    else:
        sl = max(entry + dist, entry + min_stop)
        risk = abs(sl - entry)
        tp = entry - (2.0 * risk)
        if min_stop and (entry - tp) < min_stop:
            tp = entry - min_stop

    # Final safety guard for Capital profitLevel validation.
    if direction == "BUY" and not (sl < entry < tp):
        sl = entry - max(min_stop, abs(entry - sl) or min_stop)
        tp = entry + 2.0 * abs(entry - sl)
    if direction == "SELL" and not (tp < entry < sl):
        sl = entry + max(min_stop, abs(entry - sl) or min_stop)
        tp = entry - 2.0 * abs(sl - entry)

    # Capital rejects non-positive stop/profit levels. Low-priced instruments
    # such as NATGAS can produce an invalid TP if broker distances are larger
    # than the current price. Return zeros so the caller can skip cleanly rather
    # than sending an invalid order repeatedly.
    if entry <= 0 or sl <= 0 or tp <= 0:
        return 0.0, 0.0
    if direction == "BUY" and not (sl < entry < tp):
        return 0.0, 0.0
    if direction == "SELL" and not (tp < entry < sl):
        return 0.0, 0.0

    return float(sl), float(tp)

def build_capital_size_attempts(base_size: float, market_info: dict) -> list[float]:
    min_size = float(market_info.get("min_size") or CAPITAL_AUTO_TRADE_MIN_SIZE or 0.01)
    max_size = float(market_info.get("max_size") or CAPITAL_AUTO_TRADE_MAX_SIZE or 0)
    step = float(market_info.get("step_size") or 0)
    attempts = []
    def add(x, direction="nearest"):
        try:
            x = float(x)
            if max_size and x > max_size:
                x = max_size
            x = max(min_size, x)
            x = round_to_broker_step(x, step, direction=direction)
            if x > 0 and x not in attempts:
                attempts.append(x)
        except Exception:
            pass
    add(base_size)
    add(min_size, "up")
    for mult in (2, 5, 10):
        add(min_size * mult, "up")
    for div in (2, 5, 10, 25, 50, 100):
        add(base_size / div, "down")
    return attempts[:10]


def load_enabled_auto_trade_users_for_signal_fallback(sig) -> list[dict]:
    """Load enabled user-owned Capital accounts without tying them to SCAN_OWNER."""
    try:
        conn = db_connect()
        with conn.cursor() as cur:
            cur.execute("""
                SELECT *
                FROM user_capital_connections
                WHERE COALESCE(enabled, FALSE) = TRUE
                  AND COALESCE(auto_trade_enabled, FALSE) = TRUE
                  AND COALESCE(api_key, '') <> ''
                  AND COALESCE(identifier, '') <> ''
                  AND COALESCE(password, '') <> ''
                ORDER BY updated_at DESC NULLS LAST, created_at DESC NULLS LAST
            """)
            rows = [dict(r) for r in cur.fetchall()]
        conn.close()
        return rows
    except Exception as exc:
        print(f"[CapitalAuto] Could not load enabled auto-trade users: {exc}")
        return []

def place_capital_auto_trade(sig: ScanResult) -> bool:
    """Place a Capital.com demo trade for one newly accepted BENZINO signal.

    This is intentionally opt-in via CAPITAL_AUTO_TRADE_ENABLED. Matching becomes
    perfect because the originating BENZINO signal_id is stored in
    capital_auto_orders at order time. We do not use entry/exit drift metrics for
    these trades; the research question becomes simulated R vs actual P/L/R.
    """
    grade = str(sig.grade or "").strip().upper()
    direction = str(sig.signal or "").strip().upper()
    timeframe = str(sig.timeframe or "").strip().lower()
    if not CAPITAL_AUTO_TRADE_ENABLED:
        record_capital_auto_trade_diagnostic(sig, username=SCAN_OWNER, eligible=False, order_sent=False, status="SKIPPED", skip_reason="platform_auto_trade_disabled")
        return False
    if CAPITAL_AUTO_TRADE_REQUIRE_DEMO and not CAPITAL_DEMO:
        record_capital_auto_trade_diagnostic(sig, username=SCAN_OWNER, eligible=False, order_sent=False, status="SKIPPED", skip_reason="platform_requires_demo")
        print(f"[CapitalAuto] Refusing to auto-trade {sig.asset}: CAPITAL_DEMO is false.")
        return False
    if not ensure_capital_credentials_loaded():
        record_capital_auto_trade_diagnostic(sig, username=SCAN_OWNER, eligible=False, order_sent=False, status="SKIPPED", skip_reason="capital_credentials_missing")
        print(f"[CapitalAuto] Capital credentials missing — cannot auto-trade {sig.asset}.")
        return False
    if grade not in CAPITAL_AUTO_TRADE_GRADES or direction not in {"BUY", "SELL"} or timeframe not in CAPITAL_AUTO_TRADE_TIMEFRAMES:
        reason = "platform_grade_timeframe_or_direction_block"
        record_capital_auto_trade_diagnostic(sig, username=SCAN_OWNER, eligible=False, order_sent=False, status="SKIPPED", skip_reason=reason)
        return False
    if capital_auto_order_exists(sig.signal_id):
        record_capital_auto_trade_diagnostic(sig, username=SCAN_OWNER, eligible=False, order_sent=False, status="SKIPPED", skip_reason="duplicate_existing_capital_order")
        return False

    epic = capital_find_epic(sig.asset)
    if not epic:
        record_capital_auto_order(sig, status="FAILED", error="No Capital.com epic resolved")
        record_capital_auto_trade_diagnostic(sig, username=SCAN_OWNER, eligible=False, order_sent=False, status="FAILED", skip_reason="no_capital_epic_resolved")
        print(f"[CapitalAuto] {sig.asset}: no Capital.com epic resolved; order skipped.")
        return False

    sizing = load_auto_trade_user_settings_for_signal(sig)
    if not bool(sizing.get("auto_trade_allowed")):
        reason = str(sizing.get("skip_reason") or "auto_trade_not_allowed")
        record_capital_auto_order(sig, status="SKIPPED", epic=epic, size=0, error=reason, raw={"sizing": sizing})
        record_capital_auto_trade_diagnostic(sig, username=str(sizing.get("username") or SCAN_OWNER), eligible=False, order_sent=False, status="SKIPPED", skip_reason=reason, prop_selected=False, capital_executed=False, api_response={"sizing": sizing})
        print(f"[CapitalAuto] {sig.asset} {timeframe} {direction} {grade}: skipped · {reason}.")
        return False
    trade_size = calculate_capital_position_size(sig, sizing)
    if trade_size <= 0:
        record_capital_auto_order(sig, status="FAILED", epic=epic, size=0, error="Dynamic size calculation returned 0", raw={"sizing": sizing})
        record_capital_auto_trade_diagnostic(sig, username=str(sizing.get("username") or SCAN_OWNER), eligible=False, order_sent=False, status="FAILED", skip_reason="dynamic_size_calculation_returned_0", prop_selected=False, capital_executed=False, api_response={"sizing": sizing})
        print(f"[CapitalAuto] {sig.asset} {timeframe}: size calculation failed; order skipped.")
        return False

    market_info = capital_load_market_info(sig.asset)
    size_attempts = build_capital_size_attempts(float(trade_size), market_info) if CAPITAL_AUTO_TRADE_SIZE_RETRY else [float(trade_size)]
    available_margin = capital_available_margin()
    if available_margin is not None:
        # Use Capital's effective leverage for the real margin check. FTMO stays 1:100 for simulation.
        lev = capital_effective_leverage_for_asset(sig.asset, market_info)
        capped = []
        for x in size_attempts:
            if estimate_margin_required(sig, x, lev) <= available_margin * CAPITAL_MARGIN_BUFFER_PCT:
                capped.append(x)
        if capped:
            size_attempts = capped
        else:
            record_capital_auto_order(sig, status="REJECTED", epic=epic, size=trade_size, error="Insufficient margin before order", raw={"available_margin": available_margin, "sizing": sizing})
            print(f"[CapitalAuto] {sig.asset} {timeframe} {direction} {grade}: skipped · insufficient available margin.")
            return False

    response = None
    confirm = None
    deal_reference = ""
    deal_id = ""
    confirmed_size = float(trade_size)
    last_payload = {}
    last_error = "POST /positions failed"
    adj_sl, adj_tp = adjust_levels_for_capital_constraints(sig, market_info)
    if CAPITAL_AUTO_TRADE_USE_STOPS and (adj_sl <= 0 or adj_tp <= 0):
        record_capital_auto_order(sig, status="SKIPPED", epic=epic, size=trade_size, error="Broker stop/TP constraints make a valid positive SL/TP impossible", raw={"sizing": sizing, "broker_constraints": market_info})
        record_capital_auto_trade_diagnostic(sig, username=str(sizing.get("username") or SCAN_OWNER), eligible=False, order_sent=False, status="SKIPPED", skip_reason="invalid_broker_sl_tp_constraints", prop_selected=False, capital_executed=False, api_response={"sizing": sizing, "broker_constraints": market_info})
        print(f"[CapitalAuto] {sig.asset} {timeframe} {direction} {grade}: skipped · invalid broker SL/TP constraints.")
        return False

    for attempt_size in size_attempts:
        payload = {
            "epic": epic,
            "direction": direction,
            "size": float(attempt_size),
            "guaranteedStop": False,
        }
        if CAPITAL_AUTO_TRADE_USE_STOPS:
            payload["stopLevel"] = float(adj_sl)
            payload["profitLevel"] = float(adj_tp)
        last_payload = payload

        _CAPITAL_LAST_ERROR["text"] = ""
        response = capital_request("POST", "/positions", json_body=payload, retries=1)
        if not isinstance(response, dict) and ("invalid.stoploss" in str(_CAPITAL_LAST_ERROR.get("text", "")) or "profitlevel" in str(_CAPITAL_LAST_ERROR.get("text", "")).lower()):
            adj_sl, adj_tp = adjust_levels_for_capital_constraints(sig, market_info, error_text=_CAPITAL_LAST_ERROR.get("text", ""))
            if CAPITAL_AUTO_TRADE_USE_STOPS and (adj_sl <= 0 or adj_tp <= 0):
                last_error = "Broker stop/TP constraints make a valid positive SL/TP impossible"
                break
            if CAPITAL_AUTO_TRADE_USE_STOPS:
                payload["stopLevel"] = float(adj_sl)
                payload["profitLevel"] = float(adj_tp)
            last_payload = payload
            response = capital_request("POST", "/positions", json_body=payload, retries=1)
        if not isinstance(response, dict):
            last_error = "POST /positions failed"
            continue

        deal_reference = str(response.get("dealReference") or response.get("reference") or "")
        confirm = capital_confirm_deal(deal_reference) if deal_reference else None
        confirm_status_try = str(_first_value(confirm or {}, ["dealStatus", "status"], "") or "").upper()
        reject_reason = str(_first_value(confirm or {}, ["reason", "rejectReason", "errorCode", "errorMessage", "message"], "") or "")
        deal_id_try = str(_first_value(confirm or {}, ["dealId", "dealID"], "") or "")
        if bool(deal_reference) and (not confirm_status_try or confirm_status_try in {"ACCEPTED", "OPEN", "SUCCESS", "CONFIRMED"}):
            deal_id = deal_id_try
            confirmed_size = float(attempt_size)
            break
        last_error = f"Capital confirmation status: {confirm_status_try or 'unknown'}" + (f" · {reject_reason}" if reject_reason else "")
        # If a broker-side size/limit rejection happens, retry smaller. For other
        # rejections, keep trying smaller once because Capital often omits the reason.
        if not CAPITAL_AUTO_TRADE_SIZE_RETRY:
            break
    else:
        response = response if isinstance(response, dict) else None

    confirm_status = str(_first_value(confirm or {}, ["dealStatus", "status"], "") or "").upper()
    ok = bool(deal_reference) and (not confirm_status or confirm_status in {"ACCEPTED", "OPEN", "SUCCESS", "CONFIRMED"})
    status = "OPENED" if ok else "REJECTED"
    error = "" if ok else last_error
    _auto_raw = {"payload": last_payload, "original_size": trade_size, "adjusted_sl": adj_sl, "adjusted_tp": adj_tp, "broker_constraints": market_info, "sizing": sizing, "response": response or {}, "confirm": confirm or {}, "ftmo_leverage": FTMO_COMPARISON_LEVERAGE, "capital_leverage": capital_effective_leverage_for_asset(sig.asset, market_info), "ftmo_normalization_factor": ftmo_normalization_factor(sig.asset, market_info)}
    record_capital_auto_order(sig, status=status, deal_reference=deal_reference, deal_id=deal_id, epic=epic, size=confirmed_size, error=error, raw=_auto_raw)
    record_capital_auto_trade_diagnostic(sig, username=str(sizing.get("username") or SCAN_OWNER), eligible=ok, order_sent=ok, status="EXECUTED" if ok else "REJECTED", skip_reason=error, deal_reference=deal_reference, deal_id=deal_id, prop_selected=ok, capital_executed=ok, api_response=_auto_raw)
    user_label = str(sizing.get("username") or SCAN_OWNER)
    if ok:
        update_capital_auto_daily_state_count(str(sizing.get("username") or SCAN_OWNER), timeframe, 1)
        print(f"[CapitalAuto] {sig.asset} {timeframe} {direction} {grade}: demo trade opened for {user_label} · size {confirmed_size} · ref {deal_reference}.")
    else:
        print(f"[CapitalAuto] {sig.asset} {timeframe} {direction} {grade}: order not accepted · {error}.")
    return ok


def rebuild_capital_execution_audit(limit: int = 500) -> int:
    """Build the Capital.com Execution Audit from BENZINO-created broker orders.

    This is no longer a simulated-vs-actual matching engine. Because Capital.com is
    the pricing source, the audit starts from capital_auto_orders (orders BENZINO
    actually sent), links the imported Capital.com execution row by deal id/reference,
    and records execution quality: planned levels, broker fills, slippage, broker
    P/L, and replay/broker outcome.
    """
    try:
        conn = db_connect()
        with conn:
            with conn.cursor() as cur:
                cur.execute(
                    """
                    SELECT
                        ao.*,
                        ss.exit_price AS replay_exit,
                        ss.r_multiple AS replay_r,
                        ss.status AS replay_status,
                        ss.exit_reason AS replay_exit_reason
                    FROM capital_auto_orders ao
                    LEFT JOIN scanner_signals ss ON ss.signal_id = ao.signal_id
                    WHERE ao.status IN ('OPENED','CLOSED','ACCEPTED')
                    ORDER BY ao.created_at DESC
                    LIMIT %s
                    """,
                    (int(limit),),
                )
                rows = [dict(r) for r in cur.fetchall()]
                upserted = 0
                for row in rows:
                    actual = None
                    if row.get("deal_id") or row.get("deal_reference"):
                        cur.execute(
                            """
                            SELECT *
                            FROM capital_executed_trades
                            WHERE (deal_id = %s AND %s <> '')
                               OR (deal_reference = %s AND %s <> '')
                            ORDER BY updated_at DESC
                            LIMIT 1
                            """,
                            (
                                row.get("deal_id") or "", row.get("deal_id") or "",
                                row.get("deal_reference") or "", row.get("deal_reference") or "",
                            ),
                        )
                        actual = cur.fetchone()
                    actual = dict(actual) if actual else {}

                    order_raw = _json_dict(row.get("raw_json"))
                    actual_raw = _json_dict(actual.get("raw_json")) if actual else {}

                    # Signal plan stays as the reference price. Broker levels come
                    # from Capital.com open-position/confirm data where available.
                    planned_entry = _parse_float_or_none(row.get("entry"))
                    executed_entry = (
                        _parse_float_or_none(actual.get("entry_price"))
                        or _capital_level_from_raw(actual_raw, "entry")
                        or _capital_level_from_raw(order_raw, "entry")
                    )
                    planned_exit = _parse_float_or_none(row.get("replay_exit"))
                    actual_exit = (
                        _parse_float_or_none(actual.get("exit_price"))
                        or _capital_level_from_raw(actual_raw, "exit")
                    )
                    broker_sl = (
                        _capital_level_from_raw(actual_raw, "stop")
                        or _capital_level_from_raw(order_raw, "stop")
                        or _parse_float_or_none(row.get("sl"))
                    )
                    broker_tp = (
                        _capital_level_from_raw(actual_raw, "limit")
                        or _capital_level_from_raw(order_raw, "limit")
                        or _parse_float_or_none(row.get("tp"))
                    )
                    entry_slippage = (executed_entry - planned_entry) if executed_entry is not None and planned_entry is not None else None
                    exit_slippage = (actual_exit - planned_exit) if actual_exit is not None and planned_exit is not None else None

                    actual_r = None
                    try:
                        sl = float(row.get("sl") or 0)
                        if actual_exit is not None and planned_entry is not None and abs(planned_entry - sl) > 0:
                            actual_r = r_multiple_for_exit(str(row.get("direction")), planned_entry, sl, actual_exit, "ACTUAL")
                    except Exception:
                        actual_r = None

                    audit_id = deterministic_uuid_text(f"EXEC_AUDIT::{row.get('signal_id')}")
                    cur.execute(
                        """
                        INSERT INTO capital_execution_audit(
                            id, capital_trade_id, signal_id, scan_owner, asset, timeframe,
                            direction, grade, auto_trade,
                            planned_entry, executed_entry, entry_slippage,
                            planned_sl, planned_tp, planned_exit, actual_exit, exit_slippage,
                            planned_r, actual_r, broker_pnl, broker_pnl_ftmo_equiv,
                            ftmo_leverage, capital_leverage, ftmo_normalization_factor,
                            replay_outcome, broker_status, size, currency, environment, epic,
                            deal_reference, deal_id, opened_at, closed_at, updated_at
                        ) VALUES (%s,%s,%s,%s,%s,%s,%s,%s,TRUE,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,NOW())
                        ON CONFLICT (id) DO UPDATE SET
                            capital_trade_id = EXCLUDED.capital_trade_id,
                            executed_entry = EXCLUDED.executed_entry,
                            entry_slippage = EXCLUDED.entry_slippage,
                            planned_sl = EXCLUDED.planned_sl,
                            planned_tp = EXCLUDED.planned_tp,
                            planned_exit = EXCLUDED.planned_exit,
                            actual_exit = EXCLUDED.actual_exit,
                            exit_slippage = EXCLUDED.exit_slippage,
                            planned_r = EXCLUDED.planned_r,
                            actual_r = EXCLUDED.actual_r,
                            broker_pnl = EXCLUDED.broker_pnl,
                            broker_pnl_ftmo_equiv = EXCLUDED.broker_pnl_ftmo_equiv,
                            replay_outcome = EXCLUDED.replay_outcome,
                            broker_status = EXCLUDED.broker_status,
                            size = EXCLUDED.size,
                            currency = EXCLUDED.currency,
                            environment = EXCLUDED.environment,
                            deal_reference = EXCLUDED.deal_reference,
                            deal_id = EXCLUDED.deal_id,
                            opened_at = EXCLUDED.opened_at,
                            closed_at = EXCLUDED.closed_at,
                            updated_at = NOW()
                        """,
                        (
                            audit_id, actual.get("id"), row.get("signal_id"), row.get("scan_owner"), row.get("asset"), row.get("timeframe"),
                            row.get("direction"), row.get("grade"),
                            planned_entry, executed_entry, entry_slippage,
                            broker_sl, broker_tp, planned_exit, actual_exit, exit_slippage,
                            _parse_float_or_none(row.get("replay_r")), actual_r,
                            _parse_float_or_none(actual.get("pnl")), _parse_float_or_none(actual.get("pnl_ftmo_equiv")),
                            _parse_float_or_none(row.get("ftmo_leverage")), _parse_float_or_none(row.get("capital_leverage")), _parse_float_or_none(row.get("ftmo_normalization_factor")),
                            row.get("replay_status") or row.get("replay_exit_reason"), actual.get("status") or row.get("status"),
                            _parse_float_or_none(actual.get("size")) or _parse_float_or_none(row.get("size")), actual.get("currency"), actual.get("environment") or row.get("environment"), row.get("epic"),
                            row.get("deal_reference"), row.get("deal_id"), actual.get("opened_at") or row.get("created_at"), actual.get("closed_at"),
                        ),
                    )
                    upserted += 1
        conn.close()
        if upserted:
            print(f"[ExecutionAudit] Updated {upserted} Capital.com execution audit row(s).")
        return upserted
    except Exception as exc:
        print(f"[ExecutionAudit] Audit rebuild failed: {exc}")
        return 0


def rebuild_capital_auto_comparisons(limit: int = 500) -> int:
    """Backward-compatible wrapper. New code writes capital_execution_audit only."""
    return rebuild_capital_execution_audit(limit=limit)


def sync_capital_actual_executions() -> int:
    """Read Capital.com open positions/history into Supabase for the Execution Audit."""
    if not CAPITAL_SYNC_EXECUTIONS:
        return 0
    if not ensure_capital_credentials_loaded():
        print("[CapitalSync] No enabled user Capital connection found — skipping actual execution sync.")
        return 0
    rows: list[dict] = []
    for pos in capital_fetch_open_positions():
        normalised = normalise_capital_position(pos)
        if normalised:
            rows.append(normalised)
    for activity in capital_fetch_activity_history():
        normalised = normalise_capital_activity(activity)
        if normalised:
            rows.append(normalised)
    saved = upsert_capital_executed_trades(rows)
    audited = rebuild_capital_execution_audit()
    print(f"[CapitalSync] Saved {saved} actual execution row(s); execution audit rows updated: {audited}.")
    return saved


# ═══════════════════════════════════════════════════════════════════════════════
#  MAIN SCAN LOOP
# ═══════════════════════════════════════════════════════════════════════════════


def refresh_missing_capital_constraints(limit: int = 40) -> None:
    """One-time-style repair for capital_epic_map rows with 0/null constraints.

    It only touches rows whose broker constraint columns are still empty. Once
    they have real values, future scanner runs skip this automatically.
    """
    if not capital_configured():
        return
    try:
        conn = db_connect()
        with conn.cursor() as cur:
            cur.execute(
                """
                SELECT asset, epic
                FROM capital_epic_map
                WHERE (
                        COALESCE(min_size,0) = 0
                     OR COALESCE(step_size,0) = 0
                     OR COALESCE(min_stop_distance,0) = 0
                )
                  AND (
                        last_refreshed_at IS NULL
                     OR last_refreshed_at <= NOW() - (%s::int * INTERVAL '1 hour')
                  )
                ORDER BY asset
                LIMIT %s
                """,
                (int(CAPITAL_CONSTRAINT_REFRESH_HOURS), int(limit),),
            )
            rows = [dict(r) for r in cur.fetchall()]
        conn.close()
    except Exception as exc:
        print(f"[CapitalConstraints] refresh lookup skipped: {exc}")
        return

    if not rows:
        return
    refreshed = 0
    still_empty = 0
    for row in rows:
        asset = str(row.get("asset") or "").upper().strip()
        epic = str(row.get("epic") or "").strip()
        info = capital_refresh_market_constraints(asset, epic)
        if any(float(info.get(k) or 0) > 0 for k in ("min_size", "step_size", "min_stop_distance")):
            refreshed += 1
        else:
            still_empty += 1
    print(f"[CapitalConstraints] Refreshed {refreshed}/{len(rows)} missing broker constraint row(s). Still empty: {still_empty}.")


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
    _MINUTE_REPLAY_CACHE.clear()
    _CAPITAL_PRICE_CACHE.clear()
    _RUNTIME_BREAKDOWN.clear()
    _t = _runtime_start()
    init_tables()
    _runtime_stop("db_init", _t)
    _t = _runtime_start()
    refresh_missing_capital_constraints(limit=40)
    validate_capital_epic_map_for_assets(set(scan_assets.keys()))
    _runtime_stop("capital_constraints", _t)
    if LOCK_HISTORICAL_SIGNAL_PLANS:
        print("[Replay1mBackfill] Historical signal plans locked: entry/sl/tp are preserved; only outcomes are updated.")
    _t = _runtime_start()
    force_open_graded_setups()
    _runtime_stop("force_open_fix", _t)

    # 1. Resolve outcomes for everything already open BEFORE scanning for new setups.
    # Important: outcome evaluation must NOT be limited to active_tfs. A 4h/1d
    # trade can hit TP/SL while the scheduled run is only generating 15m signals.
    # Therefore every run checks every open timeframe using Capital.com replay.
    all_replay_tfs = set(TIMEFRAME_CONFIGS.keys())
    evaluate_open_trades(assets=set(scan_assets.keys()), timeframes=all_replay_tfs)
    _t = _runtime_start()
    evaluate_shadow_trades(assets=set(scan_assets.keys()), timeframes=all_replay_tfs)
    _runtime_stop("shadow_replay", _t)
    if REPLAY_EXISTING_OUTCOMES:
        _t = _runtime_start()
        replay_existing_resolved_outcomes()
        _runtime_stop("historical_resolved_replay", _t)
    _t = _runtime_start()
    sync_capital_actual_executions()
    _runtime_stop("execution_audit_sync", _t)

    journaled, alerted, shadowed = 0, 0, 0
    assets_scanned = 0
    asset_seconds: list[float] = []

    _scan_loop_start = _runtime_start()
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
                place_capital_auto_trade(result)

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

    _runtime_stop("signal_generation_loop", _scan_loop_start)
    _t = _runtime_start()
    force_open_graded_setups()
    _runtime_stop("force_open_fix", _t)
    finished = datetime.now(timezone.utc)
    elapsed = (finished - started).total_seconds()
    print(f"\n{'='*70}")
    print(f"  Scan complete in {elapsed:.1f}s")
    open_count = len(fetch_open_trades(assets=set(scan_assets.keys()), timeframes=set(active_tfs)))
    print(f"  Journaled (A+/A/B/C): {journaled} | Open trades: {open_count} | Alerted: {alerted} | Shadowed (NO TRADE): {shadowed}")
    print(f"  Runtime: fastest asset {min(asset_seconds) if asset_seconds else 0:.1f}s | slowest {max(asset_seconds) if asset_seconds else 0:.1f}s | avg {float(np.mean(asset_seconds)) if asset_seconds else 0:.1f}s")
    if _RUNTIME_BREAKDOWN:
        ordered_runtime = sorted(_RUNTIME_BREAKDOWN.items(), key=lambda kv: kv[1], reverse=True)
        print("  Runtime breakdown:")
        for name, seconds in ordered_runtime:
            if name == "capital_api_calls":
                continue
            print(f"    - {name}: {seconds:.1f}s")
        if "capital_api_calls" in _RUNTIME_BREAKDOWN:
            print(f"    - capital_api_calls: {int(_RUNTIME_BREAKDOWN.get('capital_api_calls', 0))}")
    if ENABLE_LEGACY_GLOBAL_PROP_LEDGER:
        state = load_prop_firm_state()
        print(f"  Legacy global prop ledger: equity ${float(state['current_equity']):,.2f} "
              f"({(float(state['current_equity'])/float(state['starting_balance'])-1)*100:+.2f}%) "
              f"| status {state['status']} | trading days {state['trading_days']}")
    else:
        print("  User prop analytics: handled per logged-in user in app.py; legacy global prop ledger disabled.")
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