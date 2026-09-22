"""
NFL Money Bombs — main.py
Sportsbook lines: The Odds API
Historical stats:  nfl_data_py (nfl-verse GitHub data — no rate limits)
Schedule:          ESPN scoreboard API
"""

import os, re, asyncio, uuid, time, json, pathlib, csv, io, math, gc, copy
import threading as _bt_th
from concurrent.futures import ThreadPoolExecutor
from functools import partial
from typing import Dict, List, Optional
from datetime import datetime, timedelta, timezone
from zoneinfo import ZoneInfo

import httpx
from fastapi import FastAPI, Request, HTTPException
from fastapi.responses import HTMLResponse, JSONResponse, FileResponse
from starlette.background import BackgroundTask
from jose import jwt as jose_jwt

# ── Config ─────────────────────────────────────────────────────────────────────
ODDS_API_KEY  = os.environ.get("ODDS_API_KEY", "")
ODDS_BASE     = "https://api.the-odds-api.com/v4"
JWT_SECRET    = os.environ.get("JWT_SECRET", "")
# Use five completed seasons of nfl-verse player-stat history. The current file
# is optional before Week 1; completed seasons provide the baseline until the
# new season has real games. Recent-form calculations still explicitly use L10.
_now_utc      = datetime.now(timezone.utc)
_cur_season   = _now_utc.year if _now_utc.month >= 9 else _now_utc.year - 1
NFL_SEASONS   = list(range(_cur_season - 5, _cur_season + 1))

PROP_MARKETS = [
    # passing
    "player_pass_yds", "player_pass_tds", "player_pass_completions",
    "player_pass_attempts", "player_pass_interceptions",
    # rushing
    "player_rush_yds", "player_rush_reception_yds",
    "player_rush_attempts", "player_anytime_td",
    # receiving
    "player_reception_yds", "player_receptions",
    # defense
    "player_tackles_assists", "player_sacks", "player_defensive_interceptions",
    # kicking
    "player_kicking_points", "player_field_goals",
]
ALT_PROP_MARKET_TO_BASE = {
    "player_pass_yds_alternate": "player_pass_yds",
    "player_pass_tds_alternate": "player_pass_tds",
    "player_pass_completions_alternate": "player_pass_completions",
    "player_pass_attempts_alternate": "player_pass_attempts",
    "player_pass_interceptions_alternate": "player_pass_interceptions",
    "player_rush_yds_alternate": "player_rush_yds",
    "player_rush_attempts_alternate": "player_rush_attempts",
    "player_reception_yds_alternate": "player_reception_yds",
    "player_receptions_alternate": "player_receptions",
    "player_sacks_alternate": "player_sacks",
    "player_kicking_points_alternate": "player_kicking_points",
    "player_field_goals_alternate": "player_field_goals",
}
ALT_PROP_MARKETS = list(ALT_PROP_MARKET_TO_BASE)
PROP_LABELS = {
    "player_pass_yds":"Pass Yds", "player_pass_tds":"Pass TDs",
    "player_pass_completions":"Completions", "player_pass_attempts":"Pass Att",
    "player_pass_interceptions":"INT Thrown",
    "player_rush_yds":"Rush Yds", "player_rush_attempts":"Rush Att",
    "player_rush_reception_yds":"RB Total Yds",
    "player_anytime_td":"Anytime TD",
    "player_reception_yds":"Rec Yds", "player_receptions":"Receptions",
    "player_tackles_assists":"Tackles+Ast", "player_sacks":"Sacks",
    "player_defensive_interceptions":"Def INT",
    "player_kicking_points":"Kick Pts", "player_field_goals":"FG Made",
}
# nfl-verse column names (offense from player_stats, defense from player_stats_def,
# kicking from player_stats_kicking; def/kicking columns are merged in at load time)
PROP_TO_COL = {
    "player_pass_yds":               "passing_yards",
    "player_pass_tds":               "passing_tds",
    "player_pass_completions":       "completions",
    "player_pass_attempts":          "attempts",
    "player_pass_interceptions":     "interceptions",
    "player_rush_yds":               "rushing_yards",
    "player_rush_reception_yds":     "rush_rec_yards",
    "player_rush_attempts":          "carries",
    "player_anytime_td":             "anytime_td",       # computed
    "player_reception_yds":          "receiving_yards",
    "player_receptions":             "receptions",
    "player_tackles_assists":        "tackles_assists",  # def CSV: def_tackles
    "player_sacks":                  "def_sacks",        # def CSV
    "player_defensive_interceptions":"def_ints",         # def CSV: def_interceptions
    "player_kicking_points":         "kicking_points",   # kicking CSV: computed
    "player_field_goals":            "fg_made",          # kicking CSV
}

# Full team name ↔ abbreviation
_TEAM_NAME_TO_ABBR = {
    "arizona cardinals":"ARI","atlanta falcons":"ATL","baltimore ravens":"BAL",
    "buffalo bills":"BUF","carolina panthers":"CAR","chicago bears":"CHI",
    "cincinnati bengals":"CIN","cleveland browns":"CLE","dallas cowboys":"DAL",
    "denver broncos":"DEN","detroit lions":"DET","green bay packers":"GB",
    "houston texans":"HOU","indianapolis colts":"IND","jacksonville jaguars":"JAX",
    "kansas city chiefs":"KC","los angeles chargers":"LAC","los angeles rams":"LAR",
    "las vegas raiders":"LV","miami dolphins":"MIA","minnesota vikings":"MIN",
    "new england patriots":"NE","new orleans saints":"NO","new york giants":"NYG",
    "new york jets":"NYJ","philadelphia eagles":"PHI","pittsburgh steelers":"PIT",
    "seattle seahawks":"SEA","san francisco 49ers":"SF","tampa bay buccaneers":"TB",
    "tennessee titans":"TEN","washington commanders":"WSH","washington football team":"WSH",
    "raiders":"LV","rams":"LAR","chargers":"LAC","49ers":"SF",
}

def _name_to_abbr(full_name: str) -> str:
    return _TEAM_NAME_TO_ABBR.get(full_name.lower().strip(), "")

def _norm(s): return re.sub(r"[^a-z0-9]", "", s.lower())

def _team_nick(s: str) -> str:
    """Canonical team nickname — the unique mascot word that identifies the
    franchise. Shared-city clubs (New York Jets/Giants, Los Angeles
    Rams/Chargers) must NEVER match on the city word; only the nickname is
    decisive. 'Football Team' (old WSH) maps to 'team' — unique in the league."""
    w = (s or "").lower().replace(".", "").split()
    if not w:
        return ""
    return w[-1]

def _match(t1, t2):
    """Shared team-name matcher — nickname-based, never substring/last-word
    overlap on city words (Jets/Giants, Rams/Chargers collide on 'new york' /
    'los angeles')."""
    a, b = (t1 or "").lower().strip(), (t2 or "").lower().strip()
    if not a or not b:
        return False
    if a == b:
        return True
    na, nb = _team_nick(a), _team_nick(b)
    return bool(na) and na == nb

# ── Best-of-books odds selection ───────────────────────────────────────────────
_PRIORITY_BOOKS = ("draftkings", "fanduel", "betmgm", "williamhill_us", "caesars",
                   "betrivers", "ballybet", "bet365", "espnbet",
                   "bet99", "thescore", "fliff", "mybookieag", "betonlineag", "bovada")
_BOOK_PRIORITY = {b: i for i, b in enumerate(_PRIORITY_BOOKS)}
# Keep every prop market, but do not pull the same lines from every regional
# bookmaker. These books cover the user's main US/Canadian options while
# reducing the response size and Odds API point usage substantially.
ODDS_BOOKMAKERS = "draftkings,fanduel,betmgm,caesars,bet365,bet99,thescore"
_NFL_PROP_FETCH_CONCURRENCY = 6
_NFL_PROP_GAME_TIMEOUT = 28
# Independent per-game deadlines are not enough when later games are still
# waiting for the concurrency semaphore. Cap the complete slate fetch as well
# so the job always advances to analysis instead of appearing frozen at N/13.
_NFL_PROP_STAGE_TIMEOUT = 90
# Game Predictor lines are auxiliary to the stats forecast.  Keep each
# sportsbook request independent so one slow provider response cannot hold the
# whole predictor (or the status endpoint) open indefinitely.
_NFL_GP_GAME_LINE_TIMEOUT = 15
# Alternate ladders are still one Odds API request per game, but fetching them
# serially can exceed the two-minute UI deadline on a full slate. Match the
# standard prop fetcher's conservative concurrency without increasing call count.
_NFL_ALT_FETCH_CONCURRENCY = 3
_NFL_ALT_GAME_TIMEOUT = 24
_NFL_ALT_FETCH_STAGE_TIMEOUT = 90
_NFL_ALT_LOAD_STAGE_TIMEOUT = 180
_NFL_ALT_ANALYSIS_STAGE_TIMEOUT = 180
_NFL_ALT_OVERALL_TIMEOUT = 300
_NFL_ALT_MIN_ODDS = -1000

def _nfl_alt_fetch_deadline(game_count):
    """Allow every game a bounded number of semaphore waves, not a fixed
    deadline that expires halfway through a full Sunday slate."""
    waves = max(1, math.ceil(max(0, int(game_count)) /
                             max(1, _NFL_ALT_FETCH_CONCURRENCY)))
    setup_margin = 15
    return min(_NFL_ALT_OVERALL_TIMEOUT,
               max(_NFL_ALT_FETCH_STAGE_TIMEOUT,
                   setup_margin + waves * _NFL_ALT_GAME_TIMEOUT + 5))
_BOOK_LABEL = {"bet99":"Bet99","thescore":"theScore","bet365":"Bet365","draftkings":"DK",
               "fanduel":"FanDuel","betmgm":"BetMGM","caesars":"Caesars",
               "williamhill_us":"Caesars","betrivers":"BetRivers","ballybet":"Bally Bet",
               "espnbet":"ESPN BET","fliff":"Fliff","mybookieag":"MyBookie",
               "betonlineag":"BetOnline","bovada":"Bovada"}

async def _collect_prop_fetch_tasks(tasks, espn_games, date_str, progress=None):
    """Collect game prop tasks without letting one request stall the slate."""
    def report(message):
        if progress:
            progress(message)

    fetched_games = [None] * len(tasks)
    completed = 0
    pending = set(tasks)
    stage_deadline = (
        asyncio.get_running_loop().time() + _NFL_PROP_STAGE_TIMEOUT)
    while pending:
        remaining = stage_deadline - asyncio.get_running_loop().time()
        if remaining <= 0:
            break
        done, pending = await asyncio.wait(
            pending,
            timeout=remaining,
            return_when=asyncio.FIRST_COMPLETED,
        )
        if not done:
            break
        for task in done:
            try:
                gi, ev, lines = task.result()
            except Exception as exc:
                print(f"[OddsAPI props] game task failed: {exc}")
                continue
            fetched_games[gi] = (ev, lines)
            completed += 1
            report(f"Prop lines complete — {completed}/{len(espn_games)}: "
                   f"{ev.get('game','')} ({len(lines)} lines)")

    if pending:
        print(f"[OddsAPI props] slate hard deadline after "
              f"{_NFL_PROP_STAGE_TIMEOUT}s; cancelling {len(pending)} "
              f"unfinished game request(s)")
        for task in pending:
            task.cancel()
        await asyncio.gather(*pending, return_exceptions=True)

    # Fill every unfinished/failed slot explicitly. Downstream analysis can
    # finish with the complete schedule and a visible skipped-game warning
    # instead of hanging or crashing while unpacking a missing result.
    for gi, item in enumerate(fetched_games):
        if item is not None:
            continue
        ev = espn_games[gi]
        _NFL_PROP_FETCH_STATUS[
            (str(ev.get("id", "")), str(date_str), False)] = "timeout"
        fetched_games[gi] = (ev, [])
        completed += 1
        report(f"Prop lines skipped — {completed}/{len(espn_games)}: "
               f"{ev.get('game','')} (provider deadline)")

    return fetched_games

def _prop_fetch_skipped_matchups(fetched_games, date_str):
    skipped = []
    for ev, _ in fetched_games:
        fetch_status = _NFL_PROP_FETCH_STATUS.get(
            (str(ev.get("id", "")), str(date_str), False))
        if fetch_status != "success":
            skipped.append(
                ev.get("game")
                or f"{ev.get('away_abbr', '')} at {ev.get('home_abbr', '')}".strip()
                or "Unknown matchup")
    return skipped

def _book_label(k):
    return _BOOK_LABEL.get(k, (k or "").replace("_", " ").title())

def _take_odds(entry, price_field, book_field, price, book_key):
    """All books: keep the best American price; tie-break by book priority."""
    if price is None:
        return
    cur = entry.get(price_field)
    cur_book = entry.get(book_field)
    if cur is None or price > cur or (price == cur and _BOOK_PRIORITY.get(book_key, 999) < _BOOK_PRIORITY.get(cur_book, 999)):
        entry[price_field] = price
        entry[book_field] = book_key

app  = FastAPI(title="NFL Money Bombs", docs_url=None, redoc_url=None)
JOBS: Dict[str, Dict] = {}
SEASON_JOBS: Dict[str, Dict] = {}
# Daily analysis uses a process-wide serial lock. Keep weekly work serial too:
# running two slates at once only makes the second slate spend its deadline
# waiting for the first one, especially on the large Sunday board.
_NFL_WEEK_DAY_TIMEOUT = 720
_NFL_WEEK_JOB_TIMEOUT = 3600
# A selected Sunday can contain 700+ standard/TD candidates. It uses the same
# memory-safe serial analyzer as weekly mode, so give it the same full two-window
# allowance instead of cancelling a healthy run at the old five-minute mark.
_NFL_SINGLE_DAY_TIMEOUT = _NFL_WEEK_DAY_TIMEOUT * 2

def _nfl_prune_completed_jobs(max_age_seconds: int = 86400) -> None:
    """Release completed board payloads after the browser has had time to poll."""
    now = time.time()
    for stale_id, stale_job in list(JOBS.items()):
        if stale_job.get("status") == "running":
            continue
        finished = stale_job.get("finished_at")
        # Jobs created before timestamps were added are necessarily from an
        # older request and can be released before starting new analysis.
        if (finished is None
                or now - float(finished) >= max_age_seconds):
            response_path = stale_job.get("response_path")
            if response_path:
                pathlib.Path(response_path).unlink(missing_ok=True)
            JOBS.pop(stale_id, None)

# ── File cache ─────────────────────────────────────────────────────────────────
_CACHE_DIR = pathlib.Path("/tmp/mpa_cache")
_CACHE_DIR.mkdir(parents=True, exist_ok=True)
_CACHE_TTL = 15 * 60
_NFL_LINE_MOVEMENT_APP = "nfl_line_movement"
_NFL_LINE_OPEN_CATEGORY = "__wednesday_open__"

def _nfl_today_date():
    """NFL calendar day in the league's Eastern reporting timezone."""
    return datetime.now(ZoneInfo("America/New_York")).date()

def _nfl_today() -> str:
    return _nfl_today_date().isoformat()

def _is_past_date(date_key) -> bool:
    """Past dates are FINAL — historical odds/results never change, so their
    caches never expire. (Historical Odds API calls cost 10x live ones, so
    re-buying the same finished lines burns credits for nothing.)"""
    try:
        return str(date_key) < _nfl_today()
    except Exception:
        return False

# ── NFL game weather ─────────────────────────────────────────────────────────
# Coordinates are stadium coordinates (not city-centre estimates).  Keeping the
# map in-code makes the weather input deterministic and avoids a second
# geocoder, whose nearest result can be wrong for shared-city teams.
_NFL_STADIUM_COORDS = {
    "ARI": (33.5276, -112.2626), "ATL": (33.7554, -84.4008),
    "BAL": (39.2780, -76.6227), "BUF": (42.7738, -78.7870),
    "CAR": (35.2258, -80.8528), "CHI": (41.8623, -87.6167),
    "CIN": (39.0954, -84.5160), "CLE": (41.5061, -81.6995),
    "DAL": (32.7473, -97.0945), "DEN": (39.7439, -105.0201),
    "DET": (42.3400, -83.0456), "GB": (44.5013, -88.0622),
    "HOU": (29.6847, -95.4107), "IND": (39.7601, -86.1639),
    "JAX": (30.3239, -81.6373), "KC": (39.0489, -94.4839),
    "LV": (36.0908, -115.1830), "LAC": (33.9535, -118.3392),
    "LAR": (33.9535, -118.3392), "MIA": (25.9580, -80.2389),
    "MIN": (44.9736, -93.2575), "NE": (42.0909, -71.2643),
    "NO": (29.9511, -90.0812), "NYG": (40.8135, -74.0745),
    "NYJ": (40.8135, -74.0745), "PHI": (39.9008, -75.1675),
    "PIT": (40.4468, -80.0158), "SEA": (47.5952, -122.3316),
    "SF": (37.4030, -121.9700), "TB": (27.9759, -82.5033),
    "TEN": (36.1665, -86.7713), "WSH": (38.9076, -76.8645),
}
_NFL_WEATHER_TTL = 30 * 60
_NFL_WEATHER_TIMEOUT = 10
_NFL_WEATHER_CONCURRENCY = 6
_NFL_WEATHER_CACHE_PREFIX = "nfl_weather_v1_"
_NFL_PROTECTED_VENUES = frozenset(("sofi stadium",))

def _nfl_weather_empty(game=None, status="UNAVAILABLE", reason=""):
    game = game or {}
    return {
        "status": status, "provider": "Open-Meteo",
        "venue": game.get("venue_full_name", ""),
        "venue_city": game.get("venue_city", ""),
        "venue_state": game.get("venue_state", ""),
        "venue_country": game.get("venue_country", ""),
        "indoor": bool(game.get("indoor")),
        "protected": bool(game.get("indoor")),
        "kickoff": None, "severity": 0, "label": "",
        "summary": reason, "reason": reason, "factors": {},
    }

def _nfl_weather_cache_get(date_str):
    if _is_past_date(date_str):
        return None
    path = _CACHE_DIR / f"{_NFL_WEATHER_CACHE_PREFIX}{date_str}.json"
    try:
        if path.exists() and time.time() - path.stat().st_mtime < _NFL_WEATHER_TTL:
            value = json.loads(path.read_text(encoding="utf-8"))
            return value if isinstance(value, dict) else None
    except Exception as exc:
        print(f"[NFL weather cache] read error: {exc}")
    return None

def _nfl_weather_cache_set(date_str, value):
    if _is_past_date(date_str):
        return
    try:
        path = _CACHE_DIR / f"{_NFL_WEATHER_CACHE_PREFIX}{date_str}.json"
        temporary = path.with_name(path.name + "." + uuid.uuid4().hex + ".tmp")
        temporary.write_text(json.dumps(value, ensure_ascii=False, allow_nan=False),
                             encoding="utf-8")
        temporary.replace(path)
    except Exception as exc:
        print(f"[NFL weather cache] write error: {exc}")

def _nfl_weather_severity(wind, gust, rain, snow, precip, temp):
    wind_score = min(1.0, max(0.0, (max(wind or 0, (gust or 0) * .78) - 10) / 25))
    precip_score = min(1.0, max(0.0, (max(rain or 0, precip or 0) - .01) / .24))
    snow_score = min(1.0, max(0.0, (snow or 0) / .20))
    cold_score = min(1.0, max(0.0, (32 - (temp if temp is not None else 50)) / 35))
    return int(round(min(100, 100 * (.52 * wind_score + .30 * max(precip_score, snow_score)
                                      + .18 * cold_score))))

def _nfl_weather_factors(snapshot, market, position=""):
    """Return one bounded market factor; unavailable weather is exactly neutral."""
    if not snapshot or snapshot.get("status") != "OK" or snapshot.get("protected"):
        return 1.0
    factors = snapshot.get("factors") or {}
    key = str(market or "")
    if key == "player_anytime_td":
        group = str(position or "").upper()
        return float(factors.get("td_rb" if group == "RB" else
                                 "td_qb" if group == "QB" else
                                 "td_te" if group == "TE" else
                                 "td_wr" if group == "WR" else "player_anytime_td", 1.0))
    factor = factors.get(key, 1.0)
    try:
        return max(.82, min(1.12, float(factor)))
    except (TypeError, ValueError):
        return 1.0

def _nfl_weather_snapshot(game, hourly):
    if not hourly:
        return _nfl_weather_empty(game, reason="Weather forecast unavailable")
    try:
        kickoff = datetime.fromisoformat(str(game.get("start", "")).replace("Z", "+00:00"))
        if kickoff.tzinfo is None:
            kickoff = kickoff.replace(tzinfo=timezone.utc)
        kickoff = kickoff.astimezone(timezone.utc)
        times = []
        for value in (hourly.get("time") or []):
            parsed = datetime.fromisoformat(str(value).replace("Z", "+00:00"))
            times.append(parsed.replace(tzinfo=timezone.utc)
                         if parsed.tzinfo is None else parsed.astimezone(timezone.utc))
        if not times:
            raise ValueError("no hourly forecast")
        idx = min(range(len(times)), key=lambda i: abs(times[i] - kickoff))
        def val(key):
            values = hourly.get(key) or []
            return values[idx] if idx < len(values) else None
        temp, prob, rain, snow = val("temperature_2m"), val("precipitation_probability"), val("rain"), val("snowfall")
        precip, wind, gust, code = val("precipitation"), val("wind_speed_10m"), val("wind_gusts_10m"), val("weather_code")
        temp = float(temp) if temp is not None else None
        prob = float(prob) if prob is not None else None
        rain = float(rain or 0); snow = float(snow or 0); precip = float(precip or 0)
        wind = float(wind or 0); gust = float(gust or 0)
        severity = _nfl_weather_severity(wind, gust, rain, snow, precip, temp)
        if severity < 20: label = "MINOR"
        elif severity < 45: label = "NOTABLE"
        elif severity < 70: label = "HIGH"
        else: label = "EXTREME"
        weather_load = severity / 100.0
        pass_yds = 1 - min(.18, .18 * weather_load)
        pass_att = 1 - min(.12, .12 * weather_load)
        rush_att = 1 + min(.12, .12 * weather_load)
        rush_yds = 1 + min(.06, .06 * weather_load)
        kick = 1 - min(.18, .18 * weather_load)
        factors = {
            "player_pass_yds": pass_yds, "player_pass_tds": 1 - .15 * weather_load,
            "player_pass_completions": 1 - .14 * weather_load,
            "player_pass_attempts": pass_att, "player_pass_interceptions": 1 + .12 * weather_load,
            "player_reception_yds": 1 - .16 * weather_load,
            "player_receptions": 1 - .12 * weather_load,
            "player_rush_yds": rush_yds, "player_rush_attempts": rush_att,
            "player_rush_reception_yds": 1 + .025 * weather_load,
            "player_kicking_points": kick, "player_field_goals": kick,
            "player_anytime_td": 1.0,
        }
        # Store positional TD factors separately; the analyzer chooses one.
        factors["td_rb"] = 1 + .045 * weather_load
        factors["td_qb"] = 1 + .025 * weather_load
        factors["td_wr"] = 1 - .075 * weather_load
        factors["td_te"] = 1 - .075 * weather_load
        precipitation_text = (f"{prob:.0f}% precip, {precip:.2f} in" if prob is not None
                              else f"{precip:.2f} in precip")
        summary = (f"{label.title()} weather: {temp:.0f}°F, {precipitation_text}, "
                   f"{wind:.0f} mph wind / {gust:.0f} mph gusts")
        return {
            "status": "OK", "provider": "Open-Meteo",
            "venue": game.get("venue_full_name", ""),
            "venue_city": game.get("venue_city", ""), "venue_state": game.get("venue_state", ""),
            "venue_country": game.get("venue_country", ""), "indoor": False, "protected": False,
            "kickoff": {"time": kickoff.isoformat(), "temperature_f": temp,
                        "precipitation_probability": prob, "precipitation_in": precip,
                        "rain_in": rain, "snowfall_in": snow, "wind_mph": wind,
                        "gust_mph": gust, "weather_code": code},
            "severity": severity, "label": label, "summary": summary, "reason": summary,
            "factors": factors,
        }
    except Exception as exc:
        return _nfl_weather_empty(game, reason=f"Weather forecast unavailable: {exc}")

async def _nfl_fetch_weather(date_str, games):
    if _is_past_date(date_str):
        return {}
    cached = await asyncio.to_thread(_nfl_weather_cache_get, date_str)
    if cached is not None:
        return cached
    results = {}
    semaphore = asyncio.Semaphore(_NFL_WEATHER_CONCURRENCY)
    async with httpx.AsyncClient(timeout=_NFL_WEATHER_TIMEOUT) as client:
        async def one(game):
            key = str(game.get("id") or f"{game.get('away_abbr')}@{game.get('home_abbr')}")
            venue = str(game.get("venue_full_name") or "").strip().lower()
            country = str(game.get("venue_country") or "").upper()
            home = str(game.get("home_abbr") or "").upper()
            protected = bool(game.get("indoor")) or venue in _NFL_PROTECTED_VENUES
            if country not in ("", "USA") or home not in _NFL_STADIUM_COORDS:
                results[key] = _nfl_weather_empty(game, reason="Unsupported or international venue")
                return
            if protected:
                item = _nfl_weather_empty(game, status="PROTECTED",
                    reason="Indoor or weather-protected stadium; outdoor weather neutral")
                item["protected"] = True
                results[key] = item
                return
            lat, lon = _NFL_STADIUM_COORDS[home]
            try:
                start = datetime.fromisoformat(str(game.get("start", "")).replace("Z", "+00:00"))
                date = start.astimezone(timezone.utc).date().isoformat()
                async with semaphore:
                    response = await client.get("https://api.open-meteo.com/v1/forecast", params={
                        "latitude": lat, "longitude": lon, "hourly": ",".join((
                            "temperature_2m", "precipitation_probability", "precipitation",
                            "rain", "snowfall", "wind_speed_10m", "wind_gusts_10m", "weather_code")),
                        "temperature_unit": "fahrenheit", "wind_speed_unit": "mph",
                        "precipitation_unit": "inch", "timezone": "UTC",
                        "start_date": date, "end_date": date,
                    })
                    response.raise_for_status()
                    results[key] = _nfl_weather_snapshot(game, response.json().get("hourly"))
            except Exception as exc:
                results[key] = _nfl_weather_empty(game, reason=f"Weather provider unavailable: {exc}")
        await asyncio.gather(*(one(game) for game in games))
    await asyncio.to_thread(_nfl_weather_cache_set, date_str, results)
    return results

def _cache_get(date_key, allow_stale=False):
    # v4 invalidates pre-weather results without invalidating the
    # separate raw-odds cache (so recalculation does not re-buy sportsbook data).
    p = _CACHE_DIR / f"nfl_v4_weather_{date_key}.json"
    try:
        if p.exists() and (allow_stale or _is_past_date(date_key)
                           or (time.time() - p.stat().st_mtime) < _CACHE_TTL):
            return json.loads(p.read_text(encoding="utf-8"))
    except: pass
    return None

def _cache_set(date_key, result):
    try:
        _nfl_write_board_cache(
            _CACHE_DIR / f"nfl_v4_weather_{date_key}.json", result)
    except Exception as exc:
        print(f"[NFL cache] Could not save OLD board for {date_key}: {exc}")

def _nfl_write_board_cache(path, result):
    """Stream to a private file, then atomically replace the completed board."""
    temporary = path.with_name(path.name + "." + uuid.uuid4().hex + ".tmp")
    try:
        _nfl_json_ready(result)
        with temporary.open("w", encoding="utf-8") as handle:
            json.dump(result, handle, ensure_ascii=False, allow_nan=False)
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)

# NEW is deliberately stored outside the legacy short-lived result cache.  The
# raw sportsbook cache remains shared (it is an input, not a model result), but
# a NEW board can never be served as an OLD board.
_NEW_CACHE_PREFIX = "nfl_new_v2_weather_"
def _new_cache_get(date_key, allow_stale=False):
    p = _CACHE_DIR / f"{_NEW_CACHE_PREFIX}{date_key}.json"
    try:
        if p.exists() and (allow_stale or _is_past_date(date_key)
                           or (time.time() - p.stat().st_mtime) < _CACHE_TTL):
            value = json.loads(p.read_text(encoding="utf-8"))
            return value if isinstance(value, dict) else None
    except Exception:
        pass
    return None

def _new_cache_set(date_key, result):
    try:
        _nfl_write_board_cache(
            _CACHE_DIR / f"{_NEW_CACHE_PREFIX}{date_key}.json", result)
    except Exception as exc:
        print(f"[NFL cache] Could not save NEW board for {date_key}: {exc}")

# Odds-layer cache: stores the raw Odds API prop lines per date so re-runs
# (forced re-rank, runs after the result cache expires) reuse the odds already
# pulled instead of hitting the Odds API again. Shorter TTL than the result
# cache so lines still refresh over the day. Cleared by /api/clear-cache (which
# globs nfl_*.json), so a true fresh run still re-pulls.
_ODDS_TTL = 15 * 60

def _odds_cache_get(date_key):
    """Returns (props_list, game_lines_by_id, skipped_matchups) on hit.
    Handles the old list-only format for backward compat."""
    # Historical replays keep the original permanent filename so paid archived
    # Odds API data remains reusable. Live slates use v2 for quote timestamps.
    p = _CACHE_DIR / (
        f"nfl_odds_{date_key}.json" if _is_past_date(date_key)
        else f"nfl_odds_v2_{date_key}.json")
    try:
        if p.exists() and (_is_past_date(date_key)
                           or (time.time() - p.stat().st_mtime) < _ODDS_TTL):
            print(f"[OddsCache] HIT nfl/{date_key}")
            raw = json.loads(p.read_text(encoding="utf-8"))
            if isinstance(raw, dict) and "props" in raw:
                return (raw["props"], raw.get("game_lines", {}),
                        raw.get("skipped_matchups", []))
            return raw, {}, []   # old list-only format
    except Exception as e:
        print(f"[OddsCache] read error: {e}")
    return None, None, []

def _odds_cache_set(date_key, props, game_lines, skipped_matchups=None):
    try:
        p = _CACHE_DIR / (
            f"nfl_odds_{date_key}.json" if _is_past_date(date_key)
            else f"nfl_odds_v2_{date_key}.json")
        p.write_text(
            json.dumps({
                "props": props,
                "game_lines": game_lines,
                "skipped_matchups": list(skipped_matchups or []),
            }, ensure_ascii=False),
            encoding="utf-8")
        print(f"[OddsCache] SET nfl/{date_key} ({len(props)} props, {len(game_lines)} games)")
    except Exception as e:
        print(f"[OddsCache] write error: {e}")

_ALT_COACH_TTL = 15 * 60
# v4 invalidates old alternate eligibility payloads. Raw ladders are cached
# separately so a partial refresh retries only unfinished games.
_ALT_COACH_CACHE_VERSION = 4
_ALT_COACH_RAW_TTL = 15 * 60
_ALT_COACH_INFLIGHT: Dict[str, asyncio.Task] = {}
_ALT_COACH_DEFERRED: set = set()
_ALT_COACH_NEXT_RETRY: Dict[str, float] = {}
_ALT_COACH_RETRY_COUNT: Dict[str, int] = {}
_ALT_COACH_RETRY_BASE = 30

def _alt_coach_cache_get(date_key, allow_stale=False, system="OLD"):
    prefix = "nfl_new_alt_coach" if str(system).upper() == "NEW" else "nfl_alt_coach"
    p = _CACHE_DIR / f"{prefix}_v{_ALT_COACH_CACHE_VERSION}_{date_key}.json"
    try:
        if p.exists() and (allow_stale or
                           (time.time() - p.stat().st_mtime) < _ALT_COACH_TTL):
            value = json.loads(p.read_text(encoding="utf-8"))
            if isinstance(value, dict):
                value.setdefault(
                    "generated_at",
                    datetime.fromtimestamp(
                        p.stat().st_mtime, timezone.utc).isoformat())
                return value
    except Exception as e:
        print(f"[AltCoachCache] read error: {e}")
    return None

def _alt_coach_cache_set(date_key, result, system="OLD"):
    try:
        prefix = "nfl_new_alt_coach" if str(system).upper() == "NEW" else "nfl_alt_coach"
        result = dict(result or {})
        result.setdefault("generated_at", datetime.now(timezone.utc).isoformat())
        (_CACHE_DIR / f"{prefix}_v{_ALT_COACH_CACHE_VERSION}_{date_key}.json").write_text(
            json.dumps(result, ensure_ascii=False), encoding="utf-8")
    except Exception as e:
        print(f"[AltCoachCache] write error: {e}")

def _alt_coach_raw_cache_get(date_key, allow_stale=False):
    """Return successful per-event ladders, including successful empty events."""
    p = _CACHE_DIR / f"nfl_alt_raw_v1_{date_key}.json"
    try:
        if p.exists() and (allow_stale or
                           (time.time() - p.stat().st_mtime) < _ALT_COACH_RAW_TTL):
            raw = json.loads(p.read_text(encoding="utf-8"))
            return raw if isinstance(raw, dict) else {}
    except Exception as e:
        print(f"[AltCoachRawCache] read error: {e}")
    return {}

def _alt_coach_raw_cache_set(date_key, events):
    try:
        target = _CACHE_DIR / f"nfl_alt_raw_v1_{date_key}.json"
        temp = target.with_suffix(".tmp")
        temp.write_text(json.dumps({"events": events, "saved_at": datetime.now(
            timezone.utc).isoformat()}, ensure_ascii=False), encoding="utf-8")
        temp.replace(target)
    except Exception as e:
        print(f"[AltCoachRawCache] write error: {e}")

def _alt_coach_raw_events(raw):
    events = raw.get("events") if isinstance(raw, dict) else {}
    return events if isinstance(events, dict) else {}

def _alt_coach_task_done(task, date_key="", system="OLD"):
    """Consume a shared task exception so one failed warm is not noisy."""
    try:
        task.result()
    except asyncio.CancelledError:
        pass
    except Exception as exc:
        print(f"[AltCoachCache] shared scan failed: {exc}")
        if date_key:
            retry_key = f"{system}:{date_key}"
            count = _ALT_COACH_RETRY_COUNT.get(retry_key, 0) + 1
            _ALT_COACH_RETRY_COUNT[retry_key] = min(count, 6)
            _ALT_COACH_NEXT_RETRY[retry_key] = time.time() + min(
                15 * 60, _ALT_COACH_RETRY_BASE * (2 ** (count - 1)))

def _alt_coach_start_task(date_str: str, system: str = "OLD"):
    """Get/create one scan without waiting in an HTTP request."""
    system = "NEW" if str(system).upper() == "NEW" else "OLD"
    task_key = f"{system}:{date_str}"
    task = _ALT_COACH_INFLIGHT.get(task_key)
    if task is not None and not task.done():
        return task, False
    if task is not None and time.time() < _ALT_COACH_NEXT_RETRY.get(task_key, 0):
        return task, False
    task = asyncio.create_task(_build_alt_coach(date_str, system))
    _ALT_COACH_INFLIGHT[task_key] = task
    task.add_done_callback(partial(_alt_coach_task_done, date_key=date_str,
                                   system=system))
    return task, True

def _hist_alt_raw_cache_get(date_key):
    p = _CACHE_DIR / f"nfl_hist_alt_raw_{date_key}.json"
    try:
        if p.exists():
            raw = json.loads(p.read_text(encoding="utf-8"))
            return raw if isinstance(raw, dict) else {}
    except Exception as e:
        print(f"[HistAltCache] read error: {e}")
    return {}

def _hist_alt_raw_cache_set(date_key, result):
    try:
        (_CACHE_DIR / f"nfl_hist_alt_raw_{date_key}.json").write_text(
            json.dumps(result, ensure_ascii=False), encoding="utf-8")
    except Exception as e:
        print(f"[HistAltCache] write error: {e}")

async def _warm_alt_coach(date_str: str) -> dict:
    """Share one live alternate-line scan between normal runs and Coach requests."""
    today = _nfl_today()
    if date_str < today:
        return {}
    # Cache helpers use synchronous filesystem I/O.  The alternate scan is
    # intentionally shared with the Coach endpoint, so do not let a cache read
    # briefly pause unrelated HTTP requests.
    cached = await asyncio.to_thread(_alt_coach_cache_get, date_str)
    if cached is not None and not cached.get("partial"):
        return cached
    task, _ = _alt_coach_start_task(date_str)
    try:
        return await asyncio.shield(task)
    except Exception:
        stale = await asyncio.to_thread(_alt_coach_cache_get, date_str,
                                        allow_stale=True)
        if stale:
            return stale
        raise

async def _deferred_alt_coach_warm(date_str: str) -> None:
    """Warm alternates only after foreground Run Picks work is idle."""
    await asyncio.sleep(60)
    while any(job.get("status") == "running" for job in JOBS.values()):
        await asyncio.sleep(15)
    _alt_coach_start_task(date_str)

def _schedule_alt_coach_warm(date_str: str) -> None:
    """Schedule alternate cache work behind foreground standard boards."""
    try:
        if date_str >= _nfl_today():
            # Give the user time to launch another day/full-week foreground run,
            # then remain deferred while any Run Picks job is active.
            task = asyncio.create_task(_deferred_alt_coach_warm(date_str))
            _ALT_COACH_DEFERRED.add(task)
            task.add_done_callback(_ALT_COACH_DEFERRED.discard)
    except Exception as e:
        print(f"[AltCoachCache] warm schedule error: {e}")

# ── nfl_data_py stats loader ───────────────────────────────────────────────────
_nfl_df = None
_nfl_df_lock = asyncio.Lock()
_nfl_stats_load_task = None
_NFL_PKL      = _CACHE_DIR / "nfl_df_cache_v7.pkl"  # v7: validated role-aware schema

# nfl-verse team codes that differ from ESPN's (ESPN is what the schedule,
# H/A lookup and card display all use). Normalized ONCE at data load so every
# comparison in the app speaks the same language. Without this, LAR/WSH
# players look "traded" (wrong team + wrong home/away on cards, starters
# evicted by mislabeled players) and their vs-opponent history comes up empty.
_NFLVERSE_TO_ESPN = {"LA": "LAR", "WAS": "WSH"}
_NFL_PKL_TTL  = 20 * 3600  # 20h — refresh once a day

def _nfl_cache_valid(frame):
    required = {"player_display_name", "recent_team", "opponent_team",
                "season", "week", "position"}
    return (frame is not None and hasattr(frame, "columns")
            and required.issubset(set(frame.columns)) and len(frame) > 0)

# ── ESPN H/A Lookup — (season, week, team_abbr) → 'HOME' or 'AWAY' ───────────
_HA_LOOKUP: dict = {}
_HA_LOADED = False
_HA_LOCK   = asyncio.Lock()

_HA_CACHE_FILE = _CACHE_DIR / "nfl_ha_lookup_v5_nflverse.json"

def _nfl_ha_cache_valid(lookup, cache_path=None) -> bool:
    """Validate useful schedule coverage without requiring an unpublished season."""
    try:
        if not isinstance(lookup, dict) or not lookup:
            return False
        seasons, teams_by_season = set(), {}
        for key, venue in lookup.items():
            if (not isinstance(key, tuple) or len(key) != 4
                    or venue not in {"HOME", "AWAY"}):
                return False
            season, season_type, week, team = key
            season, week = int(season), int(week)
            if (season < min(NFL_SEASONS) or season > _cur_season
                    or str(season_type) not in {"REG", "POST"}
                    or week < 1 or not str(team).strip()):
                return False
            seasons.add(season)
            teams_by_season.setdefault(season, set()).add(str(team))
        # A current-season schedule is optional before publication.  The latest
        # completed season must still have broad league coverage so a truncated
        # or stale partial write cannot silently become authoritative.
        latest_required = _cur_season - 1
        if latest_required not in seasons or len(
                teams_by_season.get(latest_required, set())) < 20:
            return False
        # Refresh on age even when the optional current schedule was not yet
        # published; otherwise a historical-only cache could live forever and
        # never discover the newly released season.
        if (cache_path is not None
                and time.time() - cache_path.stat().st_mtime > 7 * 86400):
            return False
        return True
    except Exception:
        return False

async def _build_ha_lookup():
    """Build HOME/AWAY lookup from the single cached nflverse schedule file."""
    global _HA_LOOKUP, _HA_LOADED
    async with _HA_LOCK:
        if _HA_LOADED:
            return
        # Try disk cache first — survives spin-down within the same deploy
        try:
            if _HA_CACHE_FILE.exists():
                raw = json.loads(_HA_CACHE_FILE.read_text(encoding="utf-8"))
                disk_lookup = {
                    tuple(int(x) if x.isdigit() else x for x in k.split("|")): v
                    for k, v in raw.items()
                }
                if _nfl_ha_cache_valid(disk_lookup, _HA_CACHE_FILE):
                    _HA_LOOKUP = disk_lookup
                    _HA_LOADED = True
                    print(f"[H/A] Loaded from disk cache: {len(_HA_LOOKUP)} entries")
                    return
                if _nfl_ha_cache_valid(disk_lookup):
                    # Keep a structurally complete stale map as a fallback while
                    # refreshing. A transient schedule outage must not erase
                    # authoritative historical venue coverage.
                    _HA_LOOKUP = disk_lookup
                    print(f"[H/A] Refreshing aged disk cache: {len(_HA_LOOKUP)} entries")
                else:
                    print("[H/A] Ignoring partial or invalid disk cache")
        except Exception as e:
            print(f"[H/A] Disk cache load failed: {e}")

        print("[H/A] Building HOME/AWAY lookup from nflverse games.csv…")
        try:
            schedule_rows = await _load_nfl_games_history()
            valid_post_types = {"WC", "DIV", "CON", "SB", "POST"}
            for game_row in schedule_rows:
                try:
                    season = int(game_row.get("season") or 0)
                    raw_week = int(game_row.get("week") or 0)
                except (TypeError, ValueError):
                    continue
                if season not in NFL_SEASONS or raw_week < 1:
                    continue
                game_type = str(game_row.get("game_type") or "REG").upper()
                if game_type == "REG":
                    season_type, lookup_week = "REG", raw_week
                elif game_type in valid_post_types:
                    season_type = "POST"
                    lookup_week = _espn_ha_week("POST", raw_week)
                else:
                    continue
                for column, venue in (("home_team", "HOME"),
                                      ("away_team", "AWAY")):
                    team = str(game_row.get(column) or "").strip().upper()
                    team = _NFLVERSE_TO_ESPN.get(team, team)
                    if not team:
                        continue
                    _HA_LOOKUP[(season, season_type, lookup_week, team)] = venue
        except Exception as exc:
            print(f"[H/A] nflverse schedule lookup failed: {exc}")
        _HA_LOADED = bool(_HA_LOOKUP)
        print(f"[H/A] Built lookup: {len(_HA_LOOKUP)} entries")
        if not _HA_LOADED:
            return
        # Persist to disk so the next request skips this step
        try:
            serializable = {f"{s}|{st}|{w}|{a}": v
                            for (s, st, w, a), v in _HA_LOOKUP.items()}
            _HA_CACHE_FILE.write_text(json.dumps(serializable), encoding="utf-8")
            print(f"[H/A] Saved to disk cache")
        except Exception as e:
            print(f"[H/A] Disk cache save failed: {e}")

async def _nfl_gp_ensure_ha(timeout: float = 18.0) -> bool:
    """Ensure the shared nflverse venue map is ready without duplicate builds."""
    if _HA_LOADED:
        return True
    try:
        await asyncio.wait_for(_build_ha_lookup(), timeout=timeout)
    except asyncio.TimeoutError:
        print(f"[H/A] Game Predictor venue lookup skipped after {timeout}s")
    except Exception as exc:
        print(f"[H/A] Game Predictor venue lookup unavailable: {exc}")
    return bool(_HA_LOADED)

# Direct nfl-verse CSV URLs (no package needed)
_NFL_CSV_URL  = "https://github.com/nflverse/nflverse-data/releases/download/player_stats/player_stats_{year}.csv"
_NFL_DEF_URL  = "https://github.com/nflverse/nflverse-data/releases/download/player_stats/player_stats_def_{year}.csv"
_NFL_KICK_URL = "https://github.com/nflverse/nflverse-data/releases/download/player_stats/player_stats_kicking_{year}.csv"
# nfl-verse retired the per-type player_stats files after 2024. Seasons 2025+
# live in ONE combined weekly file (offense + defense + kicking per player-week).
_NFL_NEW_URL       = "https://github.com/nflverse/nflverse-data/releases/download/stats_player/stats_player_week_{year}.csv"
_NFL_SNAP_URL      = "https://github.com/nflverse/nflverse-data/releases/download/snap_counts/snap_counts_{year}.csv"
_NFL_NEW_FMT_START = 2025
_KEEP_COLS   = ["player_display_name","player_id","headshot_url","position","recent_team","opponent_team",
                "season","week","season_type","rushing_yards","receiving_yards","passing_yards",
                "receptions","targets","passing_tds","rushing_tds","receiving_tds",
                "completions","attempts","interceptions","carries",
                # Opportunity fields retained when nflverse publishes them. The
                # weekly player-stat feed currently supplies target_share; the
                # remaining names make the model forward-compatible without
                # inventing unavailable red-zone/end-zone or snap data.
                "target_share","air_yards_share","wopr","offense_pct","snap_share",
                "red_zone_carries","redzone_carries","carries_inside_10",
                "end_zone_targets","endzone_targets"]

_NFL_SOURCE_COLS = set(_KEEP_COLS) | {
    # Alternate source names used by the combined, defense, kicking, and snap
    # releases before they are normalized into the model schema.
    "team", "player", "player_name", "passing_interceptions",
    "def_tackles", "def_tackles_solo", "def_tackle_assists",
    "def_interceptions", "def_sacks", "fg_made", "pat_made",
    "offense_snaps",
}

def _compact_nfl_stats_frame(df):
    """Shrink the retained nflverse frame without changing model values."""
    if df is None:
        return df
    try:
        import pandas as pd
        # IDs and headshots repeat across player-weeks but are never grouping
        # dimensions. Keep player/team/position fields as ordinary strings:
        # pandas categorical groupby can materialize unobserved combinations.
        for col in ("player_id", "headshot_url"):
            if col in df.columns and str(df[col].dtype) == "object":
                values = df[col].fillna("").astype(str)
                df[col] = pd.Categorical(values)
        # nflverse numeric releases commonly arrive as float64 even for small
        # counts. float32 is far more precise than any displayed/model input and
        # halves those columns' resident memory.
        for col in df.columns:
            dtype = df[col].dtype
            if pd.api.types.is_float_dtype(dtype) and dtype.itemsize > 4:
                df[col] = pd.to_numeric(df[col], downcast="float")
            elif pd.api.types.is_integer_dtype(dtype) and dtype.itemsize > 4:
                df[col] = pd.to_numeric(df[col], downcast="integer")
    except Exception as exc:
        print(f"[NFL Data] memory compaction skipped: {exc}")
    return df

def _dl_csv(url):
    """Download one nfl-verse CSV (regular season + playoffs) as a DataFrame.
    Uses httpx with a hard 60-second total timeout so a stalled download
    fails fast instead of hanging forever."""
    import pandas as pd
    import tempfile
    last_err = None
    for attempt in range(3):   # retry — a single flaky download must not silently
        try:                   # drop a whole season of stats from every pick
            # Keep bounded parallel downloads, but spool their bytes to disk
            # rather than retaining response.content plus BytesIO copies.
            with tempfile.TemporaryFile() as source:
                with httpx.stream("GET", url, headers={"User-Agent": "Mozilla/5.0"},
                                  timeout=60, follow_redirects=True) as r:
                    r.raise_for_status()
                    deadline = time.monotonic() + 60
                    for chunk in r.iter_bytes(chunk_size=65536):
                        if time.monotonic() > deadline:
                            raise TimeoutError("NFL CSV download exceeded 60 seconds")
                        source.write(chunk)
                source.seek(0)
                d = pd.read_csv(source, low_memory=False,
                                usecols=lambda name: name in _NFL_SOURCE_COLS)
            if "season_type" in d.columns:
                d = d[d["season_type"].isin(["REG", "POST"])]
            return _compact_nfl_stats_frame(d)
        except Exception as e:
            last_err = e
            print(f"[NFL Data] download attempt {attempt+1}/3 failed for {url}: {e}")
            time.sleep(2 * (attempt + 1))
    else:
        raise last_err

def _load_nfl_stats_sync():
    """Download offense + defense + kicking CSVs from nfl-verse GitHub.
    ALL files are fetched in parallel (ThreadPoolExecutor) so total download
    time = slowest single file, not sum of all files.
    Result is pickled to disk so spin-down restarts load in ~1 second."""
    global _nfl_df
    if _nfl_df is not None:
        return _nfl_df
    # ── Disk cache (pickle) ───────────────────────────────────────────────────
    try:
        if _NFL_PKL.exists() and (time.time() - _NFL_PKL.stat().st_mtime) < _NFL_PKL_TTL:
            import pickle
            with _NFL_PKL.open("rb") as handle:
                _nfl_df = pickle.load(handle)
            if not _nfl_cache_valid(_nfl_df):
                print("[NFL Data] Disk cache schema invalid; rebuilding")
                _NFL_PKL.unlink(missing_ok=True)
                _nfl_df = None
                raise ValueError("invalid NFL cache schema")
            if ("rush_rec_yards" not in _nfl_df.columns
                    and {"rushing_yards", "receiving_yards"}.issubset(_nfl_df.columns)):
                _nfl_df["rush_rec_yards"] = (
                    _nfl_df["rushing_yards"].fillna(0)
                    + _nfl_df["receiving_yards"].fillna(0))
            _nfl_df = _compact_nfl_stats_frame(_nfl_df)
            print(f"[NFL Data] Loaded from disk cache: {len(_nfl_df):,} rows")
            return _nfl_df
    except Exception as e:
        print(f"[NFL Data] Disk cache load failed: {e}")
    print(f"[NFL Data] Downloading REG+POST stats for seasons {NFL_SEASONS} in parallel from nfl-verse…")
    try:
        import pandas as pd
        from concurrent.futures import ThreadPoolExecutor, as_completed

        # Build the full list of (tag, url) pairs for parallel download.
        # Seasons < 2025 use the old 3-file layout; 2025+ use the single
        # combined weekly file (nfl-verse retired the old files).
        old_years = [y for y in NFL_SEASONS if y < _NFL_NEW_FMT_START]
        new_years = [y for y in NFL_SEASONS if y >= _NFL_NEW_FMT_START]
        off_urls  = [(f"off_{y}",  _NFL_CSV_URL.format(year=y))  for y in old_years]
        def_urls  = [(f"def_{y}",  _NFL_DEF_URL.format(year=y))  for y in old_years]
        kick_urls = [(f"kick_{y}", _NFL_KICK_URL.format(year=y)) for y in old_years]
        new_urls  = [(f"new_{y}",  _NFL_NEW_URL.format(year=y))  for y in new_years]
        # Snap counts are one small season-level file per year (not player
        # fanout). Failure is optional and never blocks the offense board.
        snap_urls = [(f"snap_{y}", _NFL_SNAP_URL.format(year=y)) for y in NFL_SEASONS]
        all_tasks = off_urls + def_urls + kick_urls + new_urls + snap_urls

        results: dict = {}
        # Keep the full-history download parallel without opening one socket per
        # file; the old layout can produce dozens of requests.
        with ThreadPoolExecutor(max_workers=min(3, max(1, len(all_tasks)))) as ex:
            fut_map = {ex.submit(_dl_csv, url): tag for tag, url in all_tasks}
            for fut in as_completed(fut_map):
                tag = fut_map[fut]
                try:
                    results[tag] = fut.result()
                    print(f"[NFL Data] {tag}: {len(results[tag])} rows")
                except Exception as e:
                    print(f"[NFL Data] {tag} failed: {e}")

        # ---- new combined format (2025+): one file has off + def + kicking ----
        def _new_fmt_transform(d):
            d = d.rename(columns={"team": "recent_team",
                                  "passing_interceptions": "interceptions"})
            def col(name):
                return d[name].fillna(0) if name in d.columns else 0
            d["anytime_td"]      = col("rushing_tds") + col("receiving_tds")  # scorer only — no passing TDs
            d["rush_rec_yards"]  = col("rushing_yards") + col("receiving_yards")
            d["tackles_assists"] = col("def_tackles_solo") + col("def_tackle_assists")
            d["def_ints"]        = col("def_interceptions")
            d["kicking_points"]  = col("fg_made") * 3 + col("pat_made")
            extra = ["anytime_td","rush_rec_yards","tackles_assists","def_sacks","def_ints",
                     "fg_made","kicking_points"]
            keep  = [c for c in _KEEP_COLS + extra if c in d.columns]
            return d[keep]

        # ---- offense (skill-position) ----
        off_frames = []
        for y in old_years:
            df_yr = results.get(f"off_{y}")
            if df_yr is not None:
                keep = [c for c in _KEEP_COLS if c in df_yr.columns]
                off_frames.append(df_yr[keep])
        for y in new_years:
            df_yr = results.get(f"new_{y}")
            if df_yr is not None:
                try:
                    off_frames.append(_new_fmt_transform(df_yr))
                except Exception as e:
                    print(f"[NFL Data] new-format {y} transform failed: {e}")
        if not off_frames:
            print("[NFL Data] No offense data downloaded — aborting")
            return None
        off = pd.concat(off_frames, ignore_index=True)
        snap_frames = []
        for y in NFL_SEASONS:
            sd = results.get(f"snap_{y}")
            if sd is None:
                continue
            try:
                sd = sd.rename(columns={"team":"recent_team","player":"player_display_name","player_name":"player_display_name"})
                if "offense_pct" in sd.columns:
                    numeric_pct = pd.to_numeric(sd["offense_pct"], errors="coerce")
                    if numeric_pct.max(skipna=True) <= 1.5:
                        sd["offense_pct"] = numeric_pct * 100.0
                wanted = ["player_display_name","recent_team","season","week","position","offense_pct","offense_snaps"]
                snap_frames.append(sd[[c for c in wanted if c in sd.columns]].copy())
            except Exception as exc:
                print(f"[NFL Data] snap_{y} transform failed: {exc}")
        if snap_frames:
            snaps = pd.concat(snap_frames, ignore_index=True)
            for c in ("recent_team",):
                if c in snaps.columns: snaps[c] = snaps[c].replace(_NFLVERSE_TO_ESPN)
            keys = ["player_display_name","recent_team","season","week"]
            if all(c in off.columns for c in keys) and all(c in snaps.columns for c in keys):
                snap_cols = [c for c in ["offense_pct","offense_snaps"] if c in snaps.columns]
                snaps = snaps.groupby(keys, as_index=False)[snap_cols].mean()
                off = off.merge(snaps, on=keys, how="left", suffixes=("","_snap"))
                if "offense_pct_snap" in off: off["offense_pct"] = off["offense_pct"].fillna(off["offense_pct_snap"])
                if "offense_snaps_snap" in off: off["offense_snaps"] = off["offense_snaps"].fillna(off["offense_snaps_snap"])
                off = off.drop(columns=[c for c in ["offense_pct_snap","offense_snaps_snap"] if c in off])
            print(f"[NFL Data] snap counts merged: {len(snaps):,} player-weeks")
        else:
            print("[NFL Data] snap counts unavailable; role engine uses stats usage only")
        if {"rushing_yards", "receiving_yards"}.issubset(off.columns):
            off["rush_rec_yards"] = (
                off["rushing_yards"].fillna(0)
                + off["receiving_yards"].fillna(0))

        # Compute anytime TD (offense only). Anytime-TD props pay when the player
        # SCORES — rushing or receiving TDs only. Passing TDs don't count (and
        # would double-count the receiver's score in team aggregates).
        td_cols = [c for c in ["rushing_tds","receiving_tds"] if c in off.columns]
        if td_cols:
            off["anytime_td"] = off[td_cols].sum(axis=1)

        # (season, week, team) -> opponent_team map from offense rows
        opp_map = {}
        try:
            sched = off[["season","week","recent_team","opponent_team"]].dropna()
            sched = sched.drop_duplicates(subset=["season","week","recent_team"])
            for t in sched.itertuples(index=False):
                opp_map[(int(t.season), int(t.week), str(t.recent_team))] = str(t.opponent_team)
        except Exception as e:
            print(f"[NFL Data] opp map failed: {e}")

        def _merge_extra(tag_prefix, url_tpl, rename, computed):
            parts = []
            ident = ["player_display_name","player_id","headshot_url","season","week","season_type"]
            for y in NFL_SEASONS:
                d = results.get(f"{tag_prefix}_{y}")
                if d is None:
                    continue
                try:
                    if "team" in d.columns:
                        d = d.rename(columns={"team": "recent_team"})
                    for src, dst in rename.items():
                        if src in d.columns and src != dst:
                            d[dst] = d[src]
                    for dst, fn in computed.items():
                        try: d[dst] = fn(d)
                        except Exception: pass
                    d["opponent_team"] = [
                        opp_map.get((int(s), int(w), str(tm)), "")
                        for s, w, tm in zip(d["season"], d["week"], d["recent_team"])
                    ]
                    want = ident + ["recent_team","opponent_team"] + list(rename.values()) + list(computed.keys())
                    cols = [c for c in dict.fromkeys(want) if c in d.columns]
                    parts.append(d[cols])
                except Exception as e:
                    print(f"[NFL Data] merge {tag_prefix}_{y} failed: {e}")
            return pd.concat(parts, ignore_index=True) if parts else None

        deff = _merge_extra("def", _NFL_DEF_URL,
            rename={"def_tackles":"tackles_assists","def_sacks":"def_sacks",
                    "def_interceptions":"def_ints"},
            computed={})
        kick = _merge_extra("kick", _NFL_KICK_URL,
            rename={"fg_made":"fg_made"},
            computed={"kicking_points": lambda d: d.get("fg_made", pd.Series(dtype=float)).fillna(0)*3
                                                 + d.get("pat_made", pd.Series(dtype=float)).fillna(0)})

        all_frames = [off] + [f for f in (deff, kick) if f is not None]
        _nfl_df = pd.concat(all_frames, ignore_index=True)
        # Normalize team codes to ESPN style (LA→LAR, WAS→WSH) so schedule,
        # H/A lookup, starter filter and cards all agree on team identity.
        for _c in ("recent_team", "opponent_team"):
            if _c in _nfl_df.columns:
                _nfl_df[_c] = _nfl_df[_c].replace(_NFLVERSE_TO_ESPN)
        _nfl_df = _compact_nfl_stats_frame(_nfl_df)
        print(f"[NFL Data] Total: {len(_nfl_df):,} rows "
              f"(off {len(off):,}"
              + (f", def {len(deff):,}" if deff is not None else "")
              + (f", kick {len(kick):,}" if kick is not None else "") + ")")
        # Persist to disk so spin-down restarts skip the download entirely.
        # ONLY cache a COMPLETE dataset — pickling a partial one (a season's
        # download failed) would serve season-less picks for hours.
        try:
            got_seasons = {int(s) for s in _nfl_df["season"].dropna().unique()}
            required_seasons = [y for y in NFL_SEASONS if y != _cur_season]
            if all(y in got_seasons for y in required_seasons):
                import pickle
                temporary = _NFL_PKL.with_suffix(".tmp")
                with temporary.open("wb") as handle:
                    pickle.dump(_nfl_df, handle, protocol=pickle.HIGHEST_PROTOCOL)
                temporary.replace(_NFL_PKL)
                print(f"[NFL Data] Saved to disk cache ({_NFL_PKL})")
            else:
                print(f"[NFL Data] NOT caching — missing completed seasons "
                      f"{sorted(set(required_seasons) - got_seasons)}; next run retries")
        except Exception as pe:
            print(f"[NFL Data] Disk cache save failed: {pe}")
    except Exception as e:
        print(f"[NFL Data] Error: {e}")
        import traceback; traceback.print_exc()
        _nfl_df = None
    return _nfl_df

async def get_nfl_stats():
    global _nfl_stats_load_task
    # Fire H/A lookup in background — analysis falls back gracefully when not ready
    if not _HA_LOADED:
        asyncio.create_task(_build_ha_lookup())
    async with _nfl_df_lock:
        if _nfl_df is not None and (
                _nfl_stats_load_task is None or _nfl_stats_load_task.done()):
            return _nfl_df
        if _nfl_stats_load_task is None or _nfl_stats_load_task.done():
            _nfl_stats_load_task = asyncio.create_task(
                asyncio.to_thread(_load_nfl_stats_sync))
        task = _nfl_stats_load_task
    try:
        # The caller times out, but the shared worker remains the only loader.
        return await asyncio.wait_for(asyncio.shield(task), timeout=150)
    except asyncio.TimeoutError:
        # Cancellation cannot stop a running thread. Share that same loader
        # with the next caller instead of starting a second full pandas build.
        print("[NFL Data] Stats load still running; no duplicate loader started")
        return None

@app.on_event("startup")
async def _startup_preload():
    """Kick off stat downloads and H/A lookup immediately on server start.
    Runs entirely in the background — the server accepts requests immediately.
    By the time the first user clicks Run the data is usually ready."""
    async def _bg():
        try:
            await get_nfl_stats()   # handles lock, disk cache, parallel download
            print("[Startup] Preload complete — stats ready")
        except Exception as e:
            print(f"[Startup] Preload error (non-fatal): {e}")
    asyncio.create_task(_bg())

# ── ESPN Schedule ──────────────────────────────────────────────────────────────
async def get_espn_games(date_str: str) -> List[Dict]:
    dc = date_str.replace("-", "")
    endpoint = "https://site.api.espn.com/apis/site/v2/sports/football/nfl/scoreboard"

    def parse_games(payload, wanted_date):
        games = []
        for ev in (payload or {}).get("events", []):
            comp = ev.get("competitions", [{}])[0]
            raw_start = ev.get("date", "") or comp.get("date", "")
            try:
                event_date = (
                    datetime.fromisoformat(str(raw_start).replace("Z", "+00:00"))
                    .astimezone(ZoneInfo("America/New_York"))
                    .strftime("%Y-%m-%d")
                )
            except Exception:
                event_date = str(raw_start)[:10]
            if wanted_date and event_date != wanted_date:
                continue
            try:
                competitors = comp.get("competitors", [])
                teams = {t["homeAway"]: t["team"] for t in competitors}
                team_rows = {t["homeAway"]: t for t in competitors}
                home  = teams.get("home", {})
                away  = teams.get("away", {})
                home_row = team_rows.get("home", {})
                away_row = team_rows.get("away", {})
                venue = comp.get("venue") or {}
                address = venue.get("address") or {}
                season_obj = ev.get("season") or {}
                season_type_num = season_obj.get("type")
                week_obj = ev.get("week") or {}
                games.append({
                    "id":        "",
                    "home_team": home.get("displayName", ""),
                    "away_team": away.get("displayName", ""),
                    "home_abbr": home.get("abbreviation", ""),
                    "away_abbr": away.get("abbreviation", ""),
                    "home_team_id": str(home.get("id") or ""),
                    "away_team_id": str(away.get("id") or ""),
                    "game":      f"{away.get('displayName','')} @ {home.get('displayName','')}",
                    # ISO kickoff time — picks carry this so finished games drop off board
                    "start":     raw_start,
                    "season":    season_obj.get("year"),
                    "season_type": "POST" if str(season_type_num) == "3" else "REG",
                    "week":      week_obj.get("number"),
                    "home_score": home_row.get("score"),
                    "away_score": away_row.get("score"),
                    "completed": ev.get("status", {}).get("type", {}).get("completed", False),
                    "venue_full_name": venue.get("fullName", ""),
                    "venue_city": address.get("city", ""),
                    "venue_state": address.get("state", ""),
                    "venue_country": address.get("country", "USA"),
                    "indoor": bool(venue.get("indoor")),
                })
            except Exception as exc:
                print(f"[ESPN] skipped malformed event: {exc}")
        return games

    daily_succeeded = False
    last_error = None
    async with httpx.AsyncClient(timeout=12) as c:
        for attempt in range(3):
            try:
                r = await c.get(endpoint, params={"dates": dc})
                r.raise_for_status()
                daily_succeeded = True
                games = parse_games(r.json(), date_str)
                if games:
                    print(f"[ESPN] {len(games)} NFL games for {date_str}")
                    return games
            except Exception as exc:
                last_error = exc
                print(f"[ESPN] daily attempt {attempt + 1}/3 failed: {exc}")
            if attempt < 2:
                await asyncio.sleep(0.6 * (attempt + 1))

        # ESPN occasionally returns a transient empty daily scoreboard. Its
        # season response still contains the event, keyed by UTC kickoff, so
        # filter that fallback using the Eastern football date.
        try:
            r = await c.get(endpoint, params={
                "dates": date_str[:4], "limit": "1000"})
            r.raise_for_status()
            games = parse_games(r.json(), date_str)
            print(f"[ESPN] season fallback found {len(games)} NFL games for {date_str}")
            return games
        except Exception as exc:
            last_error = exc
            print(f"[ESPN] season fallback failed: {exc}")

    if daily_succeeded:
        return []
    raise RuntimeError(f"ESPN schedule lookup failed for {date_str}: {last_error}")

# ── Historical season batch scheduling ─────────────────────────────────────────
# Season discovery is ESPN-only. It deliberately does not call the Odds API, so
# an admin can see the size and worst-case historical request count before
# starting a batch. Individual dates are still processed through run_pipeline,
# which owns the point-in-time filter and historical-only persistence boundary.
_NFL_BATCH_SCHEDULE_CACHE: dict = {}
_NFL_BATCH_SCHEDULE_TTL = 6 * 3600
_NFL_BATCH_MAX_SEASON_DATES = 100
_NFL_HIST_BATCHES: dict = {}
_NFL_HIST_BATCH_LOCK = _bt_th.RLock()
_NFL_HIST_BATCH_JOB_CAT = "__historical_batch_job__"

def _nfl_batch_season_year(value) -> int:
    try:
        year = int(str(value).strip())
    except (TypeError, ValueError):
        raise HTTPException(status_code=400, detail="Choose a valid NFL season")
    now = datetime.now(timezone.utc)
    latest_completed = now.year - 1 if now.month >= 3 else now.year - 2
    if year not in NFL_SEASONS or year > latest_completed:
        raise HTTPException(
            status_code=400,
            detail="Choose a completed season from the available NFL seasons",
        )
    return year

async def _nfl_season_schedule(season: int) -> dict:
    """Return unique completed-season game dates and game counts from ESPN.

    ESPN's weekly scoreboard is much cheaper and more reliable than probing
    every calendar date. Regular-season and postseason weeks are requested in
    parallel, then collapsed by the event's game date.
    """
    season = _nfl_batch_season_year(season)
    now = time.time()
    cached = _NFL_BATCH_SCHEDULE_CACHE.get(season)
    if cached and now - cached.get("ts", 0) < _NFL_BATCH_SCHEDULE_TTL:
        return cached["schedule"]

    sem = asyncio.Semaphore(8)
    found: dict = {}
    seen_events = set()
    fetched_weeks = set()
    failed_weeks = []

    async def fetch_week(client, season_type: int, week: int):
        async with sem:
            try:
                response = await client.get(
                    "https://site.api.espn.com/apis/site/v2/sports/football/nfl/scoreboard",
                    params={
                        "seasontype": season_type,
                        "week": week,
                        # ESPN ignores `season` on this endpoint and silently
                        # returns the current year. `dates=YYYY` is the actual
                        # season selector for weekly scoreboard requests.
                        "dates": season,
                    },
                )
                if not response.is_success:
                    failed_weeks.append(
                        f"type {season_type} week {week} returned HTTP {response.status_code}"
                    )
                    return
                fetched_weeks.add((season_type, week))
                for event in response.json().get("events", []):
                    comp = (event.get("competitions") or [{}])[0]
                    team_names = {
                        str((row.get("team") or {}).get("abbreviation") or
                            (row.get("team") or {}).get("displayName") or "").upper()
                        for row in (comp.get("competitors") or [])
                    }
                    # ESPN includes the AFC-vs-NFC Pro Bowl in postseason week 4.
                    # It is an exhibition without a normal NFL prop slate.
                    if team_names == {"AFC", "NFC"}:
                        continue
                    raw_date = event.get("date") or comp.get("date") or ""
                    try:
                        date_key = (
                            datetime.fromisoformat(str(raw_date).replace("Z", "+00:00"))
                            .astimezone(ZoneInfo("America/New_York"))
                            .strftime("%Y-%m-%d")
                        )
                    except Exception:
                        date_key = str(raw_date)[:10]
                    if not re.fullmatch(r"\d{4}-\d{2}-\d{2}", date_key):
                        continue
                    # Never queue a future date as a historical replay.
                    if date_key >= _nfl_today():
                        continue
                    event_id = str(event.get("id") or "")
                    if event_id and event_id in seen_events:
                        continue
                    if event_id:
                        seen_events.add(event_id)
                    bucket = found.setdefault(date_key, {"games": 0, "events": []})
                    bucket["games"] += 1
                    bucket["events"].append(event_id)
            except Exception as exc:
                print(f"[NFL batch schedule] {season} type={season_type} week={week}: {exc}")
                failed_weeks.append(f"type {season_type} week {week}: {exc}")

    async with httpx.AsyncClient(timeout=12) as client:
        requests = [
            fetch_week(client, season_type, week)
            for season_type, max_week in ((2, 18), (3, 5))
            for week in range(1, max_week + 1)
        ]
        await asyncio.gather(*requests)

    if failed_weeks or len(fetched_weeks) != 23:
        detail = "; ".join(failed_weeks[:4]) or "one or more ESPN weeks were not returned"
        raise HTTPException(
            status_code=502,
            detail=f"Could not verify the complete {season} NFL schedule: {detail}",
        )
    dates = sorted(found)
    schedule = {
        "season": season,
        "dates": dates,
        "games_by_date": {d: int(found[d]["games"]) for d in dates},
        "games_total": sum(int(found[d]["games"]) for d in dates),
        "schedule_requests": 23,
    }
    _NFL_BATCH_SCHEDULE_CACHE[season] = {"ts": now, "schedule": schedule}
    return schedule

def _nfl_batch_odds_bound(schedule: dict) -> int:
    """Worst-case historical Odds API request count for one fresh batch.

    get_odds_events can make two historical event snapshots per date, and the
    pipeline normally makes one standard-props, one alternate-props, and one
    game-lines request per scheduled game. Alternate fetches may retry twice.
    Existing odds caches reduce actual usage below this upper bound.
    """
    dates = len(schedule.get("dates") or [])
    games = int(schedule.get("games_total") or 0)
    return dates * 2 + games * 5

def _nfl_batch_public(job: dict) -> dict:
    with _NFL_HIST_BATCH_LOCK:
        failures = [dict(item) for item in job.get("failures", [])]
        payload = {
            "job_id": job.get("job_id"),
            "status": job.get("status"),
            "season": job.get("season"),
            "total_dates": len(job.get("dates") or []),
            "dates": list(job.get("dates") or []),
            "completed_dates": list(job.get("completed_dates") or []),
            "failures": failures,
            "failed_dates": [item.get("date") for item in failures if item.get("date")],
            "current_date": job.get("current_date"),
            "current_progress": job.get("current_progress") or "",
            "estimated_odds_api_calls": job.get("estimated_odds_api_calls", 0),
            "odds_bound_note": job.get("odds_bound_note", ""),
            "started_at": job.get("started_at"),
            "finished_at": job.get("finished_at"),
            "retry_count": int(job.get("retry_count") or 0),
        }
        if str(job.get("system") or "OLD").upper() == "NEW":
            payload["system"] = "NEW"
        return payload

def _nfl_batch_persist(job: dict) -> bool:
    """Persist resumable batch state in the existing Supabase ledger."""
    if "_nfl_sb_upsert" not in globals():
        return False
    payload = _nfl_batch_public(job)
    payload["games_by_date"] = dict(job.get("games_by_date") or {})
    payload["heartbeat_at"] = datetime.now(timezone.utc).isoformat()
    cfg = _nfl_store_config(job.get("system"))
    return _nfl_sb_upsert("mpa_track_ledger", [{
        "app": cfg["app"],
        "date": f"{int(job.get('season'))}-01-01",
        "category": cfg["hist_batch"],
        "side": str(job.get("job_id") or ""),
        "wins": len(job.get("completed_dates") or []),
        "losses": len(job.get("failures") or []),
        "locked": False,
        "detail": payload,
    }], on_conflict="app,date,category,side")

def _nfl_batch_restore(job_id: str, system: str = "OLD") -> Optional[dict]:
    if "_nfl_sb_get" not in globals():
        return None
    cfg = _nfl_store_config(system)
    rows = _nfl_sb_get("mpa_track_ledger", {
        "app": f"eq.{cfg['app']}",
        "category": f"eq.{cfg['hist_batch']}",
        "side": f"eq.{job_id}",
        "select": "detail",
        "limit": "1",
    })
    detail = (rows[0] or {}).get("detail") if rows else None
    if isinstance(detail, str):
        try:
            detail = json.loads(detail)
        except Exception:
            detail = None
    if not isinstance(detail, dict) or not detail.get("job_id"):
        return None
    return {
        "job_id": detail["job_id"],
        "status": detail.get("status") or "queued",
        "season": int(detail.get("season") or 0),
        "dates": list(detail.get("dates") or []),
        "games_by_date": dict(detail.get("games_by_date") or {}),
        "completed_dates": list(detail.get("completed_dates") or []),
        "failures": list(detail.get("failures") or []),
        "current_date": detail.get("current_date"),
        "current_progress": detail.get("current_progress") or "",
        "estimated_odds_api_calls": int(detail.get("estimated_odds_api_calls") or 0),
        "odds_bound_note": detail.get("odds_bound_note") or "",
        "started_at": detail.get("started_at"),
        "finished_at": detail.get("finished_at"),
        "retry_count": int(detail.get("retry_count") or 0),
        # The queried namespace is authoritative; never let a persisted detail
        # field redirect a job into the other model's ledger.
        "system": "NEW" if str(system).upper() == "NEW" else "OLD",
    }

def _nfl_batch_restore_active(system: str = "OLD") -> Optional[dict]:
    if "_nfl_sb_get" not in globals():
        return None
    cfg = _nfl_store_config(system)
    rows = _nfl_sb_get("mpa_track_ledger", {
        "app": f"eq.{cfg['app']}",
        "category": f"eq.{cfg['hist_batch']}",
        "select": "detail",
        "order": "date.desc",
        "limit": "10",
    })
    for row in rows or []:
        detail = (row or {}).get("detail")
        if isinstance(detail, str):
            try:
                detail = json.loads(detail)
            except Exception:
                continue
        if isinstance(detail, dict) and detail.get("status") in ("queued", "running"):
            return _nfl_batch_restore(
                str(detail.get("job_id") or ""), system)
    return None

async def _nfl_run_historical_batch(job_id: str):
    while True:
        # User-facing day/week runs always take priority over a bulk replay.
        # Pause only between historical dates so the current date remains
        # atomic and resumable.
        if any(item.get("status") == "running" for item in JOBS.values()):
            with _NFL_HIST_BATCH_LOCK:
                active = _NFL_HIST_BATCHES.get(job_id)
                if active:
                    active["current_progress"] = (
                        "Paused between dates while a live NFL run finishes.")
            await asyncio.sleep(5)
            continue
        persist_job = None
        finished = False
        with _NFL_HIST_BATCH_LOCK:
            job = _NFL_HIST_BATCHES.get(job_id)
            if not job:
                return
            pending = [
                d for d in job.get("dates", [])
                if d not in job.get("completed_dates", [])
                and d not in {x.get("date") for x in job.get("failures", [])}
            ]
            if not pending:
                job["status"] = "completed" if not job.get("failures") else "failed"
                job["current_date"] = None
                job["current_progress"] = (
                    "Season replay complete."
                    if job["status"] == "completed"
                    else "Season replay finished with failed dates."
                )
                job["finished_at"] = datetime.now(timezone.utc).isoformat()
                persist_job = job
                finished = True
            else:
                date_str = pending[0]
                job["status"] = "running"
                job["current_date"] = date_str
                job["current_progress"] = f"Starting historical replay for {date_str}…"
                persist_job = job
        if persist_job is not None:
            # Supabase uses synchronous httpx helpers; never await it while
            # holding the threading lock (the worker would need that lock to
            # serialize its payload).
            await asyncio.to_thread(_nfl_batch_persist, persist_job)
        if finished:
            return

        def progress(message):
            with _NFL_HIST_BATCH_LOCK:
                active = _NFL_HIST_BATCHES.get(job_id)
                if active:
                    active["current_progress"] = str(message)

        try:
            result = await asyncio.wait_for(
                run_pipeline(
                    date_str, progress=progress, simulate=True,
                    system=job.get("system", "OLD")),
                timeout=360,
            )
            error = result.get("error") if isinstance(result, dict) else "Invalid replay result"
            if error:
                raise RuntimeError(str(error))
            expected_games = int((job.get("games_by_date") or {}).get(date_str) or 0)
            actual_games = len(result.get("games") or []) if isinstance(result, dict) else 0
            if expected_games and actual_games != expected_games:
                raise RuntimeError(
                    f"Schedule completeness check failed: expected {expected_games} games, "
                    f"replay returned {actual_games}"
                )
            if not result.get("historicalSaved"):
                raise RuntimeError("Historical Analysis save was not confirmed")
            if not result.get("historicalCoachSaved"):
                raise RuntimeError("Historical Edge Coach save was not confirmed")
            persist_job = None
            with _NFL_HIST_BATCH_LOCK:
                active = _NFL_HIST_BATCHES.get(job_id)
                if active:
                    active["completed_dates"].append(date_str)
                    active["current_progress"] = f"Completed historical replay for {date_str}."
                    persist_job = active
            if persist_job is not None:
                await asyncio.to_thread(_nfl_batch_persist, persist_job)
        except Exception as exc:
            persist_job = None
            with _NFL_HIST_BATCH_LOCK:
                active = _NFL_HIST_BATCHES.get(job_id)
                if active:
                    failures = active.setdefault("failures", [])
                    existing = next((x for x in failures if x.get("date") == date_str), None)
                    attempts = int((existing or {}).get("attempts") or 0) + 1
                    item = {"date": date_str, "error": str(exc), "attempts": attempts}
                    if existing:
                        failures[failures.index(existing)] = item
                    else:
                        failures.append(item)
                    active["current_progress"] = f"Failed {date_str}: {exc}"
                    persist_job = active
            if persist_job is not None:
                await asyncio.to_thread(_nfl_batch_persist, persist_job)

@app.get("/api/nfl/historical-batch/estimate")
async def nfl_historical_batch_estimate(
    request: Request, season: int = 0, token: str = "", admin: str = "",
    system: str = "OLD"
):
    if not _nfl_batch_admin_ok(request, token, admin):
        raise HTTPException(status_code=403, detail="Admin only")
    selected = _nfl_batch_season_year(season)
    schedule = await _nfl_season_schedule(selected)
    if not schedule["dates"]:
        raise HTTPException(status_code=404, detail="No completed game dates found for that season")
    if len(schedule["dates"]) > _NFL_BATCH_MAX_SEASON_DATES:
        raise HTTPException(status_code=400, detail="Season contains more dates than the batch limit")
    payload = {
        "season": selected,
        "dates": schedule["dates"],
        "date_count": len(schedule["dates"]),
        "games_total": schedule["games_total"],
        "estimated_odds_api_calls": _nfl_batch_odds_bound(schedule),
        "odds_bound_note": (
            "Retry-inclusive ceiling: 2 historical event snapshots per date plus "
            "5 historical Odds API calls per game. The normal no-retry estimate is "
            "2 per date plus 3 per game; cached lines reduce usage."
        ),
        "historical_only": True,
    }
    if str(system).upper() == "NEW":
        payload["system"] = "NEW"
    return payload

@app.post("/api/nfl/historical-batch")
async def nfl_historical_batch_start(request: Request):
    body = await request.json() if request.headers.get("content-type", "").startswith("application/json") else {}
    if not _nfl_batch_admin_ok(request, body.get("token", ""), body.get("admin", "")):
        raise HTTPException(status_code=403, detail="Admin only")
    selected = _nfl_batch_season_year(body.get("season"))
    system = "NEW" if str(body.get("system") or "OLD").upper() == "NEW" else "OLD"
    schedule = await _nfl_season_schedule(selected)
    dates = schedule.get("dates") or []
    if not dates:
        raise HTTPException(status_code=404, detail="No completed game dates found for that season")
    if len(dates) > _NFL_BATCH_MAX_SEASON_DATES:
        raise HTTPException(status_code=400, detail="Season contains more dates than the batch limit")
    with _NFL_HIST_BATCH_LOCK:
        running = next(
            (item for item in _NFL_HIST_BATCHES.values()
             if item.get("status") in ("queued", "running")
             and str(item.get("system") or "OLD") == system),
            None,
        )
        restored = False
        if not running:
            running = _nfl_batch_restore_active(system)
            if running:
                restored = True
                _NFL_HIST_BATCHES[running["job_id"]] = running
        if running:
            if restored and running.get("status") in ("queued", "running"):
                running["status"] = "queued"
                asyncio.create_task(_nfl_run_historical_batch(running["job_id"]))
            return JSONResponse({"job": _nfl_batch_public(running), "already_running": True}, status_code=409)
        job_id = str(uuid.uuid4())[:8]
        job = {
            "job_id": job_id,
            "status": "queued",
            "season": selected,
            "system": system,
            "dates": dates,
            "games_by_date": dict(schedule.get("games_by_date") or {}),
            "completed_dates": [],
            "failures": [],
            "current_date": None,
            "current_progress": "Queued — historical replays run one date at a time.",
            "estimated_odds_api_calls": _nfl_batch_odds_bound(schedule),
            "odds_bound_note": (
                "Retry-inclusive ceiling: 2 historical event snapshots per date plus "
                "5 historical Odds API calls per game. Normal no-retry usage is "
                "2 per date plus 3 per game; cached lines reduce usage."
            ),
            "started_at": datetime.now(timezone.utc).isoformat(),
            "finished_at": None,
            "retry_count": 0,
        }
        _NFL_HIST_BATCHES[job_id] = job
        _nfl_batch_persist(job)
    asyncio.create_task(_nfl_run_historical_batch(job_id))
    return {"job": _nfl_batch_public(job), "already_running": False}

@app.get("/api/nfl/historical-batch/{job_id}")
async def nfl_historical_batch_status(
    job_id: str, request: Request, token: str = "", admin: str = "",
    system: str = "OLD"
):
    if not _nfl_batch_admin_ok(request, token, admin):
        raise HTTPException(status_code=403, detail="Admin only")
    with _NFL_HIST_BATCH_LOCK:
        job = _NFL_HIST_BATCHES.get(job_id)
        if job and str(job.get("system") or "OLD") != (
                "NEW" if str(system).upper() == "NEW" else "OLD"):
            raise HTTPException(status_code=404, detail="Historical batch not found")
        if not job:
            job = _nfl_batch_restore(job_id, system)
            if not job:
                raise HTTPException(status_code=404, detail="Historical batch not found")
            _NFL_HIST_BATCHES[job_id] = job
            if job.get("status") in ("queued", "running"):
                job["status"] = "queued"
                asyncio.create_task(_nfl_run_historical_batch(job_id))
        return _nfl_batch_public(job)

@app.post("/api/nfl/historical-batch/{job_id}/retry")
async def nfl_historical_batch_retry(job_id: str, request: Request):
    body = await request.json() if request.headers.get("content-type", "").startswith("application/json") else {}
    if not _nfl_batch_admin_ok(request, body.get("token", ""), body.get("admin", "")):
        raise HTTPException(status_code=403, detail="Admin only")
    requested = body.get("dates") or []
    system = "NEW" if str(body.get("system") or "OLD").upper() == "NEW" else "OLD"
    with _NFL_HIST_BATCH_LOCK:
        job = _NFL_HIST_BATCHES.get(job_id)
        if job and str(job.get("system") or "OLD") != system:
            raise HTTPException(status_code=404, detail="Historical batch not found")
        if not job:
            job = _nfl_batch_restore(job_id, system)
            if job:
                _NFL_HIST_BATCHES[job_id] = job
        if not job:
            raise HTTPException(status_code=404, detail="Historical batch not found")
        if job.get("status") in ("queued", "running"):
            raise HTTPException(status_code=409, detail="Batch is still running")
        failure_dates = [x.get("date") for x in job.get("failures", [])]
        dates = [d for d in requested if d in failure_dates] if requested else failure_dates
        if not dates:
            raise HTTPException(status_code=400, detail="There are no failed dates to retry")
        job["failures"] = [x for x in job.get("failures", []) if x.get("date") not in dates]
        job["retry_count"] = int(job.get("retry_count") or 0) + 1
        job["status"] = "queued"
        job["finished_at"] = None
        job["current_progress"] = f"Queued {len(dates)} failed date(s) for retry."
        _nfl_batch_persist(job)
    asyncio.create_task(_nfl_run_historical_batch(job_id))
    return {"job": _nfl_batch_public(job)}

# ── NFL Game Predictor matchup history ─────────────────────────────────────────
# This is free nfl-verse schedule data only — it does not touch the Odds API.
# The history loads only after the user opens a predictor card and is cached.
_NFL_H2H_CACHE: dict = {}
_NFL_H2H_TTL = 24 * 3600
_NFL_GP_HISTORY_TIMEOUT = 18
_NFL_GAMES_HISTORY: list = []
_NFL_GAMES_HISTORY_TS = 0.0
_NFL_GAMES_HISTORY_LOCK = asyncio.Lock()
_NFL_GAMES_HISTORY_URL = (
    "https://github.com/nflverse/nflverse-data/releases/download/schedules/games.csv"
)
_NFL_HISTORY_TEAM_ALIASES = {
    "LA": "LAR", "STL": "LAR", "SD": "LAC", "OAK": "LV", "WAS": "WSH",
}

def _nfl_history_team(abbr: str) -> str:
    code = str(abbr or "").upper().strip()
    return _NFL_HISTORY_TEAM_ALIASES.get(code, code)

def _nfl_score_value(value):
    try:
        if isinstance(value, dict):
            value = value.get("value", value.get("displayValue"))
        return int(float(str(value).replace(",", "").strip()))
    except Exception:
        return None

def _nfl_history_date_label(iso_date: str) -> str:
    try:
        return datetime.fromisoformat(iso_date.replace("Z", "+00:00")).strftime("%b %-d, %Y")
    except Exception:
        return str(iso_date or "")[:10]

async def _load_nfl_games_history() -> list:
    """Load nfl-verse's single all-games schedule file once per day."""
    global _NFL_GAMES_HISTORY, _NFL_GAMES_HISTORY_TS
    now = time.time()
    if _NFL_GAMES_HISTORY and now - _NFL_GAMES_HISTORY_TS < _NFL_H2H_TTL:
        return _NFL_GAMES_HISTORY
    async with _NFL_GAMES_HISTORY_LOCK:
        now = time.time()
        if _NFL_GAMES_HISTORY and now - _NFL_GAMES_HISTORY_TS < _NFL_H2H_TTL:
            return _NFL_GAMES_HISTORY
        try:
            async with httpx.AsyncClient(timeout=30, follow_redirects=True) as c:
                r = await c.get(_NFL_GAMES_HISTORY_URL)
            if not r.is_success:
                return []
            # CSV decoding can be sizeable on a cold deploy; keep it off the
            # loop just like the later matchup filtering.
            rows = await asyncio.to_thread(
                lambda: list(csv.DictReader(
                    io.StringIO(r.content.decode("utf-8-sig")))))
            if rows:
                _NFL_GAMES_HISTORY = rows
                _NFL_GAMES_HISTORY_TS = now
            return rows
        except Exception as e:
            print(f"[NFL H2H] Schedule history failed: {e}")
            return []

def _nfl_game_history_payload(home: str, away: str, before_date: str,
                              schedule_rows: list) -> dict:
    """Filter/shape one matchup from the cached schedule off the event loop."""
    meetings = []
    for row in schedule_rows:
        raw_home = str(row.get("home_team") or "").upper()
        raw_away = str(row.get("away_team") or "").upper()
        h_team = _nfl_history_team(raw_home)
        a_team = _nfl_history_team(raw_away)
        if {h_team, a_team} != {home, away}:
            continue
        iso_date = str(row.get("gameday") or "")
        if before_date and iso_date >= before_date:
            continue
        hs = _nfl_score_value(row.get("home_score"))
        a_s = _nfl_score_value(row.get("away_score"))
        if hs is None or a_s is None:
            continue
        winner = h_team if hs > a_s else (a_team if a_s > hs else "TIE")
        meetings.append({
            "event_id": str(row.get("game_id") or ""),
            "date": iso_date,
            "date_label": _nfl_history_date_label(iso_date),
            "season": _nfl_score_value(row.get("season")),
            "season_type": str(row.get("game_type") or "REG").upper(),
            "week": _nfl_score_value(row.get("week")),
            "home_abbr": h_team, "away_abbr": a_team,
            "home_score": hs, "away_score": a_s,
            "winner": winner,
            "venue": str(row.get("stadium") or "Stadium unavailable"),
            "city_state": "",
        })
    meetings.sort(key=lambda x: x.get("date", ""), reverse=True)
    return {"games": meetings[:5], "home_abbr": home, "away_abbr": away}

async def get_nfl_game_history(home_abbr: str, away_abbr: str,
                               before_date: str = "") -> dict:
    """Return the five most recent completed meetings before the selected game.
    ESPN team schedules give us venue, home/away, final scores, and winner
    without making any additional sportsbook request."""
    home = str(home_abbr or "").upper().strip()
    away = str(away_abbr or "").upper().strip()
    if not home or not away or home == away:
        return {"games": [], "error": "Invalid matchup"}
    key = f"{away}@{home}:{before_date or _cur_season}"
    now = time.time()
    cached = _NFL_H2H_CACHE.get(key)
    if cached and now - cached.get("ts", 0) < _NFL_H2H_TTL:
        return cached.get("payload", {"games": []})

    schedule_rows = await _load_nfl_games_history()
    payload = await asyncio.to_thread(
        _nfl_game_history_payload, home, away, before_date, schedule_rows)
    _NFL_H2H_CACHE[key] = {"ts": now, "payload": payload}
    return payload

@app.get("/api/nfl/game-history")
async def nfl_game_history(home: str = "", away: str = "", before: str = "",
                            system: str = "OLD"):
    return await get_nfl_game_history(home, away, before)

# ── Current post-preseason roster ─────────────────────────────────────────────
# Week 1 cannot rely on nfl-verse's latest team column: the new season has no
# regular-season rows yet, so traded/free-agent players still carry last year's
# team. ESPN's roster is current after final preseason cuts. Sportsbook props
# remain the expected-game lineup; this map assigns those players to the right
# team and excludes explicit inactive/practice-squad listings.
_NFL_ROSTER_CACHE: dict = {}
_NFL_ROSTER_TTL = 15 * 60

def _nfl_injury_status(athlete: dict) -> tuple:
    """Return normalized status, note, and participation probability."""
    status = athlete.get("status") or {}
    parts = [status.get("type"), status.get("name"), status.get("description")]
    for injury in athlete.get("injuries") or []:
        parts.extend([
            injury.get("status"), injury.get("type"), injury.get("details"),
            injury.get("shortComment"), injury.get("longComment"),
        ])
    text = " ".join(str(x or "") for x in parts).strip()
    low = text.lower().replace("_", " ")
    token = re.sub(r"[^a-z0-9]+", "", low)
    if any(x in token for x in ("injuredreserve", "suspended",
                                "practicesquad")):
        return "OUT", text or "Unavailable", 0.0
    if "out" in low or "inactive" in low:
        return "OUT", text or "Out", 0.0
    if "doubtful" in low:
        return "DOUBTFUL", text or "Doubtful", 0.25
    if "questionable" in low or "game time" in low or "day-to-day" in low:
        return "QUESTIONABLE", text or "Questionable", 0.65
    if "probable" in low or "limited" in low:
        return "LIMITED", text or "Limited/Probable", 0.9
    return "ACTIVE", text or "Active", 1.0

def _nfl_position_group(value: str) -> str:
    pos = str(value or "").upper()
    return "RB" if pos in ("RB", "HB", "FB") else pos

def _nfl_depth_chart_map(payload: dict) -> dict:
    """Return ESPN athlete id -> offensive depth metadata.

    ESPN's core depth-chart endpoint is unofficial and has used both `athletes`
    and `items` containers. Parse either shape and fail neutral when fields move.
    """
    out = {}
    for chart in (payload or {}).get("items") or []:
        chart_name = str(chart.get("name") or chart.get("displayName") or "")
        chart_low = chart_name.lower()
        if "defense" in chart_low or "special" in chart_low:
            continue
        positions = chart.get("positions") or {}
        if isinstance(positions, list):
            positions = {str(i): row for i, row in enumerate(positions)}
        for slot_key, slot in positions.items():
            if not isinstance(slot, dict):
                continue
            pos_obj = slot.get("position") or {}
            position = str(
                pos_obj.get("abbreviation") or pos_obj.get("name")
                or slot.get("abbreviation") or slot_key or "").upper()
            entries = (slot.get("athletes") or slot.get("items")
                       or slot.get("entries") or [])
            if isinstance(entries, dict):
                entries = list(entries.values())
            for index, entry in enumerate(entries):
                if not isinstance(entry, dict):
                    continue
                athlete = entry.get("athlete") or entry.get("player") or entry
                if not isinstance(athlete, dict):
                    athlete = {}
                athlete_id = str(athlete.get("id") or entry.get("athleteId") or "")
                ref = str(athlete.get("$ref") or entry.get("$ref") or "")
                if not athlete_id and ref:
                    match = re.search(r"/athletes/(\d+)", ref)
                    athlete_id = match.group(1) if match else ""
                if not athlete_id:
                    continue
                rank = entry.get("rank")
                if rank is None:
                    rank = entry.get("slot")
                if rank is None:
                    rank = entry.get("order")
                try:
                    rank = max(1, int(rank))
                except (TypeError, ValueError):
                    rank = index + 1
                existing = out.get(athlete_id)
                candidate = {
                    "depth_rank": rank, "depth_position": position,
                    "depth_chart": chart_name or "ESPN offensive depth chart",
                }
                if existing is None or rank < existing.get("depth_rank", 999):
                    out[athlete_id] = candidate
    return out

def _apply_nfl_injury_context(lines: list, roster_map: dict) -> None:
    """Stamp availability and conservative same-position opportunity changes."""
    by_group = {}
    for info in (roster_map or {}).values():
        key = (info.get("team", ""), _nfl_position_group(info.get("position")))
        if all(key):
            by_group.setdefault(key, []).append(info)
    market_ok = {
        "player_rush_yds", "player_rush_reception_yds",
        "player_rush_attempts", "player_anytime_td",
        "player_reception_yds", "player_receptions",
    }
    # Conservative scenario scale for a same-position teammate absence.
    # Multiple unavailable teammates still cannot exceed the 10% total cap.
    base_share = {"RB": 0.10, "WR": 0.10, "TE": 0.10}
    status_weight = {"OUT": 1.0, "DOUBTFUL": 0.75,
                     "QUESTIONABLE": 0.40, "LIMITED": 0.20}
    caps = {"RB": 0.10, "WR": 0.10, "TE": 0.10}
    # Depths at or beyond these positions are not promoted into premium boards.
    # WR3 remains eligible because three-receiver personnel is a normal starting
    # package; TE3/RB3 and backup quarterbacks are materially different roles.
    depth_avoid = {"QB": 2, "RB": 3, "TE": 3, "WR": 5}
    depth_watch = {"RB": 2, "TE": 2, "WR": 4}
    for line in lines:
        info = roster_map.get(_norm(line.get("name", ""))) if roster_map else None
        line["availability_verified"] = bool(info)
        line["coach_eligible"] = bool(info and info.get("eligible", True))
        line["injury_status"] = (info or {}).get("injury_status", "UNVERIFIED")
        line["injury_note"] = (info or {}).get("injury_note",
                                                "Player not verified on current ESPN roster")
        line["injury_updated_at"] = (info or {}).get("injury_updated_at")
        line["participation_probability"] = (info or {}).get(
            "participation_probability")
        line["roster_experience_years"] = (info or {}).get(
            "experience_years")
        line["rookie_verified"] = bool(
            info and info.get("rookie_verified"))
        line["is_rookie"] = bool(
            info and info.get("rookie_verified")
            and info.get("is_rookie"))
        position = _nfl_position_group((info or {}).get("position"))
        depth_rank = (info or {}).get("depth_rank")
        depth_position = (info or {}).get("depth_position") or position
        line["depth_rank"] = depth_rank
        line["depth_position"] = depth_position
        line["depth_chart"] = (info or {}).get("depth_chart", "")
        line["depth_updated_at"] = (info or {}).get("depth_updated_at")
        risk_status, risk_reasons, block_premium = "CLEAR", [], False
        player_status = (info or {}).get("injury_status", "UNVERIFIED")
        if info and (not info.get("eligible", True) or player_status == "OUT"):
            risk_status, block_premium = "AVOID", True
            risk_reasons.append(
                (info or {}).get("injury_note") or "Unavailable on current ESPN roster")
        elif player_status == "DOUBTFUL":
            risk_status, block_premium = "AVOID", True
            risk_reasons.append((info or {}).get("injury_note") or "Doubtful")
        elif player_status in ("QUESTIONABLE", "LIMITED"):
            risk_status = "WATCH"
            risk_reasons.append((info or {}).get("injury_note") or player_status.title())
        try:
            depth_rank_int = int(depth_rank)
        except (TypeError, ValueError):
            depth_rank_int = None
        if depth_rank_int is not None:
            if position in depth_avoid and depth_rank_int >= depth_avoid[position]:
                risk_status, block_premium = "AVOID", True
                risk_reasons.append(
                    f"ESPN depth chart lists {position}{depth_rank_int}")
            elif position in depth_watch and depth_rank_int >= depth_watch[position]:
                if risk_status == "CLEAR":
                    risk_status = "WATCH"
                risk_reasons.append(
                    f"ESPN depth chart lists {position}{depth_rank_int}")
        if not info:
            risk_status = "UNVERIFIED"
            risk_reasons = ["Current ESPN roster/depth status unavailable"]
        line["role_risk_status"] = risk_status
        line["role_risk_reasons"] = risk_reasons
        line["role_risk_block_premium"] = block_premium
        line["role_risk_source"] = (
            "ESPN roster + offensive depth chart" if depth_rank_int is not None
            else "ESPN roster")
        factor, reasons = 1.0, []
        if info and line.get("market") in market_ok and position in base_share:
            for mate in by_group.get((info.get("team", ""), position), []):
                if mate.get("name_norm") == _norm(line.get("name", "")):
                    continue
                status = mate.get("injury_status", "ACTIVE")
                weight = status_weight.get(status, 0)
                if weight <= 0:
                    continue
                bump = base_share[position] * weight
                factor += bump
                reasons.append({
                    "player": mate.get("name", "Teammate"), "status": status,
                    "position": position, "bump_pct": round(bump * 100, 1),
                })
            factor = min(factor, 1.0 + caps[position])
        line["injury_opportunity_factor"] = round(factor, 4)
        line["injury_opportunity_reasons"] = reasons

async def get_espn_roster_map(espn_games: List[Dict], date_str: str) -> dict:
    """Return normalized player name -> current roster metadata for slate teams.
    Used only for current/future games in the active season; historical runs keep
    their date-appropriate nfl-verse team history."""
    today = _nfl_today()
    try:
        if date_str < today or int(date_str[:4]) != _cur_season:
            return {}
    except Exception:
        return {}
    team_specs = {}
    for game in espn_games:
        for side in ("home", "away"):
            abbr = str(game.get(f"{side}_abbr") or "")
            if abbr:
                team_specs[abbr] = str(game.get(f"{side}_team_id") or "")
    teams = sorted(team_specs)
    now = time.time()

    async def _one(team):
        cached = _NFL_ROSTER_CACHE.get(team)
        if cached and now - cached.get("ts", 0) < _NFL_ROSTER_TTL:
            return cached.get("players", {})
        players = {}
        try:
            async with httpx.AsyncClient(timeout=12) as c:
                roster_call = c.get(
                    f"https://site.api.espn.com/apis/site/v2/sports/football/nfl/teams/{team}/roster")
                team_id = team_specs.get(team) or team
                depth_call = c.get(
                    "https://sports.core.api.espn.com/v2/sports/football/"
                    f"leagues/nfl/seasons/{_cur_season}/teams/{team_id}/depthcharts")
                roster_result, depth_result = await asyncio.gather(
                    roster_call, depth_call, return_exceptions=True)
            r = roster_result if isinstance(roster_result, httpx.Response) else None
            depth_map = {}
            if isinstance(depth_result, httpx.Response) and depth_result.is_success:
                depth_map = _nfl_depth_chart_map(depth_result.json())
            if r is not None and r.is_success:
                for group in r.json().get("athletes", []):
                    bucket = str(group.get("position") or "")
                    for athlete in group.get("items", []):
                        name = str(athlete.get("fullName") or "").strip()
                        if not name:
                            continue
                        status = athlete.get("status") or {}
                        pos = athlete.get("position") or {}
                        athlete_id = str(athlete.get("id") or "")
                        status_type = str(status.get("type") or "").lower()
                        injury_status, injury_note, participation = (
                            _nfl_injury_status(athlete))
                        experience = athlete.get("experience") or {}
                        experience_years = experience.get("years")
                        try:
                            experience_years = int(experience_years)
                            rookie_verified = experience_years >= 0
                        except (TypeError, ValueError):
                            experience_years = None
                            rookie_verified = False
                        eligible = (bucket in ("offense", "defense", "specialTeam")
                                    and status_type not in
                                    ("injuredreserve", "out", "suspended", "practicesquad")
                                    and injury_status != "OUT")
                        depth = depth_map.get(athlete_id) or {}
                        players[_norm(name)] = {
                            "team": team, "eligible": eligible,
                            "bucket": bucket,
                            "position": str(pos.get("abbreviation") or ""),
                            "name": name, "name_norm": _norm(name),
                            "injury_status": injury_status,
                            "injury_note": injury_note,
                            "participation_probability": participation,
                            "experience_years": experience_years,
                            "rookie_verified": rookie_verified,
                            "is_rookie": bool(
                                rookie_verified and experience_years == 0),
                            "athlete_id": athlete_id,
                            "depth_rank": depth.get("depth_rank"),
                            "depth_position": depth.get("depth_position"),
                            "depth_chart": depth.get("depth_chart", ""),
                            "depth_updated_at": (
                                datetime.now(timezone.utc).isoformat()
                                if depth else None),
                            "injury_updated_at": datetime.now(
                                timezone.utc).isoformat(),
                        }
        except Exception as e:
            print(f"[Roster] {team} failed: {e}")
        if players:
            _NFL_ROSTER_CACHE[team] = {"ts": now, "players": players}
        return players

    out = {}
    for team_players in await asyncio.gather(*[_one(t) for t in teams]):
        out.update(team_players)
    print(f"[Roster] {len(out)} current players across {len(teams)} slate teams")
    return out

# ── Odds API ───────────────────────────────────────────────────────────────────
async def get_odds_events(date_str: str, espn_games: List[Dict]) -> List[Dict]:
    if not ODDS_API_KEY: return []
    today    = _nfl_today()
    tomorrow = (datetime.fromisoformat(date_str) + timedelta(days=1)).strftime("%Y-%m-%d")
    def _match_events(odds_evs):
        matched = 0
        for g in espn_games:
            if g.get("id"):
                matched += 1
                continue
            for ev in odds_evs:
                if (_match(g["home_team"], ev.get("home_team", "")) and
                        _match(g["away_team"], ev.get("away_team", ""))):
                    g["id"] = ev.get("id", "")
                    matched += 1
                    break
        return matched
    try:
        async with httpx.AsyncClient(timeout=15) as c:
            if date_str >= today:
                r = await c.get(f"{ODDS_BASE}/sports/americanfootball_nfl/events",
                    params={"apiKey": ODDS_API_KEY, "dateFormat": "iso",
                            "commenceTimeFrom": f"{date_str}T00:00:00Z",
                            "commenceTimeTo":   f"{tomorrow}T06:00:00Z"})
                odds_evs = r.json() if r.is_success and isinstance(r.json(), list) else []
                matched = _match_events(odds_evs)
                print(f"[OddsAPI events] HTTP {r.status_code} found={len(odds_evs)} matched={matched}/{len(espn_games)}")
            else:
                # Try two snapshots: pre-game (T18:00:00Z = 1pm ET) then post-game (next day T04:00:00Z).
                # T18:00:00Z catches lines before any kickoff; the next-day fallback grabs games
                # that didn't have odds until later (e.g. night playoff games).
                for snap in [f"{date_str}T12:00:00Z", f"{date_str}T20:00:00Z"]:
                    r = await c.get(f"{ODDS_BASE}/historical/sports/americanfootball_nfl/events",
                        params={"apiKey": ODDS_API_KEY, "date": snap, "dateFormat": "iso"})
                    data = r.json()
                    odds_evs = data.get("data", data) if isinstance(data, dict) else []
                    odds_evs = odds_evs if isinstance(odds_evs, list) else []
                    matched = _match_events(odds_evs)
                    print(f"[OddsAPI events] snap={snap} found={len(odds_evs)} matched={matched}/{len(espn_games)}")
                    if matched >= len(espn_games):
                        break   # all matched, no need for second snapshot
            return espn_games
    except Exception as e:
        print(f"[OddsAPI events] {e}"); return espn_games

_NFL_PROP_FETCH_STATUS = {}

async def get_prop_lines(event_id: str, date_str: str,
                         alternate_only: bool = False) -> List[Dict]:
    """Fetch player prop lines for one NFL game. Returns a list of prop dicts.
    Kept as a props-only call (PROP_MARKETS only) so it stays within Odds API
    plan market limits. Game-level lines (h2h/totals) are fetched separately."""
    fetch_key = (str(event_id), str(date_str), bool(alternate_only))
    _NFL_PROP_FETCH_STATUS[fetch_key] = "error"
    if not event_id or not ODDS_API_KEY: return []
    today = _nfl_today()
    is_past = date_str < today
    try:
        async with httpx.AsyncClient(timeout=20) as c:
            requested_markets = ALT_PROP_MARKETS if alternate_only else PROP_MARKETS
            if is_past:
                base = f"{ODDS_BASE}/historical/sports/americanfootball_nfl/events/{event_id}/odds"
                params = {"apiKey": ODDS_API_KEY, "bookmakers": ODDS_BOOKMAKERS,
                         "markets": ",".join(requested_markets), "oddsFormat": "american",
                         "date": f"{date_str}T12:00:00Z"}
            else:
                base = f"{ODDS_BASE}/sports/americanfootball_nfl/events/{event_id}/odds"
                params = {"apiKey": ODDS_API_KEY, "bookmakers": ODDS_BOOKMAKERS,
                         "markets": ",".join(requested_markets), "oddsFormat": "american"}
            r = None
            for attempt in range(3):
                try:
                    r = await c.get(base, params=params)
                except (httpx.TimeoutException, httpx.NetworkError) as exc:
                    if attempt >= 2:
                        print(f"[OddsAPI props] {event_id} request failed: {exc}")
                        return []
                    await asyncio.sleep((attempt + 1) * .75)
                    continue
                if r.status_code in (401, 403):
                    print(f"[OddsAPI props] {event_id} permanent HTTP {r.status_code}")
                    return []
                if r.status_code == 429 or 500 <= r.status_code < 600:
                    if attempt >= 2:
                        print(f"[OddsAPI props] {event_id} HTTP {r.status_code}")
                        return []
                    retry_after = 0
                    try:
                        retry_after = min(4.0, max(0.0, float(
                            r.headers.get("Retry-After", "0"))))
                    except (TypeError, ValueError):
                        pass
                    await asyncio.sleep(retry_after or (attempt + 1) * .75)
                    continue
                if not r.is_success:
                    print(f"[OddsAPI props] {event_id} HTTP {r.status_code}")
                    return []
                try:
                    probe = r.json()
                    probe_data = (probe.get("data", probe)
                                  if isinstance(probe, dict) and "data" in probe
                                  else probe)
                    if (isinstance(probe_data, dict)
                            and isinstance(probe_data.get("bookmakers"), list)):
                        if probe_data.get("bookmakers") or attempt >= 2:
                            break
                        await asyncio.sleep((attempt + 1) * .75)
                        continue
                except (ValueError, TypeError):
                    pass
                if attempt < 2:
                    await asyncio.sleep((attempt + 1) * .75)
                    continue
                print(f"[OddsAPI props] {event_id} invalid response schema")
                return []
            raw  = r.json()
            data = raw.get("data", raw) if isinstance(raw, dict) and "data" in raw else raw
            if not isinstance(data, dict): return []
            lines = {}
            for bm in data.get("bookmakers", []):
                bkey = bm.get("key", "")
                for mkt in bm.get("markets", []):
                    raw_mk = mkt.get("key", "")
                    if raw_mk not in requested_markets: continue
                    mk = ALT_PROP_MARKET_TO_BASE.get(raw_mk, raw_mk)
                    is_alternate = raw_mk in ALT_PROP_MARKET_TO_BASE
                    for oc in mkt.get("outcomes", []):
                        name  = oc.get("description") or oc.get("name", "")
                        side  = oc.get("name", "")
                        point = oc.get("point")
                        price = oc.get("price")
                        if mk == "player_anytime_td":
                            if side in ("Yes", "No", "Over", "Under"):
                                if side != "Yes": continue
                            else:
                                name = oc.get("name", ""); side = "Yes"
                                if (oc.get("description") or "") in ("No",): continue
                            point = 0.5
                            side  = "Over"
                        if not name or point is None: continue
                        key = (
                            f"{_norm(name)}_{raw_mk}_{float(point):g}"
                            if is_alternate else f"{_norm(name)}_{mk}")
                        if key not in lines:
                            lines[key] = {"name": name, "market": mk,
                                "label": PROP_LABELS.get(mk, mk),
                                "stat_col": PROP_TO_COL.get(mk, ""),
                                "line": float(point), "over_odds": None, "under_odds": None,
                                "over_book": None, "under_book": None,
                                "source_market": raw_mk,
                                "is_alternate": is_alternate}
                        if (not is_alternate
                                and abs(float(point) - lines[key]["line"]) > 1e-9):
                            continue
                        if side == "Over":
                            _take_odds(lines[key], "over_odds", "over_book", price, bkey)
                        elif side == "Under":
                            _take_odds(lines[key], "under_odds", "under_book", price, bkey)
            out = list(lines.values())
            for l in out:
                l["over_book"]  = _book_label(l["over_book"])  if l.get("over_book")  else ""
                l["under_book"] = _book_label(l["under_book"]) if l.get("under_book") else ""
                l["quote_fetched_at"] = datetime.now(timezone.utc).isoformat()
                l["quote_status"] = "ARCHIVED" if is_past else "LIVE"
            _NFL_PROP_FETCH_STATUS[fetch_key] = "success"
            if not out:
                _NFL_PROP_FETCH_STATUS[fetch_key] = "empty"
            return out
    except Exception as e:
        print(f"[OddsAPI props] {e}"); return []

async def get_nfl_game_lines(event_id: str, date_str: str) -> dict:
    """Fetch moneyline (h2h) + totals for one NFL game — separate call so it
    never competes with the player-prop market quota."""
    if not event_id or not ODDS_API_KEY: return {}
    today = _nfl_today()
    is_past = date_str < today
    try:
        async with httpx.AsyncClient(timeout=15) as c:
            if is_past:
                base   = f"{ODDS_BASE}/historical/sports/americanfootball_nfl/events/{event_id}/odds"
                params = {"apiKey": ODDS_API_KEY, "bookmakers": ODDS_BOOKMAKERS,
                          "markets": "h2h,totals", "oddsFormat": "american",
                          "date": f"{date_str}T12:00:00Z"}
            else:
                base   = f"{ODDS_BASE}/sports/americanfootball_nfl/events/{event_id}/odds"
                params = {"apiKey": ODDS_API_KEY, "bookmakers": ODDS_BOOKMAKERS,
                          "markets": "h2h,totals", "oddsFormat": "american"}
            r = await c.get(base, params=params)
            if not r.is_success: return {}
            raw  = r.json()
            data = raw.get("data", raw) if isinstance(raw, dict) and "data" in raw else raw
            if not isinstance(data, dict): return {}
            res = {"away_ml": None, "home_ml": None, "away_ml_book": None, "home_ml_book": None,
                   "total_line": None, "total_over_odds": None, "total_under_odds": None,
                   "_tot_over_book": None, "_tot_under_book": None}
            home_team = data.get("home_team", "")
            away_team = data.get("away_team", "")
            for bm in data.get("bookmakers", []):
                bkey = bm.get("key", "")
                for mkt in bm.get("markets", []):
                    mk = mkt.get("key", "")
                    if mk == "h2h":
                        for oc in mkt.get("outcomes", []):
                            nm = oc.get("name", ""); price = oc.get("price")
                            if _match(nm, home_team):
                                _take_odds(res, "home_ml", "home_ml_book", price, bkey)
                            elif _match(nm, away_team):
                                _take_odds(res, "away_ml", "away_ml_book", price, bkey)
                    elif mk == "totals":
                        for oc in mkt.get("outcomes", []):
                            side = oc.get("name",""); point = oc.get("point"); price = oc.get("price")
                            if point is not None:
                                if res["total_line"] is None:
                                    res["total_line"] = float(point)
                                if side == "Over":
                                    _take_odds(res, "total_over_odds", "_tot_over_book", price, bkey)
                                elif side == "Under":
                                    _take_odds(res, "total_under_odds", "_tot_under_book", price, bkey)
            res["away_ml_book"] = _book_label(res["away_ml_book"]) if res.get("away_ml_book") else ""
            res["home_ml_book"] = _book_label(res["home_ml_book"]) if res.get("home_ml_book") else ""
            res["total_over_book"] = _book_label(res.pop("_tot_over_book")) if res.get("_tot_over_book") else ""
            res["total_under_book"] = _book_label(res.pop("_tot_under_book")) if res.get("_tot_under_book") else ""
            return res
    except Exception as e:
        print(f"[GP GameLines] {e}"); return {}

# Keep a small candidate pool for each team/market before running the expensive
# history analysis. The final starter filter below still chooses one player, but
# there is no value in analyzing every backup and deep-roster prop first.
_MAX_PROP_CANDIDATES_PER_TEAM_MARKET = 3
_DEFENSIVE_PROP_MARKETS = {
    "player_tackles_assists", "player_sacks", "player_defensive_interceptions",
}

def _limit_prop_candidates(lines: list, volume_maps: dict,
                           latest_team: dict) -> list:
    """Apply per-team candidate limits after dataframe stats are summarized."""
    groups = {}
    for idx, line in enumerate(lines):
        name = _nfl_player_identity_key(line.get("name"))
        market = line.get("market") or ""
        home = line.get("home_abbr") or ""
        away = line.get("away_abbr") or ""
        team = line.get("roster_team") or (latest_team.get(name) or ((0, ""), ""))[1]
        if team not in (home, away):
            # Match the analyzer's conservative traded-player fallback.
            team = home or away or ""
        stat_col = line.get("stat_col") or ""
        score = volume_maps.get(stat_col, {}).get(name, 0) or 0
        limit = _MAX_PROP_CANDIDATES_PER_TEAM_MARKET
        if market in _DEFENSIVE_PROP_MARKETS:
            # Defensive boards need depth across the active unit rather
            # than one volume leader. Five per team allows up to ten
            # genuine candidates from each matchup before side ranking.
            limit = 5
            position_group = "PRIMARY"
        elif market == "player_anytime_td":
            position = str(line.get("roster_position") or "").upper().strip()
            if position == "QB":
                position_group = "QB"
                limit = 1
            elif position == "RB":
                position_group = "RB"
                limit = 1
            elif position == "WR":
                position_group = "WR"
                limit = 3
            elif position == "TE":
                position_group = "TE"
                limit = 1
            else:
                continue
        else:
            position_group = "PRIMARY"
        group_key = (home, away, market, team, position_group)
        groups.setdefault(group_key, {"limit": limit, "rows": []})["rows"].append(
            (float(score), idx))

    keep = set()
    for group in groups.values():
        candidates = group["rows"]
        candidates.sort(key=lambda item: (-item[0], item[1]))
        keep.update(idx for _, idx in candidates[:group["limit"]])
    return [line for idx, line in enumerate(lines) if idx in keep]

def _trim_prop_lines(lines: list, df) -> list:
    if not lines or df is None:
        return lines
    try:
        cols = {"player_display_name", "recent_team", "season", "week"}
        if not cols.issubset(df.columns):
            return lines

        # Latest team prevents a traded player's old team from taking the
        # candidate slot for the current matchup.
        latest_team = {}
        for row in df[["player_display_name", "recent_team", "season", "week"]].itertuples(index=False):
            name = _nfl_player_identity_key(row.player_display_name)
            if not name:
                continue
            try:
                stamp = (int(row.season), int(row.week))
            except Exception:
                stamp = (0, 0)
            if name not in latest_team or stamp >= latest_team[name][0]:
                latest_team[name] = (stamp, str(row.recent_team or "").strip())

        # Career volume is the same signal used by the final starter filter.
        # Precomputing these maps keeps the reduction cheap even with thousands
        # of raw Odds API props.
        volume_maps = {}
        name_series = df["player_display_name"].map(_nfl_player_identity_key)
        for stat_col in set(PROP_TO_COL.values()):
            if stat_col not in df.columns:
                continue
            totals = df.assign(_n=name_series).groupby("_n")[stat_col].sum()
            volume_maps[stat_col] = totals.to_dict()

        return _limit_prop_candidates(lines, volume_maps, latest_team)
    except Exception as e:
        print(f"[PropTrim] skipped: {e}")
        return lines

def _analysis_prop_lines(lines: list, df) -> list:
    """Preserve every standard prop; prefilter only the Anytime TD pool."""
    standard_lines = [
        line for line in lines if line.get("market") != "player_anytime_td"
    ]
    td_lines = [
        line for line in lines if line.get("market") == "player_anytime_td"
    ]
    return standard_lines + _trim_prop_lines(td_lines, df)

# ── Analysis using nfl_data_py ─────────────────────────────────────────────────
def _espn_ha_week(season_type, week):
    """Translate nfl-verse postseason weeks (19-22) to ESPN rounds (1-4)."""
    week = int(week)
    if str(season_type or "REG").upper() == "POST" and 19 <= week <= 22:
        return week - 18
    return week

def _nflverse_week(season_type, week):
    """Translate ESPN postseason rounds to nflverse weeks 19-22.

    ESPN can insert the Pro Bowl at round 4 and label the Super Bowl round 5;
    nflverse consistently stores the Super Bowl as week 22.
    """
    week = int(week)
    if str(season_type or "REG").upper() == "POST":
        if 1 <= week <= 3:
            return week + 18
        if week in (4, 5):
            return 22
    return week

def _ha_side(row, is_home):
    if not _HA_LOADED:
        return True
    season_type = str(row.get("season_type", "REG") or "REG").upper()
    week = _espn_ha_week(season_type, row["week"])
    key = (int(row["season"]), season_type, week, str(row["recent_team"]))
    val = _HA_LOOKUP.get(key)
    if val is None:
        return True
    return val == ("HOME" if is_home else "AWAY")

def _nfl_history_venue(row) -> str:
    """Return the player's actual HOME/AWAY side for a historical stat row."""
    if not _HA_LOADED:
        return ""
    try:
        season_type = str(row.get("season_type", "REG") or "REG").upper()
        week = _espn_ha_week(season_type, row["week"])
        key = (
            int(row["season"]), season_type, week,
            str(row.get("recent_team") or ""),
        )
        side = str(_HA_LOOKUP.get(key) or "").upper()
        return side if side in {"HOME", "AWAY"} else ""
    except Exception:
        return ""

def _book_tag_nfl(pick, score, gap, under_rate):
    """SUGGESTED when the OVER side has a strong recent hit rate + edge over the
    line; FADE when the UNDER side is strong + the line sits above the average."""
    if pick == "OVER" and score is not None and score >= 65 and (gap or 0) > 0:
        return "SUGGESTED"
    if pick == "UNDER" and score is not None and score >= 65 and (gap or 0) < 0:
        return "FADE"   # score is side-aware — for UNDER picks it already measures under-hits
    return ""

def _nfl_implied_prob(odds):
    """Break-even probability for an American price, as a 0-100 percentage."""
    try:
        o = float(odds)
        if o == 0:
            return None
        return (100.0 / (o + 100.0) * 100.0) if o > 0 else (
            abs(o) / (abs(o) + 100.0) * 100.0)
    except Exception:
        return None


def _first_str(series):
    """Return the first non-empty string value in a pandas series, else ''."""
    try:
        for v in series.tolist():
            if isinstance(v, str) and v.strip():
                return v.strip()
    except Exception:
        pass
    return ""


# ── Opponent defensive strength factor ─────────────────────────────────────────
# For each offensive stat, measure how much of it every defense ALLOWS per game
# recently vs the league average. A leaky defense (>1) nudges the projection up
# (helps OVERS); a stingy one (<1) nudges it down. Clamped to ±10% — a modest
# reorder nudge, never a takeover. Computed from data already in memory: zero
# extra API calls or credits.
_OPP_ADJ_COLS = {
    "passing_yards": "pass D", "passing_tds": "pass D", "completions": "pass D",
    "attempts": "pass D", "interceptions": "INT D",
    "rushing_yards": "rush D", "rush_rec_yards": "RB total D", "carries": "rush D",
    "receiving_yards": "pass D", "receptions": "pass D",
    "anytime_td": "TD D",
}
_DEFF_CACHE: dict = {"df_ref": None, "maps": {}}
_TD_CAL_CACHE: dict = {"df_ref": None, "bins": None, "report": None}
_TD_OPP_CACHE: dict = {"df_ref": None, "values": {}}
# Standard runs, Coach warms, and historical replays can now analyze in worker
# threads.  Keep the existing serial cache semantics for pandas/model caches
# without putting the lock on the ASGI event loop.
_NFL_ANALYSIS_LOCK = _bt_th.RLock()
_NFL_ANALYSIS_EVENTS = None

def _td_mean(rows, col, default=None):
    try:
        vals = [float(v) for v in rows[col].dropna().tolist()]
        return sum(vals) / len(vals) if vals else default
    except Exception:
        return default

def _td_recent(rows, n=10):
    """Newest player/team rows with REG weeks before POST weeks each season."""
    try:
        d = rows.copy()
        if "season_type" in d.columns:
            d["_td_phase"] = d["season_type"].fillna("REG").astype(str).str.upper().map(
                {"REG": 0, "POST": 1}).fillna(0)
            return d.sort_values(["season", "_td_phase", "week"], ascending=False).head(n)
        return d.sort_values(["season", "week"], ascending=False).head(n)
    except Exception:
        return rows.head(n)

def _td_opportunity_features(pdf, df, team):
    """Point-in-time TD opportunity inputs from the retained nflverse rows.

    Weekly player stats do not currently publish goal-line carries, end-zone
    targets, or offensive snap share. We use them only when present; otherwise
    carries/targets and target_share provide the supported workload signal.
    """
    if _TD_OPP_CACHE["df_ref"] is not df:
        _TD_OPP_CACHE.update({"df_ref": df, "values": {}})
    try:
        player_key = str(pdf["player_display_name"].dropna().iloc[0]).lower()
    except Exception:
        player_key = str(id(pdf))
    cache_key = (player_key, team)
    if cache_key in _TD_OPP_CACHE["values"]:
        return dict(_TD_OPP_CACHE["values"][cache_key])
    offense_pdf = pdf[pdf["anytime_td"].notna()] if "anytime_td" in pdf.columns else pdf
    recent = _td_recent(offense_pdf, 10)
    out = {"games": len(recent)}
    carries = _td_mean(recent, "carries", 0.0) or 0.0
    targets = _td_mean(recent, "targets", 0.0) or 0.0
    out["carries"] = round(carries, 1)
    out["targets"] = round(targets, 1)
    shares = []
    for col in ("target_share", "offense_pct", "snap_share"):
        if col in recent.columns:
            v = _td_mean(recent, col)
            if v is not None:
                if v > 1.5:
                    v /= 100.0
                shares.append(max(0.0, min(1.0, v)))
                out[col] = round(v * 100, 1)
    rz = None
    for col in ("red_zone_carries", "redzone_carries", "carries_inside_10"):
        if col in recent.columns:
            rz = _td_mean(recent, col)
            if rz is not None:
                out["red_zone_carries"] = round(rz, 2)
                break
    ez = None
    for col in ("end_zone_targets", "endzone_targets"):
        if col in recent.columns:
            ez = _td_mean(recent, col)
            if ez is not None:
                out["end_zone_targets"] = round(ez, 2)
                break
    # Team scoring environment uses only rows already available before kickoff.
    team_rows = df[df["recent_team"] == team] if team and "recent_team" in df.columns else df.iloc[0:0]
    if not team_rows.empty:
        team_rows = team_rows.copy()
        if "season_type" in team_rows.columns:
            team_rows["_td_phase"] = team_rows["season_type"].fillna("REG").astype(str).str.upper().map(
                {"REG": 0, "POST": 1}).fillna(0)
            tg_cols = ["season", "_td_phase", "week"]
        else:
            tg_cols = ["season", "week"]
        tg = team_rows.groupby(tg_cols)[["rushing_tds", "receiving_tds"]].sum().reset_index()
        tg["team_td"] = tg[["rushing_tds", "receiving_tds"]].sum(axis=1)
        team_td = float(tg.sort_values(tg_cols, ascending=False).head(8)["team_td"].mean()) if len(tg) else 2.0
    else:
        team_td = 2.0
    out["team_td_per_game"] = round(team_td, 2)
    # Convert supported workload to a conservative 0..1 scorer-opportunity rate.
    volume = min(1.0, (carries + targets) / 22.0)
    share = sum(shares) / len(shares) if shares else volume
    rz_signal = min(1.0, (rz or 0.0) / 3.0) if rz is not None else None
    ez_signal = min(1.0, (ez or 0.0) / 2.0) if ez is not None else None
    components = [volume, share]
    if rz_signal is not None:
        components.extend([rz_signal, rz_signal])
    if ez_signal is not None:
        components.extend([ez_signal, ez_signal])
    out["signal"] = sum(components) / len(components)
    out["available"] = [k for k in ("target_share", "offense_pct", "snap_share",
                                      "red_zone_carries", "end_zone_targets") if k in out]
    _TD_OPP_CACHE["values"][cache_key] = dict(out)
    return out

def _td_walk_forward_calibration(df):
    """Build reliability bins from completed player-games without hindsight.

    Each example is predicted from that player's earlier games only. The first
    season is warm-up, at least five prior games are required, and each bin is
    shrunk toward its raw midpoint until it has 100 outcomes.
    """
    if _TD_CAL_CACHE["df_ref"] is df and _TD_CAL_CACHE["bins"] is not None:
        return _TD_CAL_CACHE["bins"], _TD_CAL_CACHE["report"]
    bins = {i: {"n": 0, "hits": 0, "raw_sum": 0.0} for i in range(10)}
    try:
        # Calibration only reads these columns.  Avoid carrying the complete
        # nflverse frame through the seven-season walk-forward loop.
        calibration_cols = [
            c for c in (
                "player_display_name", "recent_team", "opponent_team",
                "season", "week", "anytime_td", "season_type",
                "target_share", "carries", "targets",
            ) if c in df.columns
        ]
        d = df[calibration_cols]
        d = d[d["anytime_td"].notna()].copy()
        d = d.sort_values(["season", "week"])
        first_season = int(d["season"].min())
        history, team_history, defense_history = {}, {}, {}
        season_bins = {}
        # Process a whole week as one block. Updating state only after every
        # player in that week is predicted prevents same-week teammate leakage.
        if "season_type" in d.columns:
            d["_td_phase"] = d["season_type"].fillna("REG").astype(str).str.upper().map(
                {"REG": 0, "POST": 1}).fillna(0)
            group_cols = ["season", "_td_phase", "week"]
        else:
            group_cols = ["season", "week"]
        for _, week_rows in d.groupby(group_cols, sort=True):
            pending = []
            league_allowed = [v for vals in defense_history.values() for v in vals[-8:]]
            league_allowed_avg = (sum(league_allowed) / len(league_allowed)
                                  if league_allowed else None)
            for _, r in week_rows.iterrows():
                name = str(r.get("player_display_name") or "").lower()
                if not name:
                    continue
                h = history.setdefault(name, [])
                team = str(r.get("recent_team") or "")
                opp = str(r.get("opponent_team") or "")
                if len(h) >= 5 and int(r.get("season") or 0) > first_season:
                    recent = h[-10:]
                    td_rate = (sum(x["td"] for x in recent) + 1.0) / (len(recent) + 3.0)
                    opp_rows = [x for x in h if x["opp"] == opp]
                    opp_rate = ((sum(x["td"] for x in opp_rows) + 1.0) / (len(opp_rows) + 3.0)
                                if opp_rows else td_rate)
                    volume = min(1.0, (sum(x["carries"] + x["targets"] for x in recent)
                                       / len(recent)) / 22.0)
                    known_shares = [x["target_share"] for x in recent
                                    if x.get("target_share") is not None]
                    share = sum(known_shares) / len(known_shares) if known_shares else volume
                    opportunity = (volume + max(0.0, min(1.0, share))) / 2.0
                    team_games = team_history.get(team, [])[-8:]
                    team_rate = sum(team_games) / len(team_games) if team_games else 2.0
                    team_env = max(.65, min(1.35, team_rate / 2.6))
                    allowed = defense_history.get(opp, [])[-8:]
                    if allowed and league_allowed_avg and league_allowed_avg > 0:
                        def_factor = max(.90, min(1.10,
                            (sum(allowed) / len(allowed)) / league_allowed_avg))
                    else:
                        def_factor = 1.0
                    raw = (.50 * td_rate + .15 * opp_rate + .20 * opportunity
                           + .10 * min(1.0, team_env / 1.35) + .05 * .50)
                    raw = max(.03, min(.90, raw * def_factor))
                    season = int(r.get("season") or 0)
                    b = min(9, int(raw * 10))
                    aggregate = season_bins.setdefault(
                        season, {}).setdefault(
                            b, {"n": 0, "hits": 0, "raw_sum": 0.0})
                    aggregate["n"] += 1
                    aggregate["hits"] += int(
                        float(r.get("anytime_td") or 0) > 0)
                    aggregate["raw_sum"] += raw
                ts = r.get("target_share")
                try:
                    ts = float(ts)
                    if ts != ts:
                        ts = None
                    elif ts > 1.5:
                        ts /= 100.0
                except Exception:
                    ts = None
                td_count = float(r.get("anytime_td") or 0)
                pending.append((name, team, opp, {
                    "td": int(td_count > 0), "td_count": td_count,
                    "opp": opp, "carries": float(r.get("carries") or 0),
                    "targets": float(r.get("targets") or 0), "target_share": ts,
                }))
            team_totals = {}
            for name, team, opp, item in pending:
                history.setdefault(name, []).append(item)
                team_totals[team] = team_totals.get(team, 0.0) + item["td_count"]
            for team, total in team_totals.items():
                team_values = team_history.setdefault(team, [])
                team_values.append(total)
                del team_values[:-8]
            for team, total in team_totals.items():
                # The opponent defense allowed this team's scorer touchdowns.
                opponents = [opp for _, tm, opp, _ in pending if tm == team and opp]
                if opponents:
                    defense_values = defense_history.setdefault(opponents[0], [])
                    defense_values.append(total)
                    del defense_values[:-8]
        example_seasons = sorted(
            season for season, aggregate_bins in season_bins.items()
            if any(rec["n"] > 0 for rec in aggregate_bins.values()))
        holdout_season = example_seasons[-1] if len(example_seasons) >= 2 else None
        training_seasons = (
            [season for season in example_seasons if season < holdout_season]
            if holdout_season is not None else example_seasons)
        if not any(season_bins.get(season) for season in training_seasons):
            training_seasons = example_seasons
            holdout_season = None
        for season in training_seasons:
            for b, aggregate in season_bins.get(season, {}).items():
                bins[b]["n"] += aggregate["n"]
                bins[b]["hits"] += aggregate["hits"]
                bins[b]["raw_sum"] += aggregate["raw_sum"]
        report = []
        for b, rec in bins.items():
            midpoint = (b + .5) / 10.0
            n = rec["n"]
            actual = rec["hits"] / n if n else midpoint
            weight = min(1.0, n / 100.0)
            rec["calibrated"] = actual * weight + midpoint * (1.0 - weight)
        eval_bins = {i: {"n": 0, "hits": 0, "raw_sum": 0.0,
                         "calibrated_sum": 0.0} for i in range(10)}
        if holdout_season is not None:
            for b, aggregate in season_bins.get(holdout_season, {}).items():
                trained = bins[b]
                eval_bins[b]["n"] += aggregate["n"]
                eval_bins[b]["hits"] += aggregate["hits"]
                eval_bins[b]["raw_sum"] += aggregate["raw_sum"]
                eval_bins[b]["calibrated_sum"] += (
                    trained["calibrated"] * aggregate["n"]
                    if trained["n"] >= 25 else aggregate["raw_sum"])
        for b, rec in bins.items():
            midpoint = (b + .5) / 10.0
            n = rec["n"]
            actual = rec["hits"] / n if n else midpoint
            ev = eval_bins[b]
            report.append({
                "range": f"{b*10}-{b*10+9}%",
                "training_n": n,
                "training_predicted": round((rec["raw_sum"] / n if n else midpoint) * 100, 1),
                "training_actual": round(actual * 100, 1),
                "holdout_season": holdout_season,
                "holdout_n": ev["n"],
                "holdout_raw": round((ev["raw_sum"] / ev["n"]) * 100, 1) if ev["n"] else None,
                "holdout_predicted": round((ev["calibrated_sum"] / ev["n"]) * 100, 1) if ev["n"] else None,
                "holdout_actual": round((ev["hits"] / ev["n"]) * 100, 1) if ev["n"] else None,
            })
    except Exception as e:
        print(f"[TD calibration] failed: {e}")
        for b, rec in bins.items():
            rec["calibrated"] = (b + .5) / 10.0
        report = []
    _TD_CAL_CACHE.update({"df_ref": df, "bins": bins, "report": report})
    return bins, report

def _td_calibrated_probability(pdf, df, team, opp_abbr, def_factor):
    offense_pdf = pdf[pdf["anytime_td"].notna()] if "anytime_td" in pdf.columns else pdf
    recent = _td_recent(offense_pdf, 10)
    td_hits = int((recent["anytime_td"].fillna(0) > 0).sum())
    td_rate = (td_hits + 1.0) / (len(recent) + 3.0)
    opp_rows = (offense_pdf[offense_pdf["opponent_team"] == opp_abbr]
                if opp_abbr else offense_pdf.iloc[0:0])
    opp_hits = int((opp_rows["anytime_td"].fillna(0) > 0).sum()) if not opp_rows.empty else 0
    opp_rate = ((opp_hits + 1.0) / (len(opp_rows) + 3.0)) if len(opp_rows) else td_rate
    opportunity = _td_opportunity_features(offense_pdf, df, team)
    team_env = max(.65, min(1.35, opportunity["team_td_per_game"] / 2.6))
    raw = (.50 * td_rate + .15 * opp_rate + .20 * opportunity["signal"]
           + .10 * min(1.0, team_env / 1.35) + .05 * .50)
    raw = max(.03, min(.90, raw * def_factor))
    bins, report = _td_walk_forward_calibration(df)
    rec = bins[min(9, int(raw * 10))]
    # Sparse bins remain mostly raw; populated bins apply empirical reliability.
    calibrated = rec.get("calibrated", raw) if rec.get("n", 0) >= 25 else raw
    return round(calibrated * 100, 1), round(raw * 100, 1), opportunity, rec.get("n", 0), report

def _def_factor_map(df, stat_col: str, n_games: int = 8) -> dict:
    """{team_abbr: (factor, rank)} using the restrained defensive nudge.

    The underlying allowed-per-game ratio is deliberately shrunk toward 1.0
    before it reaches a player projection.  Defense is a supporting signal, not
    a replacement for the player's own history.
    """
    if _DEFF_CACHE["df_ref"] is not df:   # hold the object itself, not id() (reusable after gc)
        _DEFF_CACHE["df_ref"] = df
        _DEFF_CACHE["maps"] = {}
    if stat_col in _DEFF_CACHE["maps"]:
        return _DEFF_CACHE["maps"][stat_col]
    out: dict = {}
    try:
        d = df[["season", "week", "opponent_team", stat_col]].dropna(
            subset=["opponent_team", stat_col])
        d = d[d["opponent_team"].astype(str) != ""]
        g = (d.groupby(["opponent_team", "season", "week"])[stat_col].sum()
               .reset_index().sort_values(["season", "week"], ascending=False))
        per_team = {}
        for team, grp in g.groupby("opponent_team"):
            vals = grp[stat_col].head(n_games).tolist()
            if len(vals) >= 3:
                per_team[str(team)] = sum(vals) / len(vals)
        if per_team:
            lg = sum(per_team.values()) / len(per_team)
            if lg > 0:
                ranked = sorted(per_team.items(), key=lambda kv: kv[1])
                for i, (tm, allowed) in enumerate(ranked):
                    f = _nfl_restrained_def_factor(allowed / lg)
                    out[tm] = (round(f, 3), i + 1)
    except Exception as e:
        print(f"[DefFactor] {stat_col} failed: {e}")
    _DEFF_CACHE["maps"][stat_col] = out
    return out

def _nfl_restrained_def_factor(raw_factor: float) -> float:
    """Shrink positional-defense influence to a maximum +/-3% nudge.

    Raw ratios are bounded at +/-10% for audit consistency, then shrunk
    linearly around league average.  Thus .90 -> .97 and 1.10 -> 1.03.
    """
    try:
        raw = max(.90, min(1.10, float(raw_factor)))
    except (TypeError, ValueError):
        raw = 1.0
    return round(1.0 + (raw - 1.0) * .30, 3)

# Auditable, point-in-time role and positional-defense inputs.  These consume
# the caller's already-filtered nflverse frame, so historical replay cannot see
# future weeks and no auxiliary feed can blank the board.
_ROLE_CACHE = {}
_POSDEF_CACHE = {}
_POSDEF_PANEL_CACHE = {"df_ref": None, "panels": {}}
_DEF_CONTEXT_CACHE = {"df_ref": None, "records_by_position": None}

_NFL_POSDEF_OFFENSIVE_STATS = {
    "passing_yards", "passing_tds", "completions", "attempts",
    "interceptions", "rushing_yards", "carries", "receiving_yards",
    "receptions", "rush_rec_yards", "anytime_td",
}
_NFL_POSDEF_FRAME_LOCAL = _bt_th.local()

def _nfl_posdef_panel(df, pos, stat):
    """Return a compact zero-complete position/stat/venue game panel."""
    global _POSDEF_PANEL_CACHE
    import pandas as pd
    pos = _nfl_position_group(pos)
    cache = _POSDEF_PANEL_CACHE
    if cache.get("df_ref") is not df:
        cache = {"df_ref": df, "panels": {}}
        _POSDEF_PANEL_CACHE = cache
    key = (pos, stat)
    if key in cache["panels"]:
        return cache["panels"][key]
    panel = pd.DataFrame()
    try:
        required = {
            "recent_team", "opponent_team", "position", "season", "week", stat,
        }
        if _HA_LOADED and required.issubset(df.columns):
            cols = ["recent_team", "opponent_team", "position", "season",
                    "week", stat]
            if "season_type" in df.columns:
                cols.append("season_type")
            compact = df.loc[:, cols]
            if "season_type" in compact.columns:
                season_type = compact["season_type"].fillna("REG").astype(
                    str).str.upper()
            else:
                season_type = pd.Series("REG", index=compact.index)
            season_type = season_type.where(
                season_type.isin(["REG", "POST"]), "REG")
            normalized = pd.DataFrame({
                "season": pd.to_numeric(compact["season"], errors="coerce"),
                "season_type": season_type,
                "week": pd.to_numeric(compact["week"], errors="coerce"),
                "offense": compact["recent_team"].fillna("").astype(
                    str).str.upper(),
                "defense": compact["opponent_team"].fillna("").astype(
                    str).str.upper(),
                "value": pd.to_numeric(compact[stat], errors="coerce"),
                "position": compact["position"].fillna("").astype(
                    str).str.upper().replace({"HB": "RB", "FB": "RB"}),
            })
            normalized = normalized[
                normalized["season"].notna() & normalized["week"].notna()
                & normalized["offense"].ne("") & normalized["defense"].ne("")
            ].copy()
            normalized["season"] = normalized["season"].astype(int)
            normalized["week"] = normalized["week"].astype(int)
            game_keys = [
                "defense", "offense", "season", "season_type", "week",
            ]
            # Coverage is established before position filtering. Wholly missing
            # stat games are excluded; genuine games with no matching position
            # contribution are retained and left-filled with an authentic zero.
            coverage = normalized.assign(
                covered=normalized["value"].notna()).groupby(
                    game_keys, as_index=False, sort=False)["covered"].any()
            coverage = coverage[coverage["covered"]].drop(columns="covered")
            contributions = normalized[
                normalized["position"].eq(pos) & normalized["value"].notna()
            ].groupby(game_keys, as_index=False, sort=False)["value"].sum()
            panel = coverage.merge(contributions, how="left", on=game_keys)
            panel["value"] = panel["value"].fillna(0.0)
            # Only compact unique team/game metadata touches the schedule map;
            # no per-prop full-frame copy or player-row DataFrame.apply.
            offense_sides = []
            for season, stype, week, offense in panel[
                    ["season", "season_type", "week", "offense"]].itertuples(
                        index=False, name=None):
                offense_sides.append(_HA_LOOKUP.get((
                    int(season), stype, _espn_ha_week(stype, week), offense)))
            panel["defenseVenue"] = pd.Series(
                offense_sides, index=panel.index).map(
                    {"HOME": "AWAY", "AWAY": "HOME"})
            panel = panel[
                panel["defenseVenue"].isin(["HOME", "AWAY"])
            ][game_keys + ["defenseVenue", "value"]]
    except Exception as exc:
        print(f"[PosDef panel] {pos}/{stat} failed: {exc}")
        panel = pd.DataFrame()
    if len(cache["panels"]) >= 32:
        cache["panels"].pop(next(iter(cache["panels"])))
    cache["panels"][key] = panel
    return panel

def _nfl_defense_context_profile(df, defense, position, defense_venue):
    """Display-only offensive context from the same point-in-time game frame.

    Values are opponent allowances, not model inputs.  Build one compact
    per-game panel per frame so OLD/NEW standard and alternate cards share the
    corrected venue and zero-complete arithmetic.  Passing TDs and receiving
    yards are intentionally never added to the team totals.
    """
    global _DEF_CONTEXT_CACHE
    import pandas as pd
    out = {
        "contextSchemaVersion": 1, "contextVenue": defense_venue,
        "contextPosition": _nfl_position_group(position),
        "contextDefense": defense, "contextSourceSeasons": [],
        "contextSourceWindow": "", "contextSample": 0,
        "contextPositionTDAvg": None, "contextOffenseTDAvg": None,
        "contextPositionYardsAvg": None, "contextOffenseYardsAvg": None,
        "contextPositionTDSample": 0, "contextOffenseTDSample": 0,
        "contextPositionYardsSample": 0, "contextOffenseYardsSample": 0,
        "contextUnavailable": None,
    }
    if not defense_venue or _nfl_position_group(position) not in {"QB","RB","WR","TE"}:
        out["contextUnavailable"] = "Neutral: no offensive defense context for this market"
        return out
    try:
        if _DEF_CONTEXT_CACHE.get("df_ref") is not df:
            _DEF_CONTEXT_CACHE = {"df_ref": df, "records_by_position": None}
        if _DEF_CONTEXT_CACHE["records_by_position"] is None:
            required = {"recent_team","opponent_team","season","week",
                        "rushing_tds","receiving_tds","rushing_yards",
                        "receiving_yards","passing_yards","position"}
            if not _HA_LOADED or not required.issubset(df.columns):
                out["contextUnavailable"] = "Authentic completed-game context unavailable"
                return out
            cols = list(required) + (["season_type"] if "season_type" in df.columns else [])
            raw = df.loc[:, cols].copy()
            st = (raw["season_type"].fillna("REG").astype(str).str.upper()
                  if "season_type" in raw else pd.Series("REG", index=raw.index))
            st = st.where(st.isin(["REG","POST"]), "REG")
            n = pd.DataFrame({
                "season": pd.to_numeric(raw["season"], errors="coerce"),
                "season_type": st, "week": pd.to_numeric(raw["week"], errors="coerce"),
                "offense": raw["recent_team"].fillna("").astype(str).str.upper(),
                "defense": raw["opponent_team"].fillna("").astype(str).str.upper(),
                "position": raw["position"].fillna("").astype(str).str.upper().replace({"FB":"RB","HB":"RB"}),
            })
            for c in ["rushing_tds","receiving_tds","rushing_yards","receiving_yards","passing_yards"]:
                n[c] = pd.to_numeric(raw[c], errors="coerce")
            n = n[n.season.notna() & n.week.notna() & n.offense.ne("") & n.defense.ne("")].copy()
            n["season"], n["week"] = n["season"].astype(int), n["week"].astype(int)
            records = {p: [] for p in ("QB","RB","WR","TE")}
            keys = ["defense","offense","season","season_type","week"]
            for key, g in n.groupby(keys, sort=False):
                venue = _HA_LOOKUP.get((int(key[2]), key[3], _espn_ha_week(key[3], key[4]), key[1]))
                if venue not in {"HOME","AWAY"}: continue
                dvenue = "AWAY" if venue == "HOME" else "HOME"
                def summed(columns, mask=None):
                    z = g if mask is None else g.loc[mask]
                    s = z[columns].sum(axis=1, min_count=1)
                    return float(s.sum()) if s.notna().any() else None
                # Source coverage is game-level.  Missing position rows become
                # authentic zero whenever the relevant game source is covered.
                td_all = summed(["rushing_tds","receiving_tds"])
                pass_y, rush_y = summed(["passing_yards"]), summed(["rushing_yards"])
                off_y = pass_y + rush_y if pass_y is not None and rush_y is not None else None
                for pos in records:
                    pmask = g["position"].eq(pos)
                    td = summed(["rushing_tds","receiving_tds"], pmask)
                    if td is None and td_all is not None: td = 0.0
                    yard_cols = (["passing_yards"] if pos == "QB" else
                                 ["rushing_yards","receiving_yards"] if pos == "RB" else
                                 ["receiving_yards"])
                    py = summed(yard_cols, pmask)
                    if py is None and summed(yard_cols) is not None: py = 0.0
                    records[pos].append({
                        "defense": key[0], "venue": dvenue, "season": key[2],
                        "position_td": td, "offense_td": td_all,
                        "position_yards": py, "offense_yards": off_y})
            _DEF_CONTEXT_CACHE["records_by_position"] = records
        all_records = [r for r in _DEF_CONTEXT_CACHE["records_by_position"][_nfl_position_group(position)]
                       if r["defense"] == str(defense).upper()]
        records = [r for r in all_records if r["venue"] == defense_venue]
        seasons = sorted({int(r["season"]) for r in all_records})
        out["contextSourceSeasons"] = seasons
        out["contextSourceWindow"] = f"{seasons[0]}–{seasons[-1]} point-in-time" if seasons else ""
        for key, label in (("position_td","contextPositionTD"),("offense_td","contextOffenseTD"),
                           ("position_yards","contextPositionYards"),("offense_yards","contextOffenseYards")):
            vals = [r[key] for r in records if r[key] is not None]
            out[label+"Avg"] = round(sum(vals)/len(vals), 1) if vals else None
            out[label+"Sample"] = len(vals)
            for venue in ("HOME", "AWAY"):
                venue_vals = [r[key] for r in all_records
                              if r["venue"] == venue and r[key] is not None]
                out[label+venue.title()+"Avg"] = (
                    round(sum(venue_vals)/len(venue_vals), 1)
                    if venue_vals else None)
                out[label+venue.title()+"Sample"] = len(venue_vals)
        out["contextSample"] = len(records)
        if not records:
            out["contextUnavailable"] = "No authoritative completed games for this defense venue"
    except Exception as exc:
        out["contextUnavailable"] = "Authentic completed-game context unavailable"
        print(f"[Defense context] failed: {exc}")
    return out
def _nfl_role_position(pl, stat_col):
    p = str(pl.get("roster_position") or pl.get("position") or "").upper()
    if p in {"QB","RB","FB","WR","TE"}: return "RB" if p == "FB" else p
    return ("QB" if stat_col in {"passing_yards","passing_tds","completions","attempts","interceptions"}
            else "RB" if stat_col in {"rushing_yards","rush_rec_yards","carries"} else "WR")
def _nfl_role_profile(df, team, pos, name, stat_col=""):
    key=(id(df),str(team),pos)
    if key not in _ROLE_CACHE:
        cols=[c for c in ["player_display_name","recent_team","position","targets","receptions",
                          "receiving_yards","carries","rushing_yards","season","week"] if c in df.columns]
        if "offense_pct" in df.columns: cols.append("offense_pct")
        d=df.loc[df.recent_team.astype(str).str.upper()==str(team).upper(), cols].copy()
        if "position" in d:
            pp=d.position.fillna("").astype(str).str.upper()
            typed=d[pp.isin([pos,"FB" if pos=="RB" else pos])]
            if not typed.empty: d=typed
        if d.empty: _ROLE_CACHE[key]=d
        else:
            def _num(c):
                return d[c].fillna(0) if c in d else 0
            d["_usage"]=_num("targets")*(1 if pos in {"WR","TE"} else .15)+_num("receptions")*.35+_num("carries")*(1 if pos=="RB" else .05)+_num("receiving_yards")*.025+_num("rushing_yards")*.02
            # Participation is a modest tie-break/confidence input, never the
            # primary role signal.
            if "offense_pct" in d:
                d["_usage"] += d["offense_pct"].fillna(0).clip(0,100) * .015
            d=d.sort_values(["season","week"],ascending=False)
            d["_player_recent_n"]=d.groupby("player_display_name").cumcount()
            recent=d[d["_player_recent_n"]<10]
            agg=recent.groupby("player_display_name",as_index=False).agg(usage=("_usage","sum"),games=("week","nunique")).sort_values("usage",ascending=False).reset_index(drop=True)
            if "offense_pct" in recent:
                snap_conf = recent.groupby("player_display_name")["offense_pct"].mean()
                agg["snap_mean"] = agg.player_display_name.map(snap_conf)
                snap_recent = recent[recent["_player_recent_n"] < 2].groupby(
                    "player_display_name")["offense_pct"].mean()
                snap_prior = recent[
                    (recent["_player_recent_n"] >= 2)
                    & (recent["_player_recent_n"] < 7)
                ].groupby("player_display_name")["offense_pct"].mean()
                agg["snap_recent"] = agg.player_display_name.map(snap_recent)
                agg["snap_prior"] = agg.player_display_name.map(snap_prior)
            # Receiving option rank deliberately spans WR/TE/RB and never uses carries.
            rec=df[df.recent_team.astype(str).str.upper()==str(team).upper()].copy()
            if "position" in rec:
                rec=rec[rec.position.fillna("").astype(str).str.upper().isin(["WR","TE","RB","FB"])]
            if not rec.empty:
                for c in ["targets","receptions","receiving_yards"]:
                    if c not in rec: rec[c]=0
                rec["_rn"]=rec.groupby("player_display_name").cumcount()
                rec=rec[rec["_rn"]<10]
                rec["_recv_usage"]=rec.targets.fillna(0)*1.0+rec.receptions.fillna(0)*.35+rec.receiving_yards.fillna(0)*.025
                recv=rec.groupby("player_display_name")["_recv_usage"].sum().sort_values(ascending=False)
                agg["team_option_rank"]=agg.player_display_name.map({n:i+1 for i,n in enumerate(recv.index)})
            _ROLE_CACHE[key]=agg
    d=_ROLE_CACHE[key]
    if d is None or d.empty: return {"role":pos+"?","option_rank":None,"confidence":.15,"factor":1.0,"reason":"No point-in-time teammate usage"}
    names=d.player_display_name.fillna("").astype(str).str.lower().tolist()
    try: ix=names.index(str(name).lower())
    except ValueError: return {"role":pos+"?","option_rank":None,"confidence":.2,"factor":1.0,"reason":"Player absent from point-in-time usage"}
    slots={"WR":["WR1","WR2","WR3","WR4"],"TE":["TE1","TE2"],"RB":["RB1","RB2"],"QB":["QB1"]}.get(pos,[pos])
    role=slots[min(ix,len(slots)-1)]
    lead,tail={"WR":(1.08,.96),"TE":(1.06,.97),"RB":(1.07,.95),"QB":(1.04,.98)}.get(pos,(1,1))
    is_receiving = stat_col in {"receiving_yards","receptions"} or pos in {"WR","TE"} and stat_col in {"targets","receiving_yards","receptions"}
    is_rushing = stat_col in {"rushing_yards","carries"}
    if pos == "QB": lead, tail = (1.0, 1.0)
    elif is_receiving: lead, tail = (1.06,.98) if pos in {"WR","TE"} else (1.03,.985)
    elif is_rushing: lead, tail = (1.05,.97) if pos=="RB" else (1.0,1.0)
    elif stat_col == "anytime_td": lead, tail = (1.025,.99)
    else: lead, tail = (1.0,1.0)
    option_rank = None
    try:
        if is_receiving and "team_option_rank" in d and math.isfinite(float(d.iloc[ix].team_option_rank)):
            option_rank = int(d.iloc[ix].team_option_rank)
    except (TypeError, ValueError):
        option_rank = None
    snap_bonus = 0.0
    try: snap_bonus = min(.12, max(0.0, float(d.iloc[ix].get("snap_mean") or 0) / 1000.0))
    except (TypeError, ValueError): pass
    snap_recent = snap_prior = snap_delta = None
    try:
        snap_recent = float(d.iloc[ix].get("snap_recent"))
        if not math.isfinite(snap_recent): snap_recent = None
    except (TypeError, ValueError):
        snap_recent = None
    try:
        snap_prior = float(d.iloc[ix].get("snap_prior"))
        if not math.isfinite(snap_prior): snap_prior = None
    except (TypeError, ValueError):
        snap_prior = None
    if snap_recent is not None and snap_prior is not None:
        snap_delta = round(snap_recent - snap_prior, 1)
    return {"role":role,"roleRank":ix+1,"option_rank":option_rank,
            "confidence":round(min(.9,.35+min(float(d.iloc[ix].games),10)*.055+snap_bonus),2),
            "factor":round(lead if ix==0 else 1+(tail-1)*min(ix,2)/2,3),
            "reason":"Recent usage ranking; snap participation blended when available",
            "snapRecent":round(snap_recent,1) if snap_recent is not None else None,
            "snapPrior":round(snap_prior,1) if snap_prior is not None else None,
            "snapDelta":snap_delta}

def _nfl_role_risk_context(pl: dict, role: dict) -> dict:
    """Combine verified current status with historical snap-trend context."""
    status = str(pl.get("role_risk_status") or "UNVERIFIED").upper()
    reasons = [str(x) for x in (pl.get("role_risk_reasons") or []) if str(x)]
    block_premium = bool(pl.get("role_risk_block_premium"))
    snap_recent = role.get("snapRecent")
    snap_prior = role.get("snapPrior")
    snap_delta = role.get("snapDelta")
    try:
        usage_drop = (
            snap_recent is not None and snap_delta is not None
            and float(snap_recent) < 55.0 and float(snap_delta) <= -20.0)
    except (TypeError, ValueError):
        usage_drop = False
    if usage_drop:
        if status == "CLEAR":
            status = "WATCH"
        reasons.append(
            f"Recent offense snaps fell to {float(snap_recent):.0f}% "
            f"from {float(snap_prior):.0f}%")
    confidence_factor = 0.76 if status == "AVOID" else (0.88 if status == "WATCH" else 1.0)
    return {
        "status": status, "reasons": reasons, "blockPremium": block_premium,
        "source": pl.get("role_risk_source") or "ESPN roster",
        "updatedAt": pl.get("depth_updated_at") or pl.get("injury_updated_at"),
        "confidenceFactor": confidence_factor,
        "snapRecent": snap_recent, "snapPrior": snap_prior,
        "snapDelta": snap_delta,
    }

def _nfl_posdef_profile(df, defense, pos, stat, defense_venue=None):
    """Point-in-time positional defense profile split by the defense's venue.

    nflverse player rows carry the offense venue.  A HOME offense row is an
    AWAY game for its opponent's defense, and vice versa.  Rows without an
    authoritative ESPN venue are deliberately excluded rather than guessed.
    """
    defense_venue = str(defense_venue or "").upper() or None
    # Alternate Coach intentionally keeps its full history frame for unrelated
    # player evidence. Its worker supplies a thread-local two-season pregame
    # defense frame so only this profile is scoped, once per alternate slate.
    defense_df = getattr(_NFL_POSDEF_FRAME_LOCAL, "frame", None)
    if defense_df is None:
        defense_df = df
    pos = _nfl_position_group(pos)
    key=(id(defense_df),str(defense),pos,stat,defense_venue)
    if key in _POSDEF_CACHE:return _POSDEF_CACHE[key]
    out={"factor":1.0,"rank":None,"allowed":None,"sample":0,
         "defenseVenue":defense_venue,
         "defHomeAllowed":None,"defHomeSample":0,
         "defAwayAllowed":None,"defAwaySample":0,
         "label":f"vs {pos} · {stat.replace('_',' ')} allowed/game",
         "confidence":.15, "defSchemaVersion":2,
         "defPositionGroup":pos, "defStat":stat,
         "defMetric":"team positional total per completed game",
         "defSourceSeasons":[], "defSourceWindow":"",
         "defUnavailable":None}
    try:
        if stat not in _NFL_POSDEF_OFFENSIVE_STATS:
            out["defUnavailable"] = (
                "Neutral: no sensible opponent offensive-position allowance "
                "for this defensive/kicking player market")
            _POSDEF_CACHE[key]=out; return out
        panel = _nfl_posdef_panel(defense_df, pos, stat)
        if panel is None or panel.empty:
            out["defUnavailable"] = (
                "Exact position/stat venue allowance unavailable")
            _POSDEF_CACHE[key]=out; return out
        d=panel[panel["defense"].astype(str).str.upper().eq(
            str(defense).upper())]
        source_seasons=sorted(int(x) for x in panel["season"].unique())
        out["defSourceSeasons"]=source_seasons
        out["defSourceWindow"]=(
            f"{source_seasons[0]}–{source_seasons[-1]} point-in-time"
            if source_seasons else "point-in-time")
        def _venue_games(frame, venue):
            rows=frame[frame["defenseVenue"].eq(venue)]
            return rows.set_index(
                ["season","season_type","week","offense"])["value"].sort_index(
                    ascending=False)
        def _summary(venue):
            games=_venue_games(d,venue)
            if len(games):
                # The UI says allowed per game, so expose and model the actual
                # arithmetic mean of the selected venue games. Do not relabel a
                # prior/current/recent weighted blend as a venue average.
                return round(float(games.mean()),1),len(games)
            return None,0
        home_allowed,home_sample=_summary("HOME")
        away_allowed,away_sample=_summary("AWAY")
        out.update({"defHomeAllowed":home_allowed,"defHomeSample":home_sample,
                    "defAwayAllowed":away_allowed,"defAwaySample":away_sample})
        selected_allowed, selected_sample = _summary(defense_venue) if defense_venue else (None, 0)
        games=_venue_games(d,defense_venue) if defense_venue else d.iloc[0:0]
        if len(games)<2:
            _POSDEF_CACHE[key]=out; return out
        # League baseline is venue-specific and uses the same point-in-time
        # season/week frame. Never substitute the combined defense sample.
        e=panel
        league_games=e[e["defenseVenue"].eq(defense_venue)]["value"]
        # Compare the defense with the same two-season, point-in-time,
        # venue-specific sample used by its displayed allowed/game figure.
        baseline=(float(league_games.mean()) if len(league_games)
                  else float(games.mean()))
        allowed=float(selected_allowed) if selected_allowed is not None else float(games.mean())
        factor=max(.9,min(1.1,allowed/baseline if baseline else 1))
        vals={}
        for tm,g in e.groupby("defense"):
            gg=g[g["defenseVenue"].eq(defense_venue)]["value"]
            if len(gg)>=2: vals[str(tm)]=float(gg.mean())
        raw_factor = max(.90, min(1.10, float(factor)))
        out={"factor":_nfl_restrained_def_factor(raw_factor),
             "rawFactor":round(raw_factor,3),
             "rank":1+sum(v<allowed for v in vals.values()),
             "allowed":round(float(allowed),1),"sample":len(games),
             "defenseVenue":defense_venue,
             "defHomeAllowed":home_allowed,"defHomeSample":home_sample,
             "defAwayAllowed":away_allowed,"defAwaySample":away_sample,
              "label":f"vs {pos} · {stat.replace('_',' ')} allowed/game",
              "confidence":round(min(.95,.25+len(games)*.035),2),
              "defSchemaVersion":2,
              "defPositionGroup":pos,"defStat":stat,
              "defMetric":"team positional total per completed game",
              "defSourceSeasons":source_seasons,
              "defSourceWindow":out["defSourceWindow"],
              "defUnavailable":None}
    except Exception as exc: print(f"[PosDef] {pos}/{stat} failed: {exc}")
    _POSDEF_CACHE[key]=out; return out

_NFL_PLAYER_LOOKUP = {"df_ref": None, "groups": {}, "matches": {}}
_NFL_OPP_PLAYER_LOOKUP = {"df_ref": None, "groups": {}, "matches": {}}

def _nfl_player_identity_key(name) -> str:
    """Match full player names across provider suffix/punctuation variations."""
    tokens = re.sub(r"[^a-z0-9 ]+", " ", str(name or "").lower()).split()
    suffixes = {"jr", "sr", "ii", "iii", "iv", "v"}
    while tokens and tokens[-1] in suffixes:
        tokens.pop()
    return " ".join(tokens)

def _nfl_player_history(df, name, lookup=None):
    """Reuse full-name player slices, including suffix variants and old teams."""
    cache = lookup if lookup is not None else _NFL_PLAYER_LOOKUP
    if cache["df_ref"] is not df:
        # Keep only the small row-position index.  A pandas Series containing a
        # normalized copy of every player name is needlessly retained for the
        # lifetime of the process (and was especially costly for weekly replays).
        groups = {}
        for row_number, player_name in enumerate(df["player_display_name"]):
            identity = _nfl_player_identity_key(player_name)
            groups.setdefault(identity, []).append(row_number)
        cache.update({"df_ref": df, "groups": groups, "matches": {}})
    key = _nfl_player_identity_key(name)
    if key not in cache["matches"]:
        positions = cache["groups"].get(key)
        if positions is None:
            positions = []
        # Cache tiny row-position arrays, not a second copy of every player's
        # full history alongside the source dataframe.
        cache["matches"][key] = positions
    return df.iloc[cache["matches"][key]]


def _nfl_clear_slate_caches():
    """Release caches whose keys are derived from one daily analysis frame.

    The process-wide nflverse frame and its expensive long-lived caches are
    intentionally untouched.  Role/positional-defense entries, however, hold
    compact DataFrames derived from a replay slate and otherwise accumulate
    across the seven sequential dates of a full-week run.
    """
    global _NFL_PLAYER_LOOKUP, _NFL_OPP_PLAYER_LOOKUP, _POSDEF_PANEL_CACHE
    global _DEF_CONTEXT_CACHE
    _ROLE_CACHE.clear()
    _POSDEF_CACHE.clear()
    _POSDEF_PANEL_CACHE = {"df_ref": None, "panels": {}}
    _DEF_CONTEXT_CACHE = {"df_ref": None, "records_by_position": None}
    _NFL_PLAYER_LOOKUP = {
        "df_ref": None, "groups": {}, "matches": {}
    }
    _NFL_OPP_PLAYER_LOOKUP = {
        "df_ref": None, "groups": {}, "matches": {}
    }
    _DEFF_CACHE.update({"df_ref": None, "maps": {}})
    _TD_OPP_CACHE.update({"df_ref": None, "values": {}})
    # Keep the calibration for the process-global base frame: it is expensive
    # and safe to reuse.  Replay/date-specific frames must not stay retained.
    if _TD_CAL_CACHE.get("df_ref") is not _nfl_df:
        _TD_CAL_CACHE.update({"df_ref": None, "bins": None, "report": None})
    gc.collect()

def _analyze_prop(pl: Dict, df, home_abbr: str, away_abbr: str,
                   opponent_df=None) -> Optional[Dict]:
    """Emit the shared NORMALIZED pick-field contract (same keys as the NHL app)
    so the card grid, ladder modal, special boxes and parlay are market-agnostic.
    Stats: career vs opponent (H/A filtered) + last-10 H/A + hits-vs-book-line L10."""
    name     = pl["name"]
    line     = pl["line"]
    label    = pl["label"]
    stat_col = pl.get("stat_col", "")
    market   = pl.get("market", "")

    if not stat_col or stat_col not in df.columns:
        return None

    # Find player
    pdf = _nfl_player_history(df, name)
    if pdf.empty:
        return None

    # Use MOST RECENT team (not historical mode) so traded players show correct team
    pdf_sorted = pdf.sort_values(["season", "week"], ascending=False) if not pdf.empty else pdf
    recent_team = pdf_sorted["recent_team"].iloc[0] if not pdf_sorted.empty else ""
    historical_position = (
        _first_str(pdf_sorted["position"])
        if "position" in pdf_sorted.columns else "")
    effective_position = _nfl_position_group(
        pl.get("roster_position") or historical_position)
    if market == "player_rush_reception_yds" and effective_position != "RB":
        return None
    current_team = pl.get("roster_team") or recent_team

    # Determine home/away using current game teams first, fall back to historical
    if home_abbr and current_team == home_abbr:
        opp_abbr = away_abbr; is_home = True;  home_road = "H"; side = "HOME"; game_team = home_abbr
    elif away_abbr and current_team == away_abbr:
        opp_abbr = home_abbr; is_home = False; home_road = "R"; side = "AWAY"; game_team = away_abbr
    elif home_abbr and away_abbr:
        # Player traded — nfl-verse team is stale; assume home until ESPN confirms
        opp_abbr = away_abbr; is_home = True;  home_road = "H"; side = "HOME"; game_team = home_abbr
    else:
        opp_abbr = home_abbr; is_home = None;  home_road = "";  side = "--"; game_team = recent_team

    if game_team and game_team == opp_abbr:
        return None

    # Headshot URL + player id (most recent non-empty row)
    head = _first_str(pdf_sorted["headshot_url"]) if "headshot_url" in pdf_sorted.columns else ""
    pid  = _first_str(pdf_sorted["player_id"])    if "player_id"    in pdf_sorted.columns else ""
    if not pid:
        pid = _norm(name)

    # Opponent history deliberately uses its own all-season, point-in-time
    # frame.  The regular ``df`` is the strict two-season model frame and must
    # never make an old Goff-vs-BUF meeting disappear from this section.
    opp_source = opponent_df if opponent_df is not None else df
    opp_pdf = (
        _nfl_player_history(opp_source, name, _NFL_OPP_PLAYER_LOOKUP)
        if opp_source is not None else pdf
    )
    # Career vs opponent (H/A filtered, fallback to all-vs-opp).  All venues
    # remain available for the displayed game log and last-five sample.
    vs_opp_all = opp_pdf[opp_pdf["opponent_team"] == opp_abbr] if opp_abbr else opp_pdf
    # Matchup history is venue-neutral.  Home/away remains relevant to the
    # side-aware L10/UNDER rates below, not to this opponent sample.
    vs_opp = vs_opp_all.sort_values(["season", "week"], ascending=False)

    # OLD treats every valid, completed game against today's opponent as an
    # observation. The separate team-strength factor below is the only input
    # restricted to the current and previous season.
    vs_opp = vs_opp.dropna(subset=[stat_col])
    vs_vals = vs_opp[stat_col].tolist() if not vs_opp.empty else []
    avg_a   = round(sum(vs_vals)/len(vs_vals), 1) if vs_vals else None
    hits_a  = sum(1 for v in vs_vals if v > line)
    tot_a   = len(vs_vals)
    rate_a  = round(hits_a/tot_a*100, 1) if tot_a >= 1 else None
    opp_under_hits = sum(1 for v in vs_vals if v < line)
    history_lock = None
    if market != "player_anytime_td" and tot_a >= 2:
        if hits_a == tot_a:
            history_lock = "OVER"
        elif opp_under_hits == tot_a:
            history_lock = "UNDER"
    history_lock_reason = (
        f"Opponent history {tot_a}/{tot_a} {history_lock} today's line sets the pick side"
        if history_lock else "")

    # Last 10 H/A games (any opponent)
    if is_home is not None and _HA_LOADED:
        l10_pool = pdf[pdf.apply(lambda r: _ha_side(r, is_home), axis=1)]
    else:
        l10_pool = pdf
    l10 = l10_pool.sort_values(["season","week"], ascending=False).head(10) if not l10_pool.empty else l10_pool
    l10_vals = l10[stat_col].dropna().tolist() if not l10.empty else []
    avg_b    = round(sum(l10_vals)/len(l10_vals), 1) if l10_vals else None
    hits_b   = sum(1 for v in l10_vals if v > line)
    tot_b    = len(l10_vals)
    rate_b   = round(hits_b/tot_b*100, 1) if tot_b >= 1 else None
    under_hits = sum(1 for v in l10_vals if v < line)
    under_rate = round(under_hits/tot_b*100, 1) if tot_b >= 1 else None

    # Hits vs the book line over last 10 games (any location)
    last10_any = pdf_sorted.head(10)
    la_vals    = last10_any[stat_col].dropna().tolist() if not last10_any.empty else []
    vsl_hits   = sum(1 for v in la_vals if v > line)
    vsl_tot    = len(la_vals)
    vsl_rate   = round(vsl_hits/vsl_tot*100, 1) if vsl_tot >= 1 else None

    # Projection volume comes from current-form L10 at today's venue. Historical
    # meetings against the opponent influence the side-aware probability below,
    # but their raw stat average must never become the yardage projection (one
    # outlier game can make that number meaningless).
    ref_avg = avg_b

    # Market-specific opponent positional defense and current offensive role
    # change the projection itself; generic defense remains a low-data fallback.
    role = _nfl_role_profile(df, game_team, effective_position, name, stat_col)
    role_risk = _nfl_role_risk_context(pl, role)
    defense_venue = ("AWAY" if is_home else "HOME") if is_home is not None else None
    posdef = (_nfl_posdef_profile(df, opp_abbr, effective_position, stat_col,
                                  defense_venue)
              if opp_abbr else {})
    defcontext = (_nfl_defense_context_profile(
        df, opp_abbr, effective_position, defense_venue)
        if opp_abbr else {})
    def_factor = float(posdef.get("factor", 1.0))
    def_rank = posdef.get("rank")
    def_lbl = posdef.get("label") or _OPP_ADJ_COLS.get(stat_col, "")
    # A missing selected venue is intentionally neutral; never fall back to a
    # combined home+away or league defense factor.
    role_factor = float(role.get("factor", 1.0))
    combined_factor = max(.86, min(1.14, role_factor * def_factor))
    def_rank_factor = 1.0 + max(-0.05, min(0.05, (def_factor - 1) * 0.5))
    base_proj_avg = ref_avg
    injury_factor = float(pl.get("injury_opportunity_factor") or 1.0)
    adj_avg = (round(ref_avg * combined_factor * injury_factor, 1)
               if ref_avg is not None else None)
    weather_snapshot = pl.get("weather") if isinstance(pl.get("weather"), dict) else {}
    weather_factor = _nfl_weather_factors(
        weather_snapshot, market, effective_position)
    weather_base_projection = adj_avg
    if adj_avg is not None and weather_snapshot.get("status") == "OK":
        adj_avg = round(adj_avg * weather_factor, 1)
    injury_adj = (round(adj_avg - ref_avg, 1)
                  if ref_avg is not None and adj_avg is not None else 0.0)
    def_adj = round((def_factor - 1) * 100)

    gap     = round(adj_avg - line, 1) if adj_avg is not None else None
    # EVERY player with any history gets a pick — a 0.0 average is a real
    # signal (obvious UNDER), not "no data". Ties lean UNDER (book gets the push).
    pick    = None
    if adj_avg is not None:
        pick = "OVER" if adj_avg > line else "UNDER"
    # Anytime TD is a one-sided Yes/OVER market. Its side is determined by the
    # calibrated scoring probability and price below, never by average TD count
    # (a multi-TD game must not distort side eligibility).
    if market == "player_anytime_td" and tot_b:
        pick = "OVER"
    elif history_lock:
        # A perfect record in at least two completed meetings against today's
        # opponent takes precedence over generic venue form. The restrained
        # defense adjustment still changes projection/confidence, not this side.
        pick = history_lock

    # Side-aware stats: on an UNDER card every rate + the score describe the
    # UNDER side (times the player stayed BELOW the line). A green 100% must
    # always SUPPORT the printed pick — never contradict it.
    if pick == "UNDER":
        hits_a = sum(1 for v in vs_vals if v < line)
        rate_a = round(hits_a/tot_a*100, 1) if tot_a >= 1 else None
        hits_b = under_hits
        rate_b = under_rate
        vsl_hits = sum(1 for v in la_vals if v < line)
        vsl_rate = round(vsl_hits/vsl_tot*100, 1) if vsl_tot >= 1 else None

    rates = [r for r in [rate_a, rate_b] if r is not None]
    base_score = round(sum(rates)/len(rates), 1) if rates else 0
    signed_factor = combined_factor if pick == "OVER" else (2.0 - combined_factor if pick == "UNDER" else 1.0)
    score = round(max(0.0, min(100.0, base_score + (signed_factor - 1.0) * 35)), 1)
    player_injury_status = str(pl.get("injury_status") or "UNVERIFIED")
    # Positional factor is already applied above; do not apply the legacy
    # ranking multiplier a second time.  It remains projection-neutral fallback.
    td_raw_score = None
    td_opportunity = {}
    td_calibration_n = 0
    td_calibration_report = []
    if market == "player_anytime_td" and pick == "OVER":
        score, td_raw_score, td_opportunity, td_calibration_n, td_calibration_report = (
            _td_calibrated_probability(pdf, df, game_team, opp_abbr, def_factor)
        )
        # TD model already includes opportunity and defense; role is intentionally
        # a small nudge only, avoiding a second volume count.
        score = round(max(0.0, min(100.0, score + (role_factor - 1.0) * 20.0)), 1)
    weather_base_probability = score
    if weather_snapshot.get("status") == "OK" and weather_factor != 1.0:
        probability_factor = (
            2.0 - weather_factor if pick == "UNDER" else weather_factor)
        score = round(max(0.0, min(100.0,
            50.0 + (score - 50.0) * probability_factor)), 1)
    # Apply teammate opportunity and player-status uncertainty to the final
    # probability, including the separately calibrated anytime-TD probability.
    if pick and injury_factor != 1.0:
        side_factor = injury_factor if pick == "OVER" else (2.0 - injury_factor)
        score = round(max(0.0, min(100.0, score * side_factor)), 1)
    if player_injury_status == "QUESTIONABLE":
        score = round(50.0 + (score - 50.0) * 0.80, 1)
    elif player_injury_status == "LIMITED":
        score = round(50.0 + (score - 50.0) * 0.92, 1)
    if role_risk["confidenceFactor"] != 1.0:
        score = round(50.0 + (score - 50.0)
                      * role_risk["confidenceFactor"], 1)
    tag     = _book_tag_nfl(pick, score, gap, under_rate)
    # Anytime TD is a binary, price-sensitive market. A raw historical hit
    # rate is not enough: a 44% TD rate loses at +100 and only starts to clear
    # the break-even point around +127. Keep the signal in `all` for review,
    # but only promote it to the bet board when it has a real over price,
    # enough recent observations, and positive model edge over the book's
    # break-even rate. Team-level selection includes the leading QB and RB,
    # plus the established WR/TE candidate limits for each team.
    bet_qualified = True
    value_edge = None
    value_reason = ""
    if market == "player_anytime_td":
        td_odds = pl.get("over_odds")
        implied = _nfl_implied_prob(td_odds)
        value_edge = round(score - implied, 1) if implied is not None else None
        bet_qualified = bool(
            pick == "OVER" and implied is not None
            and tot_b >= 5 and value_edge is not None and value_edge > 0
        )
        if not bet_qualified:
            if implied is None:
                value_reason = "No TD price available"
            elif tot_b < 5:
                value_reason = "Needs at least 5 recent games"
            elif value_edge is None or value_edge <= 0:
                value_reason = "No positive model edge over break-even"
            else:
                value_reason = "Model does not project an OVER"
    if role_risk["blockPremium"]:
        bet_qualified = False
        value_reason = (
            "Role Risk: " + "; ".join(role_risk["reasons"])
            if role_risk["reasons"] else "Role Risk: verified reduced role")

    # Recent game log (newest first) for the ladder modal
    glog = []
    for _, r in last10_any.iterrows():
        try:
            v = r[stat_col]
            if v is None or (isinstance(v, float) and v != v):
                continue
            ro = ""
            try:
                ro = str(r["opponent_team"]) if r.get("opponent_team") else ""
            except Exception:
                ro = ""
            glog.append({"d": f"{int(r['season'])} W{int(r['week'])}", "v": round(float(v), 1), "o": ro})
        except Exception:
            continue

    # Every career game vs THIS opponent (newest first) so the ladder modal can
    # show the actual stat line from each past meeting even when it falls outside
    # the recent-10 window (e.g. a single old game vs a rare opponent). Use the
    # UNFILTERED vs_opp_all (both venues) — this section is "every meeting", not the
    # H/A-filtered set that drives the vs-opp RATE stats.
    vs_opp_log = []
    if not vs_opp_all.empty:
        for _, r in (vs_opp_all.sort_values(["season", "week"], ascending=False)
                     .dropna(subset=[stat_col]).iterrows()):
            try:
                v = r[stat_col]
                if v is None or (isinstance(v, float) and v != v):
                    continue
                vs_opp_log.append({
                    "d": f"{int(r['season'])} W{int(r['week'])}",
                    "v": round(float(v), 1),
                    "ha": _nfl_history_venue(r),
                })
            except Exception:
                continue

    return {
        # identity
        "name": name, "pid": pid, "position": effective_position,
        "team": game_team, "opponent": opp_abbr or "--",
        "homeRoad": home_road, "side": side, "head": head, "game": pl.get("game",""),
        "game_start": pl.get("game_start",""),
        # market
        "mkt": label, "label": label, "market": market,
        "line": line, "dispLine": line, "realLine": line,
        "realOdds": pl.get("over_odds"), "realUnderOdds": pl.get("under_odds"),
        "over_odds": pl.get("over_odds"), "under_odds": pl.get("under_odds"),
        "over_book": pl.get("over_book", ""), "under_book": pl.get("under_book", ""),
        "isAlternate": bool(pl.get("is_alternate")),
        "sourceMarket": pl.get("source_market", market),
        "quoteFetchedAt": pl.get("quote_fetched_at"),
        "quoteStatus": pl.get("quote_status", "UNVERIFIED"),
        # averages
        "avg": avg_b if avg_b is not None else (avg_a if avg_a is not None else 0),
        "avgA": avg_a if avg_a is not None else 0,
        # career vs opp
        "rateA": rate_a, "hitsA": hits_a, "totA": tot_a,
        # L10 H/A
        "rateB": rate_b, "hitsB": hits_b, "totB": tot_b,
        # hits vs book line L10
        "vsLineHits": vsl_hits, "vsLineTotal": vsl_tot, "vsLineRate": vsl_rate or 0,
        # under track
        "underHits": under_hits, "underTotal": tot_b, "underRate": under_rate or 0, "underLine": line,
        # opponent-defense ranking factor
        "defAdj": def_adj, "defRank": def_rank, "defLbl": def_lbl,
        "projAvg": adj_avg,
        "role": role.get("role"), "teamOptionRank": role.get("option_rank"),
        "roleConfidence": role.get("confidence"), "roleFactor": role_factor,
        "roleReason": role.get("reason"), "positionGroup": effective_position,
        "recentSnapPct": role.get("snapRecent"),
        "priorSnapPct": role.get("snapPrior"),
        "snapTrendPct": role.get("snapDelta"),
        "depthRank": pl.get("depth_rank"),
        "depthPosition": pl.get("depth_position"),
        "depthChart": pl.get("depth_chart", ""),
        "roleRiskStatus": role_risk["status"],
        "roleRiskReasons": role_risk["reasons"],
        "roleRiskSource": role_risk["source"],
        "roleRiskUpdatedAt": role_risk["updatedAt"],
        "roleRiskBlockPremium": role_risk["blockPremium"],
        "defAllowed": posdef.get("allowed"), "defSample": posdef.get("sample", 0),
        "defenseVenue": posdef.get("defenseVenue"),
        "defHomeAllowed": posdef.get("defHomeAllowed"),
        "defHomeSample": posdef.get("defHomeSample", 0),
        "defAwayAllowed": posdef.get("defAwayAllowed"),
        "defAwaySample": posdef.get("defAwaySample", 0),
        "defConfidence": posdef.get("confidence", .15),
        "defRawFactor": posdef.get("rawFactor"),
        "defFactor": def_factor,
        "defSchemaVersion": posdef.get("defSchemaVersion", 2),
        "defPositionGroup": posdef.get("defPositionGroup", effective_position),
        "defStat": posdef.get("defStat", stat_col),
        "defMetric": posdef.get("defMetric"),
        "defSourceSeasons": posdef.get("defSourceSeasons") or [],
        "defSourceWindow": posdef.get("defSourceWindow") or "",
        "defUnavailable": posdef.get("defUnavailable"),
        **defcontext,
        "combinedFactor": combined_factor, "baseProjection": ref_avg,
        "baseProbability": base_score, "adjustedProjection": adj_avg,
        "adjustedProbability": score,
        "historyLock": history_lock,
        "historyLockReason": history_lock_reason,
        "baseProjAvg": base_proj_avg, "injuryAdj": injury_adj,
        "weatherApplied": bool(weather_snapshot.get("status") == "OK"
                               and weather_factor != 1.0),
        "weatherFactor": weather_factor,
        "weatherBaseProjection": weather_base_projection,
        "weatherAdjustment": (round(adj_avg - weather_base_projection, 1)
                              if adj_avg is not None and weather_base_projection is not None else 0),
        "weatherBaseProbability": weather_base_probability,
        "weatherSeverity": weather_snapshot.get("severity", 0),
        "weatherLabel": weather_snapshot.get("label", ""),
        "weatherSummary": weather_snapshot.get("summary", ""),
        "weatherStatus": weather_snapshot.get("status", "UNAVAILABLE"),
        "isRookie": bool(pl.get("rookie_verified") and pl.get("is_rookie")),
        "rookieVerified": bool(pl.get("rookie_verified")),
        "rosterExperienceYears": pl.get("roster_experience_years"),
        "injuryOpportunityFactor": injury_factor,
        "injuryOpportunityReasons": pl.get("injury_opportunity_reasons") or [],
        "injuryStatus": player_injury_status,
        "injuryNote": pl.get("injury_note", ""),
        "injuryUpdatedAt": pl.get("injury_updated_at"),
        "participationProbability": pl.get("participation_probability"),
        "availabilityVerified": bool(pl.get("availability_verified")),
        "coachEligible": bool(pl.get("coach_eligible", True)),
        # score / pick
        "score": score, "dispScore": score, "gap": gap, "pick": pick, "tag": tag,
        "betQualified": bet_qualified, "valueEdge": value_edge, "valueReason": value_reason,
        "tdRawProbability": td_raw_score, "tdOpportunity": td_opportunity,
        "tdCalibrationSample": td_calibration_n,
        "tdCalibrationReport": td_calibration_report if market == "player_anytime_td" else [],
        "glog": glog, "vsOppLog": vs_opp_log,
        # ── legacy keys (kept for backward compatibility with cached payloads /
        #    any downstream consumer that predates the normalized contract) ──
        "opp": opp_abbr or "--",
        "vs_opp_avg": avg_a, "vs_opp_games": tot_a,
        "vs_opp_hits": hits_a, "vs_opp_rate": rate_a,
        "l10_avg": avg_b, "l10_games": tot_b,
        "l10_hits": hits_b, "l10_rate": rate_b,
        "games": tot_a,
        "history": ", ".join(str(int(v)) for v in vs_vals[:8]) or "--",
    }


def _new_weighted_mean(values, decay=0.16):
    """Newest-first exponentially weighted mean, without turning NaNs into 0."""
    clean = []
    for value in values:
        try:
            value = float(value)
            if math.isfinite(value):
                clean.append(value)
        except (TypeError, ValueError):
            continue
    if not clean:
        return None
    weights = [pow(2.718281828, -decay * i) for i in range(len(clean))]
    return sum(v * w for v, w in zip(clean, weights)) / sum(weights)


def _new_sanitize_json(value):
    """Normalize NEW payloads without allocating a second complete board."""
    return _nfl_json_ready(value)


def _nfl_json_ready(value):
    """Normalize model scalars in place; do not duplicate a full weekly board."""
    if isinstance(value, dict):
        for key in value:
            value[key] = _nfl_json_ready(value[key])
    elif isinstance(value, list):
        for index in range(len(value)):
            value[index] = _nfl_json_ready(value[index])
    elif isinstance(value, tuple):
        return [_nfl_json_ready(item) for item in value]
    elif hasattr(value, "item"):
        return _nfl_json_ready(value.item())
    elif isinstance(value, float) and not math.isfinite(value):
        return None
    return value


def _new_participation_rows(pdf, market, position, stat_col=""):
    """Return only rows with verified, market-relevant participation."""
    if pdf is None or pdf.empty:
        return pdf
    columns = set(pdf.columns)
    def num(row, name):
        if name not in columns:
            return 0.0
        try:
            value = float(row.get(name))
            return value if math.isfinite(value) and value >= 0 else 0.0
        except (TypeError, ValueError):
            return 0.0
    keep = []
    for _, row in pdf.iterrows():
        if market in {"player_pass_yds", "player_pass_tds",
                      "player_pass_completions", "player_pass_attempts",
                      "player_pass_interceptions"}:
            participated = (num(row, "attempts") > 0 or
                            num(row, "completions") > 0 or
                            num(row, "passing_yards") > 0)
        elif market in {"player_reception_yds", "player_receptions"}:
            participated = (num(row, "targets") > 0 or
                            num(row, "receptions") > 0 or
                            num(row, "receiving_yards") > 0)
        elif market in {"player_rush_yds", "player_rush_attempts",
                        "player_rush_reception_yds", "player_anytime_td"}:
            participated = (num(row, "carries") > 0 or
                            num(row, "rushing_yards") > 0 or
                            num(row, "targets") > 0 or
                            num(row, "receptions") > 0 or
                            num(row, "receiving_yards") > 0)
        else:
            # Defense/kicking feeds do not consistently publish opportunity
            # columns. A non-zero market stat is still verified participation;
            # a missing/zero row is never converted into an Under observation.
            try:
                raw = float(row.get(stat_col, 0))
                participated = math.isfinite(raw) and raw != 0
            except (TypeError, ValueError, StopIteration):
                participated = False
        if participated:
            keep.append(row.name)
    return pdf.loc[keep]


def _new_numeric_values(rows, column, limit=None):
    values = []
    if rows is None or column not in rows.columns:
        return values
    source = rows[column].tolist()
    if limit is not None:
        source = source[:limit]
    for raw_value in source:
        try:
            value = float(raw_value)
            if math.isfinite(value):
                values.append(value)
        except (TypeError, ValueError):
            continue
    return values


def _new_market_gap(market, line):
    # Small counting markets need a smaller absolute gap than yardage markets.
    if market in ("player_anytime_td", "player_pass_tds",
                  "player_pass_interceptions", "player_sacks",
                  "player_defensive_interceptions", "player_field_goals"):
        return 0.12
    if market in ("player_receptions", "player_rush_attempts",
                  "player_pass_completions", "player_pass_attempts"):
        return 0.45
    return max(1.0, abs(float(line or 0)) * 0.035)


def _new_exact_history(df, name, lookup=None):
    """NEW full-name identity includes suffix variants and previous teams."""
    if df is None or "player_display_name" not in df.columns:
        return df.iloc[0:0] if df is not None else None
    return _nfl_player_history(df, name, lookup)


def _analyze_new_prop_raw(pl: Dict, df, home_abbr: str, away_abbr: str,
                          opponent_df=None) -> Optional[Dict]:
    """Independent NEW model.

    It intentionally has a different contract internally from OLD: identity is
    exact and game-team canonical, recent/H-A/opponent samples are exponentially
    weighted and shrunk, and a line is a prior rather than a zero observation.
    The returned fields retain the display contract so existing cards/categories
    continue to work.
    """
    name, line = str(pl.get("name") or "").strip(), pl.get("line")
    market, label, stat_col = (pl.get("market") or ""), pl.get("label") or "", pl.get("stat_col") or ""
    try:
        line = float(line)
    except (TypeError, ValueError):
        return None
    if not name or not stat_col:
        return None
    pdf = _new_exact_history(df, name)
    if pdf is None:
        return None
    pdf_sorted = pdf.sort_values(["season", "week"], ascending=False) if not pdf.empty else pdf
    historical_position = (_first_str(pdf_sorted["position"])
                           if "position" in pdf_sorted.columns else "")
    position = _nfl_position_group(pl.get("roster_position") or historical_position)
    if market == "player_anytime_td" and position not in {"QB", "RB", "WR", "TE"}:
        return None
    if market == "player_rush_reception_yds" and position != "RB":
        return None

    # NEW never invents a team or assumes home.  A sportsbook backup remains
    # eligible when roster data identifies it; established players may use an
    # exact nflverse team as a canonical fallback.
    roster_team = str(pl.get("roster_team") or "").upper().strip()
    hist_team = str(pdf_sorted["recent_team"].iloc[0] if not pdf_sorted.empty else "").upper().strip()
    team = roster_team or hist_team
    if team == home_abbr:
        opp, home_road, side = away_abbr, "H", "HOME"
    elif team == away_abbr:
        opp, home_road, side = home_abbr, "R", "AWAY"
    else:
        # A no-history player without a current roster match is not a canonical
        # official pick. Keep this closed rather than guessing a matchup.
        return None
    if not opp or opp == team:
        return None

    pid = _first_str(pdf_sorted["player_id"]) if "player_id" in pdf_sorted.columns else ""
    head = _first_str(pdf_sorted["headshot_url"]) if "headshot_url" in pdf_sorted.columns else ""
    if not pid:
        pid = _norm(name)
    # A zero stat from a row with no verified opportunity is missing history,
    # not an observed Under. Keep the sportsbook line as the sparse prior.
    participation_pdf = _new_participation_rows(
        pdf_sorted, market, position, stat_col)
    values = []
    values = _new_numeric_values(participation_pdf, stat_col)
    # Anytime TD is represented by the derived loader column where available.
    n_total = len(values)
    sparse = n_total < 5
    sparse_status = "ROOKIE/SPARSE" if sparse else "ESTABLISHED"
    recent = values[:10]
    recent_mean = _new_weighted_mean(recent)
    if home_road and _HA_LOADED and not participation_pdf.empty:
        ha_rows = participation_pdf[participation_pdf.apply(
            lambda r: _ha_side(r, home_road == "H"), axis=1)]
    else:
        ha_rows = participation_pdf
    ha_values = _new_numeric_values(ha_rows, stat_col, 10)
    ha_mean = _new_weighted_mean(ha_values[:10])
    # NEW participation logic applies to the separate all-season opponent
    # frame; recent form above remains restricted to the two-season model df.
    opp_source = opponent_df if opponent_df is not None else df
    opp_pdf = _new_exact_history(
        opp_source, name, _NFL_OPP_PLAYER_LOOKUP)
    opp_participation_pdf = _new_participation_rows(
        opp_pdf.sort_values(["season", "week"], ascending=False),
        market, position, stat_col)
    opp_rows = opp_participation_pdf[
        opp_participation_pdf["opponent_team"].astype(str).str.upper() == opp
    ] if (not opp_participation_pdf.empty and "opponent_team" in opp_participation_pdf.columns) \
        else opp_participation_pdf.iloc[0:0]
    opp_rows = opp_rows.sort_values(["season", "week"], ascending=False)
    opp_values = _new_numeric_values(opp_rows, stat_col)
    opp_mean = _new_weighted_mean(opp_values)
    opp_over_hits = sum(1 for value in opp_values if value > line)
    opp_under_hits = sum(1 for value in opp_values if value < line)
    history_lock = None
    if market != "player_anytime_td" and len(opp_values) >= 2:
        if opp_over_hits == len(opp_values):
            history_lock = "OVER"
        elif opp_under_hits == len(opp_values):
            history_lock = "UNDER"
    history_lock_reason = (
        f"Opponent history {len(opp_values)}/{len(opp_values)} {history_lock} today's line sets the pick side"
        if history_lock else "")

    role = _nfl_role_profile(df, team, position, name, stat_col)
    role_risk = _nfl_role_risk_context(pl, role)
    defense_venue = "AWAY" if home_road == "H" else "HOME"
    posdef = _nfl_posdef_profile(df, opp, position, stat_col, defense_venue)
    defcontext = _nfl_defense_context_profile(
        df, opp, position, defense_venue)
    def_factor, def_rank = float(posdef.get("factor",1.0)), posdef.get("rank")
    def_lbl = posdef.get("label") or _OPP_ADJ_COLS.get(stat_col, "")
    role_factor=float(role.get("factor",1.0))
    combined_factor=max(.86,min(1.14,role_factor*def_factor))
    # For sparse players the line is the primary prior. Actual participation,
    # availability, and same-position opportunity factors only move the
    # projection away from that prior conservatively.
    injury_status = str(pl.get("injury_status") or "UNVERIFIED").upper()
    try:
        participation_probability = float(pl.get("participation_probability"))
        if not math.isfinite(participation_probability):
            raise ValueError
        participation_probability = max(0.0, min(1.0, participation_probability))
    except (TypeError, ValueError):
        participation_probability = (
            1.0 if pl.get("availability_verified") and injury_status == "ACTIVE"
            else 0.85)
    try:
        injury_opportunity_factor = float(
            pl.get("injury_opportunity_factor") or 1.0)
        if not math.isfinite(injury_opportunity_factor):
            raise ValueError
        injury_opportunity_factor = max(0.90, min(1.10, injury_opportunity_factor))
    except (TypeError, ValueError):
        injury_opportunity_factor = 1.0
    participation_scale = 0.15 + 0.85 * participation_probability
    # Projection volume uses current-form and venue form only. Opponent history
    # remains side/rate evidence and must not inject its raw stat average into
    # the projection, where one outlier meeting can overwhelm the estimate.
    components = [(recent_mean, .70), (ha_mean, .30)]
    known = [(v, w) for v, w in components if v is not None]
    if known:
        denom = sum(w for _, w in known)
        evidence = sum(v * w for v, w in known) / denom
        defensive = evidence * combined_factor
        defensive = line + (
            (defensive - line) * participation_scale * injury_opportunity_factor)
        evidence_weight = min(1.0, n_total / 8.0)
        projection = line * (1.0 - evidence_weight) + defensive * evidence_weight
    else:
        evidence, projection, evidence_weight = None, line, 0.0
    projection = round(float(projection), 1)
    weather_snapshot = pl.get("weather") if isinstance(pl.get("weather"), dict) else {}
    weather_factor = _nfl_weather_factors(weather_snapshot, market, position)
    weather_base_projection = projection
    if weather_snapshot.get("status") == "OK":
        projection = round(projection * weather_factor, 1)
    gap = round(projection - line, 1)

    # Side-aware, recency-weighted hit rate.  Missing history is not a hit or
    # miss and therefore never manufactures an Under.
    def weighted_rate(vals, over=True):
        pairs = []
        for i, value in enumerate(vals[:10]):
            try:
                value = float(value)
                if not math.isfinite(value):
                    continue
                pairs.append((value, pow(2.718281828, -.16 * i)))
            except (TypeError, ValueError):
                continue
        if not pairs:
            return None
        return sum(w for v, w in pairs if (v > line if over else v < line)) / sum(w for _, w in pairs) * 100
    over_rate = weighted_rate(recent, True)
    under_rate = weighted_rate(recent, False)
    weather_base_over = over_rate
    weather_base_under = under_rate
    if weather_snapshot.get("status") == "OK" and weather_factor != 1.0:
        over_rate = (round(50.0 + (over_rate - 50.0) * weather_factor, 1)
                     if over_rate is not None else None)
        under_factor = 2.0 - weather_factor
        under_rate = (round(50.0 + (under_rate - 50.0) * under_factor, 1)
                      if under_rate is not None else None)
    side_rate = None
    pick = None
    value_edge = None
    if market == "player_anytime_td":
        implied = _nfl_implied_prob(pl.get("over_odds"))
        value_edge = round((over_rate or 0) - implied, 1) if implied is not None and over_rate is not None else None
        if (over_rate is not None and over_rate >= 55 and value_edge is not None
                and value_edge >= 4 and abs(gap) >= _new_market_gap(market, line)):
            pick, side_rate = "OVER", over_rate
    else:
        if gap >= _new_market_gap(market, line) and (over_rate or 0) >= 55:
            pick, side_rate = "OVER", over_rate
        elif gap <= -_new_market_gap(market, line) and (under_rate or 0) >= 55:
            pick, side_rate = "UNDER", under_rate
        if history_lock:
            pick = history_lock
            recent_side_rate = over_rate if history_lock == "OVER" else under_rate
            side_rate = round(
                (100.0 + recent_side_rate) / 2.0, 1
            ) if recent_side_rate is not None else 100.0
    # A confirmed absence is not an Under signal. Suppress the card rather than
    # letting zero participation or a stale historical rate create certainty.
    if injury_status in {"OUT", "DOUBTFUL"} and participation_probability <= 0.25:
        pick, side_rate, value_edge = None, None, None
    elif side_rate is not None and participation_scale < 0.999:
        side_rate = 50.0 + (side_rate - 50.0) * participation_scale
        if side_rate < 55.0:
            pick, side_rate, value_edge = None, None, value_edge
    # A sparse player needs genuine observed participation and a stronger edge;
    # a missing history row remains an eligible visible no-play, never Under.
    meaningful_opportunity = False
    if not participation_pdf.empty:
        for _, observed in participation_pdf.head(3).iterrows():
            try:
                if market in {"player_pass_yds", "player_pass_tds",
                              "player_pass_completions", "player_pass_attempts",
                              "player_pass_interceptions"}:
                    opportunity = float(observed.get("attempts") or 0)
                elif market in {"player_reception_yds", "player_receptions"}:
                    opportunity = max(
                        float(observed.get("targets") or 0),
                        float(observed.get("receptions") or 0))
                else:
                    opportunity = max(
                        float(observed.get("carries") or 0),
                        float(observed.get("targets") or 0),
                        float(observed.get("receptions") or 0))
                if math.isfinite(opportunity) and opportunity >= 3:
                    meaningful_opportunity = True
                    break
            except (TypeError, ValueError):
                continue
    if sparse and (
        n_total < 1
        or not meaningful_opportunity
        or abs(gap) < _new_market_gap(market, line) * 1.35
    ):
        pick, side_rate, value_edge = None, None, value_edge
    score = round(side_rate if side_rate is not None else 0, 1)
    if side_rate is not None and pick:
        # A permissive defense helps an OVER but hurts an UNDER, and vice versa.
        side_factor = combined_factor if pick == "OVER" else (2.0 - combined_factor)
        score = round(max(0.0, min(100.0, 50.0 + (score - 50.0) * side_factor)), 1)
    if pick and role_risk["confidenceFactor"] != 1.0:
        score = round(50.0 + (score - 50.0)
                      * role_risk["confidenceFactor"], 1)
    avg = round(recent_mean, 1) if recent_mean is not None else None
    def_adj = round((def_factor - 1.0) * 100)
    unadjusted_projection = (
        line * (1.0 - evidence_weight)
        + (evidence if evidence is not None else line) * evidence_weight)
    injury_adj = round(projection - unadjusted_projection, 1)
    glog = []
    for _, row in participation_pdf.head(10).iterrows():
        try:
            val = float(row[stat_col])
            if math.isfinite(val):
                glog.append({"d": f"{int(row['season'])} W{int(row['week'])}",
                             "v": round(val, 1), "o": str(row.get("opponent_team") or "")})
        except (TypeError, ValueError, KeyError):
            continue
    vs_opp_log = []
    if not opp_rows.empty:
        for _, observed in opp_rows.sort_values(
                ["season", "week"], ascending=False).iterrows():
            try:
                value = float(observed.get(stat_col))
                if math.isfinite(value):
                    vs_opp_log.append({
                        "d": f"{int(observed['season'])} W{int(observed['week'])}",
                        "v": round(value, 1),
                        "ha": _nfl_history_venue(observed),
                    })
            except (TypeError, ValueError, KeyError):
                continue
    # The legacy cards expect an integer hit count, sample count, and a short
    # percentage for the selected side. Keep NEW's weighted rates, but satisfy
    # that display contract instead of leaking None and raw float precision.
    display_over = pick != "UNDER"
    def display_sample(vals):
        clean = []
        for value in vals:
            try:
                number = float(value)
                if math.isfinite(number):
                    clean.append(number)
            except (TypeError, ValueError):
                continue
        hits = sum(1 for value in clean
                   if (value > line if display_over else value < line))
        rate = weighted_rate(clean, display_over)
        return hits, len(clean), (round(rate, 1) if rate is not None else None)
    opp_hits, opp_total, opp_rate = display_sample(opp_values)
    ha_hits, ha_total, ha_rate = display_sample(ha_values)
    recent_hits, recent_total, recent_rate = display_sample(recent)
    return {
        "name": name, "pid": pid, "position": position, "roster_position": position,
        "team": team, "opponent": opp, "homeRoad": home_road, "side": side,
        "head": head, "game": pl.get("game", ""), "game_start": pl.get("game_start", ""),
        "mkt": label, "label": label, "market": market, "line": line,
        "dispLine": line, "realLine": line, "realOdds": pl.get("over_odds"),
        "realUnderOdds": pl.get("under_odds"), "over_odds": pl.get("over_odds"),
        "under_odds": pl.get("under_odds"), "over_book": pl.get("over_book", ""),
        "under_book": pl.get("under_book", ""), "isAlternate": bool(pl.get("is_alternate")),
        "sourceMarket": pl.get("source_market", market), "quoteFetchedAt": pl.get("quote_fetched_at"),
        "quoteStatus": pl.get("quote_status", "UNVERIFIED"), "avg": avg,
        "avgA": round(opp_mean, 1) if opp_mean is not None else None,
        "rateA": opp_rate, "hitsA": opp_hits, "totA": opp_total,
        "rateB": ha_rate, "hitsB": ha_hits, "totB": ha_total,
        "vsLineHits": recent_hits, "vsLineTotal": recent_total,
        "vsLineRate": recent_rate,
        "underHits": sum(1 for value in recent if value < line),
        "underTotal": recent_total,
        "underRate": round(under_rate, 1) if under_rate is not None else None,
        "underLine": line, "defAdj": def_adj, "defRank": def_rank, "defLbl": def_lbl,
        "role": role.get("role"), "roleRank": role.get("roleRank"),
        "teamOptionRank": role.get("option_rank"), "roleConfidence": role.get("confidence"),
        "roleFactor": role_factor, "roleReason": role.get("reason"),
        "positionGroup": position,
        "recentSnapPct": role.get("snapRecent"),
        "priorSnapPct": role.get("snapPrior"),
        "snapTrendPct": role.get("snapDelta"),
        "depthRank": pl.get("depth_rank"),
        "depthPosition": pl.get("depth_position"),
        "depthChart": pl.get("depth_chart", ""),
        "roleRiskStatus": role_risk["status"],
        "roleRiskReasons": role_risk["reasons"],
        "roleRiskSource": role_risk["source"],
        "roleRiskUpdatedAt": role_risk["updatedAt"],
        "roleRiskBlockPremium": role_risk["blockPremium"],
        "defAllowed": posdef.get("allowed"), "defSample": posdef.get("sample",0),
        "defenseVenue": posdef.get("defenseVenue"),
        "defHomeAllowed": posdef.get("defHomeAllowed"),
        "defHomeSample": posdef.get("defHomeSample",0),
        "defAwayAllowed": posdef.get("defAwayAllowed"),
        "defAwaySample": posdef.get("defAwaySample",0),
        "defConfidence": posdef.get("confidence",.15),
        "defRawFactor": posdef.get("rawFactor"), "defFactor": def_factor,
        "defSchemaVersion": posdef.get("defSchemaVersion", 2),
        "defPositionGroup": posdef.get("defPositionGroup", position),
        "defStat": posdef.get("defStat", stat_col),
        "defMetric": posdef.get("defMetric"),
        "defSourceSeasons": posdef.get("defSourceSeasons") or [],
        "defSourceWindow": posdef.get("defSourceWindow") or "",
        "defUnavailable": posdef.get("defUnavailable"),
         **defcontext,
        "combinedFactor": combined_factor, "baseProjection": evidence,
        "baseProbability": side_rate, "adjustedProjection": projection,
        "adjustedProbability": score,
        "historyLock": history_lock,
        "historyLockReason": history_lock_reason,
        "projAvg": projection, "baseProjAvg": evidence, "injuryAdj": injury_adj,
        "injuryOpportunityFactor": injury_opportunity_factor,
        "injuryOpportunityReasons": pl.get("injury_opportunity_reasons") or [],
        "weatherApplied": bool(weather_snapshot.get("status") == "OK"
                               and weather_factor != 1.0),
        "weatherFactor": weather_factor,
        "weatherBaseProjection": weather_base_projection,
        "weatherAdjustment": round(projection - weather_base_projection, 1),
        "weatherBaseProbability": (weather_base_under if pick == "UNDER"
                                   else weather_base_over),
        "weatherSeverity": weather_snapshot.get("severity", 0),
        "weatherLabel": weather_snapshot.get("label", ""),
        "weatherSummary": weather_snapshot.get("summary", ""),
        "weatherStatus": weather_snapshot.get("status", "UNAVAILABLE"),
        "isRookie": bool(pl.get("rookie_verified") and pl.get("is_rookie")),
        "rookieVerified": bool(pl.get("rookie_verified")),
        "rosterExperienceYears": pl.get("roster_experience_years"),
        "injuryStatus": injury_status,
        "injuryNote": pl.get("injury_note", ""), "injuryUpdatedAt": pl.get("injury_updated_at"),
        "participationProbability": participation_probability,
        "availabilityVerified": bool(pl.get("availability_verified")),
        "coachEligible": bool(pl.get("coach_eligible", True)), "score": score, "dispScore": score,
        "gap": gap, "pick": pick, "tag": "SUGGESTED" if pick else "",
        "betQualified": bool(pick) and not role_risk["blockPremium"],
        "valueEdge": value_edge,
        "valueReason": "" if pick else ("Sparse history / no meaningful projection gap"
                                        if sparse else "No meaningful model gap"),
        "glog": glog, "vsOppLog": vs_opp_log, "sparseHistory": sparse,
        "sparseStatus": sparse_status, "model_version": "NEW-v2-ewma-weather",
        "opp": opp, "vs_opp_avg": round(opp_mean, 1) if opp_mean is not None else None,
        "vs_opp_games": opp_total, "vs_opp_hits": opp_hits,
        "vs_opp_rate": opp_rate, "l10_avg": avg,
        "l10_games": recent_total, "l10_hits": recent_hits, "l10_rate": recent_rate,
        "games": n_total, "history": ", ".join(str(round(float(v), 1)) for v in recent[:8]) or "--",
        "system": "NEW",
    }

def _analyze_new_prop(pl: Dict, df, home_abbr: str, away_abbr: str,
                      opponent_df=None) -> Optional[Dict]:
    return _new_sanitize_json(
        _analyze_new_prop_raw(pl, df, home_abbr, away_abbr, opponent_df))


# ── NFL Game Predictor helpers ─────────────────────────────────────────────────

_NFL_GP_WORKER = ThreadPoolExecutor(max_workers=1, thread_name_prefix="nfl-gp")

async def _nfl_gp_compute(fn, *args, **kwargs):
    # One worker across all dates/jobs bounds simultaneous pandas allocations.
    return await asyncio.get_running_loop().run_in_executor(
        _NFL_GP_WORKER, partial(fn, *args, **kwargs))

def _nfl_gp_frame(df):
    """All rows/seasons, but only columns actually read by Game Predictor."""
    columns = ["season", "season_type", "week", "recent_team", "opponent_team",
               "passing_yards", "rushing_yards", "player_display_name", "position",
               # nflverse has these on some releases; retaining them enables
               # point-in-time venue splits without making them required.
               "home_team", "away_team"]
    return df.loc[:, [c for c in columns if c in df.columns]]

def _nfl_stats_before_game(df, target_season=None, target_week=None,
                           target_type: str = "REG"):
    """Exclude every stats row at or after the selected game's week."""
    try:
        if target_season is None or "season" not in df.columns:
            return df
        seasons = df["season"].fillna(0).astype(int)
        older = seasons < int(target_season)
        same_season = seasons == int(target_season)
        weeks = df["week"].fillna(0).astype(int)
        target_week = _nflverse_week(target_type, target_week or 1)
        if "season_type" in df.columns:
            types = df["season_type"].fillna("REG").astype(str).str.upper()
            if str(target_type or "REG").upper() == "POST":
                prior_same = (types == "REG") | ((types == "POST") & (weeks < target_week))
            else:
                prior_same = (types == "REG") & (weeks < target_week)
        else:
            prior_same = weeks < target_week
        return df[older | (same_season & prior_same)]
    except Exception:
        try:
            return df.iloc[0:0]
        except Exception:
            return df

def _nfl_prop_analysis_frame(df, target_season=None, target_week=None,
                             target_type: str = "REG"):
    """Return the point-in-time two-season window used by player props.

    The source frame intentionally retains older seasons for Game Predictor
    H2H/replay support, but player props should not repeatedly scan or blend
    every season ever downloaded. The selected season and its immediately
    preceding season are the complete model window.
    """
    try:
        if df is None or "season" not in df.columns:
            return df
        if target_season is None:
            seasons = df["season"].dropna()
            if seasons.empty:
                return df
            target_season = int(seasons.max())
        target_type = str(target_type or "REG").upper()
        seasons = df["season"].fillna(0).astype(int)
        weeks = df["week"].fillna(0).astype(int)
        target_week = _nflverse_week(target_type, target_week or 1)
        target_season = int(target_season)
        # Build one final mask against the compact process-wide frame. The old
        # path first materialized every pre-game season and then copied the
        # two-season subset, briefly holding two large derived DataFrames.
        mask = seasons.eq(target_season - 1)
        same_season = seasons.eq(target_season)
        if "season_type" in df.columns:
            types = df["season_type"].fillna("REG").astype(str).str.upper()
            if target_type == "POST":
                prior_same = types.eq("REG") | (
                    types.eq("POST") & weeks.lt(target_week))
            else:
                prior_same = types.eq("REG") & weeks.lt(target_week)
        else:
            prior_same = weeks.lt(target_week)
        mask = mask | (same_season & prior_same)
        # Regular-season boards must compare regular-season games only. Older
        # postseason rows otherwise leak into the prior-season window and
        # distort venue averages, history rates, and recent-form inputs.
        if target_type == "REG" and "season_type" in df.columns:
            mask = mask & types.eq("REG")
        out = df.loc[mask].copy()
        out.attrs["nfl_target_season"] = target_season
        out.attrs["nfl_target_week"] = int(target_week or 1)
        out.attrs["nfl_target_type"] = target_type
        return out
    except Exception as exc:
        print(f"[NFL Analysis] two-season point-in-time filter failed closed: {exc}")
        try:
            empty = df.iloc[0:0].copy()
            if target_season is not None:
                empty.attrs["nfl_target_season"] = int(target_season)
                empty.attrs["nfl_target_week"] = int(target_week or 1)
                empty.attrs["nfl_target_type"] = str(
                    target_type or "REG").upper()
            return empty
        except Exception:
            return df

# Response-only compatibility layer for boards written before the venue split.
# This never writes a cache or tracking ledger and is intentionally keyed by the
# requested board identity. Do not retain complete enriched boards in RAM.
_NFL_ENRICHED_RESULTS = {}

def _nfl_enrich_cached_result(result, df=None, target_season=None,
                              target_week=None, target_type="REG",
                              system="OLD"):
    if not isinstance(result, dict):
        return result
    if result.get("_nflVenueEnrichedV5"):
        return result
    # Callers own freshly decoded disk/Supabase payloads, not shared objects.
    out = result
    frame = (_nfl_prop_analysis_frame(df, target_season, target_week, target_type)
             if df is not None and target_season is not None else None)
    seen = set()
    for bucket in ("picks", "all", "td_picks"):
        rows = out.get(bucket) or []
        for pick in rows:
            if not isinstance(pick, dict) or id(pick) in seen:
                continue
            seen.add(id(pick))
            opponent = str(pick.get("opponent") or "").upper()
            team = str(pick.get("team") or "").upper()
            # Historical opponent logs predate the venue field.  The opponent
            # is the stable identity across player team changes, so invert its
            # nflverse venue first; only then fall back to the player's team.
            for log in pick.get("vsOppLog") or []:
                if not isinstance(log, dict) or log.get("ha"):
                    continue
                m = re.search(r"^\s*(\d{4})\s+W(\d+)", str(log.get("d") or ""))
                if not m or not _HA_LOADED:
                    continue
                season, week = int(m.group(1)), int(m.group(2))
                stype = "POST" if week >= 19 else "REG"
                lookup_week = _espn_ha_week(stype, week)
                venue = _HA_LOOKUP.get((season, stype, lookup_week, opponent))
                if venue in ("HOME", "AWAY"):
                    log["ha"] = "AWAY" if venue == "HOME" else "HOME"
                    continue
                venue = _HA_LOOKUP.get((season, stype, lookup_week, team))
                if venue in ("HOME", "AWAY"):
                    log["ha"] = venue

            # Recompute every cached row from the current point-in-time frame.
            # Older snapshots can already contain the retired weighted values,
            # so field presence alone does not prove the venue averages are
            # current or correctly calculated.
            market = str(pick.get("market") or "")
            stat = PROP_TO_COL.get(market)
            venue = ("AWAY" if pick.get("homeRoad") == "H" else "HOME"
                     if pick.get("homeRoad") == "R" else None)
            if frame is None or not stat or not opponent or not venue:
                pick.update({
                    "defenseVenue": venue, "defHomeAllowed": None,
                    "defHomeSample": 0, "defAwayAllowed": None,
                    "defAwaySample": 0, "defAllowed": None, "defSample": 0,
                    "defFactor": 1.0, "defRawFactor": 1.0,
                    "defConfidence": .15,
                    "defUnavailable": "Venue defense split unavailable",
                    "defSchemaVersion": 2,
                    "defPositionGroup": _nfl_position_group(
                        pick.get("positionGroup") or pick.get("position")
                        or pick.get("roster_position") or ""),
                    "defStat": stat,
                    "defMetric": "team positional total per completed game",
                    "defSourceSeasons": [],
                    "defSourceWindow": "",
                    "contextSchemaVersion": 1,
                    "contextVenue": venue,
                    "contextUnavailable": "Authentic completed-game context unavailable",
                })
                continue
            pos = _nfl_position_group(
                pick.get("positionGroup") or pick.get("position")
                or pick.get("roster_position") or "")
            profile = _nfl_posdef_profile(frame, opponent, pos, stat, venue)
            context = _nfl_defense_context_profile(frame, opponent, pos, venue)
            pick.update({
                "defenseVenue": profile.get("defenseVenue") or venue,
                "defHomeAllowed": profile.get("defHomeAllowed"),
                "defHomeSample": profile.get("defHomeSample", 0),
                "defAwayAllowed": profile.get("defAwayAllowed"),
                "defAwaySample": profile.get("defAwaySample", 0),
                "defAllowed": profile.get("allowed"),
                "defSample": profile.get("sample", 0),
                "defFactor": profile.get("factor", 1.0),
                "defRawFactor": profile.get("rawFactor", 1.0),
                "defRank": profile.get("rank"),
                "defConfidence": profile.get("confidence", .15),
                "defAdj": round((profile.get("factor", 1.0) - 1) * 100, 1),
                "defSchemaVersion": profile.get("defSchemaVersion", 2),
                "defPositionGroup": profile.get("defPositionGroup", pos),
                "defStat": profile.get("defStat", stat),
                "defMetric": profile.get("defMetric"),
                "defSourceSeasons": profile.get("defSourceSeasons") or [],
                "defSourceWindow": profile.get("defSourceWindow") or "",
                "defUnavailable": profile.get("defUnavailable"),
                **context,
            })
            # A saved base probability is sufficient to restore the exact
            # side-aware venue nudge without reconstructing player history.
            # A perfect opponent-history record locks only the pick direction;
            # the selected HOME/AWAY defense still changes confidence.
            if (pick.get("baseProbability") is not None
                    and market != "player_anytime_td"):
                try:
                    base = float(pick["baseProbability"])
                    role_factor = float(pick.get("roleFactor") or 1.0)
                    combined = max(.86, min(
                        1.14, role_factor * float(profile.get("factor", 1.0))))
                    side = str(pick.get("pick") or "").upper()
                    side_factor = (
                        combined if side == "OVER"
                        else 2.0 - combined if side == "UNDER"
                        else 1.0)
                    if str(system).upper() == "NEW":
                        adjusted = 50.0 + (base - 50.0) * side_factor
                    else:
                        adjusted = base + (side_factor - 1.0) * 35.0
                        injury_factor = float(
                            pick.get("injuryOpportunityFactor") or 1.0)
                        if injury_factor != 1.0:
                            injury_side_factor = (
                                injury_factor if side == "OVER"
                                else 2.0 - injury_factor)
                            adjusted *= injury_side_factor
                        injury_status = str(
                            pick.get("injuryStatus") or "").upper()
                        if injury_status == "QUESTIONABLE":
                            adjusted = 50.0 + (adjusted - 50.0) * .80
                        elif injury_status == "LIMITED":
                            adjusted = 50.0 + (adjusted - 50.0) * .92
                    adjusted = max(0.0, min(100.0, adjusted))
                    pick["adjustedProbability"] = round(adjusted, 1)
                    pick["score"] = pick["dispScore"] = pick["adjustedProbability"]
                    pick["combinedFactor"] = round(combined, 3)
                except (TypeError, ValueError):
                    pass
    out.pop("_nflVenueEnrichedV1", None)
    out.pop("_nflVenueEnrichedV2", None)
    out.pop("_nflVenueEnrichedV3", None)
    out["_nflVenueEnrichedV5"] = True
    out["defense_schema_version"] = 3
    return _nfl_json_ready(out)

async def _nfl_enrich_cached_response(result, date_str, system="OLD"):
    """Enrich an old saved board without calling ESPN."""
    # Get Picks is a frozen read path.  A pre-context snapshot is displayed
    # with an explicit warning; never download/analyze it or fabricate context.
    if isinstance(result, dict) and result.get("defense_schema_version") != 3:
        result["defense_legacy_warning"] = (
            "Legacy saved board: defensive venue/context metrics are unverified "
            "and were not recomputed.")
        return result
    if not isinstance(result, dict) or result.get("_nflVenueEnrichedV5") \
            or result.get("defense_schema_version") == 3:
        return result
    try:
        await _build_ha_lookup()
        df = await get_nfl_stats()
        schedule_rows = await _load_nfl_games_history()
        game_row = next(
            (row for row in schedule_rows
             if str(row.get("gameday") or "") == str(date_str)),
            {})
        game_type = str(game_row.get("game_type") or "REG").upper()
        target_type = "REG" if game_type == "REG" else "POST"
        target_week = game_row.get("week")
        if target_type == "POST":
            try:
                target_week = _espn_ha_week("POST", int(target_week))
            except (TypeError, ValueError):
                pass
        enriched = await asyncio.to_thread(
            _nfl_enrich_cached_result, result, df,
            game_row.get("season"), target_week, target_type,
            system)
    except Exception as exc:
        print(f"[NFL cache enrichment] failed closed: {exc}")
        enriched = _nfl_enrich_cached_result(result, system=system)
    return enriched
def _nfl_gp_ha_value(season, season_type, week, team):
    """Resolve nflverse team/week identity against the shared ESPN map."""
    if not _HA_LOADED:
        return None
    try:
        st = str(season_type or "REG").upper()
        raw_week = int(week)
        if st == "POST" and raw_week == 22:
            candidates = (5, 4)
        elif st == "POST" and 19 <= raw_week <= 21:
            candidates = (raw_week - 18,)
        else:
            candidates = (_espn_ha_week(st, raw_week),)
        abbr = _NFLVERSE_TO_ESPN.get(str(team).upper(), str(team).upper())
        for wk in candidates:
            value = _HA_LOOKUP.get((int(season), st, int(wk), abbr))
            if value:
                return value
        return None
    except (TypeError, ValueError):
        return None

def _nfl_gp_point_profiles(df, target_season, target_week, target_type="REG",
                           matchup_teams=None):
    """Compact point-in-time team offense/defense and venue profiles.

    This deliberately uses the same player-yardage game aggregation as the
    existing model.  It is a single grouped pass for a slate, rather than 32
    independent full-frame scans, and fails open when venue columns are absent.
    """
    out = {}
    try:
        off_sources = {}
        def_sources = {}
        sdf = _nfl_stats_before_game(df, target_season, target_week, target_type)
        # Select each team's target-season rows independently.  A team with
        # no target-season pregame data gets exactly the prior regular season;
        # older seasons are never mixed into this point-in-time rank pool.
        if "season" in sdf.columns and "recent_team" in sdf.columns:
            norm = lambda s: _NFLVERSE_TO_ESPN.get(str(s).upper(), str(s).upper())
            current = sdf[sdf["season"].astype(int) == int(target_season)]
            prior = sdf[sdf["season"].astype(int) == int(target_season) - 1]
            if "season_type" in prior.columns:
                prior = prior[prior["season_type"].astype(str).str.upper() == "REG"]
            current = current.copy()
            prior = prior.copy()
            for frame in (current, prior):
                frame["recent_team"] = frame["recent_team"].map(norm)
                if "opponent_team" in frame.columns:
                    frame["opponent_team"] = frame["opponent_team"].map(norm)
                for venue_col in ("home_team", "away_team"):
                    if venue_col in frame.columns:
                        frame[venue_col] = frame[venue_col].map(norm)
            candidates = set(norm(x) for x in current["recent_team"].dropna())
            if "opponent_team" in current.columns:
                candidates.update(norm(x) for x in current["opponent_team"].dropna())
            candidates.update(norm(x) for x in prior["recent_team"].dropna())
            if "opponent_team" in prior.columns:
                candidates.update(norm(x) for x in prior["opponent_team"].dropna())
            candidates.update(norm(x) for x in (matchup_teams or []))
            selected = []
            for team in candidates:
                c_mask = current["recent_team"].map(norm).eq(team)
                if "opponent_team" in current.columns:
                    c_mask = c_mask | current["opponent_team"].map(norm).eq(team)
                if c_mask.any():
                    selected.append(current[c_mask])
                else:
                    p_mask = prior["recent_team"].map(norm).eq(team)
                    if "opponent_team" in prior.columns:
                        p_mask = p_mask | prior["opponent_team"].map(norm).eq(team)
                    if p_mask.any():
                        selected.append(prior[p_mask])
            if selected:
                sdf = pd.concat(selected, ignore_index=True).drop_duplicates()
            sdf["recent_team"] = sdf["recent_team"].map(norm)
            if "opponent_team" in sdf.columns:
                sdf["opponent_team"] = sdf["opponent_team"].map(norm)
            for venue_col in ("home_team", "away_team"):
                if venue_col in sdf.columns:
                    sdf[venue_col] = sdf[venue_col].map(norm)
            off_sources = {}
            def_sources = {}
            for team in candidates:
                off_now = current[current["recent_team"].eq(team)]
                off_sources[team] = (off_now if not off_now.empty else
                                     prior[prior["recent_team"].eq(team)])
                def_now = (current[current["opponent_team"].eq(team)]
                           if "opponent_team" in current.columns else current.iloc[0:0])
                def_sources[team] = (def_now if not def_now.empty else
                                     (prior[prior["opponent_team"].eq(team)]
                                      if "opponent_team" in prior.columns else prior.iloc[0:0]))
        yards = [c for c in ("passing_yards", "rushing_yards") if c in sdf.columns]
        if not yards or sdf.empty:
            return out
        sdf = sdf.copy()
        sdf["_gp_yards"] = sdf[yards].fillna(0).sum(axis=1)
        keys = [c for c in ("season", "week") if c in sdf.columns]
        if "recent_team" not in sdf.columns or not keys:
            return out
        venue_columns = (
            "home_team" in sdf.columns and "away_team" in sdf.columns and
            sdf["home_team"].notna().any() and sdf["away_team"].notna().any())
        venue_lookup = bool(_HA_LOADED)
        if venue_lookup and not venue_columns:
            # Resolve only unique game/team tuples, not every player row.
            venue_cols = ["season", "week", "recent_team", "opponent_team"]
            if "season_type" in sdf.columns:
                venue_cols.insert(1, "season_type")
            venue_rows = sdf[venue_cols].drop_duplicates()
            if "season_type" not in venue_rows.columns:
                venue_rows["season_type"] = "REG"
            venue_map = {}
            for row in venue_rows.itertuples(index=False):
                rv = _nfl_gp_ha_value(row.season, row.season_type, row.week,
                                      row.recent_team)
                ov = _nfl_gp_ha_value(row.season, row.season_type, row.week,
                                      row.opponent_team)
                venue_map[(row.season, row.week, row.recent_team,
                           row.opponent_team)] = (rv, ov)
            sdf["_gp_recent_venue"] = [
                venue_map.get((r.season, r.week, r.recent_team,
                               r.opponent_team), (None, None))[0]
                for r in sdf.itertuples(index=False)
            ]
            sdf["_gp_opp_venue"] = [
                venue_map.get((r.season, r.week, r.recent_team,
                               r.opponent_team), (None, None))[1]
                for r in sdf.itertuples(index=False)
            ]
        # Side-specific sources prevent a team's fallback offense from
        # becoming another team's current-season defense (and vice versa).
        side_off = {}
        side_def = {}
        teams = set(off_sources) | set(def_sources)
        for team in teams:
            odf = off_sources.get(team, sdf.iloc[0:0]).copy()
            ddf = def_sources.get(team, sdf.iloc[0:0]).copy()
            for frame in (odf, ddf):
                if not frame.empty:
                    frame["_gp_yards"] = frame[yards].fillna(0).sum(axis=1)
            side_off[team] = (odf.groupby(keys)["_gp_yards"].sum()
                              if not odf.empty else pd.Series(dtype=float))
            side_def[team] = (ddf.groupby(keys)["_gp_yards"].sum()
                              if not ddf.empty else pd.Series(dtype=float))
        off_means = [float(v.mean()) for v in side_off.values() if len(v)]
        def_means = [float(v.mean()) for v in side_def.values() if len(v)]
        all_off = sum(off_means) / len(off_means) if off_means else 350.0
        all_def = sum(def_means) / len(def_means) if def_means else 350.0
        for team in teams:
            off_games = side_off[team]
            def_games = side_def[team]
            om = float(off_games.mean()) if len(off_games) else all_off
            dm = float(def_games.mean()) if len(def_games) else all_def
            # Shrink small samples toward the league pool.
            on = float(len(off_games))
            dn = float(len(def_games))
            os = (om * on + all_off * 4) / (on + 4)
            ds = (dm * dn + all_def * 4) / (dn + 4)
            rec = {"off_yards": os, "def_yards_allowed": ds,
                   "off_pts": max(10.0, min(45.0, os * 23.0 / 350.0)),
                   "def_factor": max(.86, min(1.14, ds / 350.0)),
                   "off_games": int(on), "def_games": int(dn),
                   "venue_data_available": False}
            # Prefer actual venue columns; otherwise use the bounded ESPN map.
            if venue_columns or venue_lookup:
                off_frame = off_sources.get(team, sdf.iloc[0:0]).copy()
                def_frame = def_sources.get(team, sdf.iloc[0:0]).copy()
                for frame in (off_frame, def_frame):
                    if "_gp_yards" not in frame.columns:
                        frame["_gp_yards"] = frame[yards].fillna(0).sum(axis=1)
                for frame, column in ((off_frame, "_gp_recent_venue"),
                                      (def_frame, "_gp_opp_venue")):
                    if not venue_columns and not frame.empty:
                        frame[column] = [
                            _nfl_gp_ha_value(r.season, getattr(r, "season_type", "REG"),
                                             r.week,
                                             getattr(r, "recent_team", None)
                                             if column == "_gp_recent_venue"
                                             else getattr(r, "opponent_team", None))
                            for r in frame.itertuples(index=False)]
                if venue_columns:
                    home = off_frame[off_frame["home_team"].eq(team)]
                    away = off_frame[off_frame["away_team"].eq(team)]
                    dh = def_frame[def_frame["home_team"].eq(team)]
                    da = def_frame[def_frame["away_team"].eq(team)]
                else:
                    home = off_frame[off_frame["_gp_recent_venue"].eq("HOME")]
                    away = off_frame[off_frame["_gp_recent_venue"].eq("AWAY")]
                    dh = def_frame[def_frame["_gp_opp_venue"].eq("HOME")]
                    da = def_frame[def_frame["_gp_opp_venue"].eq("AWAY")]
                for label, rows in (("home", home), ("away", away)):
                    if not rows.empty:
                        grouped = rows.groupby(keys)["_gp_yards"].sum()
                        n = len(grouped)
                        val = (float(grouped.mean()) * n + os * 4) / (n + 4)
                        rec[label + "_off_pts"] = max(10., min(45., val * 23. / 350.))
                        rec[label + "_off_games"] = n
                        rec["venue_data_available"] = True
                # Defensive venue split is where the defense played.
                for label, rows in (("home", dh), ("away", da)):
                    if not rows.empty:
                        grouped = rows.groupby(keys)["_gp_yards"].sum()
                        n = len(grouped)
                        val = (float(grouped.mean()) * n + ds * 4) / (n + 4)
                        rec[label + "_def_factor"] = max(.86, min(1.14, val / 350.))
                        rec[label + "_def_games"] = n
                        rec["venue_data_available"] = True
            out[str(team)] = rec
        # Rank direction: offense high points is best; defense low allowed is best.
        op = sorted(out, key=lambda t: (-out[t]["off_pts"], str(t)))
        dp = sorted(out, key=lambda t: (out[t]["def_factor"], str(t)))
        for rank, team in enumerate(op, 1):
            out[team]["off_rank"] = rank
        for rank, team in enumerate(dp, 1):
            out[team]["def_rank"] = rank
    except Exception:
        return {}
    return out

def _nfl_team_pts_projection(team_abbr: str, df, n_games: int = 5,
                             target_season=None, target_week=None,
                             target_type: str = "REG") -> float:
    """Project a team's offensive point output from their L5 total yards (nfl-verse).
    ~350 total yards per game ≈ league avg 23 pts; clamped 10-45."""
    try:
        df = df[df["recent_team"] == team_abbr]
        df = _nfl_stats_before_game(df, target_season, target_week, target_type)
        off_cols = [c for c in ["passing_yards", "rushing_yards"] if c in df.columns]
        if not off_cols:
            return 23.0
        team_df = df[df["recent_team"] == team_abbr].copy()
        if team_df.empty:
            return 23.0
        team_df["_yards"] = team_df[off_cols].fillna(0).sum(axis=1)
        gw = (team_df.groupby(["season", "week"])["_yards"].sum()
              .reset_index().sort_values(["season", "week"], ascending=False).head(n_games))
        if gw.empty:
            return 23.0
        avg_yards = gw["_yards"].mean()
        pts = round(avg_yards * 23.0 / 350.0, 1)
        return max(10.0, min(45.0, pts))
    except Exception:
        return 23.0

def _nfl_team_def_strength(opp_abbr: str, df, n_games: int = 5,
                           target_season=None, target_week=None,
                           target_type: str = "REG") -> float:
    """Defensive strength multiplier (1.0 = league avg, <1 = strong, >1 = weak).
    Measures how many offensive yards opponents piled up against this team."""
    try:
        df = df[df["opponent_team"] == opp_abbr]
        df = _nfl_stats_before_game(df, target_season, target_week, target_type)
        off_cols = [c for c in ["passing_yards", "rushing_yards"] if c in df.columns]
        if not off_cols or "opponent_team" not in df.columns:
            return 1.0
        vs_df = df[df["opponent_team"] == opp_abbr].copy()
        if vs_df.empty:
            return 1.0
        vs_df["_yards"] = vs_df[off_cols].fillna(0).sum(axis=1)
        gw = (vs_df.groupby(["season", "week"])["_yards"].sum()
              .reset_index().sort_values(["season", "week"], ascending=False).head(n_games))
        avg_vs = gw["_yards"].mean() if not gw.empty else 350.0
        return round(avg_vs / 350.0, 3)
    except Exception:
        return 1.0

def _nfl_season_team_profiles(df, season: int) -> dict:
    """Build full-season offensive and defensive yardage profiles by team.
    Player rows are aggregated to team/game first so player volume is not
    mistaken for games played."""
    profiles = {}
    try:
        if "season" not in df.columns:
            return profiles
        sdf = df[df["season"] == season].copy()
        if "season_type" in sdf.columns:
            sdf = sdf[sdf["season_type"].fillna("REG").astype(str).str.upper() == "REG"]
        if sdf.empty:
            return profiles
        off_cols = [c for c in ["passing_yards", "rushing_yards"] if c in sdf.columns]
        if not off_cols:
            return profiles
        sdf["_yards"] = sdf[off_cols].fillna(0).sum(axis=1)
        if "recent_team" in sdf.columns:
            og = (sdf[sdf["recent_team"].notna()]
                  .groupby(["recent_team", "week"])["_yards"].sum()
                  .groupby(level=0).mean())
        else:
            og = {}
        if "opponent_team" in sdf.columns:
            dg = (sdf[sdf["opponent_team"].notna()]
                  .groupby(["opponent_team", "week"])["_yards"].sum()
                  .groupby(level=0).mean())
        else:
            dg = {}
        teams = set(getattr(og, "index", [])) | set(getattr(dg, "index", []))
        for team in teams:
            off_yards = float(og.get(team, 350.0))
            allowed_yards = float(dg.get(team, 350.0))
            profiles[str(team)] = {
                "off_yards": off_yards,
                "off_pts": max(10.0, min(45.0, off_yards * 23.0 / 350.0)),
                "def_factor": round(allowed_yards / 350.0, 3),
            }
    except Exception:
        return {}
    return profiles

def _nfl_pythagorean(proj_home: float, proj_away: float, exp: float = 2.37):
    """NFL Pythagorean win probability (exponent 2.37)."""
    try:
        denom = proj_home ** exp + proj_away ** exp
        if denom <= 0:
            return 50, 50
        wh = round((proj_home ** exp / denom) * 100)
        return wh, 100 - wh
    except Exception:
        return 50, 50

def _devig_nfl(odds_home, odds_away):
    """Convert American ML to de-vigged implied probabilities (additive method)."""
    def to_prob(o):
        if o is None:
            return None
        return (100 / (o + 100)) if o > 0 else (abs(o) / (abs(o) + 100))
    ph, pa = to_prob(odds_home), to_prob(odds_away)
    if ph is None or pa is None:
        return None, None
    tot = ph + pa
    return round(ph / tot * 100), round(pa / tot * 100)

def _nfl_starter_name(team_abbr: str, df, col: str = "passing_yards",
                      roster_map: dict = None) -> str:
    """Name of the CURRENT starter for this team: latest season only, and only
    players whose most recent game was with this team (excludes traded players
    like Geno Smith whose old-team rows would otherwise win on career volume)."""
    try:
        if col not in df.columns:
            return "TBD"
        latest = int(df["season"].max())
        cur = df[df["season"] == latest]
        team_df = cur[cur["recent_team"] == team_abbr]
        roster_override = False
        if roster_map:
            active_names = {k for k, v in roster_map.items()
                            if v.get("team") == team_abbr and v.get("eligible")
                            and (not v.get("position") or v.get("position") == "QB")}
            if active_names:
                all_df = df[df["player_display_name"].astype(str).map(_norm).isin(active_names)]
                if not all_df.empty:
                    team_df = all_df
                    roster_override = True
        if not team_df.empty and not roster_override:
            # Keep only players still on this team (their latest row is here)
            last_rows = (cur.sort_values(["season", "week"])
                            .groupby("player_display_name").tail(1))
            on_team = set(last_rows[last_rows["recent_team"] == team_abbr]
                          ["player_display_name"])
            team_df = team_df[team_df["player_display_name"].isin(on_team)]
        if team_df.empty:
            team_df = df[df["recent_team"] == team_abbr]
        if team_df.empty:
            return "TBD"
        grp = (team_df.groupby("player_display_name")[col].sum()
               .sort_values(ascending=False))
        return grp.index[0] if not grp.empty else "TBD"
    except Exception:
        return "TBD"

async def _build_nfl_game_predictions(espn_games: list, df, date_str: str,
                                      gl_cache: dict = None,
                                      roster_map: dict = None,
                                      progress=None, weather_by_game: dict = None) -> tuple:
    """Build Game Predictor payload for every game on today's slate.
    Fetches h2h + totals for all games concurrently via get_nfl_game_lines.
    Uses cached game lines when available (past-date lines are final) and
    returns (predictions, newly_fetched_lines_by_event_id) so the caller can
    persist them — every skipped historical call saves 10x-priced credits."""
    # Venue splits carry most of the home/away signal when available; retain
    # only a modest league residual so the effect is not counted twice.
    HOME_ADJ = 1.025
    df = await _nfl_gp_compute(_nfl_gp_frame, df)
    predictions = []
    gl_cache = dict(gl_cache or {})
    fetched: dict = {}
    season_profile_cache = {}
    point_profile_cache = {}
    venue_lookup_available = await _nfl_gp_ensure_ha()
    completed_lines = 0

    def report(message):
        if progress:
            try:
                progress(message)
            except Exception:
                pass

    async def _one_gl(g):
        nonlocal completed_lines
        eid = g.get("id", "")
        game_name = g.get("game", "") or f"{g.get('away_abbr', '')} @ {g.get('home_abbr', '')}"
        try:
            if eid and eid in gl_cache:
                return gl_cache[eid]
            if not eid:
                return {}
            # A separate deadline is required even though the underlying
            # httpx client has a timeout: connection retries and provider
            # response-body reads can otherwise keep one game pending while
            # the rest of a 13-game slate is already complete.
            gl = await asyncio.wait_for(
                get_nfl_game_lines(eid, date_str),
                timeout=_NFL_GP_GAME_LINE_TIMEOUT)
            if eid and gl:
                fetched[eid] = gl
            return gl
        except asyncio.TimeoutError:
            print(f"[GP GameLines] {game_name} skipped after "
                  f"{_NFL_GP_GAME_LINE_TIMEOUT}s deadline")
            return {}
        except Exception as exc:
            print(f"[GP GameLines] {game_name} failed: {exc}")
            return {}
        finally:
            completed_lines += 1
            report(f"Game Predictor: game lines {completed_lines}/{len(espn_games)}")

    report(f"Game Predictor: fetching game lines for {len(espn_games)} games…")

    async def _all_h2h():
        # H2H is a secondary, free-data nudge. Download it in parallel with
        # sportsbook game lines and fail open to the stats baseline if GitHub
        # is slow; it must never hold the whole picks run at this stage.
        report("Game Predictor: loading matchup history…")
        try:
            rows = await asyncio.wait_for(
                _load_nfl_games_history(), timeout=_NFL_GP_HISTORY_TIMEOUT)
        except asyncio.TimeoutError:
            print(f"[NFL H2H] skipped after {_NFL_GP_HISTORY_TIMEOUT}s deadline")
            return [{} for _ in espn_games]
        if not rows:
            return [{} for _ in espn_games]
        return await asyncio.gather(*[
            get_nfl_game_history(
                g.get("home_abbr", ""), g.get("away_abbr", ""), date_str)
            for g in espn_games
        ])

    all_gl, h2h_payloads = await asyncio.gather(
        asyncio.gather(*[_one_gl(g) for g in espn_games]),
        _all_h2h(),
    )
    report("Game Predictor: sportsbook lines and matchup history loaded")
    for game_index, (g, gl) in enumerate(zip(espn_games, all_gl)):
        report(f"Game Predictor: modeling game {game_index + 1}/{len(espn_games)}")
        gl = gl or {}
        ha = g.get("home_abbr", ""); aa = g.get("away_abbr", "")
        if not ha or not aa:
            continue
        try:
            target_season = int(g.get("season") or str(date_str)[:4])
        except Exception:
            target_season = _cur_season
        try:
            target_week = int(g.get("week") or 1)
        except Exception:
            target_week = 1
        target_type = str(g.get("season_type") or "REG").upper()
        reference_season = target_season if target_type == "POST" else target_season - 1
        if reference_season not in season_profile_cache:
            # Team profiles and the L5 projections below perform pandas
            # groupby/filter work.  Keep it off the ASGI loop while preserving
            # the same per-reference-season cache and model inputs.
            season_profile_cache[reference_season] = await _nfl_gp_compute(
                _nfl_season_team_profiles, df, reference_season)
        season_profiles = season_profile_cache[reference_season]
        profile_key = (target_season, target_week, target_type)
        if profile_key not in point_profile_cache:
            point_profile_cache[profile_key] = await _nfl_gp_compute(
                _nfl_gp_point_profiles, df, target_season, target_week, target_type,
                [g.get("home_abbr", ""), g.get("away_abbr", "")])
        point_profiles = point_profile_cache[profile_key]
        # Offensive projections (L5 team yards → pts)
        # Defensive strength belongs to the opponent being faced: away defense
        # suppresses home scoring and home defense suppresses away.  These four
        # Keep these sequential: concurrent full-history copies exceeded the
        # 512 MB instance limit. The worker keeps HTTP responsive without
        # multiplying the memory needed by pandas.
        home_off = await _nfl_gp_compute(
                _nfl_team_pts_projection, ha, df,
                target_season=target_season, target_week=target_week,
                target_type=target_type)
        away_off = await _nfl_gp_compute(
                _nfl_team_pts_projection, aa, df,
                target_season=target_season, target_week=target_week,
                target_type=target_type)
        home_def_str = await _nfl_gp_compute(
                _nfl_team_def_strength, ha, df,
                target_season=target_season, target_week=target_week,
                target_type=target_type)
        away_def_str = await _nfl_gp_compute(
                _nfl_team_def_strength, aa, df,
                target_season=target_season, target_week=target_week,
                target_type=target_type)
        home_profile = point_profiles.get(ha, {})
        away_profile = point_profiles.get(aa, {})
        home_off_split = home_profile.get("home_off_pts")
        away_off_split = away_profile.get("away_off_pts")
        home_def_split = home_profile.get("home_def_factor")
        away_def_split = away_profile.get("away_def_factor")
        effective_home_off = (0.65 * home_off + 0.35 * home_off_split
                              if home_off_split is not None else home_off)
        effective_away_off = (0.65 * away_off + 0.35 * away_off_split
                              if away_off_split is not None else away_off)
        effective_away_def = (0.65 * away_def_str + 0.35 * away_def_split
                              if away_def_split is not None else away_def_str)
        effective_home_def = (0.65 * home_def_str + 0.35 * home_def_split
                              if home_def_split is not None else home_def_str)
        venue_active = any(v is not None for v in (
            home_off_split, away_off_split, home_def_split, away_def_split))
        residual_home_adj = HOME_ADJ if venue_active else 1.05
        recent_home = effective_home_off * effective_away_def * residual_home_adj
        recent_away = effective_away_off * effective_home_def
        hp = season_profiles.get(ha, {})
        ap = season_profiles.get(aa, {})
        last_home = (float(hp.get("off_pts", 23.0)) *
                     float(ap.get("def_factor", 1.0)) * residual_home_adj)
        last_away = float(ap.get("off_pts", 23.0)) * float(hp.get("def_factor", 1.0))
        # Last completed season anchors the model while L5 captures current
        # form. A missing team profile falls back to league average.
        stat_home = 0.45 * recent_home + 0.55 * last_home
        stat_away = 0.45 * recent_away + 0.55 * last_away

        # H2H is a major but bounded matchup adjustment. Only the five most
        # recent pre-target meetings are allowed; exact venue orientation is
        # substantially more informative than a reversed venue.
        h2h = h2h_payloads[game_index] if game_index < len(h2h_payloads) else {}
        hgames = (h2h.get("games", []) if h2h else [])[:5]
        def _weighted_h2h_score(team, target_side):
            total_score = total_weight = 0.0
            for pos, meeting in enumerate(hgames):
                if meeting.get("home_abbr") == team:
                    score, side = meeting.get("home_score"), "home"
                else:
                    score, side = meeting.get("away_score"), "away"
                if score is None:
                    continue
                # Newer meetings matter much more; matching today's venue gets
                # an additional boost while reverse-venue games still count.
                weight = (0.64 ** pos) * (2.20 if side == target_side else 0.72)
                total_score += float(score) * weight
                total_weight += weight
            return total_score / total_weight if total_weight else None

        h2h_home_avg = _weighted_h2h_score(ha, "home")
        h2h_away_avg = _weighted_h2h_score(aa, "away")
        try:
            target_year = int(str(date_str)[:4])
            latest_h2h_year = int(str(hgames[0].get("date", ""))[:4]) if hgames else target_year
            meeting_age = max(0, target_year - latest_h2h_year)
        except Exception:
            meeting_age = 0
        # Reliability grows with sample size and consistency, while old
        # meetings fade. A single old meeting cannot move the call materially.
        h2h_recency = max(0.25, 1.0 - meeting_age * 0.12)
        venue_count = sum(1 for m in hgames if m.get("home_abbr") == ha)
        sample_reliability = min(1.0, len(hgames) / 4.0)
        h2h_weight = (min(0.34, (0.06 + len(hgames) * 0.055)
                          * h2h_recency * (.72 + .28 * sample_reliability))
                      if hgames else 0.0)
        proj_home = round(stat_home * (1 - h2h_weight) +
                          (h2h_home_avg if h2h_home_avg is not None else stat_home) * h2h_weight, 1)
        proj_away = round(stat_away * (1 - h2h_weight) +
                          (h2h_away_avg if h2h_away_avg is not None else stat_away) * h2h_weight, 1)
        weather_key = f"{aa}@{ha}"
        weather = (weather_by_game or {}).get(weather_key) or g.get("weather") or {}
        weather_base_home, weather_base_away = proj_home, proj_away
        weather_severity = int(weather.get("severity") or 0) if weather.get("status") == "OK" else 0
        weather_score_factor = 1 - min(.12, .12 * weather_severity / 100.0)
        proj_home = round(proj_home * weather_score_factor, 1)
        proj_away = round(proj_away * weather_score_factor, 1)
        proj_total = round(proj_home + proj_away, 1)
        win_home, win_away = _nfl_pythagorean(proj_home, proj_away)
        pick_home = win_home >= win_away
        pick_abbr = ha if pick_home else aa
        margin = abs(win_home - win_away)
        conf = "STRONG" if margin >= 15 else ("MODERATE" if margin >= 8 else "LEAN")
        # Market odds
        away_ml = gl.get("away_ml"); home_ml = gl.get("home_ml")
        total_line = gl.get("total_line")
        total_over_odds = gl.get("total_over_odds"); total_under_odds = gl.get("total_under_odds")
        mkt_home_pct, mkt_away_pct = _devig_nfl(home_ml, away_ml)
        model_pct = win_home if pick_home else win_away
        mkt_pct   = (mkt_home_pct if pick_home else mkt_away_pct)
        mkt_edge  = round(model_pct - mkt_pct) if mkt_pct is not None else None
        value_flag = (mkt_edge is not None and mkt_edge >= 5)
        # Total pick
        total_pick = total_edge = None
        if total_line is not None:
            total_pick = "OVER" if proj_total > total_line else "UNDER"
            total_edge = round(proj_total - total_line, 1)
        # Starter names (QB = highest career passing_yards)
        away_sp = await _nfl_gp_compute(
            _nfl_starter_name, aa, df, "passing_yards", roster_map)
        home_sp = await _nfl_gp_compute(
            _nfl_starter_name, ha, df, "passing_yards", roster_map)
        # Driver phrases
        drivers = []
        if pick_home:
            drivers.append(f"{ha} projects {proj_home} pts vs {aa} projects {proj_away} pts")
        else:
            drivers.append(f"{aa} projects {proj_away} pts vs {ha} projects {proj_home} pts")
        if away_def_str < 0.95:
            drivers.append(f"{aa} defense has allowed fewer yards than average")
        elif home_def_str < 0.95:
            drivers.append(f"{ha} defense has allowed fewer yards than average")
        if hgames:
            h2h_winner = (sum(1 for m in hgames if m.get("winner") == ha),
                          sum(1 for m in hgames if m.get("winner") == aa))
            drivers.append(f"last {len(hgames)} H2H: {ha} {h2h_winner[0]} wins, "
                           f"{aa} {h2h_winner[1]} wins; recency/venue weight "
                           f"{round(h2h_weight * 100)}%")
            drivers.append(f"exact venue meetings: {venue_count}/{len(hgames)}; "
                           f"newest weighted most")
        if weather.get("status") == "OK" and weather_severity:
            drivers.append(f"{weather.get('summary','Weather')} — model scoring factor "
                           f"{weather_score_factor:.3f}; passing/kicking risk and "
                           f"run tendency are reflected in player props")
        if reference_season is not None:
            drivers.append(f"{reference_season} full-season offense/defense anchors recent L5 form")
        if venue_active:
            drivers.append("team venue splits active: "
                           f"home O {home_profile.get('home_off_games', 0)} / "
                           f"home D {home_profile.get('home_def_games', 0)}, "
                           f"away O {away_profile.get('away_off_games', 0)} / "
                           f"away D {away_profile.get('away_def_games', 0)} games")
        else:
            drivers.append("team-specific venue split unavailable; league home edge fallback used")
        if value_flag and mkt_edge:
            drivers.append(f"model {pick_abbr} {model_pct}% vs market {mkt_pct}% — +{mkt_edge}% value edge")
        elif mkt_edge is not None:
            drivers.append(f"model {pick_abbr} {model_pct}% vs market {mkt_pct}%")
        odds_warning_parts = []
        if away_ml is None or home_ml is None:
            odds_warning_parts.append("moneyline prices unavailable")
        if total_line is None:
            odds_warning_parts.append("total price unavailable")
        odds_warning = ""
        if odds_warning_parts:
            odds_warning = (
                "Sportsbook game lines are unavailable for this matchup "
                f"({'; '.join(odds_warning_parts)}); model prediction shown without prices."
            )
            drivers.append(f"⚠️ {odds_warning}")
        predictions.append({
            "away_abbr": aa, "home_abbr": ha,
            "away_sp": away_sp, "home_sp": home_sp,
            "proj_away": proj_away, "proj_home": proj_home, "proj_total": proj_total,
            "weather": weather, "weather_applied": bool(weather_severity),
            "weather_base_home": weather_base_home, "weather_base_away": weather_base_away,
            "weather_score_factor": weather_score_factor,
            "weather_adjustment_home": round(proj_home - weather_base_home, 1),
            "weather_adjustment_away": round(proj_away - weather_base_away, 1),
            "weather_severity": weather_severity,
            "weather_label": weather.get("label", ""),
            "weather_summary": weather.get("summary", ""),
            "weather_status": weather.get("status", "UNAVAILABLE"),
            "win_away": win_away, "win_home": win_home,
            "pick_home": pick_home, "pick_abbr": pick_abbr, "conf": conf,
            "away_ml_odds": away_ml, "home_ml_odds": home_ml,
            "away_ml_book": gl.get("away_ml_book", ""),
            "home_ml_book": gl.get("home_ml_book", ""),
            "total_line": total_line, "total_pick": total_pick, "total_edge": total_edge,
            "total_over_odds": total_over_odds, "total_under_odds": total_under_odds,
            "total_over_book": gl.get("total_over_book", ""),
            "total_under_book": gl.get("total_under_book", ""),
            "mkt_home_pct": mkt_home_pct, "mkt_away_pct": mkt_away_pct,
            "mkt_edge": mkt_edge, "value_flag": value_flag,
            "game_line_available": bool(gl),
            "odds_warning": odds_warning,
            "drivers": drivers, "game_start": g.get("start", ""),
            "h2h_games": len(hgames),
            "h2h_home_avg": round(h2h_home_avg, 1) if h2h_home_avg is not None else None,
            "h2h_away_avg": round(h2h_away_avg, 1) if h2h_away_avg is not None else None,
            "h2h_home_wins": sum(1 for m in hgames if m.get("winner") == ha),
            "h2h_away_wins": sum(1 for m in hgames if m.get("winner") == aa),
            "h2h_weight_pct": round(h2h_weight * 100),
            "h2h_exact_venue_games": venue_count,
            "h2h_reversed_venue_games": max(0, len(hgames) - venue_count),
            "venue_data_available": venue_active,
            "venue_lookup_available": bool(venue_lookup_available),
            "venue_sample_counts": {
                "home_off": point_profiles.get(ha, {}).get("home_off_games", 0),
                "away_off": point_profiles.get(aa, {}).get("away_off_games", 0),
                "home_def": point_profiles.get(ha, {}).get("home_def_games", 0),
                "away_def": point_profiles.get(aa, {}).get("away_def_games", 0),
            },
            "reference_season": reference_season,
            "away_off_rank": point_profiles.get(aa, {}).get("off_rank"),
            "home_off_rank": point_profiles.get(ha, {}).get("off_rank"),
            "away_def_rank": point_profiles.get(aa, {}).get("def_rank"),
            "home_def_rank": point_profiles.get(ha, {}).get("def_rank"),
            "away_off_pts": round(point_profiles.get(aa, {}).get("off_pts", away_off), 1),
            "home_off_pts": round(point_profiles.get(ha, {}).get("off_pts", home_off), 1),
            "away_def_factor": point_profiles.get(aa, {}).get("def_factor", away_def_str),
            "home_def_factor": point_profiles.get(ha, {}).get("def_factor", home_def_str),
            "home_venue_off_pts": point_profiles.get(ha, {}).get("home_off_pts"),
            "away_venue_off_pts": point_profiles.get(aa, {}).get("away_off_pts"),
            "home_venue_def_factor": point_profiles.get(ha, {}).get("home_def_factor"),
            "away_venue_def_factor": point_profiles.get(aa, {}).get("away_def_factor"),
            "recent_home": round(recent_home, 1), "recent_away": round(recent_away, 1),
            "last_home": round(last_home, 1), "last_away": round(last_away, 1),
            "stat_home": round(stat_home, 1), "stat_away": round(stat_away, 1),
        })
    return predictions, fetched

# ── Pipeline ───────────────────────────────────────────────────────────────────
_NFL_PIPELINE_MEMORY_LOCK = asyncio.Lock()

def _nfl_release_analysis_memory():
    # A cancelled asyncio worker can still be finishing its current player.
    # Wait for it (or a Coach analysis) before touching shared derived caches.
    with _NFL_ANALYSIS_LOCK:
        _nfl_clear_slate_caches()

async def run_pipeline(date_str: str, progress=None, simulate: bool = False,
                       force_refresh: bool = False,
                       capture_official: bool = True, system: str = "OLD") -> Dict:
    """Serialize full analyses across OLD/NEW, cron, and replay callers."""
    if _NFL_PIPELINE_MEMORY_LOCK.locked() and progress:
        progress("Waiting for the active NFL analysis to release memory…")
    async with _NFL_PIPELINE_MEMORY_LOCK:
        try:
            return await _run_pipeline_unlocked(
                date_str, progress=progress, simulate=simulate,
                force_refresh=force_refresh,
                capture_official=capture_official, system=system)
        finally:
            await asyncio.to_thread(_nfl_release_analysis_memory)

async def _run_pipeline_unlocked(date_str: str, progress=None, simulate: bool = False,
                                 force_refresh: bool = False,
                                 capture_official: bool = True, system: str = "OLD") -> Dict:
    system = "NEW" if str(system or "OLD").upper() == "NEW" else "OLD"
    opening_captured_early = False
    def _p(msg):
        print(f"[Pipeline] {msg}")
        if progress:
            try: progress(msg)
            except Exception: pass
    def _error_result(payload):
        if system == "NEW":
            payload.setdefault("system", "NEW")
            payload.setdefault("model_version", "NEW-v2-ewma-weather")
            return _new_sanitize_json(payload)
        return payload

    # Every past-date request is a historical replay, regardless of which
    # caller initiated it. This prevents the Run Picks endpoint from analyzing
    # a completed date with stats from that date or later.
    if not simulate:
        try:
            if date_str < _nfl_today():
                simulate = True
        except Exception:
            pass
    cached = (
        None if (simulate or force_refresh)
        else await asyncio.to_thread(
            _new_cache_get if system == "NEW" else _cache_get, date_str)
    )
    if cached:
        if system == "NEW" and isinstance(cached, dict):
            cached.setdefault("system", "NEW")
            cached.setdefault("model_version", "NEW-v2-ewma-weather")
            cached = _new_sanitize_json(cached)
        cached = await _nfl_enrich_cached_response(cached, date_str, system)
        return cached
    # Do not start full Coach analysis here: it shares the analysis lock with
    # the standard board and can consume the foreground job's entire deadline.
    # Warm it automatically after the main board has been saved instead.

    # 1. Get game schedule from ESPN
    _p("Fetching NFL schedule from ESPN…")
    try:
        espn_games = await get_espn_games(date_str)
    except Exception as exc:
        return _error_result({
            "picks": [], "all": [],
            "error": (
                "NFL schedule is temporarily unavailable. ESPN could not be "
                f"reached after retries: {exc}"
            ),
        })
    if not espn_games:
        return _error_result({"picks":[],"all":[],"error":f"No NFL games found for {date_str} — NFL season runs Sept–Feb. (Note: check the exact date — e.g. Championship Sunday was Jan 26, not Jan 25.)"})
    weather_by_game = {}
    if not simulate:
        _p("Fetching game weather…")
        try:
            weather_by_game = await _nfl_fetch_weather(date_str, espn_games)
        except Exception as exc:
            print(f"[NFL weather] slate fetch failed open: {exc}")
            weather_by_game = {}
        for game in espn_games:
            key = str(game.get("id") or f"{game.get('away_abbr')}@{game.get('home_abbr')}")
            game["weather"] = weather_by_game.get(
                key, _nfl_weather_empty(game, reason="Weather unavailable"))
    if simulate:
        # Historical replays use the players listed by the archived sportsbook
        # board. Current ESPN rosters would incorrectly remove traded/retired
        # players from a past slate.
        roster_map = {}
    else:
        _p("Loading current post-preseason rosters…")
        roster_map = await get_espn_roster_map(espn_games, date_str)

    # Historical alternate lines and cached game lines still need stable Odds
    # event IDs. Restore those mappings independently of the standard prop cache
    # so a resumed paid replay never fails merely because props were cached.
    if simulate:
        _p(f"Matching {len(espn_games)} games with historical sportsbook events…")
        espn_games = await get_odds_events(date_str, espn_games)
        unmatched = [g.get("game") or "Unknown game" for g in espn_games if not g.get("id")]
        if unmatched:
            return _error_result({
                "picks": [], "all": [], "games": len(espn_games),
                "error": (
                    "Historical event matching was incomplete for "
                    + ", ".join(unmatched[:4])
                    + (" and more." if len(unmatched) > 4 else ".")
                ),
            })

    # 2+3. Odds layer — ONE call per game fetches props + h2h + totals together.
    #      All games are fetched concurrently (asyncio.gather) then cached for 6h.
    #      On a cache hit the result cache (6h) fires first so no API calls happen.
    all_lines, game_lines_by_id, skipped_matchups = (
        (None, None, [])
        if force_refresh
        else await asyncio.to_thread(_odds_cache_get, date_str))
    if all_lines is None:
        # 2. Match Odds API event IDs
        _p(f"Matching {len(espn_games)} games with sportsbook events…")
        if not simulate:
            espn_games = await get_odds_events(date_str, espn_games)

        # 3. Fetch prop lines with bounded concurrency. A 13-game Sunday slate
        # must not run 13 independent 20-second requests serially, but keeping
        # the cap low avoids a burst that can trigger provider rate limits.
        all_lines = []
        fetch_limit = min(_NFL_PROP_FETCH_CONCURRENCY, len(espn_games))
        fetch_sem = asyncio.Semaphore(max(1, fetch_limit))
        _p(f"Fetching prop lines for {len(espn_games)} games — "
           f"up to {fetch_limit} at once…")

        async def _fetch_game_props(gi, ev):
            ev_id = ev.get("id", "")
            async with fetch_sem:
                print(f"[OddsAPI props] start game {gi+1}/{len(espn_games)}: "
                      f"{ev.get('game','')}")
                try:
                    lines = (
                        await asyncio.wait_for(
                            get_prop_lines(ev_id, date_str),
                            timeout=_NFL_PROP_GAME_TIMEOUT)
                        if ev_id else [])
                except asyncio.TimeoutError:
                    fetch_key = (str(ev_id), str(date_str), False)
                    _NFL_PROP_FETCH_STATUS[fetch_key] = "timeout"
                    print(f"[OddsAPI props] hard timeout after "
                          f"{_NFL_PROP_GAME_TIMEOUT}s for game "
                          f"{gi+1}/{len(espn_games)}: {ev.get('game','')}")
                    lines = []
                # A live response can occasionally succeed with no markets.
                # Retry that exact game without adding any new API calls when
                # the first response is complete.
                today_date = _nfl_today_date()
                try:
                    slate_date = datetime.strptime(date_str, "%Y-%m-%d").date()
                except (TypeError, ValueError):
                    slate_date = today_date
                # Retry transient empties only on game-day/next-day slates.
                # Future weekly dates commonly have no posted player props yet;
                # waiting through two more 20-second calls cannot create them.
                if (ev_id and not simulate and not lines
                        and slate_date <= today_date + timedelta(days=1)):
                    for retry in range(2):
                        wait_s = 1.5 * (retry + 1)
                        print(f"[OddsAPI props] empty for {ev_id}; "
                              f"retry {retry + 1}/2 in {wait_s:.1f}s")
                        await asyncio.sleep(wait_s)
                        try:
                            lines = await asyncio.wait_for(
                                get_prop_lines(ev_id, date_str),
                                timeout=_NFL_PROP_GAME_TIMEOUT)
                        except asyncio.TimeoutError:
                            _NFL_PROP_FETCH_STATUS[
                                (str(ev_id), str(date_str), False)] = "timeout"
                            print(f"[OddsAPI props] retry hard timeout after "
                                  f"{_NFL_PROP_GAME_TIMEOUT}s for "
                                  f"{ev.get('game','')}")
                            lines = []
                        if lines:
                            print(f"[OddsAPI props] retry recovered "
                                  f"{len(lines)} lines for {ev_id}")
                            break
                return gi, ev, lines

        tasks = [
            asyncio.create_task(_fetch_game_props(gi, ev))
            for gi, ev in enumerate(espn_games)
        ]
        fetched_games = await _collect_prop_fetch_tasks(
            tasks, espn_games, date_str, _p)
        skipped_matchups.extend(
            _prop_fetch_skipped_matchups(fetched_games, date_str))

        # Preserve schedule order so downstream ranking remains deterministic.
        for ev, lines in fetched_games:
            home_abbr = ev.get("home_abbr", "") or _name_to_abbr(ev.get("home_team",""))
            away_abbr = ev.get("away_abbr", "") or _name_to_abbr(ev.get("away_team",""))
            for l in lines:
                l["home_team"] = ev.get("home_team","")
                l["away_team"] = ev.get("away_team","")
                l["home_abbr"] = home_abbr
                l["away_abbr"] = away_abbr
                l["game"]      = ev.get("game","")
                l["game_start"]= ev.get("start","")
                l["target_season"] = ev.get("season")
                l["target_week"] = ev.get("week")
                l["target_type"] = ev.get("season_type", "REG")
                key = f"{away_abbr}@{home_abbr}"
                # Attach after the raw odds cache is read as well as after a
                # fresh fetch; weather is not sportsbook input.
                l["weather"] = weather_by_game.get(
                    key, _nfl_weather_empty(ev, reason="Weather unavailable")
                ) if not simulate else l.get("weather")
            all_lines.extend(lines)
        if all_lines:
            await asyncio.to_thread(
                _odds_cache_set, date_str,
                [{k: v for k, v in line.items() if k != "weather"}
                 for line in all_lines], {}, skipped_matchups)
        # Completed asyncio Tasks retain their return values and request frames.
        # They are no longer needed after the normalized rows enter all_lines.
        tasks.clear()
        fetched_games.clear()

    if not simulate and weather_by_game:
        for line in all_lines:
            home = line.get("home_abbr", "")
            away = line.get("away_abbr", "")
            key = f"{away}@{home}"
            line["weather"] = weather_by_game.get(
                key, _nfl_weather_empty(line, reason="Weather unavailable"))
    elif simulate:
        # Raw odds caches are not point-in-time weather snapshots.  Historical
        # replays remain weather-neutral unless a previously persisted board
        # already supplied weather directly to its player rows.
        for line in all_lines:
            line.pop("weather", None)

    if not all_lines:
        today = _nfl_today()
        if date_str < today:
            msg = f"No prop data found for {date_str} — the Odds API may not have archived lines for these games."
        else:
            msg = "No prop lines available yet — check back closer to game time"
        return _error_result({
            "picks": [], "all": [], "games": len(espn_games),
            "skipped_matchups": skipped_matchups, "error": msg,
        })
    if simulate:
        uncovered = []
        for game in espn_games:
            home = game.get("home_abbr", "") or _name_to_abbr(game.get("home_team", ""))
            away = game.get("away_abbr", "") or _name_to_abbr(game.get("away_team", ""))
            covered = any(
                line.get("home_abbr") == home and line.get("away_abbr") == away
                for line in all_lines
            )
            if not covered:
                uncovered.append(game.get("game") or f"{away} at {home}")
        if uncovered:
            return _error_result({
                "picks": [], "all": [], "games": len(espn_games),
                "error": (
                    "Archived prop coverage was incomplete for "
                    + ", ".join(uncovered[:4])
                    + (" and more." if len(uncovered) > 4 else ".")
                ),
            })

    # Sportsbook-listed players are the expected game lineup. Stamp each one
    # with ESPN's current post-cut team so Week 1 trades/free-agent moves do not
    # inherit last season's team; remove only players explicitly off the active
    # roster. Names absent from ESPN are retained rather than silently dropped.
    roster_filtered = []
    for line in all_lines:
        ri = roster_map.get(_norm(line.get("name", ""))) if roster_map else None
        if ri:
            line["roster_team"] = ri.get("team", "")
            line["roster_position"] = ri.get("position", "")
            if not ri.get("eligible", True):
                continue
            if (line.get("market") == "player_rush_reception_yds"
                    and _nfl_position_group(ri.get("position")) != "RB"):
                continue
        roster_filtered.append(line)
    all_lines = roster_filtered
    if not simulate:
        await asyncio.to_thread(_apply_nfl_injury_context, all_lines, roster_map)
    # Keep the complete sportsbook set for later game-line cache updates.
    # _trim_prop_lines intentionally reduces analysis volume, but that reduced
    # list must never overwrite the raw odds cache.
    raw_cached_lines = list(all_lines)
    expected_prop_games = {
        (str(g.get("away_abbr") or _name_to_abbr(g.get("away_team", ""))),
         str(g.get("home_abbr") or _name_to_abbr(g.get("home_team", ""))))
        for g in espn_games
    }
    covered_prop_games = {
        (str(line.get("away_abbr") or ""), str(line.get("home_abbr") or ""))
        for line in raw_cached_lines
    }
    prop_coverage_complete = bool(expected_prop_games) and expected_prop_games.issubset(
        covered_prop_games)
    # Friday's Sunday opening odds are valuable even if the heavier player
    # history analysis later runs out of time or the host restarts.  Persist the
    # complete raw standard-line board now, before loading/analyzing nflverse.
    # The helper's weekday/target guard makes this a no-op on other dates.
    if not simulate:
        opening_captured_early = await asyncio.to_thread(
            _nfl_capture_opening_lines, date_str, {"all": raw_cached_lines})

    # 4. Load NFL stats (nfl_data_py — downloads once, cached in memory)
    _p(f"Loading player stats ({len(all_lines)} props to analyze) — first run after deploy downloads ~20s…")
    df = await get_nfl_stats()
    if df is None:
        return _error_result({"picks":[],"all":[],"error":"Could not load NFL stats data — try again in a moment"})

    # Historical replay analysis is strictly point-in-time: only rows from
    # before the selected game's week may influence picks. The selected-week
    # row is consulted only to identify the player's team on that past slate.
    analysis_df = df
    target_rows = None
    target_teams = {}
    target_positions = {}
    # Player props use only the selected season and its immediately previous
    # season.  Keep the complete df for Game Predictor, whose H2H meeting
    # lookup intentionally spans historical seasons.
    prop_target = espn_games[0] if espn_games else {}
    prop_season = prop_target.get("season")
    prop_week = prop_target.get("week")
    prop_type = prop_target.get("season_type", "REG")
    if simulate and espn_games:
        tg = espn_games[0]
        ts, tw, tt = tg.get("season"), tg.get("week"), tg.get("season_type", "REG")
        def _point_in_time_filter():
            try:
                stats_week = _nflverse_week(tt, tw or 1)
                selected_rows = df[
                    (df["season"].fillna(0).astype(int) == int(ts)) &
                    (df["week"].fillna(0).astype(int) == int(stats_week))
                ]
                if "season_type" in selected_rows.columns:
                    selected_rows = selected_rows[
                        selected_rows["season_type"].fillna("REG").astype(str).str.upper()
                        == str(tt).upper()
                    ]
                selected_teams = {}
                selected_positions = {}
                for _, tr in selected_rows.iterrows():
                    raw_name = tr.get("player_display_name", "")
                    nm = _norm(str(raw_name)) if raw_name is not None else ""
                    tm = str(tr.get("recent_team") or "")
                    if nm:
                        selected_positions[nm] = str(tr.get("position") or "").strip()
                        if tm:
                            selected_teams[nm] = tm
                for line in all_lines:
                    tm = selected_teams.get(_norm(line.get("name", "")))
                    if tm in (line.get("home_abbr"), line.get("away_abbr")):
                        line["roster_team"] = tm
                        line["roster_position"] = selected_positions.get(
                            _norm(line.get("name", "")), "")
                    elif _norm(line.get("name", "")) in selected_positions:
                        line["roster_position"] = selected_positions[
                            _norm(line.get("name", ""))]
                return (
                    selected_rows, selected_teams, selected_positions,
                    _nfl_stats_before_game(df, ts, tw, tt))
            except Exception as exc:
                print(f"[nfl_sim] point-in-time filter failed closed: {exc}")
                try:
                    empty = df.iloc[0:0]
                except Exception:
                    empty = df
                return empty, {}, {}, empty
        target_rows, target_teams, target_positions, analysis_df = await asyncio.to_thread(
            _point_in_time_filter)
    elif espn_games:
        analysis_df = await asyncio.to_thread(
            _nfl_prop_analysis_frame, df, prop_season, prop_week, prop_type)
    if simulate and espn_games:
        analysis_df = await asyncio.to_thread(
            _nfl_prop_analysis_frame, analysis_df, prop_season, prop_week, prop_type)
    # Keep matchup history separate from the model frame.  General form,
    # role, positional defense, projections, and probabilities use only the
    # selected season plus its predecessor; vs-opponent uses all available
    # prior seasons, still cut off before the selected game.
    if simulate:
        opponent_history_df = await asyncio.to_thread(
            _nfl_stats_before_game, df, prop_season, prop_week, prop_type)
    else:
        # Live/future boards cannot see future nflverse rows: the source contains
        # completed games only. Reuse the base frame instead of allocating a
        # second near-full multi-season copy for every Sunday/Monday slate.
        opponent_history_df = df

    # 5. Analyze every sportsbook-listed active player in standard offense,
    # defense, and kicking markets. Anytime TD is the only exception: reduce its
    # pool to starter-level QB, RB, WR, and TE candidates before analysis so
    # backup longshots cannot displace the real starters on dedicated TD lists.
    standard_lines = [
        pl for pl in all_lines if pl.get("market") != "player_anytime_td"
    ]
    # OLD keeps its established Anytime-TD candidate caps. NEW deliberately
    # analyzes every sportsbook-listed roster-eligible QB/RB/WR/TE TD quote so
    # backups, rookies, and depth players remain visible to the independent
    # sparse-history model.
    if system == "OLD":
        all_lines = await asyncio.to_thread(
            _analysis_prop_lines, all_lines, analysis_df)
    td_starter_lines = [
        pl for pl in all_lines if pl.get("market") == "player_anytime_td"
    ]
    _p(
        f"Analyzing all {len(standard_lines)} standard player props plus "
        f"{len(td_starter_lines)} QB/RB/WR/TE Anytime TD candidates…")
    global _NFL_ANALYSIS_EVENTS
    analysis_cancelled = _bt_th.Event()
    analysis_started = _bt_th.Event()
    analysis_finished = _bt_th.Event()
    _NFL_ANALYSIS_EVENTS = (analysis_started, analysis_finished)
    def _analyze_all_props():
        # Keep the serial order (and therefore TD calibration/cache semantics)
        # while moving the pandas-heavy loop out of the event loop.
        analyzed = []
        try:
            analysis_started.set()
            with _NFL_ANALYSIS_LOCK:
                total_props = len(all_lines)
                for prop_index, pl in enumerate(all_lines, 1):
                    if analysis_cancelled.is_set():
                        break
                    if prop_index == 1 or prop_index % 50 == 0:
                        _p(
                            f"Analyzing player props… "
                            f"{prop_index}/{total_props} complete")
                    analyzer = _analyze_new_prop if system == "NEW" else _analyze_prop
                    result = analyzer(
                        pl, analysis_df,
                        pl.get("home_abbr", ""), pl.get("away_abbr", ""),
                        opponent_history_df)
                    if result:
                        analyzed.append(result)
            return analyzed
        finally:
            # asyncio cancellation cannot stop the worker created by
            # asyncio.to_thread.  The weekly runner uses this barrier before
            # permitting the next date, preventing abandoned pandas work from
            # overlapping the next slate.
            analysis_finished.set()
    try:
        all_results = await asyncio.to_thread(_analyze_all_props)
        if _NFL_ANALYSIS_EVENTS == (analysis_started, analysis_finished):
            _NFL_ANALYSIS_EVENTS = None
    except asyncio.CancelledError:
        # Cancelling to_thread alone does not stop its worker. Release shared
        # analysis resources after the current player instead of processing a
        # whole abandoned slate while a retry waits behind it.
        analysis_cancelled.set()
        raise

    # 6. Preserve every analyzed result. The TD starter prefilter above removes
    # backup longshots; there is no later team cap, so every qualifying starter
    # can compete for the slate-wide Top 10 by the displayed hit-rate ranking.

    picks   = sorted([r for r in all_results
                      if r.get("pick") and r.get("betQualified", True)],
                     key=lambda x: abs(x.get("gap") or 0), reverse=True)
    td_picks = sorted(
        [r for r in all_results
         if r.get("market") == "player_anytime_td"
         and r.get("pick") == "OVER"
         and r.get("betQualified", True)],
        key=lambda x: (float(x.get("score") or x.get("dispScore") or 0),
                       float(x.get("valueEdge") or 0)),
        reverse=True)
    if not simulate:
        # Player analysis is complete. Release the two-season frame and every
        # slate-derived lookup before Game Predictor and durable snapshot JSON
        # are built. The compact process-wide frame remains available for GP.
        analysis_df = None
        opponent_history_df = None
        target_rows = None
        await asyncio.to_thread(_nfl_release_analysis_memory)
    games_out = [{"home_team":g.get("home_team",""), "away_team":g.get("away_team",""),
                  "home_abbr":g.get("home_abbr",""), "away_abbr":g.get("away_abbr",""),
                   "game":g.get("game",""), "game_start":g.get("start",""),
                   "venue_full_name":g.get("venue_full_name",""),
                   "venue_city":g.get("venue_city",""), "venue_state":g.get("venue_state",""),
                   "venue_country":g.get("venue_country",""), "indoor":bool(g.get("indoor")),
                   "weather":g.get("weather")}
                  for g in espn_games]
    # 7. Game Predictor — fetches h2h + totals concurrently (separate calls from props
    #    so player-prop market quota is never shared with game-level markets)
    _p("Building game predictions…")
    game_predictions, new_gl = await _build_nfl_game_predictions(
        espn_games, df, date_str, game_lines_by_id, roster_map, progress=_p,
        weather_by_game=weather_by_game)
    if new_gl:
        # Persist freshly-bought game lines so re-runs never re-buy them
        merged_gl = {**(game_lines_by_id or {}), **new_gl}
        await asyncio.to_thread(
            _odds_cache_set,
            date_str, raw_cached_lines, merged_gl, skipped_matchups)
    _p("Finishing up…")
    # Data health: the current season is normally absent before its first games.
    # That is expected for Week 1, so show it as an informational note; only
    # missing completed baseline seasons are treated as a warning.
    data_warning = ""
    data_note = ""
    try:
        loaded_seasons = await asyncio.to_thread(
            lambda: sorted({int(s) for s in df["season"].dropna().unique()}))
        completed = [y for y in NFL_SEASONS if y != _cur_season]
        missing_completed = [y for y in completed if y not in loaded_seasons]
        if missing_completed:
            data_warning = ("⚠️ " + ", ".join(map(str, missing_completed)) +
                            " completed-season stats failed to download — picks below use only " +
                            ", ".join(map(str, loaded_seasons)) +
                            " data. Tap Force Refresh to retry.")
        if _cur_season not in loaded_seasons:
            usable = [y for y in loaded_seasons if y != _cur_season]
            if usable and usable == list(range(min(usable), max(usable) + 1)):
                usable_label = f"{min(usable)}–{max(usable)}"
            else:
                usable_label = ", ".join(map(str, usable))
            data_note = (f"ℹ️ {_cur_season} stats are not published yet — using "
                         + (usable_label if usable else "completed-season")
                         + " regular-season and playoff data.")
    except Exception:
        pass

    td_calibration = next((r.get("tdCalibrationReport") for r in td_picks
                           if r.get("tdCalibrationReport")), [])
    game_predictor_warnings = [
        p.get("odds_warning") for p in game_predictions
        if p.get("odds_warning")
    ]
    result  = {"picks":picks, "all":all_results, "td_picks":td_picks, "date":date_str,
               "defense_schema_version": 3,
               "games":games_out, "qualified":len(picks),
               "prop_coverage_complete": prop_coverage_complete,
               "skipped_matchups": skipped_matchups,
               "game_predictor_warnings": game_predictor_warnings,
               "data_warning": data_warning,
               "data_note": data_note,
               "td_calibration": {
                   "method": "walk-forward reliability bins",
                   "seasons": NFL_SEASONS,
                   "minimum_player_history": 5,
                   "full_bin_sample": 100,
                   "passing_touchdowns_excluded": True,
                   "bins": td_calibration,
               },
               "game_predictions": game_predictions}
    await asyncio.to_thread(_nfl_json_ready, result)
    if system == "NEW":
        result["system"] = "NEW"
        result["model_version"] = "NEW-v2-ewma-weather"
        result = _new_sanitize_json(result)
    if simulate:
        result["simulation"] = True
        replay_box = await asyncio.to_thread(_nfl_box_from_stats_rows, target_rows)
        result["historicalTrackRecord"] = await asyncio.to_thread(
            _nfl_historical_replay_payload, result, espn_games, replay_box)
        historical_saved = await asyncio.to_thread(
            _nfl_save_historical_replay,
            date_str, result["historicalTrackRecord"], system)
        _p("Building Historical Edge Coach recommendations…")
        historical_coach = await _nfl_build_historical_coach(
            date_str, picks, espn_games, analysis_df, roster_map, replay_box,
            target_teams, target_positions, system)
        historical_coach_saved = await asyncio.to_thread(
            _nfl_save_historical_coach, date_str, historical_coach, system)
        result["historical_saved"] = historical_saved
        result["historicalSaved"] = historical_saved
        result["historicalCoachSaved"] = historical_coach_saved
        result["historicalCoachCounts"] = {
            category: len(rows)
            for category, rows in historical_coach.items()
        }
        if not historical_saved or not historical_coach_saved:
            result["error"] = (
                "Historical replay was analyzed but one or more historical "
                "archives could not be saved.")
        result["simulationNotice"] = (
            "Point-in-time historical replay: player-form and Game Predictor "
            f"inputs use only data available before {date_str}. Archived sportsbook "
            "lines are used for grading. Replay results are view-only and never "
            "enter the official NFL Track Record."
        )
        result["system"] = system
        if system == "NEW":
            result["model_version"] = "NEW-v2-ewma-weather"
            result["simulationNotice"] = (
                "NEW historical replay is view-only and isolated from OLD and "
                "NEW official records.")
            result = _new_sanitize_json(result)
        return result
    # Line movement and snapshot helpers use synchronous Supabase/httpx calls.
    # Keep the tracking semantics/order intact, but never run those calls on
    # the ASGI event loop.
    # Capture the scheduled opening baseline first, then attach movement before
    # any board, Coach, or tracking payload is derived. OLD and NEW use separate
    # official ledgers, but share the genuine opening-line source.
    if not opening_captured_early:
        # Retry at the established final stage if the early durable write was
        # unavailable.  Never replace the complete raw opening board with the
        # smaller subset that survived player-history qualification.
        await asyncio.to_thread(_nfl_capture_opening_lines, date_str, result)
    await asyncio.to_thread(_nfl_attach_line_movement, date_str, result)
    await asyncio.to_thread(_nfl_json_ready, result)
    # The short-lived /tmp cache is only an accelerator. Persist each game's
    # latest completed pre-kickoff board independently so a service restart or
    # an early kickoff cannot erase/block the still-bettable late-game slate.
    await asyncio.to_thread(_nfl_save_board_snapshots, date_str, result, system)
    official_capture = (
        capture_official and _nfl_official_capture_allowed(date_str, result))
    result["official_tracking"] = official_capture
    if not capture_official:
        result["tracking_reason"] = (
            "Weekly opening-line snapshot only; official picks remain available "
            "for the first eligible game-day run.")
    if official_capture:
        await asyncio.to_thread(_nfl_save_picks_snapshot, date_str, result, system)
        await asyncio.to_thread(_nfl_save_gp_snapshot, date_str, result, system)
        await asyncio.to_thread(
            _nfl_auto_capture_coach_categories, date_str, result, system)
    else:
        print(f"[nfl_track] official snapshot skipped for {date_str}: "
              + ("weekly opening-line mode"
                 if not capture_official else "capture was not before every kickoff"))
    await asyncio.to_thread(
        _new_cache_set if system == "NEW" else _cache_set, date_str, result)
    if system == "OLD":
        try:
            from replit_push import push_picks_to_replit
            await asyncio.to_thread(push_picks_to_replit, "nfl", result)
        except Exception as _e:
            print(f"[replit_push] nfl push failed: {_e}")
        _schedule_alt_coach_warm(date_str)
    return result

# ── Routes ─────────────────────────────────────────────────────────────────────
@app.get("/api/verify-token")
async def verify_token(request: Request):
    auth = request.headers.get("Authorization","")
    tok  = auth.replace("Bearer ","").strip()
    if not tok or len(tok.split(".")) != 3:
        raise HTTPException(status_code=401, detail="Invalid token")
    return {"ok": True}

@app.get("/health")
async def health(): return {"status":"ok"}

@app.get("/api/warm")
async def api_warm():
    today = _nfl_today()
    cached = await asyncio.to_thread(_cache_get, today)
    if cached:
        return {"ok":True,"source":"cache","date":today,"picks":len(cached.get("picks",[]))}
    result = await run_pipeline(today)
    return {"ok":True,"source":"computed","date":today,
            "picks":len(result.get("picks",[])),"error":result.get("error")}

@app.post("/api/clear-cache")
async def clear_cache_route():
    for p in _CACHE_DIR.glob("nfl_*.json"): p.unlink(missing_ok=True)
    global _nfl_df; _nfl_df = None
    return {"ok": True}

def _verify_hub_token(token: str) -> bool:
    if not token or len(token.split(".")) != 3:
        return False
    if not JWT_SECRET:
        return False
    try:
        jose_jwt.decode(token, JWT_SECRET, algorithms=["HS256"])
        return True
    except Exception:
        return False

def _nfl_alt_line_key(line):
    try:
        point = round(float(line.get("line")), 6)
    except (TypeError, ValueError):
        point = line.get("line")
    return (
        _norm(str(line.get("name") or "")),
        str(line.get("market") or "").lower(),
        point,
        str(line.get("home_abbr") or ""),
        str(line.get("away_abbr") or ""),
    )

def _nfl_dedupe_alt_lines(lines):
    """One model evaluation per genuine player/market/line/game quote.

    get_prop_lines already chooses the best price across books. This final
    guard also handles duplicate ladder rows returned by provider snapshots
    without capping players, markets, or games.
    """
    unique = {}
    for line in lines or []:
        key = _nfl_alt_line_key(line)
        current = unique.get(key)
        if current is None:
            unique[key] = line
            continue
        for odds_key, book_key in (("over_odds", "over_book"),
                                   ("under_odds", "under_book")):
            incoming, existing = line.get(odds_key), current.get(odds_key)
            try:
                if incoming is not None and (existing is None or
                                             float(incoming) > float(existing)):
                    current[odds_key] = incoming
                    current[book_key] = line.get(book_key, "")
            except (TypeError, ValueError):
                pass
    return list(unique.values())

def _nfl_alt_side_metrics(result, side):
    try:
        side = str(side).upper()
        odds = (result.get("realUnderOdds") if side == "UNDER"
                else result.get("realOdds"))
        score = float(result.get("dispScore", result.get("score")))
        if str(result.get("pick") or "").upper() != side:
            score = 100.0 - score
        implied = _nfl_implied_prob(odds)
        edge = score - implied if implied is not None else None
        return score, implied, odds, edge
    except (TypeError, ValueError):
        return None, None, None, None

def _nfl_alt_result_eligible(result):
    if not result or not result.get("coachEligible", True):
        return False
    # Evaluate both priced sides. A low alternate Over must not hide a valid
    # opposite Under (and vice versa); -1000 is explicitly inclusive.
    for side in ("OVER", "UNDER"):
        app, implied, odds, edge = _nfl_alt_side_metrics(result, side)
        try:
            odds_value = float(odds)
        except (TypeError, ValueError):
            odds_value = None
        if (odds_value is not None and odds_value >= _NFL_ALT_MIN_ODDS
                and app is not None and app >= 85
                and implied is not None and implied >= 70
                and edge is not None and edge > 0):
            return True
    return False

async def _build_alt_coach(date_str: str, system: str = "OLD") -> dict:
    # Alternate warmups must not allocate a second analysis alongside NEW.
    async with _NFL_PIPELINE_MEMORY_LOCK:
        try:
            return await _build_alt_coach_unlocked(date_str, system)
        finally:
            await asyncio.to_thread(_nfl_release_analysis_memory)

async def _build_alt_coach_unlocked(date_str: str, system: str = "OLD") -> dict:
    system = "NEW" if str(system).upper() == "NEW" else "OLD"
    started = time.monotonic()
    overall_deadline = started + _NFL_ALT_OVERALL_TIMEOUT
    async def _alt_stage(coro, limit):
        remaining = min(float(limit), overall_deadline - time.monotonic())
        if remaining <= 0:
            raise asyncio.TimeoutError("alternate overall deadline")
        return await asyncio.wait_for(coro, timeout=remaining)
    cached = await asyncio.to_thread(_alt_coach_cache_get, date_str, False, system)
    if cached and not cached.get("partial"):
        await asyncio.to_thread(
            _nfl_auto_capture_alt_coach, date_str, cached, system)
        if system == "NEW":
            cached.setdefault("system", "NEW")
            cached = _new_sanitize_json(cached)
        return cached
    try:
        games = await _alt_stage(get_espn_games(date_str), 30)
        if not games:
            raise RuntimeError("No NFL games found for this date.")
        weather_by_game = {}
        if date_str >= _nfl_today():
            try:
                weather_by_game = await _alt_stage(
                    _nfl_fetch_weather(date_str, games), 30)
            except Exception as exc:
                print(f"[NFL weather] alternate scan failed open: {exc}")
        games = await _alt_stage(get_odds_events(date_str, games), 30)
        roster_map = (
            {}
            if date_str < _nfl_today()
            else await _alt_stage(get_espn_roster_map(games, date_str), 45)
        )
    except Exception as exc:
        raise RuntimeError(f"Alternate setup failed: {exc}") from exc

    raw_saved = await asyncio.to_thread(_alt_coach_raw_cache_get, date_str)
    raw_events = dict(_alt_coach_raw_events(raw_saved))
    alt_sem = asyncio.Semaphore(_NFL_ALT_FETCH_CONCURRENCY)

    async def _one_alt(game):
        event_id = str(game.get("id") or "")
        if not event_id:
            return game, None
        if (event_id in raw_events
                and isinstance(raw_events[event_id], list)):
            return game, raw_events[event_id]
        async with alt_sem:
            try:
                batch = await asyncio.wait_for(
                    get_prop_lines(event_id, date_str, alternate_only=True),
                    timeout=_NFL_ALT_GAME_TIMEOUT)
                status = _NFL_PROP_FETCH_STATUS.get(
                    (event_id, str(date_str), True))
                # get_prop_lines already retries transient empty live responses.
                # After those retries, an HTTP-successful event with no
                # published alternate markets is a valid empty sentinel—not a
                # failed game that should suppress every other game's plays.
                return game, batch if status in ("success", "empty") else None
            except Exception:
                return game, None

    requests = [asyncio.create_task(_one_alt(game)) for game in games]
    fetch_stage_timeout = _nfl_alt_fetch_deadline(len(games))
    done, pending = await asyncio.wait(
        requests, timeout=min(fetch_stage_timeout,
                              max(0, overall_deadline - time.monotonic())))
    for task in pending:
        task.cancel()
    await asyncio.gather(*pending, return_exceptions=True)
    batches, failed_events = [], []
    for task in done:
        try:
            game, batch = task.result()
        except Exception:
            continue
        if batch is None:
            failed_events.append(game.get("game") or game.get("id") or "game")
            batches.append((game, []))
        else:
            event_id = str(game.get("id") or "")
            if event_id and (batch or event_id not in raw_events):
                raw_events[event_id] = batch
            batches.append((game, batch))
    done_ids = {str(game.get("id") or "") for game, _ in batches}
    for game in games:
        event_id = str(game.get("id") or "")
        if event_id not in done_ids:
            failed_events.append(game.get("game") or event_id or "game")
            batches.append((game, []))
    if raw_events:
        await asyncio.to_thread(_alt_coach_raw_cache_set, date_str, raw_events)

    lines = []
    for game, batch in batches:
        home = game.get("home_abbr", "") or _name_to_abbr(game.get("home_team", ""))
        away = game.get("away_abbr", "") or _name_to_abbr(game.get("away_team", ""))
        for source_line in batch:
            line = dict(source_line)
            info = roster_map.get(_norm(line.get("name", ""))) if roster_map else None
            if info and not info.get("eligible", True):
                continue
            line.update({
                "home_team": game.get("home_team", ""),
                "away_team": game.get("away_team", ""),
                "home_abbr": home, "away_abbr": away,
                "game": game.get("game", ""), "game_start": game.get("start", ""),
                "roster_team": (info or {}).get("team", ""),
                "roster_position": (info or {}).get("position", ""),
                "weather": (weather_by_game or {}).get(
                    f"{away}@{home}",
                    _nfl_weather_empty(game, reason="Weather unavailable")
                ) if date_str >= _nfl_today() else None,
            })
            lines.append(line)
    lines = _nfl_dedupe_alt_lines(lines)
    if time.monotonic() - started > _NFL_ALT_OVERALL_TIMEOUT:
        failed_events.append("alternate analysis deadline")
    await asyncio.to_thread(_apply_nfl_injury_context, lines, roster_map)
    try:
        df = await _alt_stage(get_nfl_stats(), _NFL_ALT_LOAD_STAGE_TIMEOUT)
    except Exception as exc:
        raise RuntimeError(f"NFL stats are unavailable: {exc}") from exc
    if df is None:
        raise RuntimeError("NFL stats are unavailable.")
    alt_target = games[0] if games else {}
    defense_df = await asyncio.to_thread(
        _nfl_prop_analysis_frame, df, alt_target.get("season"),
        alt_target.get("week"), alt_target.get("season_type", "REG"))

    def _analyze_alt_lines():
        analyzed_picks, timed_out = [], False
        deadline = min(
            time.monotonic() + _NFL_ALT_ANALYSIS_STAGE_TIMEOUT,
            overall_deadline)
        with _NFL_ANALYSIS_LOCK:
            _NFL_POSDEF_FRAME_LOCAL.frame = defense_df
            try:
                for line in lines:
                    if time.monotonic() >= deadline:
                        timed_out = True
                        break
                    analyzer = _analyze_new_prop if system == "NEW" else _analyze_prop
                    result = analyzer(
                        line, df, line.get("home_abbr", ""), line.get("away_abbr", ""))
                    if _nfl_alt_result_eligible(result):
                        analyzed_picks.append(result)
            finally:
                try:
                    del _NFL_POSDEF_FRAME_LOCAL.frame
                except AttributeError:
                    pass
        return analyzed_picks, timed_out

    picks, analysis_timed_out = await asyncio.to_thread(_analyze_alt_lines)
    if analysis_timed_out:
        failed_events.append("alternate analysis deadline")
    partial = bool(failed_events) or (
        time.monotonic() - started > _NFL_ALT_OVERALL_TIMEOUT)
    unique_failures = list(dict.fromkeys(failed_events))
    warning = (
        "Some games or alternate analysis stages did not complete: "
        + ", ".join(unique_failures[:4])
        if failed_events else "")
    payload = {
        "date": date_str, "picks": picks if not partial else [], "lines": len(lines),
        "partial": partial, "authoritative": not partial,
        "capture_allowed": not partial,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "warning": warning,
        "failed_games": unique_failures,
        "failed_game_count": len(unique_failures),
    }
    if system == "NEW":
        payload["system"] = "NEW"
        payload = _new_sanitize_json(payload)
    # Never persist a partial board as the current result. The raw per-event
    # cache above remains useful for the next retry, while the last complete
    # board stays available through the endpoint fallback.
    if not partial:
        await asyncio.to_thread(_alt_coach_cache_set, date_str, payload, system)
        await asyncio.to_thread(
            _nfl_auto_capture_alt_coach, date_str, payload, system)
    if partial:
        retry_key = f"{system}:{date_str}"
        count = _ALT_COACH_RETRY_COUNT.get(retry_key, 0) + 1
        _ALT_COACH_RETRY_COUNT[retry_key] = min(count, 6)
        _ALT_COACH_NEXT_RETRY[retry_key] = time.time() + min(
            15 * 60, _ALT_COACH_RETRY_BASE * (2 ** (count - 1)))
    else:
        retry_key = f"{system}:{date_str}"
        _ALT_COACH_RETRY_COUNT.pop(retry_key, None)
        _ALT_COACH_NEXT_RETRY.pop(retry_key, None)
    return payload

@app.get("/api/nfl/coach-alternates")
async def api_nfl_coach_alternates(request: Request, date_str: str = "",
                                   token: str = "", system: str = "OLD"):
    tok = token or request.headers.get("Authorization", "").replace("Bearer ", "").strip()
    if not _verify_hub_token(tok):
        raise HTTPException(
            status_code=401,
            detail="Subscription required — please log in via moneypicksarena.com")
    ds = date_str or _nfl_today()
    system = "NEW" if str(system).upper() == "NEW" else "OLD"
    if ds < _nfl_today() and system == "OLD":
        raise HTTPException(
            status_code=400,
            detail="Alternate-line Coach scans are available for current and upcoming slates.")
    cached = await asyncio.to_thread(_alt_coach_cache_get, ds, False, system)
    stale_complete = await asyncio.to_thread(
        _alt_coach_cache_get, ds, True, system)
    if stale_complete and stale_complete.get("partial"):
        stale_complete = None
    if stale_complete:
        await asyncio.to_thread(
            _nfl_auto_capture_alt_coach, ds, stale_complete, system)
    if cached and not cached.get("partial"):
        return JSONResponse(cached)
    task, started = _alt_coach_start_task(ds, system)
    if not task.done():
        # Contract: HTTP 202 means the shared scan is still running. Clients
        # should poll this same URL; a disconnect never cancels the task.
        body = {
            "pending": True, "date": ds,
            "task_shared": True,
            "detail": "The alternate-line scan is still running.",
        }
        if system == "NEW":
            body["system"] = "NEW"
        if stale_complete:
            body.update({
                "stale": True, "partial": True,
                "picks": stale_complete.get("picks", []),
                "last_complete": True,
                "authoritative": False, "capture_allowed": False,
                "warning": (cached or {}).get("warning")
                    or "Showing the last known complete result while refresh continues.",
            })
        body["failed_games"] = (cached or {}).get("failed_games", [])
        body["failed_game_count"] = len(body["failed_games"])
        return JSONResponse(body, status_code=202)
    try:
        result = task.result()
    except Exception as exc:
        stale = await asyncio.to_thread(
            _alt_coach_cache_get, ds, True, system)
        if stale and not stale.get("partial"):
            payload = dict(stale)
            payload.update({
                "stale": True, "partial": True, "authoritative": False,
                "capture_allowed": False,
                "warning": f"Refresh failed; showing the last completed result: {exc}",
            })
            payload["last_complete"] = True
            return JSONResponse(payload)
        payload = {
            "pending": False, "date": ds, "partial": True,
            "authoritative": False, "capture_allowed": False,
            "error": str(exc),
        }
        if system == "NEW":
            payload["system"] = "NEW"
        return JSONResponse(payload, status_code=503)
    fallback = {
        "pending": False, "date": ds, "partial": True,
        "authoritative": False, "capture_allowed": False,
        "error": "Alternate-line scan returned no result.",
    }
    if system == "NEW":
        fallback["system"] = "NEW"
    if isinstance(result, dict) and result.get("partial"):
        if stale_complete:
            payload = dict(stale_complete)
            payload.update({
                "stale": True, "partial": True, "last_complete": True,
                "authoritative": False, "capture_allowed": False,
                "warning": result.get("warning")
                    or "Refresh incomplete; showing the last known complete result.",
                "failed_games": result.get("failed_games", []),
                "failed_game_count": result.get("failed_game_count", 0),
            })
            return JSONResponse(payload)
        result = dict(result)
        result["picks"] = []
        result["authoritative"] = False
        result["capture_allowed"] = False
    return JSONResponse(result if isinstance(result, dict) else fallback)

_ADMIN_EMAILS = {e.strip().lower() for e in os.environ.get("ADMIN_EMAIL", "higgi117711@gmail.com").split(",") if e.strip()}

def _token_email(token: str) -> str:
    if not token or len(token.split(".")) != 3 or not JWT_SECRET:
        return ""
    try:
        payload = jose_jwt.decode(token, JWT_SECRET, algorithms=["HS256"])
        return str(payload.get("sub", "")).strip().lower()
    except Exception:
        return ""

def _is_admin_token(token: str) -> bool:
    return bool(_ADMIN_EMAILS) and _token_email(token) in _ADMIN_EMAILS

def _nfl_batch_admin_ok(request: Request, token: str = "", admin: str = "") -> bool:
    """Accept an admin hub JWT or the existing internal admin token.

    The internal token is supported through the header as well as the legacy
    admin query/body value so the season controls work in the same admin
    session that already reveals the NFL admin UI.
    """
    tok = token or request.headers.get("Authorization", "").replace("Bearer ", "").strip()
    if _is_admin_token(tok):
        return True
    import hmac
    secret = os.environ.get("INTERNAL_API_TOKEN", "")
    supplied = (
        request.headers.get("X-Internal-Token", "")
        or admin
        or request.query_params.get("admin", "")
    )
    return bool(secret and supplied) and hmac.compare_digest(supplied, secret)

_CRON_BUSY_NFL = False

@app.api_route("/api/cron-run", methods=["GET", "POST"])
async def cron_run_nfl(request: Request, date_str: str = "", system: str = "OLD"):
    # Cron-friendly trigger: authed by the static INTERNAL_API_TOKEN secret sent
    # as a header (kept out of the URL so it isn't logged). No expiring hub login
    # needed. Runs the pipeline (which caches it) so members can pull the picks,
    # and wakes the free-tier app on Render. In-flight guard blocks overlapping runs.
    global _CRON_BUSY_NFL
    import hmac
    secret = os.environ.get("INTERNAL_API_TOKEN", "")
    tok = request.headers.get("X-Internal-Token", "") or request.headers.get("Authorization", "").replace("Bearer ", "").strip()
    if not secret or not hmac.compare_digest(tok or "", secret):
        raise HTTPException(status_code=401, detail="Invalid cron token")
    system = "NEW" if str(system).upper() == "NEW" else "OLD"
    ds = date_str or _nfl_today()
    if _CRON_BUSY_NFL:
        getter = _new_cache_get if system == "NEW" else _cache_get
        payload = {"ran": False, "cached": bool(getter(ds)), "date": ds,
                   "reason": "already running"}
        if system == "NEW":
            payload["system"] = "NEW"
        return payload
    _CRON_BUSY_NFL = True
    try:
        await run_pipeline(ds, system=system)
    finally:
        _CRON_BUSY_NFL = False
    getter = _new_cache_get if system == "NEW" else _cache_get
    payload = {"ran": True, "cached": bool(getter(ds)), "date": ds}
    if system == "NEW":
        payload["system"] = "NEW"
    return payload


@app.post("/api/run")
async def api_run(request: Request):
    body     = await request.json() if request.headers.get("content-type","").startswith("application/json") else {}
    tok = body.get("token","") or request.headers.get("Authorization","").replace("Bearer ","").strip()
    if not _verify_hub_token(tok):
        raise HTTPException(status_code=401, detail="Subscription required — please log in via moneypicksarena.com")
    date_str = body.get("date", _nfl_today())
    system = "NEW" if str(body.get("system") or "OLD").upper() == "NEW" else "OLD"
    scope = str(body.get("scope") or "day").lower()
    if scope not in ("day", "week"):
        raise HTTPException(status_code=400, detail="Run scope must be day or week")
    _nfl_prune_completed_jobs()
    # A reconnect or second tab must not launch another copy of the same slate.
    for existing_id, existing in JOBS.items():
        if (existing.get("status") == "running"
                and existing.get("request_key") == [date_str, system, scope]):
            return {"job_id": existing_id}
    job_id   = str(uuid.uuid4())[:8]
    JOBS[job_id] = {
        "status":"running","result":None,"error":None,"progress":"Starting…",
        "created_at": time.time(),
        "request_key": [date_str, system, scope],
    }
    if system == "NEW":
        JOBS[job_id]["system"] = "NEW"
    async def _run():
        try:
            # Job-level watchdog: no matter what hangs inside, the job always
            # resolves to done/error. Weekly runs get extra time because they
            # preserve seven independent daily caches/snapshots.
            async def _work():
                # Single-day NEW runs need the same clean starting point as
                # weekly runs. Compatibility responses and prior slate lookups
                # are optional accelerators; retaining them can push a large
                # Sunday board over a small Render instance's memory limit.
                _NFL_ENRICHED_RESULTS.clear()
                await asyncio.to_thread(_nfl_clear_slate_caches)
                if scope == "week":
                    dates = _nfl_week_dates(date_str)
                    results = [None] * len(dates)
                    today = _nfl_today()
                    completed = 0

                    async def _run_week_date(index, ds):
                        nonlocal completed
                        if ds < today:
                            saved = await asyncio.to_thread(
                                _new_cache_get if system == "NEW" else _cache_get, ds)
                            if not saved:
                                saved = await asyncio.to_thread(
                                    _nfl_load_board_snapshots, ds, system)
                            if not saved:
                                try:
                                    scheduled_games = await get_espn_games(ds)
                                except Exception as exc:
                                    scheduled_games = None
                                    schedule_error = str(exc)
                                else:
                                    schedule_error = ""
                                if scheduled_games == []:
                                    past_error = (
                                        "No NFL games found for "
                                        f"{ds} — NFL season runs Sept–Feb.")
                                elif scheduled_games is None:
                                    past_error = (
                                        "Past NFL game date could not verify "
                                        f"the schedule for {ds}: {schedule_error}")
                                else:
                                    past_error = (
                                        "Past NFL game date has no saved "
                                        f"pre-game board: {ds}")
                            else:
                                past_error = ""
                            results[index] = saved or {
                                "date": ds, "picks": [], "all": [], "games": [],
                                "game_predictions": [], "td_picks": [],
                                "error": past_error,
                            }
                        else:
                            # Do not start another daily pipeline until this one
                            # (including its one allowed retry) is finished:
                            # run_pipeline's analysis lock is process-global.
                            JOBS.get(job_id, {}).update({
                                "progress": (
                                    f"Full week: {completed}/7 complete · "
                                    f"{ds}: checking slate…")})

                            async def _run_attempt():
                                return await run_pipeline(
                                    ds,
                                    force_refresh=True,
                                    capture_official=False,
                                    system=system,
                                    progress=lambda m, d=ds: JOBS.get(
                                        job_id, {}).update({
                                            "progress": (
                                                f"Full week: {completed}/7 complete · "
                                                f"{d}: {m}")}))

                            task = asyncio.create_task(_run_attempt())
                            try:
                                result = await asyncio.wait_for(
                                    asyncio.shield(task), timeout=_NFL_WEEK_DAY_TIMEOUT)
                            except asyncio.TimeoutError:
                                JOBS.get(job_id, {}).update({
                                    "progress": (
                                        f"Full week: {completed}/7 complete · "
                                        f"{ds}: still processing beyond the first "
                                        f"{_NFL_WEEK_DAY_TIMEOUT // 60}-minute window")})
                                try:
                                    result = await asyncio.wait_for(
                                        asyncio.shield(task), timeout=_NFL_WEEK_DAY_TIMEOUT)
                                except asyncio.TimeoutError:
                                    task.cancel()
                                    # A cancelled to_thread await does not stop
                                    # its worker.  Do not begin another date
                                    # until the pandas analysis worker has
                                    # observed cancellation and released the
                                    # process-wide analysis lock.
                                    analysis_events = _NFL_ANALYSIS_EVENTS
                                    if analysis_events is not None:
                                        started_event, done_event = analysis_events
                                        # If cancellation happened before the
                                        # worker was submitted, there is no
                                        # abandoned pandas thread to drain.
                                        if started_event.is_set():
                                            await asyncio.to_thread(done_event.wait)
                                            if _NFL_ANALYSIS_EVENTS is analysis_events:
                                                _NFL_ANALYSIS_EVENTS = None
                                    results[index] = {
                                        "date": ds, "picks": [], "all": [],
                                        "games": [], "game_predictions": [],
                                        "td_picks": [],
                                        "error": (
                                            "This date exceeded the extended "
                                            "24-minute data-source deadline while "
                                            "the same analysis task remained in progress."),
                                    }
                                    result = None
                                except Exception as exc:
                                    results[index] = {
                                        "date": ds, "picks": [], "all": [],
                                        "games": [], "game_predictions": [],
                                        "td_picks": [],
                                        "error": f"This date failed during its continuation: {exc}",
                                    }
                                    result = None
                            except Exception as exc:
                                results[index] = {
                                    "date": ds, "picks": [], "all": [],
                                    "games": [], "game_predictions": [],
                                    "td_picks": [],
                                    "error": f"This date failed: {exc}",
                                }
                                result = None
                            if result is not None:
                                # A full-week run is a valid pre-kickoff
                                # Game Predictor forecast for each slate.
                                # Keep player-prop official capture in its
                                # existing game-day-only path.
                                await asyncio.to_thread(
                                    _nfl_save_gp_snapshot, ds, result, system)
                                results[index] = result
                        completed += 1
                        JOBS.get(job_id, {}).update({
                            "progress": f"Full week: {completed}/7 complete"})

                    # Sequential by design: run_pipeline's analysis lock is
                    # process-global, so daily tasks must never overlap.
                    for index, ds in enumerate(dates):
                        await _run_week_date(index, ds)
                        # A completed Sunday payload can be hundreds of
                        # thousands of fields.  Keeping it in RAM while Monday
                        # starts makes weekly mode exceed the service memory
                        # limit even though either date succeeds by itself.
                        # Spool each completed date before analyzing the next.
                        daily_payload = results[index]
                        if daily_payload is not None:
                            try:
                                spool_path = await asyncio.to_thread(
                                    _nfl_week_spool_write,
                                    job_id, index, daily_payload)
                                results[index] = {
                                    "_nfl_week_spool": str(spool_path)}
                                daily_payload = None
                            except Exception as exc:
                                # A spool failure must not discard a completed
                                # board.  Retain it and continue with the older,
                                # higher-memory behavior for this date only.
                                print(
                                    f"[NFLWeek] Could not spool {ds}: {exc}")
                        # Release DataFrame slices and role/defense aggregates
                        # before starting the next date.  The global base
                        # nflverse frame and performance caches stay intact.
                        await asyncio.to_thread(_nfl_clear_slate_caches)
                    # Consume the seven daily payloads while merging.  Keeping
                    # every full board and then copying every row into a second
                    # weekly payload briefly doubles peak memory — enough to
                    # restart the service on a large Sunday slate.  The merged
                    # result is the only payload this interactive job needs.
                    merged = await asyncio.to_thread(
                        _nfl_merge_week_results, date_str, results, consume=True)
                    results.clear()
                    gc.collect()
                    failed_dates = merged.get("failed_dates") or []
                    if failed_dates:
                        JOBS.get(job_id, {}).update({
                            "progress": (
                                f"Full week incomplete — {len(failed_dates)} "
                                f"date(s) failed: {', '.join(failed_dates)}")})
                    else:
                        JOBS.get(job_id, {}).update({
                            "progress": "Full week complete"})
                    if system == "NEW":
                        merged["system"] = "NEW"
                        merged["model_version"] = "NEW-v2-ewma-weather"
                    return merged
                result = await run_pipeline(
                    date_str,
                    system=system,
                    force_refresh=True,
                    progress=lambda m: JOBS.get(job_id, {}).update({"progress": m}))
                return result
            result = await asyncio.wait_for(
                _work(),
                timeout=(
                    _NFL_WEEK_JOB_TIMEOUT
                    if scope == "week" else _NFL_SINGLE_DAY_TIMEOUT))
            JOBS[job_id]["progress"] = "Preparing completed board for download…"
            response_path = await asyncio.to_thread(
                _nfl_write_job_response, job_id, result)
            # Retain only metadata in RAM. Polling never re-encodes the board.
            del result
            JOBS[job_id].update({
                "status":"done","response_path":str(response_path),
                "finished_at":time.time()})
        except asyncio.TimeoutError:
            last_stage = JOBS.get(job_id, {}).get("progress", "starting the run")
            print(f"[Pipeline] Job timed out during: {last_stage}")
            JOBS[job_id].update({"status":"error","finished_at":time.time(),
                "error":("Weekly run timed out after 60 minutes"
                         if scope == "week"
                         else f"Run timed out after "
                              f"{_NFL_SINGLE_DAY_TIMEOUT // 60} minutes")
                        + " during: " + last_stage
                        + ". No completed board was returned."})
        except Exception as e:
            import traceback
            traceback.print_exc()
            JOBS[job_id].update({
                "status":"error","error":str(e),"finished_at":time.time()})
    asyncio.create_task(_run())
    return {"job_id": job_id}

@app.get("/api/run/{job_id}")
async def api_poll(job_id: str, status_only: bool = False):
    job = JOBS.get(job_id)
    if not job: raise HTTPException(404, "Job not found")
    if job.get("status") in ("done", "error"):
        # Keep the payload available for this response. The next Run Picks
        # request can then release it immediately instead of retaining a whole
        # completed slate alongside fresh analysis.
        job.setdefault("delivered_at", time.time())
    if job.get("status") == "done" and not status_only:
        response_path = job.get("response_path")
        if not response_path or not pathlib.Path(response_path).is_file():
            raise HTTPException(410, "Completed job file is unavailable. Use Get Picks to load saved boards.")
        return FileResponse(response_path, media_type="application/json",
                            headers={"Cache-Control": "no-store"})
    return {key: value for key, value in job.items()
            if key not in ("response_path", "request_key", "result")}


def _nfl_write_job_response(job_id: str, result: dict) -> pathlib.Path:
    """Prepare strict JSON once, off the HTTP loop, without a second board copy."""
    target = _CACHE_DIR / f"nfl_job_response_{job_id}.json"
    temp = target.with_suffix(".tmp")
    try:
        with temp.open("w", encoding="utf-8") as stream:
            json.dump({"status": "done", "result": _nfl_json_ready(result)}, stream,
                      ensure_ascii=False, allow_nan=False, separators=(",", ":"))
        temp.replace(target)
    finally:
        temp.unlink(missing_ok=True)
    return target


def _nfl_week_dates(anchor_date: str) -> list:
    """Return the NFL display week containing anchor_date: Wednesday–Tuesday."""
    try:
        anchor = datetime.strptime(anchor_date, "%Y-%m-%d").date()
    except (TypeError, ValueError):
        raise HTTPException(status_code=400, detail="A valid NFL date is required")
    start = anchor - timedelta(days=(anchor.weekday() - 2) % 7)
    return [(start + timedelta(days=offset)).isoformat() for offset in range(7)]


def _nfl_week_spool_write(job_id: str, index: int, payload: dict) -> pathlib.Path:
    """Atomically park one completed daily board outside process memory."""
    target = _CACHE_DIR / f"nfl_week_{job_id}_{index}.json"
    temp = target.with_suffix(".tmp")
    temp.write_text(
        json.dumps(payload, ensure_ascii=False), encoding="utf-8")
    temp.replace(target)
    return target


def _nfl_merge_week_results(anchor_date: str, daily_results: list,
                            consume: bool = False) -> dict:
    """Merge daily boards without merging their tracking identity.

    Interactive full-week jobs may consume source lists as they merge to avoid
    retaining duplicate copies of a large Sunday board.  Other callers keep the
    original non-consuming behavior.
    """
    dates = _nfl_week_dates(anchor_date)
    merged = {
        "date": f"{dates[0]} through {dates[-1]}",
        "anchor_date": anchor_date,
        "week_mode": True,
        "week_start": dates[0],
        "week_end": dates[-1],
        "week_dates": dates,
        "picks": [], "all": [], "td_picks": [], "games": [],
        "game_predictions": [], "qualified": 0,
        "skipped_matchups": [],
        "daily_status": [],
    }
    notes, warnings, successful_tracking, failed_dates = [], [], [], []
    for ds, result_ref in zip(dates, daily_results):
        spool_path = None
        result = result_ref or {}
        if isinstance(result, dict) and result.get("_nfl_week_spool"):
            spool_path = pathlib.Path(result["_nfl_week_spool"])
            result = json.loads(spool_path.read_text(encoding="utf-8"))
        error = str(result.get("error") or "")
        merged["daily_status"].append({
            "date": ds, "error": error,
            "games": len(result.get("games") or []),
            "picks": len(result.get("picks") or []),
        })
        if error:
            notes.append(f"{ds}: {error}")
            # A date with no NFL slate is expected in the Wednesday–Tuesday
            # display week.  Other errors represent an incomplete week even
            # when other dates produced perfectly usable boards.
            if "No NFL games found" not in error:
                failed_dates.append(ds)
        else:
            successful_tracking.append(
                result.get("official_tracking") is True)
        for key in ("all", "picks", "td_picks"):
            source_rows = result.get(key) or []
            for row in source_rows:
                target = row if consume else dict(row)
                target["slate_date"] = ds
                merged[key].append(target)
            if consume and source_rows:
                result[key] = []
        source_games = result.get("games") or []
        for game in source_games:
            target = game if consume else dict(game)
            target["slate_date"] = ds
            merged["games"].append(target)
        if consume and source_games:
            result["games"] = []
        source_predictions = result.get("game_predictions") or []
        for game in source_predictions:
            target = game if consume else dict(game)
            target["slate_date"] = ds
            merged["game_predictions"].append(target)
        if consume and source_predictions:
            result["game_predictions"] = []
        for matchup in result.get("skipped_matchups") or []:
            merged["skipped_matchups"].append(f"{ds}: {matchup}")
        if result.get("data_warning") and result["data_warning"] not in warnings:
            warnings.append(result["data_warning"])
        if result.get("data_note") and result["data_note"] not in warnings:
            warnings.append(result["data_note"])
        if result.get("defense_legacy_warning"):
            legacy = "⚠️ " + str(result["defense_legacy_warning"])
            if legacy not in warnings:
                warnings.append(legacy)
        if consume and spool_path is not None:
            try:
                spool_path.unlink(missing_ok=True)
            except Exception:
                pass
    merged["qualified"] = len(merged["picks"])
    merged["data_warning"] = " · ".join(
        w for w in warnings if str(w).startswith("⚠"))
    merged["data_note"] = " · ".join(
        w for w in warnings if not str(w).startswith("⚠"))
    merged["incomplete"] = bool(failed_dates)
    merged["failed_dates"] = failed_dates
    merged["failed_date_count"] = len(failed_dates)
    merged["week_notice"] = (
        ("INCOMPLETE — " if failed_dates else "") +
        f"Full NFL week: {dates[0]} through {dates[-1]} (Wednesday–Tuesday). "
        f"{len(merged['games'])} games loaded. Opening lines are stored by game "
        "date; this weekly run does not lock the official pick tracker."
        + (f" Failed date(s): {', '.join(failed_dates)}." if failed_dates else "")
        + (f" {len(notes)} date(s) had no usable saved/live board."
           if notes and not failed_dates else "")
    )
    merged["official_tracking"] = (
        (not failed_dates) and bool(successful_tracking)
        and all(successful_tracking))
    if not successful_tracking and not merged["all"]:
        merged["error"] = "No saved or live NFL boards were available for this week."
    return merged

async def _nfl_season_game_dates(season: int) -> list:
    """Return every regular-season and playoff game date for one NFL season."""
    async with httpx.AsyncClient(timeout=60, follow_redirects=True) as client:
        response = await client.get(_NFL_GAMES_HISTORY_URL)
        response.raise_for_status()
    rows = csv.DictReader(io.StringIO(response.text))
    valid_types = {"REG", "WC", "DIV", "CON", "SB", "POST"}
    return sorted({
        row.get("gameday", "")
        for row in rows
        if str(row.get("season", "")) == str(season)
        and str(row.get("game_type", "")).upper() in valid_types
        and re.fullmatch(r"\d{4}-\d{2}-\d{2}", row.get("gameday", ""))
    })

@app.post("/api/historical-season")
async def api_historical_season(request: Request):
    """Run one full NFL season into the separate historical archive."""
    body = await request.json() if request.headers.get(
        "content-type", "").startswith("application/json") else {}
    tok = body.get("token", "") or request.headers.get(
        "Authorization", "").replace("Bearer ", "").strip()
    if not _nfl_batch_admin_ok(
            request, token=tok, admin=str(body.get("admin") or "")):
        raise HTTPException(status_code=403, detail="Admin access required")
    system = "NEW" if str(body.get("system") or "OLD").upper() == "NEW" else "OLD"
    try:
        season = int(body.get("season"))
    except (TypeError, ValueError):
        raise HTTPException(status_code=400, detail="A valid NFL season is required")
    if season < 1999 or season >= _cur_season:
        raise HTTPException(
            status_code=400,
            detail=f"Choose a completed NFL season from 1999 to {_cur_season - 1}")
    for existing_id, existing in SEASON_JOBS.items():
        if (existing.get("season") == season
                and existing.get("system", "OLD") == system
                and existing.get("status") == "running"):
            return {"job_id": existing_id, "already_running": True}

    job_id = "season-" + str(uuid.uuid4())[:8]
    SEASON_JOBS[job_id] = {
        "status": "running", "season": season, "system": system, "total": 0,
        "completed": 0, "saved": 0, "skipped": 0, "failed": 0,
        "failures": [], "current_date": "", "progress": "Checking dependencies…",
    }

    async def _run_season():
        job = SEASON_JOBS[job_id]
        try:
            # Fail before the first historical Odds API request if the model's
            # required dataframe dependency/data cannot load.
            stats = await get_nfl_stats()
            if stats is None or getattr(stats, "empty", True):
                raise RuntimeError(
                    "NFL player stats could not load; no historical odds were requested.")
            dates = await _nfl_season_game_dates(season)
            if not dates:
                raise RuntimeError(f"No NFL schedule dates found for {season}.")
            cfg = _nfl_store_config(system)
            saved_rows = _nfl_sb_get("mpa_track_ledger", {
                "app": f"eq.{cfg['app']}",
                "category": f"eq.{cfg['hist']}",
                "select": "date", "limit": "730",
            })
            already_saved = {row.get("date") for row in (saved_rows or [])}
            job["total"] = len(dates)
            for index, date_str in enumerate(dates, 1):
                job["current_date"] = date_str
                if date_str in already_saved:
                    job["completed"] += 1
                    job["skipped"] += 1
                    job["progress"] = (
                        f"{index}/{len(dates)} {date_str} already saved — skipping")
                    continue
                try:
                    def _progress(message, i=index, ds=date_str):
                        job["progress"] = f"{i}/{len(dates)} {ds}: {message}"
                    result = await asyncio.wait_for(
                        run_pipeline(date_str, progress=_progress, simulate=True,
                                     system=system),
                        timeout=420)
                    replay = result.get("historicalTrackRecord") or {}
                    has_props = any(
                        day.get("detail") for day in replay.get("dates") or [])
                    has_gp = any(
                        day.get("games")
                        for day in (replay.get("game_predictor") or {}).get("daily") or [])
                    if result.get("error") or not (has_props or has_gp):
                        raise RuntimeError(
                            result.get("error") or "Replay produced no graded results")
                    if result.get("historical_saved") is not True:
                        raise RuntimeError(
                            "Replay completed but Supabase did not confirm the archive write")
                    job["saved"] += 1
                except Exception as exc:
                    job["failed"] += 1
                    job["failures"].append({
                        "date": date_str, "error": str(exc)[:300]})
                finally:
                    job["completed"] += 1
            job["status"] = "done"
            job["current_date"] = ""
            job["progress"] = (
                f"Finished {season}: {job['saved']} saved, "
                f"{job['skipped']} already present, {job['failed']} failed")
        except Exception as exc:
            job["status"] = "error"
            job["error"] = str(exc)
            job["progress"] = str(exc)

    asyncio.create_task(_run_season())
    return {"job_id": job_id}

@app.get("/api/historical-season/{job_id}")
async def api_historical_season_poll(request: Request, job_id: str,
                                     token: str = "", system: str = "OLD"):
    tok = token or request.headers.get(
        "Authorization", "").replace("Bearer ", "").strip()
    if not _nfl_batch_admin_ok(request, token=tok):
        raise HTTPException(status_code=403, detail="Admin access required")
    job = SEASON_JOBS.get(job_id)
    if not job:
        raise HTTPException(status_code=404, detail="Season job not found")
    requested_system = "NEW" if str(system).upper() == "NEW" else "OLD"
    if job.get("system", "OLD") != requested_system:
        raise HTTPException(status_code=404, detail="Season job not found")
    payload = dict(job)
    if requested_system != "NEW":
        payload.pop("system", None)
    return payload

def _nfl_read_saved_board(date_str, system):
    """Read a completed board, not a freshness check for a new analysis."""
    getter = _new_cache_get if system == "NEW" else _cache_get
    saved = getter(date_str, allow_stale=True) or _nfl_load_board_snapshots(date_str, system)
    if isinstance(saved, dict):
        # A shallow response wrapper avoids mutating the frozen saved payload or
        # copying its large pick trees. Legacy values are shown as unverified;
        # Get Picks never loads stats or recomputes them.
        saved = dict(saved)
        saved["system"] = system
        saved["saved_board"] = True
        if saved.get("defense_schema_version") != 3:
            saved["defense_legacy_warning"] = (
                "Legacy saved board: defensive venue/context metrics are unverified "
                "and were not recomputed.")
        if system == "NEW":
            saved.setdefault("model_version", "NEW-v2-ewma-weather")
    return saved

def _nfl_saved_response_file(date_str, scope, system):
    """Load one day at a time and stream JSON without FastAPI's deep copy."""
    if scope == "week":
        def days():
            for ds in _nfl_week_dates(date_str):
                yield _nfl_read_saved_board(ds, system) or {
                    "date": ds, "picks": [], "all": [], "games": [],
                    "game_predictions": [], "td_picks": [],
                    "error": "No saved board for this date.",
                }
        result = _nfl_merge_week_results(date_str, days(), consume=True)
        if not (result.get("all") or result.get("picks") or result.get("games")):
            raise HTTPException(status_code=404, detail="No saved picks for this NFL week.")
    else:
        result = _nfl_read_saved_board(date_str, system)
        if not result:
            raise HTTPException(status_code=404, detail="No saved picks for this date.")
    result["system"] = system
    result["saved_board"] = True
    if system == "NEW":
        result.setdefault("model_version", "NEW-v2-ewma-weather")
    path = _CACHE_DIR / ("nfl_saved_response_" + uuid.uuid4().hex + ".json")
    _nfl_write_board_cache(path, result)
    return path

_NFL_SAVED_RESPONSE_LOCK = asyncio.Lock()

@app.get("/api/cached")
async def api_cached(request: Request, target_date: str = "", token: str = "",
                     scope: str = "day", system: str = "OLD"):
    # Read-only: serve picks already saved on file. Never runs the pipeline, so any
    # logged-in member can pull the latest saved picks without triggering a fresh run.
    tok = token or request.headers.get("Authorization", "").replace("Bearer ", "").strip()
    if not _verify_hub_token(tok):
        raise HTTPException(status_code=401, detail="Subscription required — please log in via moneypicksarena.com")
    date_str = target_date or _nfl_today()
    try:
        date_str = datetime.strptime(date_str, "%Y-%m-%d").date().isoformat()
    except ValueError:
        raise HTTPException(status_code=400, detail="Invalid NFL date.")
    scope = str(scope).lower()
    if scope not in ("day", "week"):
        raise HTTPException(status_code=400, detail="Run scope must be day or week")
    system = "NEW" if str(system).upper() == "NEW" else "OLD"
    # No stats download, model enrichment, fresh odds, or new tracking writes.
    # Synchronous disk/Supabase work must not block the ASGI event loop.
    async with _NFL_SAVED_RESPONSE_LOCK:
        response_task = asyncio.create_task(asyncio.to_thread(
            _nfl_saved_response_file, date_str, scope, system))
        try:
            path = await asyncio.shield(response_task)
        except asyncio.CancelledError:
            # The worker still owns memory/the temporary file after a client
            # disconnect. Wait for it before admitting another response build.
            try:
                path = await response_task
                path.unlink(missing_ok=True)
            finally:
                raise
    return FileResponse(
        path, media_type="application/json",
        headers={"Cache-Control": "no-store"},
        background=BackgroundTask(path.unlink, missing_ok=True))

@app.get("/api/picks")
async def api_picks(request: Request, target_date: str = "", token: str = "",
                    simulate: bool = False, admin: str = "", system: str = "OLD"):
    tok = token or request.headers.get("Authorization", "").replace("Bearer ", "").strip()
    if not _verify_hub_token(tok) and not (
            simulate and _nfl_batch_admin_ok(request, tok, admin)):
        raise HTTPException(status_code=401, detail="Subscription required — please log in via moneypicksarena.com")
    date_str = target_date or _nfl_today()
    if simulate:
        try:
            replay_date = datetime.strptime(date_str, "%Y-%m-%d").date()
        except (TypeError, ValueError):
            raise HTTPException(status_code=400, detail="A valid completed NFL date is required")
        if replay_date >= _nfl_today_date():
            raise HTTPException(status_code=400, detail="Historical replays are available only for completed dates")
    result = await run_pipeline(date_str, simulate=simulate, system=system)
    return JSONResponse(result)

@app.get("/api/whoami")
async def whoami(request: Request, token: str = ""):
    tok = token or request.headers.get("Authorization", "").replace("Bearer ", "").strip()
    return {"is_admin": _is_admin_token(tok)}

# ─────────────────────────────────────────────────────────────────────────────
#  My Bets (bet tracking) — admin-only, mirrors NBA/NHL/MLB
# ─────────────────────────────────────────────────────────────────────────────
import threading as _bt_th, uuid as _bt_uuid, hashlib as _bt_hashlib
from datetime import date as _bt_date

_NFL_BET_LOG_PATH = str(_CACHE_DIR / "_nfl_bet_log.json")
_NFL_BET_LOCK = _bt_th.Lock()
_NFL_BET_LEDGER_APP = "nfl_bets"
_NFL_BET_LEDGER_DATE = "2000-01-01"
_NFL_BET_LEDGER_PREFIX = "__my_bets__:"
_NFL_BET_STAT_KEYS = tuple(PROP_MARKETS)
_NFL_STAT_LABEL = dict(PROP_LABELS)
_NFL_CAT_ORDER = [PROP_LABELS[m] for m in PROP_MARKETS]


def _nfl_bet_ledger_category(user_key: str) -> str:
    digest = _bt_hashlib.sha256(
        str(user_key or "__admin__").encode("utf-8")).hexdigest()[:32]
    return _NFL_BET_LEDGER_PREFIX + digest


def _nfl_load_local_bets(user_key: str) -> list:
    """One-time migration source for bets saved before Supabase persistence."""
    try:
        with open(_NFL_BET_LOG_PATH) as f:
            data = json.load(f)
        bets = data.get(user_key, []) if isinstance(data, dict) else []
        return list(bets) if isinstance(bets, list) else []
    except Exception:
        return []


def _nfl_load_bets(user_key: str) -> list:
    """Load one user's NFL bets from the durable Supabase ledger."""
    if not _SB_URL or not _SB_KEY:
        raise RuntimeError("Supabase is not configured")
    category = _nfl_bet_ledger_category(user_key)
    try:
        response = httpx.get(
            f"{_SB_URL}/rest/v1/mpa_track_ledger",
            headers={"apikey": _SB_KEY, "Authorization": f"Bearer {_SB_KEY}"},
            params={
                "app": f"eq.{_NFL_BET_LEDGER_APP}",
                "date": f"eq.{_NFL_BET_LEDGER_DATE}",
                "category": f"eq.{category}",
                "side": "eq.ALL",
                "select": "detail",
                "limit": "1",
            },
            timeout=15)
        if response.status_code != 200:
            raise RuntimeError(f"Supabase read returned HTTP {response.status_code}")
        rows = response.json()
    except Exception as exc:
        raise RuntimeError(f"NFL My Bets could not be loaded: {exc}") from exc
    if rows:
        bets = rows[0].get("detail") or []
        return list(bets) if isinstance(bets, list) else []

    # Import the old local bet log once. The durable empty row created by a
    # later delete prevents removed bets from being resurrected from disk.
    local_bets = _nfl_load_local_bets(user_key)
    if local_bets:
        _nfl_save_bets(user_key, local_bets)
    return local_bets


def _nfl_save_bets(user_key: str, bets: list):
    """Replace one user's durable NFL bet list; never report false success."""
    row = {
        "app": _NFL_BET_LEDGER_APP,
        "date": _NFL_BET_LEDGER_DATE,
        "category": _nfl_bet_ledger_category(user_key),
        "side": "ALL",
        "wins": 0,
        "losses": 0,
        "locked": False,
        "detail": list(bets or []),
    }
    if not _nfl_sb_upsert(
            "mpa_track_ledger", [row],
            on_conflict="app,date,category,side"):
        raise RuntimeError("NFL My Bets could not be saved to Supabase")


def _nfl_bet_admin_ok(tok: str, admin: str) -> bool:
    return _is_admin_token(tok) or (
        bool(admin) and admin == os.environ.get("INTERNAL_API_TOKEN", "__none__"))


def _nfl_bet_user_key(tok: str, admin: str) -> str:
    em = _token_email(tok) if tok else ""
    return em.lower().strip() if em else "__admin__"


def _nfl_american_profit(odds, stake, result) -> float:
    try:
        stake = float(stake)
    except Exception:
        return 0.0
    if result == "WIN":
        try:
            o = float(odds)
        except Exception:
            return 0.0
        return stake * (o / 100.0) if o > 0 else stake * (100.0 / abs(o))
    if result == "LOSS":
        return -stake
    return 0.0


def _nfl_num(s):
    try:
        if s is None:
            return None
        return float(str(s).strip())
    except Exception:
        return None


def _nfl_made(s):
    """ESPN 'made/att' style values e.g. '20/30' -> (20.0, 30.0)."""
    try:
        a, b = str(s).split("/")[:2]
        return float(a.strip()), float(b.strip())
    except Exception:
        return None, None


def _nfl_market_from_groups(groups: dict, market: str):
    """Extract a single market value from a player's ESPN boxscore groups.
    groups = {group_name_lower: {LABEL_UPPER: raw_str}}."""
    def g(grp, lbl):
        return (groups.get(grp) or {}).get(lbl)
    if market == "player_pass_yds":            return _nfl_num(g("passing", "YDS"))
    if market == "player_pass_tds":            return _nfl_num(g("passing", "TD"))
    if market == "player_pass_completions":    return _nfl_made(g("passing", "C/ATT"))[0]
    if market == "player_pass_attempts":       return _nfl_made(g("passing", "C/ATT"))[1]
    if market == "player_pass_interceptions":  return _nfl_num(g("passing", "INT"))
    if market == "player_rush_yds":            return _nfl_num(g("rushing", "YDS"))
    if market == "player_rush_reception_yds":
        rushing = _nfl_num(g("rushing", "YDS"))
        receiving = _nfl_num(g("receiving", "YDS"))
        if rushing is None and receiving is None:
            return None
        return (rushing or 0) + (receiving or 0)
    if market == "player_rush_attempts":       return _nfl_num(g("rushing", "CAR"))
    if market == "player_anytime_td":
        rt = _nfl_num(g("rushing", "TD"))
        ct = _nfl_num(g("receiving", "TD"))
        if rt is None and ct is None:
            return None
        return (rt or 0) + (ct or 0)
    if market == "player_reception_yds":       return _nfl_num(g("receiving", "YDS"))
    if market == "player_receptions":          return _nfl_num(g("receiving", "REC"))
    if market == "player_tackles_assists":     return _nfl_num(g("defensive", "TOT"))
    if market == "player_sacks":               return _nfl_num(g("defensive", "SACKS"))
    if market == "player_defensive_interceptions": return _nfl_num(g("interceptions", "INT"))
    if market == "player_kicking_points":      return _nfl_num(g("kicking", "PTS"))
    if market == "player_field_goals":         return _nfl_made(g("kicking", "FG"))[0]
    return None


_NFL_BOX_CACHE: dict = {}
_NFL_BOX_TTL = 120

def _nfl_player_name_key(value) -> str:
    """Normalize sportsbook/ESPN player names, including trailing suffixes."""
    name = re.sub(r"[^a-z0-9]+", " ", str(value or "").lower()).strip()
    parts = name.split()
    if parts and parts[-1] in {"jr", "sr", "ii", "iii", "iv", "v"}:
        parts.pop()
    return " ".join(parts)

def _nfl_box_lookup(date_str: str) -> dict:
    """Cached wrapper (see NBA): final dates cached permanently, in-progress dates
    for _NFL_BOX_TTL seconds, to avoid repeat ESPN hits / HTTP 429 during settlement."""
    import time as _t
    ent = _NFL_BOX_CACHE.get(date_str)
    now = _t.time()
    if ent and (ent["final"] or now - ent["ts"] < _NFL_BOX_TTL):
        return ent["data"]
    res, complete = _nfl_box_lookup_raw(date_str)
    allfinal = complete and bool(res)
    _NFL_BOX_CACHE[date_str] = {"ts": now, "final": allfinal, "data": res}
    return res

def _nfl_box_lookup_raw(date_str: str):
    """Return (results, complete). results = {lowername: {'final': bool, market: value}}.
    complete is True only when EVERY event for the date is final AND its box score was
    fetched successfully, so the wrapper marks the cache permanent only on fully-complete
    data (a failed summary fetch keeps the date on the short TTL so it retries)."""
    d = date_str.replace("-", "")
    results: dict = {}
    try:
        # ESPN currently rejects the generic browser User-Agent with HTTP 403
        # on these settlement endpoints. httpx's normal client headers work.
        sb = httpx.get(
            f"https://site.api.espn.com/apis/site/v2/sports/football/nfl/scoreboard?dates={d}",
            timeout=15)
        sb.raise_for_status()
        events = sb.json().get("events", [])
    except Exception as e:
        print(f"[nfl_box] scoreboard failed {date_str}: {e}")
        return results, False
    complete = True
    for ev in events:
        is_final = ev.get("status", {}).get("type", {}).get("completed", False)
        if not is_final:
            complete = False
        ev_id = ev.get("id")
        if not ev_id:
            complete = False
            continue
        try:
            bs = httpx.get(
                f"https://site.api.espn.com/apis/site/v2/sports/football/nfl/summary?event={ev_id}",
                timeout=15)
            if bs.status_code != 200:
                complete = False
                continue
            boxscore = bs.json().get("boxscore", {})
        except Exception:
            complete = False
            continue
        for team in boxscore.get("players", []):
            per_athlete: dict = {}
            for grp in team.get("statistics", []):
                gname = (grp.get("name") or "").lower()
                labels = [str(l).upper() for l in grp.get("labels", [])]
                for ath in grp.get("athletes", []):
                    name = (ath.get("athlete", {}).get("displayName") or "").lower().strip()
                    stats_arr = ath.get("stats", [])
                    if not name or not stats_arr:
                        continue
                    bucket = per_athlete.setdefault(name, {})
                    bucket[gname] = dict(zip(labels, stats_arr))
            for name, groups in per_athlete.items():
                ps: dict = {"final": is_final}
                for mk in _NFL_BET_STAT_KEYS:
                    v = _nfl_market_from_groups(groups, mk)
                    if v is not None:
                        ps[mk] = v
                results[_nfl_player_name_key(name)] = ps
    return results, complete


def _nfl_settle_cached(bet: dict, name_stats: dict) -> bool:
    if bet.get("result") in ("WIN", "LOSS", "PUSH"):
        return False
    st = name_stats.get(_nfl_player_name_key(bet.get("name")))
    if not st or not st.get("final"):
        return False
    market = bet.get("market") or ""
    actual = st.get(market)
    # Anytime TD / any "did not record" market: a player who appears in the box
    # but has no value for the stat recorded 0 (so an OVER 0.5 loses, UNDER wins).
    if actual is None and market in ("player_anytime_td",):
        actual = 0.0
    if actual is None:
        return False
    try:
        line = float(bet.get("line"))
    except Exception:
        return False
    side = bet.get("side", "OVER")
    if actual == line:
        res = "PUSH"
    elif side == "OVER":
        res = "WIN" if actual > line else "LOSS"
    else:
        res = "WIN" if actual < line else "LOSS"
    bet["result"] = res
    bet["actual"] = actual
    bet["profit"] = round(_nfl_american_profit(bet.get("odds"), bet.get("stake"), res), 2)
    bet["settled_at"] = _nfl_today()
    return True


def _nfl_settle_bet(bet: dict) -> bool:
    if bet.get("result") in ("WIN", "LOSS", "PUSH"):
        return False
    bdate = bet.get("date")
    if not bdate or bdate >= _nfl_today():
        return False
    try:
        ns = _nfl_box_lookup(bdate)
    except Exception as e:
        print(f"[nfl_bet_log] settle lookup failed {bdate}: {e}")
        return False
    return _nfl_settle_cached(bet, ns)


def _nfl_settle_batch(bets: list) -> bool:
    today = _nfl_today()
    dates_needed: set = set()
    for b in bets:
        if b.get("result") in ("WIN", "LOSS", "PUSH"):
            continue
        if b.get("date") and b["date"] < today:
            dates_needed.add(b["date"])
    if not dates_needed:
        return False
    ns_cache: dict = {}
    for d in sorted(dates_needed):
        try:
            ns_cache[d] = _nfl_box_lookup(d)
        except Exception as e:
            print(f"[nfl_bet_log] batch settle failed {d}: {e}")
    changed = False
    for b in bets:
        bdate = b.get("date")
        if bdate and bdate in ns_cache:
            if _nfl_settle_cached(b, ns_cache[bdate]):
                changed = True
    return changed


# ─────────────────────────────────────────────────────────────────────────────
#  NFL Track Record — automated daily grading with Supabase storage
# ─────────────────────────────────────────────────────────────────────────────

# ── Supabase helpers (httpx — already a dependency) ───────────────────────────
_SB_URL_RAW = os.environ.get("SUPABASE_URL", "").strip().rstrip("/")
_SB_URL = (f"https://{_SB_URL_RAW}.supabase.co"
           if _SB_URL_RAW and not _SB_URL_RAW.startswith("http")
           else _SB_URL_RAW)
_SB_KEY = os.environ.get("SUPABASE_SERVICE_KEY", "")

def _nfl_sb_get(table, params=None):
    if not _SB_URL or not _SB_KEY:
        return []
    try:
        r = httpx.get(
            f"{_SB_URL}/rest/v1/{table}",
            headers={"apikey": _SB_KEY, "Authorization": f"Bearer {_SB_KEY}"},
            params=params or {}, timeout=15)
        if r.status_code == 200:
            return r.json()
    except Exception as e:
        print(f"[nfl_sb_get] {e}")
    return []

def _nfl_sb_upsert(table, rows, on_conflict=None):
    if not _SB_URL or not _SB_KEY or not rows:
        return False
    try:
        h = {
            "apikey": _SB_KEY, "Authorization": f"Bearer {_SB_KEY}",
            "Content-Type": "application/json",
            "Prefer": "resolution=merge-duplicates,return=minimal",
        }
        url = f"{_SB_URL}/rest/v1/{table}"
        if on_conflict:
            url += f"?on_conflict={on_conflict}"
        r = httpx.post(url, headers=h, json=rows, timeout=20)
        return r.status_code in (200, 201, 204)
    except Exception as e:
        print(f"[nfl_sb_upsert] {e}")
    return False

def _nfl_sb_insert_ignore(table, rows, on_conflict):
    """Insert without ever replacing an existing ledger snapshot.
    The returned representation is empty when PostgREST ignored a duplicate."""
    if not _SB_URL or not _SB_KEY or not rows:
        return None
    try:
        r = httpx.post(
            f"{_SB_URL}/rest/v1/{table}?on_conflict={on_conflict}",
            headers={"apikey": _SB_KEY, "Authorization": f"Bearer {_SB_KEY}",
                     "Content-Type": "application/json",
                     "Prefer": "resolution=ignore-duplicates,return=representation"},
            json=rows, timeout=20)
        if r.status_code not in (200, 201):
            return None
        return r.json() if r.content else []
    except Exception as e:
        print(f"[nfl_sb_insert_ignore] {e}")
        return None

def _nfl_sb_save_latest_unlocked(table, row, captured_at):
    """Atomically insert or replace only an older, still-unlocked snapshot."""
    inserted = _nfl_sb_insert_ignore(
        table, [row], "app,date,category,side")
    if inserted is None:
        return "error"
    if inserted:
        return "saved"
    try:
        params = {
            "app": f"eq.{row['app']}", "date": f"eq.{row['date']}",
            "category": f"eq.{row['category']}", "side": f"eq.{row['side']}",
            "locked": "eq.false",
            # While unlocked, locked_at stores the earliest kickoff deadline.
            # PostgreSQL parses `now` at statement time.
            "locked_at": "gt.now",
            "detail->0->>captured_at": f"lt.{captured_at}",
        }
        response = httpx.patch(
            f"{_SB_URL}/rest/v1/{table}", params=params,
            headers={
                "apikey": _SB_KEY, "Authorization": f"Bearer {_SB_KEY}",
                "Content-Type": "application/json",
                "Prefer": "return=representation",
            },
            # Preserve result/lock state while atomically moving the unlocked
            # deadline to the incoming snapshot's earliest kickoff.
            json={
                "detail": row["detail"],
                "locked_at": row["locked_at"],
            }, timeout=20)
        if response.status_code not in (200, 204):
            print(f"[nfl_sb_latest] HTTP {response.status_code}: {response.text[:200]}")
            return "error"
        changed = response.json() if response.content else []
        return "updated" if changed else "refused"
    except Exception as exc:
        print(f"[nfl_sb_latest] {exc}")
        return "error"

def _nfl_sb_backfill_coach_deadline(saved, deadline, app_name=None):
    """Add a kickoff deadline to a legacy unlocked Coach snapshot."""
    app_name = app_name or "nfl_coach_track"
    detail = saved.get("detail") or []
    version = str((detail[0] if detail else {}).get("captured_at") or "")
    if not version:
        return False
    try:
        response = httpx.patch(
            f"{_SB_URL}/rest/v1/mpa_track_ledger",
            params={
                "app": f"eq.{app_name}",
                "date": f"eq.{saved['date']}",
                "category": f"eq.{saved['category']}",
                "side": "eq.ALL", "locked": "eq.false",
                "locked_at": "is.null",
                "detail->0->>captured_at": f"eq.{version}",
            },
            headers={
                "apikey": _SB_KEY, "Authorization": f"Bearer {_SB_KEY}",
                "Content-Type": "application/json",
                "Prefer": "return=representation",
            },
            json={"locked_at": deadline}, timeout=20)
        return (
            response.status_code in (200, 204)
            and bool(response.json() if response.content else []))
    except Exception as exc:
        print(f"[nfl_coach_deadline] {exc}")
        return False

def _nfl_sb_lock_coach_cas(saved, graded, summary, app_name=None):
    """Lock only the exact Coach capture version that was graded."""
    app_name = app_name or "nfl_coach_track"
    detail = saved.get("detail") or []
    version = str((detail[0] if detail else {}).get("captured_at") or "")
    if not version:
        return False
    try:
        response = httpx.patch(
            f"{_SB_URL}/rest/v1/mpa_track_ledger",
            params={
                "app": f"eq.{app_name}",
                "date": f"eq.{saved['date']}",
                "category": f"eq.{saved['category']}",
                "side": "eq.ALL", "locked": "eq.false",
                "detail->0->>captured_at": f"eq.{version}",
            },
            headers={
                "apikey": _SB_KEY, "Authorization": f"Bearer {_SB_KEY}",
                "Content-Type": "application/json",
                "Prefer": "return=representation",
            },
            json={
                "wins": summary["wins"], "losses": summary["losses"],
                "locked": True,
                "locked_at": datetime.now(timezone.utc).isoformat(),
                "detail": graded,
            },
            timeout=20)
        if response.status_code not in (200, 204):
            print(f"[nfl_coach_cas] HTTP {response.status_code}: {response.text[:200]}")
            return False
        changed = response.json() if response.content else []
        return bool(changed)
    except Exception as exc:
        print(f"[nfl_coach_cas] {exc}")
        return False


def _nfl_line_identity(row: dict) -> str:
    """Stable player/market identity scoped to one game.

    Player names recur across an NFL slate, so a player+market key alone can
    incorrectly apply one game's opening number to another game.  Prefer the
    canonical two-team matchup; when a feed omits one team, infer it from the
    home/away abbreviations and the row's team.  The normalized kickoff/game
    string is retained as a final scope guard.
    """
    team = str(row.get("team") or row.get("roster_team") or "").strip().upper()
    opponent = str(row.get("opponent") or row.get("opp") or "").strip().upper()
    home = str(row.get("home_abbr") or "").strip().upper()
    away = str(row.get("away_abbr") or "").strip().upper()
    if team and not opponent and team in (home, away):
        opponent = away if team == home else home
    if opponent and not team and opponent in (home, away):
        team = away if opponent == home else home
    teams = sorted(set(x for x in (team, opponent) if x))
    matchup = "-".join(teams)
    if not matchup:
        matchup = _norm(str(row.get("game") or row.get("matchup") or "")).replace(" ", "")
    start = str(row.get("game_start") or row.get("start") or "").strip()
    if start:
        # ISO timestamps from ESPN/OddsAPI may differ only by seconds/zone
        # formatting; the date-hour-minute portion is common to both feeds.
        start = start.replace("Z", "+00:00")[:16]
    scope = matchup or start
    return "|".join((
        _norm(str(row.get("name") or row.get("player") or "")),
        str(row.get("market") or row.get("mkt") or "").strip().lower(),
        scope,
    ))


def _nfl_opening_lines(date_str: str) -> dict:
    """Read the scheduled opening-line snapshot for one game date."""
    rows = _nfl_sb_get("mpa_track_ledger", {
        "app": f"eq.{_NFL_LINE_MOVEMENT_APP}",
        "date": f"eq.{date_str}",
        "category": f"eq.{_NFL_LINE_OPEN_CATEGORY}",
        "side": "eq.ALL",
        "select": "detail",
        "limit": "1",
    })
    detail = (rows[0] or {}).get("detail") if rows else None
    if isinstance(detail, str):
        try:
            detail = json.loads(detail)
        except Exception:
            detail = None
    if not isinstance(detail, dict):
        return {}
    captured_at = detail.get("captured_at")
    out = {}
    for line in detail.get("lines") or []:
        if not isinstance(line, dict):
            continue
        key = _nfl_line_identity(line)
        if key and key != "|":
            copy = dict(line)
            copy["captured_at"] = captured_at
            out[key] = copy
    return out


def _nfl_capture_opening_lines(date_str: str, result: dict) -> bool:
    """Save the scheduled pregame baseline for Thursday, Sunday, or Monday.

    Wednesday captures Thursday, Friday captures Sunday, and Saturday captures
    Monday. A later run on the same capture day replaces the earlier one so the
    baseline includes the fullest sportsbook board available that day.
    """
    try:
        target = datetime.strptime(date_str, "%Y-%m-%d").date()
    except (TypeError, ValueError):
        return False
    capture_day = _nfl_today_date()
    weekday_to_offset = {
        2: 1,  # Wednesday -> Thursday
        4: 2,  # Friday -> Sunday
        5: 2,  # Saturday -> Monday
    }
    offset = weekday_to_offset.get(capture_day.weekday())
    if offset is None or target != capture_day + timedelta(days=offset):
        return False
    lines, seen = [], set()
    for row in result.get("all") or []:
        key = _nfl_line_identity(row)
        line = row.get("realLine")
        if line is None:
            line = row.get("line")
        if not key or key == "|" or key in seen or line is None:
            continue
        seen.add(key)
        lines.append({
            "name": row.get("name", ""),
            "team": row.get("team") or row.get("roster_team", ""),
            "opponent": row.get("opponent", ""),
            "home_abbr": row.get("home_abbr", ""),
            "away_abbr": row.get("away_abbr", ""),
            "game": row.get("game", ""),
            "market": row.get("market", ""),
            "market_label": row.get("mkt") or row.get("label") or "",
            "line": line,
            "over_odds": (
                row.get("realOdds")
                if row.get("realOdds") is not None else row.get("over_odds")),
            "under_odds": (
                row.get("realUnderOdds")
                if row.get("realUnderOdds") is not None else row.get("under_odds")),
            "over_book": row.get("over_book", ""),
            "under_book": row.get("under_book", ""),
            "game_start": row.get("game_start", ""),
        })
    if not lines:
        return False
    return _nfl_sb_upsert("mpa_track_ledger", [{
        "app": _NFL_LINE_MOVEMENT_APP,
        "date": date_str,
        "category": _NFL_LINE_OPEN_CATEGORY,
        "side": "ALL",
        "wins": 0, "losses": 0, "locked": True,
        "detail": {
            "captured_at": datetime.now(timezone.utc).isoformat(),
            "source": {
                2: "wednesday_for_thursday",
                4: "friday_for_sunday",
                5: "saturday_for_monday",
            }[capture_day.weekday()],
            "lines": lines,
        },
    }], on_conflict="app,date,category,side")


def _nfl_attach_line_movement(date_str: str, result: dict) -> dict:
    """Annotate current plays from the durable weekly opening snapshot."""
    opening = _nfl_opening_lines(date_str)
    if not opening:
        return result
    for collection in ("all", "picks", "td_picks", "coach_candidates"):
        for row in result.get(collection) or []:
            if row.get("isAlternate") or row.get("alternate"):
                continue
            saved = opening.get(_nfl_line_identity(row))
            if not saved or saved.get("line") is None or row.get("realLine") is None:
                continue
            try:
                move = round(float(row["realLine"]) - float(saved["line"]), 2)
            except (TypeError, ValueError):
                continue
            side = str(row.get("pick") or "OVER").upper()
            row["openingLine"] = saved.get("line")
            row["currentLine"] = row.get("realLine")
            row["lineMove"] = move
            row["openingOdds"] = (
                saved.get("under_odds") if side == "UNDER"
                else saved.get("over_odds"))
            row["openingBook"] = (
                saved.get("under_book") if side == "UNDER"
                else saved.get("over_book"))
            row["lineOpenCapturedAt"] = saved.get("captured_at")
            row["lineMovementAvailable"] = True
    result["line_movement_dates"] = [date_str]
    return result

# ── Pick snapshot ─────────────────────────────────────────────────────────────
_NFL_TRK_APP   = "nfl"
_NFL_PICKS_CAT = "__official_picks__"
_NFL_BOARD_CAT_PREFIX = "__saved_board__:"
_NFL_GP_CAT    = "__official_gp__"
_NFL_LEDGER_CAT = "__official_ledger__"
_NFL_DETAIL_CAT = "__official_detail__"
_NFL_OVERFLOW_CAT = "__official_overflow__"
_NFL_HIST_CAT = "__historical_replay__"
_NFL_TRK_STAKE = 20.0
_NFL_TRK_TOP   = 10   # picks per market+direction that count in main record
_NFL_MOVEMENT_CATEGORIES = frozenset((
    "Biggest Over Line Movement", "Biggest Under Line Movement"))
_NFL_COACH_TRK_APP = "nfl_coach_track"
_NFL_COACH_HIST_APP = "nfl_coach_historical"
_NFL_COACH_CATS = ("app_hit_rate_100", "safest_bets", "coach_edge", "alt_line_edge",
                   "coach_over_movement", "coach_under_movement", "passing",
                   "rushing", "receiving", "defense", "kicking",
                   "td_scorers", "best_unders", "rookie_plays")
_NFL_COACH_CAPTURE_GUARD_SECONDS = 120
_NFL_OBSERVATION_ONLY_TRACK_MARKETS = frozenset((
    "player_anytime_td",
))

def _nfl_td_observation_only(row) -> bool:
    """Identify TD recommendations that display in records without affecting totals."""
    if not isinstance(row, dict):
        return False
    market = str(
        row.get("market") or row.get("source_market")
        or row.get("sourceMarket") or "").strip().lower()
    if market in _NFL_OBSERVATION_ONLY_TRACK_MARKETS:
        return True
    label = str(
        row.get("market_label") or row.get("mkt")
        or row.get("label") or row.get("category") or "").strip().lower()
    return (
        "anytime td" in label
        or "anytime touchdown" in label
        or label == "td scorers"
    )

# NEW namespaces are intentionally separate PostgREST app values and category
# keys.  No NEW read/write is allowed to silently fall through to the OLD
# ledger.
_NFL_NEW_TRK_APP = "nfl_new"
_NFL_NEW_PICKS_CAT = "__new_official_picks__"
_NFL_NEW_BOARD_CAT_PREFIX = "__new_saved_board__:"
_NFL_NEW_GP_CAT = "__new_official_gp__"
_NFL_NEW_LEDGER_CAT = "__new_official_ledger__"
_NFL_NEW_DETAIL_CAT = "__new_official_detail__"
_NFL_NEW_OVERFLOW_CAT = "__new_official_overflow__"
_NFL_NEW_HIST_CAT = "__new_historical_replay__"
_NFL_NEW_COACH_TRK_APP = "nfl_new_coach_track"
_NFL_NEW_COACH_HIST_APP = "nfl_new_coach_historical"
_NFL_NEW_HIST_BATCH_JOB_CAT = "__new_historical_batch_job__"

def _nfl_store_config(system="OLD"):
    if str(system or "OLD").upper() == "NEW":
        return {
            "app": _NFL_NEW_TRK_APP, "picks": _NFL_NEW_PICKS_CAT,
            "board": _NFL_NEW_BOARD_CAT_PREFIX, "gp": _NFL_NEW_GP_CAT,
            "ledger": _NFL_NEW_LEDGER_CAT, "detail": _NFL_NEW_DETAIL_CAT,
            "overflow": _NFL_NEW_OVERFLOW_CAT, "hist": _NFL_NEW_HIST_CAT,
            "coach": _NFL_NEW_COACH_TRK_APP, "coach_hist": _NFL_NEW_COACH_HIST_APP,
            "hist_batch": _NFL_NEW_HIST_BATCH_JOB_CAT,
        }
    return {
        "app": _NFL_TRK_APP, "picks": _NFL_PICKS_CAT,
        "board": _NFL_BOARD_CAT_PREFIX, "gp": _NFL_GP_CAT,
        "ledger": _NFL_LEDGER_CAT, "detail": _NFL_DETAIL_CAT,
        "overflow": _NFL_OVERFLOW_CAT, "hist": _NFL_HIST_CAT,
        "coach": _NFL_COACH_TRK_APP, "coach_hist": _NFL_COACH_HIST_APP,
        "hist_batch": _NFL_HIST_BATCH_JOB_CAT,
    }

def _nfl_coach_hist_implied(odds):
    try:
        odds = float(odds)
    except (TypeError, ValueError):
        return None
    if odds == 0:
        return None
    return (-odds / (-odds + 100) * 100) if odds < 0 else (100 / (odds + 100) * 100)

def _nfl_coach_hist_family(label):
    value = str(label or "").lower()
    if "rb total yds" in value:
        return "rush"
    if "pass" in value or "completion" in value or "int thrown" in value:
        return "pass"
    if "rush" in value:
        return "rush"
    if "rec" in value:
        return "rec"
    if "touchdown" in value or "anytime td" in value:
        return "td"
    if "tackle" in value or "sack" in value or "def int" in value:
        return "def"
    if "kick" in value or "fg made" in value:
        return "kick"
    return ""

def _nfl_coach_hist_candidates(picks):
    selected, seen = [], set()
    for pick in picks or []:
        if (pick.get("betQualified") is False
                or pick.get("roleRiskBlockPremium") is True):
            continue
        side = str(pick.get("pick") or "OVER").upper()
        odds = pick.get("realUnderOdds") if side == "UNDER" else pick.get("realOdds")
        implied = _nfl_coach_hist_implied(odds)
        line = pick.get("realLine", pick.get("dispLine"))
        probability = pick.get("dispScore", pick.get("score"))
        try:
            probability, line = float(probability), float(line)
        except (TypeError, ValueError):
            continue
        if implied is None or probability <= 0:
            continue
        row = {
            "player": pick.get("name", ""), "team": pick.get("team", ""),
            "opponent": pick.get("opponent", pick.get("opp", "")),
            "game": pick.get("game", ""),
            "game_start": pick.get("game_start", ""),
            "market": pick.get("market", ""),
            "market_label": pick.get("mkt", pick.get("label", "NFL Prop")),
            "side": side, "line": line, "odds": int(float(odds)),
            "book": pick.get("under_book", "") if side == "UNDER" else pick.get("over_book", ""),
            "model_probability": max(0.0, min(100.0, probability)),
            "implied_probability": implied,
            "projection": pick.get("projAvg", pick.get("avg")),
            "alternate": bool(pick.get("isAlternate")),
            "source_market": pick.get("sourceMarket", pick.get("source_market", pick.get("market", ""))),
            "opening_line": pick.get("openingLine"),
            "current_line": pick.get("currentLine", pick.get("realLine")),
            "line_move": pick.get("lineMove"),
            "line_movement_available": bool(pick.get("lineMovementAvailable")),
            "is_rookie": bool(pick.get("rookieVerified")
                              and pick.get("isRookie")),
            "rookie_verified": bool(pick.get("rookieVerified")),
            "weather": dict(pick.get("weather") or {}),
            "weather_applied": bool(pick.get("weatherApplied")),
            "weather_factor": pick.get("weatherFactor"),
            "weather_base_projection": pick.get("weatherBaseProjection"),
            "weather_adjustment": pick.get("weatherAdjustment"),
            "weather_severity": pick.get("weatherSeverity"),
            "weather_label": pick.get("weatherLabel", ""),
            "weather_summary": pick.get("weatherSummary", ""),
            "weather_status": pick.get("weatherStatus", "UNAVAILABLE"),
        }
        row["coach_edge"] = row["model_probability"] - implied
        key = (row["player"], row["market"], side, line, row["odds"])
        if key not in seen:
            seen.add(key)
            selected.append(row)
        if _nfl_coach_hist_family(row["market_label"]) == "td":
            continue
        other_side = "UNDER" if side == "OVER" else "OVER"
        other_odds = pick.get("realUnderOdds") if other_side == "UNDER" else pick.get("realOdds")
        other_implied = _nfl_coach_hist_implied(other_odds)
        if other_implied is None:
            continue
        opposite = dict(row)
        opposite.update({
            "side": other_side, "odds": int(float(other_odds)),
            "book": pick.get("under_book", "") if other_side == "UNDER" else pick.get("over_book", ""),
            "model_probability": max(0.0, min(100.0, 100.0 - probability)),
            "implied_probability": other_implied,
        })
        opposite["coach_edge"] = opposite["model_probability"] - other_implied
        key = (opposite["player"], opposite["market"], other_side, line, opposite["odds"])
        if key not in seen:
            seen.add(key)
            selected.append(opposite)
    return selected

def _nfl_coach_tracking_candidates(picks):
    """Build record candidates; TD rows remain visible as observations."""
    return [
        {**row, "observation_only": _nfl_td_observation_only(row)}
        for row in _nfl_coach_hist_candidates(picks)
    ]

def _nfl_coach_hist_select(candidates, category, alternate=False):
    if category == "app_hit_rate_100":
        rows = [
            dict(row) for row in candidates
            if not row.get("alternate") and
            abs(float(row.get("model_probability", -1)) - 100.0) < 0.05
        ]
        rows.sort(key=lambda x: (
            float(x.get("coach_edge") or 0),
            -float(x.get("implied_probability") or 0),
        ), reverse=True)
        unique, seen_players = [], set()
        for row in rows:
            player_key = _nfl_player_name_key(row.get("player"))
            if not player_key or player_key in seen_players:
                continue
            seen_players.add(player_key)
            unique.append(row)
        return unique
    family = {
        "passing": "pass", "rushing": "rush", "receiving": "rec",
        "defense": "def", "kicking": "kick", "td_scorers": "td",
    }.get(category)
    rows = []
    for row in candidates:
        if category == "rookie_plays" and not (
                row.get("rookie_verified") and row.get("is_rookie")):
            continue
        if category not in ("safest_bets", "td_scorers") and row["coach_edge"] <= 0:
            continue
        if family and _nfl_coach_hist_family(row["market_label"]) != family:
            continue
        if category == "best_unders" and row["side"] != "UNDER":
            continue
        if category in ("coach_over_movement", "coach_under_movement"):
            if row.get("alternate"):
                continue
            if not row.get("line_movement_available"):
                continue
            try:
                move = float(row.get("line_move"))
            except (TypeError, ValueError):
                continue
            if (category == "coach_over_movement"
                    and not (row["side"] == "OVER" and move > 0)):
                continue
            if (category == "coach_under_movement"
                    and not (row["side"] == "UNDER" and move < 0)):
                continue
        if alternate and (
            row["model_probability"] < 85 or
            row["implied_probability"] < 70 or
            row["odds"] < _NFL_ALT_MIN_ODDS
        ):
            continue
        rows.append(dict(row))
    if category == "safest_bets":
        rows.sort(key=lambda x: (x["implied_probability"], x["model_probability"]), reverse=True)
    elif category == "td_scorers":
        rows.sort(
            key=lambda x: (x["model_probability"], x["coach_edge"]),
            reverse=True)
    elif category in ("coach_over_movement", "coach_under_movement"):
        rows.sort(key=lambda x: abs(float(x.get("line_move") or 0)), reverse=True)
    else:
        rows.sort(key=lambda x: (x["coach_edge"], x["model_probability"]), reverse=True)
    unique, seen_players = [], set()
    for row in rows:
        player_key = str(row.get("player") or "").strip().lower()
        if not player_key or player_key in seen_players:
            continue
        seen_players.add(player_key)
        unique.append(row)
    limit = 10
    return unique[:limit]

def _nfl_coach_game_key(team, opponent):
    values = sorted([
        str(team or "").strip().upper(),
        str(opponent or "").strip().upper(),
    ])
    return "|".join(values) if all(values) else ""

def _nfl_coach_filter_candidates(candidates, filters):
    """Filter server-owned candidates before ranking, dedupe, and Top-10 cap."""
    if not isinstance(filters, dict):
        return list(candidates or [])
    sides = set(filters["sides"]) if isinstance(filters.get("sides"), list) else None
    markets = set(filters["markets"]) if isinstance(filters.get("markets"), list) else None
    games = set(filters["games"]) if isinstance(filters.get("games"), list) else None
    rookie_only = filters.get("rookie_only") is True
    out = []
    for row in candidates or []:
        if sides is not None and str(row.get("side") or "").upper() not in sides:
            continue
        label = str(row.get("market_label") or "").strip()
        if not label:
            label = PROP_LABELS.get(row.get("market"), "")
        if markets is not None and label not in markets:
            continue
        if games is not None and _nfl_coach_game_key(
                row.get("team"), row.get("opponent")) not in games:
            continue
        if rookie_only and not (
                row.get("rookie_verified") and row.get("is_rookie")):
            continue
        out.append(row)
    return out

async def _nfl_build_historical_coach(
        date_str, picks, games, df, roster_map, replay_box, target_teams,
        target_positions=None, system="OLD"):
    system = "NEW" if str(system).upper() == "NEW" else "OLD"
    target_positions = target_positions or {}
    def _build_standard():
        standard = _nfl_coach_tracking_candidates(picks)
        return {
            category: _nfl_coach_hist_select(standard, category)
            for category in _NFL_COACH_CATS if category != "alt_line_edge"
        }
    output = await asyncio.to_thread(_build_standard)
    sem = asyncio.Semaphore(_NFL_PROP_FETCH_CONCURRENCY)
    alt_cache = await asyncio.to_thread(_hist_alt_raw_cache_get, date_str)
    alt_cache_lock = asyncio.Lock()
    async def fetch_alt(game):
        event_id = game.get("id", "")
        if not event_id:
            raise RuntimeError(
                f"Historical alternate coverage has no event id for {game.get('game', 'game')}")
        cached_lines = alt_cache.get(event_id)
        # Presence of an empty list is a durable successful-empty sentinel:
        # this event genuinely published no alternate markets after retries.
        if event_id in alt_cache and isinstance(cached_lines, list):
            return game, cached_lines
        async with sem:
            lines = []
            successful_empty = False
            for attempt in range(3):
                lines = await get_prop_lines(
                    event_id, date_str, alternate_only=True)
                if lines:
                    break
                successful_empty = (
                    _NFL_PROP_FETCH_STATUS.get(
                        (str(event_id), str(date_str), True))
                    in ("success", "empty"))
                if attempt < 2:
                    await asyncio.sleep(1.5 * (attempt + 1))
            if not lines:
                print(
                    "[Historical Coach] No alternate markets were published "
                    f"for {game.get('game') or event_id} after retries; "
                    "keeping the game's standard Coach candidates only.")
                if not successful_empty:
                    raise RuntimeError(
                        "Historical alternate sportsbook fetch failed for "
                        f"{game.get('game') or event_id}; existing archive preserved.")
                if successful_empty:
                    async with alt_cache_lock:
                        alt_cache[event_id] = []
                        await asyncio.to_thread(
                            _hist_alt_raw_cache_set, date_str, alt_cache)
                return game, []
            async with alt_cache_lock:
                alt_cache[event_id] = lines
                await asyncio.to_thread(
                    _hist_alt_raw_cache_set, date_str, alt_cache)
            return game, lines
    batches = await asyncio.gather(*(fetch_alt(game) for game in games))
    def _analyze_historical_alts():
        # Alternate-history analysis is another pandas-heavy path.  Preserve
        # batch/order/category behavior while keeping it off the event loop.
        analyzed_rows = []
        with _NFL_ANALYSIS_LOCK:
            for game, lines in batches:
                home = game.get("home_abbr", "") or _name_to_abbr(game.get("home_team", ""))
                away = game.get("away_abbr", "") or _name_to_abbr(game.get("away_team", ""))
                for line in lines:
                    player_key = _norm(line.get("name", ""))
                    info = roster_map.get(player_key) if roster_map else None
                    if info and not info.get("eligible", True):
                        continue
                    line.update({
                        "home_team": game.get("home_team", ""), "away_team": game.get("away_team", ""),
                        "home_abbr": home, "away_abbr": away, "game": game.get("game", ""),
                        "game_start": game.get("start", ""), "target_season": game.get("season"),
                        "target_week": game.get("week"), "target_type": game.get("season_type", "REG"),
                        "roster_team": target_teams.get(
                            player_key, (info or {}).get("team", "")),
                        "roster_position": target_positions.get(
                            player_key, (info or {}).get("position", "")),
                    })
                    analyzer = _analyze_new_prop if system == "NEW" else _analyze_prop
                    analyzed = analyzer(line, df, home, away)
                    if analyzed:
                        analyzed_rows.append(analyzed)
        return analyzed_rows
    alt_results = await asyncio.to_thread(_analyze_historical_alts)
    alt_candidates = await asyncio.to_thread(
        _nfl_coach_tracking_candidates, alt_results)
    output["alt_line_edge"] = await asyncio.to_thread(
        _nfl_coach_hist_select, alt_candidates, "alt_line_edge", alternate=True)
    for category, rows in output.items():
        for row in rows:
            row.update({
                "captured_at": datetime.now(timezone.utc).isoformat(),
                "source": "historical_replay", "result": "PENDING",
                "actual": None, "units": None,
            })
        output[category] = _nfl_coach_grade_snapshot(
            date_str, rows, box=replay_box)
        if any(row.get("result") not in ("WIN", "LOSS", "PUSH", "VOID")
               for row in output[category]):
            raise RuntimeError(
                f"Historical Coach grading was incomplete for {category}")
    return output

def _nfl_save_historical_coach(date_str, grouped, system: str = "OLD"):
    cfg = _nfl_store_config(system)
    rows = []
    for category in _NFL_COACH_CATS:
        detail = grouped.get(category) or []
        rows.append({
            "app": cfg["coach_hist"], "date": date_str,
            "category": category, "side": "ALL",
            "wins": sum(row.get("result") == "WIN" for row in detail),
            "losses": sum(row.get("result") == "LOSS" for row in detail),
            "locked": True, "detail": detail,
        })
    return _nfl_sb_upsert(
        "mpa_track_ledger", rows, on_conflict="app,date,category,side")

def _nfl_coach_market_key(value):
    """Coach cards use display labels; settlement needs the canonical market key."""
    raw = str(value or "")
    if raw in PROP_TO_COL:
        return raw
    folded = raw.lower().replace("alternate", "").strip()
    for key, label in PROP_LABELS.items():
        if folded == label.lower():
            return key
    return ""

def _nfl_coach_kickoff(value):
    try:
        dt = datetime.fromisoformat(str(value).replace("Z", "+00:00"))
        return dt.replace(tzinfo=timezone.utc) if dt.tzinfo is None else dt.astimezone(timezone.utc)
    except (TypeError, ValueError):
        return None

def _nfl_coach_grade_snapshot(date_str, detail, box=None):
    """Settle Coach-only rows. Existing terminal values are immutable."""
    if box is None:
        box = _nfl_box_lookup(date_str)
        # Only VOID an absent player when the wrapper confirmed that every
        # event and summary fetch for the date completed successfully.
        complete = bool((_NFL_BOX_CACHE.get(date_str) or {}).get("final"))
    else:
        complete = bool(box) and all(bool(v.get("final")) for v in box.values())
    out = []
    for saved in detail or []:
        row = dict(saved or {})
        primary_terminal = row.get("result") in ("WIN", "LOSS", "PUSH", "VOID")
        stat = (box or {}).get(_nfl_player_name_key(row.get("player")))
        actual = stat.get(row.get("market")) if stat else None
        # A completed ESPN box where the frozen participant is absent is a
        # confirmed DNP/absent participant, not an artificial 0-stat loss.
        if primary_terminal:
            pass
        elif complete and not stat:
            row.update(result="VOID", actual=None, units=0.0,
                       settled_at=datetime.now(timezone.utc).isoformat())
        elif (stat and stat.get("final") and actual is None
              and row.get("market") in _NFL_BET_STAT_KEYS):
            # ESPN omits zero-value stat groups. If this player appears in any
            # final box-score group, a missing supported counting stat is zero.
            actual = 0.0
            try:
                line = float(row["line"])
                result = ("PUSH" if actual == line else
                          ("WIN" if actual > line else "LOSS")
                          if row.get("side") == "OVER"
                          else ("WIN" if actual < line else "LOSS"))
                row.update(
                    result=result, actual=actual,
                    units=round(_nfl_american_profit(
                        row.get("odds"), _NFL_TRK_STAKE, result
                    ) / _NFL_TRK_STAKE, 4),
                    settled_at=datetime.now(timezone.utc).isoformat())
            except (TypeError, ValueError, KeyError):
                row.setdefault("result", "PENDING")
        elif stat and stat.get("final") and actual is not None:
            try:
                line = float(row["line"])
                actual = float(actual)
                result = ("PUSH" if actual == line else
                          ("WIN" if actual > line else "LOSS") if row.get("side") == "OVER"
                          else ("WIN" if actual < line else "LOSS"))
                row.update(result=result, actual=actual,
                           units=round(_nfl_american_profit(row.get("odds"), _NFL_TRK_STAKE, result) / _NFL_TRK_STAKE, 4),
                           settled_at=datetime.now(timezone.utc).isoformat())
            except (TypeError, ValueError, KeyError):
                row.setdefault("result", "PENDING")
        else:
            row["result"] = "PENDING"
        row.pop("paired_alternate", None)
        row.pop("paired_alternates", None)
        out.append(row)
    return out

def _nfl_coach_summary(rows):
    totals = {"wins": 0, "losses": 0, "pushes": 0, "voids": 0, "pending": 0,
              "observations": 0, "units": 0.0, "staked": 0.0}
    for row in rows:
        if _nfl_td_observation_only(row):
            totals["observations"] += 1
            continue
        result = str(row.get("result") or "PENDING").upper()
        if result == "WIN": totals["wins"] += 1
        elif result == "LOSS": totals["losses"] += 1
        elif result == "PUSH": totals["pushes"] += 1
        elif result == "VOID": totals["voids"] += 1
        else: totals["pending"] += 1
        if result in ("WIN", "LOSS"):
            totals["staked"] += _NFL_TRK_STAKE
            totals["units"] += float(row.get("units") or 0)
    denom = totals["wins"] + totals["losses"]
    # Units are already profit divided by stake, so ROI is units per graded
    # wager—not units divided by dollar stake.
    totals["roi"] = round(totals["units"] / denom * 100, 1) if denom else None
    totals["rate"] = round(totals["wins"] / denom * 100, 1) if denom else None
    totals["units"] = round(totals["units"], 2)
    return totals


def _nfl_auto_capture_coach_categories(
        date_str: str, result: dict, system: str = "OLD") -> dict:
    """Bank every non-empty standard Coach preset from a complete pregame run."""
    if not _nfl_official_capture_allowed(date_str, result):
        return {}
    source = (
        result.get("coach_candidates") or result.get("all")
        or result.get("picks") or [])
    candidates = _nfl_coach_tracking_candidates(source)
    if not candidates:
        return {}
    cfg = _nfl_store_config(system)
    now = datetime.now(timezone.utc)
    statuses = {}
    for category in _NFL_COACH_CATS:
        # Alternate ladders finish asynchronously and retain their dedicated
        # capture path after that scan becomes complete and authoritative.
        if category == "alt_line_edge":
            continue
        selected = _nfl_coach_hist_select(candidates, category)
        if not selected:
            statuses[category] = "empty"
            continue
        frozen, kickoffs = [], []
        for raw in selected:
            kickoff = _nfl_coach_kickoff(raw.get("game_start"))
            if not kickoff or kickoff <= now:
                frozen = []
                break
            kickoffs.append(kickoff)
            frozen.append({
                **dict(raw),
                "captured_at": now.isoformat(),
                "result": "PENDING",
                "actual": None,
                "units": None,
            })
        if not frozen:
            statuses[category] = "invalid"
            continue
        deadline = min(kickoffs).isoformat()
        for row in frozen:
            row["snapshot_deadline"] = deadline
        statuses[category] = _nfl_sb_save_latest_unlocked(
            "mpa_track_ledger", {
                "app": cfg["coach"], "date": date_str,
                "category": category, "side": "ALL",
                "wins": 0, "losses": 0, "locked": False,
                "locked_at": deadline, "detail": frozen,
            }, now.isoformat())
    print("[nfl_coach_track] automatic preset capture "
          f"{date_str} {system}: {statuses}")
    return statuses

def _nfl_auto_capture_alt_coach(
        date_str: str, cached: dict, system: str = "OLD") -> str:
    """Bank a complete alternate Coach cache using its pre-kickoff timestamp.

    This is the asynchronous counterpart to standard preset capture. A stale
    cache remains valid evidence only when it was generated before every saved
    game's kickoff; final scores never participate in selection.
    """
    if (not isinstance(cached, dict) or cached.get("partial")
            or not cached.get("authoritative", True)):
        return "invalid"
    candidates = _nfl_coach_tracking_candidates(
        cached.get("picks") or cached.get("all") or [])
    selected = _nfl_coach_hist_select(
        candidates, "alt_line_edge", alternate=True)
    if not selected:
        return "empty"
    generated_raw = str(cached.get("generated_at") or "")
    try:
        generated_at = datetime.fromisoformat(
            generated_raw.replace("Z", "+00:00"))
        if generated_at.tzinfo is None:
            generated_at = generated_at.replace(tzinfo=timezone.utc)
        generated_at = generated_at.astimezone(timezone.utc)
    except (TypeError, ValueError):
        return "missing_timestamp"
    frozen, kickoffs = [], []
    for raw in selected:
        kickoff = _nfl_coach_kickoff(raw.get("game_start"))
        kickoff_date = (
            kickoff.astimezone(ZoneInfo("America/New_York")).strftime("%Y-%m-%d")
            if kickoff else "")
        if (not kickoff or kickoff_date != date_str
                or generated_at + timedelta(
                    seconds=_NFL_COACH_CAPTURE_GUARD_SECONDS) >= kickoff):
            return "not_pregame"
        kickoffs.append(kickoff)
        frozen.append({
            **dict(raw),
            "captured_at": generated_at.isoformat(),
            "result": "PENDING",
            "actual": None,
            "units": None,
        })
    deadline = min(kickoffs).isoformat()
    for row in frozen:
        row["snapshot_deadline"] = deadline
    cfg = _nfl_store_config(system)
    status = _nfl_sb_save_latest_unlocked(
        "mpa_track_ledger", {
            "app": cfg["coach"], "date": date_str,
            "category": "alt_line_edge", "side": "ALL",
            "wins": 0, "losses": 0, "locked": False,
            "locked_at": deadline, "detail": frozen,
        }, generated_at.isoformat())
    print("[nfl_coach_track] cached alternate preset capture "
          f"{date_str} {system}: {status} ({len(frozen)} plays)")
    return status

def _nfl_official_capture_allowed(date_str: str, result: dict) -> bool:
    """Official records require a slate captured before every kickoff.
    Historical/manual after-the-fact runs remain view-only simulations."""
    today = _nfl_today_date()
    try:
        slate_date = datetime.strptime(date_str, "%Y-%m-%d").date()
    except (TypeError, ValueError):
        return False
    if slate_date < today:
        return False
    # Never bank a partial player-prop board. Every scheduled game must have at
    # least one matched sportsbook prop before a run can replace the official
    # pre-kickoff snapshot.
    if result.get("prop_coverage_complete") is not True:
        return False
    now = datetime.now(timezone.utc)
    predictions = result.get("game_predictions") or []
    if not predictions:
        return False
    for prediction in predictions:
        start = prediction.get("game_start") or ""
        try:
            kickoff = datetime.fromisoformat(str(start).replace("Z", "+00:00"))
            if kickoff.tzinfo is None:
                kickoff = kickoff.replace(tzinfo=timezone.utc)
            else:
                kickoff = kickoff.astimezone(timezone.utc)
        except (TypeError, ValueError):
            return False
        if now >= kickoff:
            return False
    return True

def _nfl_save_historical_replay(date_str: str, replay: dict, system: str = "OLD"):
    """Persist replay analytics separately from official pregame records."""
    if not date_str or not isinstance(replay, dict):
        return False
    daily = replay.get("dates") or []
    overflow_daily = replay.get("overflow_dates") or []
    props = daily[0].get("detail") if daily else []
    overflow = overflow_daily[0].get("detail") if overflow_daily else []
    props = [
        {**row, "observation_only": _nfl_td_observation_only(row)}
        for row in (props or [])
    ]
    overflow = [
        {**row, "observation_only": _nfl_td_observation_only(row)}
        for row in (overflow or [])
    ]
    gp = replay.get("game_predictor") or {}
    if not props and not overflow and not gp.get("daily"):
        return False
    cfg = _nfl_store_config(system)
    ok = _nfl_sb_upsert("mpa_track_ledger", [{
        "app": cfg["app"], "date": date_str, "category": cfg["hist"],
        "side": "ALL", "wins": 0, "losses": 0, "locked": True,
        "detail": {
            "source": "historical_replay",
            "props": props if isinstance(props, list) else [],
            "overflow": overflow if isinstance(overflow, list) else [],
            "game_predictor": gp,
        },
    }], on_conflict="app,date,category,side")
    print(f"[nfl_track] historical replay {'saved' if ok else 'FAILED'}: {date_str}")
    return ok

_NFL_PICKS_SNAPSHOT_LOCK = _bt_th.Lock()
_NFL_BOARD_SNAPSHOT_LOCK = _bt_th.Lock()

def _nfl_snapshot_kickoff(value):
    try:
        kickoff = datetime.fromisoformat(str(value or "").replace("Z", "+00:00"))
        return (kickoff.replace(tzinfo=timezone.utc) if kickoff.tzinfo is None
                else kickoff.astimezone(timezone.utc))
    except (TypeError, ValueError):
        return None

def _nfl_save_board_snapshots(date_str: str, result: dict, system: str = "OLD"):
    """Save the latest completed board separately for every unstarted game."""
    cfg = _nfl_store_config(system)
    predictions = result.get("game_predictions") or []
    now = datetime.now(timezone.utc)
    rows = []
    for prediction in predictions:
        start = str(prediction.get("game_start") or "")
        game = str(prediction.get("game") or "")
        kickoff = _nfl_snapshot_kickoff(start)
        if not kickoff or now >= kickoff:
            continue
        def _same_game(item):
            return (
                str(item.get("game_start") or "") == start
                and (not game or str(item.get("game") or "") == game)
            )
        mini = {
            key: value for key, value in result.items()
            if key not in ("picks", "all", "td_picks", "game_predictions", "games")
        }
        mini.update({
            "date": date_str,
            "picks": [p for p in (result.get("picks") or []) if _same_game(p)],
            "all": [p for p in (result.get("all") or []) if _same_game(p)],
            "td_picks": [p for p in (result.get("td_picks") or []) if _same_game(p)],
            "game_predictions": [prediction],
            "games": [g for g in (result.get("games") or []) if _same_game(g)],
            "saved_board_captured_at": now.isoformat(),
        })
        identity = f"{start}-{game}"
        category = cfg["board"] + re.sub(
            r"[^0-9A-Za-z]+", "-", identity).strip("-")
        rows.append({
            "app": cfg["app"], "date": date_str, "category": category,
            "side": "ALL", "wins": 0, "losses": 0, "locked": False,
            "locked_at": kickoff.isoformat(), "detail": mini,
        })
    if not rows:
        return False
    with _NFL_BOARD_SNAPSHOT_LOCK:
        ok = _nfl_sb_upsert(
            "mpa_track_ledger", rows, on_conflict="app,date,category,side")
    print(f"[nfl_board] {'saved' if ok else 'FAILED'}: "
          f"{len(rows)} unstarted game snapshots -> {date_str}")
    return ok

def _nfl_load_board_snapshots(date_str: str, system: str = "OLD"):
    """Rebuild a day's board from durable per-game pre-kickoff snapshots."""
    cfg = _nfl_store_config(system)
    rows = _nfl_sb_get("mpa_track_ledger", {
        "app": f"eq.{cfg['app']}", "date": f"eq.{date_str}",
        "category": f"like.{cfg['board']}*",
        "side": "eq.ALL", "select": "detail", "limit": "64",
    })
    parts = [row.get("detail") for row in rows
             if isinstance(row.get("detail"), dict)]
    if not parts:
        # Boards captured before per-game persistence was deployed still exist
        # in the official pre-kickoff ledger. Recover that final run rather
        # than telling the user the day's picks are gone.
        official = _nfl_load_picks_snapshot(date_str, system)
        if not official:
            return None
        games = {}
        for pick in official:
            game = str(pick.get("game") or "")
            start = str(pick.get("game_start") or "")
            key = (game, start)
            if key not in games:
                games[key] = {
                    "game": game, "game_start": start,
                    "home_team": pick.get("home_team", ""),
                    "away_team": pick.get("away_team", ""),
                    "home_abbr": pick.get("home_abbr", ""),
                    "away_abbr": pick.get("away_abbr", ""),
                }
        return {
            "date": date_str, "picks": official, "all": official,
            "td_picks": [
                pick for pick in official
                if pick.get("market") == "player_anytime_td"
            ],
            "games": list(games.values()), "game_predictions": [],
            "qualified": len(official), "official_tracking": True,
            "durable_snapshot": True, "recovered_official_snapshot": True,
        }
    parts.sort(key=lambda p: min(
        [str(x.get("game_start") or "") for x in p.get("game_predictions", [])]
        or [""]))
    merged = {
        key: value for key, value in parts[-1].items()
        if key not in ("picks", "all", "td_picks", "game_predictions", "games")
    }
    for key in ("picks", "all", "td_picks", "game_predictions", "games"):
        merged[key] = [
            item for part in parts for item in (part.get(key) or [])
        ]
    merged["date"] = date_str
    merged["durable_snapshot"] = True
    return merged

def _nfl_save_picks_snapshot(date_str: str, result: dict, system: str = "OLD"):
    """Persist the latest complete pre-kickoff board for later grading.

    A complete later run replaces an earlier pre-kickoff run. Once any game in
    the saved slate has started, the snapshot is immutable."""
    cfg = _nfl_store_config(system)
    captured_at = datetime.now(timezone.utc)
    picks = [
        {**pick, "snapshot_captured_at": captured_at.isoformat(),
         "observation_only": _nfl_td_observation_only(pick)}
        for pick in (result.get("picks") or [])
    ]
    if not picks:
        return
    with _NFL_PICKS_SNAPSHOT_LOCK:
        existing = _nfl_sb_get("mpa_track_ledger", {
            "app": f"eq.{cfg['app']}", "category": f"eq.{cfg['picks']}",
            "side": "eq.ALL", "date": f"eq.{date_str}",
            "select": "detail,locked", "limit": "1",
        })
        if existing and existing[0].get("locked"):
            print(f"[nfl_track] snapshot kept: official record already locked -> {date_str}")
            return
        if existing:
            starts = [
                _nfl_coach_kickoff(pick.get("game_start"))
                for pick in (existing[0].get("detail") or [])
            ]
            known_starts = [start for start in starts if start]
            if known_starts and captured_at >= min(known_starts):
                print(f"[nfl_track] snapshot kept: saved slate already started -> {date_str}")
                return
        row = {
            "app": cfg["app"], "date": date_str,
            "category": cfg["picks"], "side": "ALL",
            "wins": 0, "losses": 0, "locked": False,
            "detail": picks,
        }
        ok = _nfl_sb_upsert(
            "mpa_track_ledger", [row], on_conflict="app,date,category,side")
        action = "updated" if existing else "saved"
        print(f"[nfl_track] snapshot {action if ok else 'FAILED'}: "
              f"{len(picks)} picks -> {date_str}")

def _nfl_load_picks_snapshot(date_str: str, system: str = "OLD") -> list:
    cfg = _nfl_store_config(system)
    rows = _nfl_sb_get("mpa_track_ledger", {
        "app": f"eq.{cfg['app']}", "category": f"eq.{cfg['picks']}",
        "side": "eq.ALL", "date": f"eq.{date_str}",
        "select": "detail", "limit": "1",
    })
    if rows:
        d = rows[0].get("detail") or []
        return d if isinstance(d, list) else []
    return []

def _nfl_list_snap_dates(system: str = "OLD") -> list:
    cfg = _nfl_store_config(system)
    rows = _nfl_sb_get("mpa_track_ledger", {
        "app": f"eq.{cfg['app']}", "category": f"eq.{cfg['picks']}",
        "side": "eq.ALL", "select": "date", "limit": "365",
    })
    board_rows = _nfl_sb_get("mpa_track_ledger", {
        "app": f"eq.{cfg['app']}", "category": f"like.{cfg['board']}*",
        "side": "eq.ALL", "select": "date", "limit": "365",
    })
    return sorted({
        r["date"] for r in list(rows or []) + list(board_rows or [])
        if r.get("date")
    })


def _nfl_restore_td_observations_from_board(
        date_str: str, snapshot: list, system: str = "OLD") -> list:
    """Repair display-only TD rows from durable pre-kickoff game boards."""
    restored = [dict(row) for row in (snapshot or [])]
    board = _nfl_load_board_snapshots(date_str, system) or {}
    candidates = (
        list(board.get("picks") or [])
        + list(board.get("td_picks") or [])
    )
    def identity(row):
        return (
            _nfl_player_name_key(row.get("name") or row.get("player")),
            str(row.get("market") or row.get("source_market") or ""),
            str(row.get("pick") or row.get("side") or "OVER").upper(),
            str(row.get("realLine", row.get("line", ""))),
            str(row.get("game_start") or ""),
        )
    seen = {identity(row) for row in restored}
    for row in candidates:
        if not _nfl_td_observation_only(row):
            continue
        key = identity(row)
        if key in seen:
            continue
        seen.add(key)
        restored.append({
            **dict(row),
            "observation_only": True,
            "recovered_from_pregame_board": True,
        })
    return restored

# ── Game Predictor snapshot and grading ───────────────────────────────────────
def _nfl_gp_is_pre_game(prediction: dict) -> bool:
    """Only freeze forecasts captured before their scheduled kickoff."""
    start = prediction.get("game_start") or ""
    try:
        kickoff = datetime.fromisoformat(str(start).replace("Z", "+00:00"))
        if kickoff.tzinfo is not None:
            kickoff = kickoff.astimezone(timezone.utc).replace(tzinfo=None)
        return datetime.utcnow() < kickoff
    except (TypeError, ValueError):
        # A missing kickoff cannot prove this was a pre-game call.
        return False

def _nfl_save_gp_snapshot(date_str: str, result: dict, system: str = "OLD"):
    """Freeze Game Predictor winner/total calls separately from player props."""
    cfg = _nfl_store_config(system)
    predictions = result.get("game_predictions") or []
    # Never freeze a partial date. If any game has started (or lacks a reliable
    # kickoff), wait rather than permanently saving only the remaining games.
    if not predictions or not all(_nfl_gp_is_pre_game(p) for p in predictions):
        print(f"[nfl_track] GP snapshot skipped: incomplete pre-game slate for {date_str}")
        return
    detail = []
    for p in predictions:
        detail.append({
            "home_abbr": p.get("home_abbr", ""), "away_abbr": p.get("away_abbr", ""),
            "pick_abbr": p.get("pick_abbr", ""),
            "pick_home": bool(p.get("pick_home")),
            "win_home": p.get("win_home"), "win_away": p.get("win_away"),
            "proj_home": p.get("proj_home"), "proj_away": p.get("proj_away"),
            "proj_total": p.get("proj_total"),
            "total_line": p.get("total_line"), "total_pick": p.get("total_pick"),
            "home_ml_odds": p.get("home_ml_odds"), "away_ml_odds": p.get("away_ml_odds"),
            "home_ml_book": p.get("home_ml_book", ""),
            "away_ml_book": p.get("away_ml_book", ""),
            "total_over_odds": p.get("total_over_odds"),
            "total_under_odds": p.get("total_under_odds"),
            "total_over_book": p.get("total_over_book", ""),
            "total_under_book": p.get("total_under_book", ""),
            "game_start": p.get("game_start", ""),
            "weather": dict(p.get("weather") or {}),
            "weather_applied": bool(p.get("weather_applied")),
            "weather_base_home": p.get("weather_base_home"),
            "weather_base_away": p.get("weather_base_away"),
            "weather_score_factor": p.get("weather_score_factor"),
            "weather_adjustment_home": p.get("weather_adjustment_home"),
            "weather_adjustment_away": p.get("weather_adjustment_away"),
            "weather_severity": p.get("weather_severity"),
            "weather_label": p.get("weather_label", ""),
            "weather_summary": p.get("weather_summary", ""),
            "weather_status": p.get("weather_status", "UNAVAILABLE"),
        })
    ok = _nfl_sb_insert_ignore("mpa_track_ledger", [{
        "app": cfg["app"], "date": date_str, "category": cfg["gp"],
        "side": "ALL", "wins": 0, "losses": 0, "locked": False,
        "detail": detail,
    }], "app,date,category,side")
    print(f"[nfl_track] GP snapshot {'saved' if ok else 'FAILED'}: "
          f"{len(detail)} games -> {date_str}")

def _nfl_load_gp_snapshots(system: str = "OLD") -> list:
    cfg = _nfl_store_config(system)
    return _nfl_sb_get("mpa_track_ledger", {
        "app": f"eq.{cfg['app']}", "category": f"eq.{cfg['gp']}",
        "side": "eq.ALL", "select": "date,detail,locked", "limit": "500",
    }) or []

def _nfl_gp_schedule_scores(date_str: str) -> dict:
    """Fetch final NFL scores for one date, keyed by ESPN matchup."""
    games = {}
    try:
        r = httpx.get(
            "https://site.api.espn.com/apis/site/v2/sports/football/nfl/scoreboard",
            params={"dates": date_str.replace("-", "")}, timeout=20)
        if not r.is_success:
            return games
        for event in r.json().get("events", []):
            comp = (event.get("competitions") or [{}])[0]
            rows = comp.get("competitors") or []
            by_side = {x.get("homeAway"): x for x in rows}
            home = (by_side.get("home") or {}).get("team") or {}
            away = (by_side.get("away") or {}).get("team") or {}
            ha, aa = home.get("abbreviation", ""), away.get("abbreviation", "")
            if not ha or not aa:
                continue
            status = event.get("status", {}).get("type", {}) or {}
            games[(ha, aa)] = {
                "home_score": (by_side.get("home") or {}).get("score"),
                "away_score": (by_side.get("away") or {}).get("score"),
                "completed": bool(status.get("completed")),
            }
    except Exception as exc:
        print(f"[nfl_track] GP score fetch failed {date_str}: {exc}")
    return games

def _nfl_grade_gp_date(date_str: str, snapshot: list) -> dict:
    """Grade winners and totals without mixing them into prop P/L."""
    score_map = _nfl_gp_schedule_scores(date_str)
    detail, all_found, all_final = [], True, True
    for saved in snapshot or []:
        row = dict(saved or {})
        row.update({
            "winner_result": None, "total_result": None,
            "actual_home": None, "actual_away": None, "actual_total": None,
        })
        game = score_map.get((row.get("home_abbr"), row.get("away_abbr")))
        if not game:
            all_found = all_final = False
            detail.append(row)
            continue
        if not game.get("completed"):
            all_final = False
            detail.append(row)
            continue
        try:
            hs, aws = float(game.get("home_score")), float(game.get("away_score"))
            row["actual_home"] = int(hs) if hs.is_integer() else hs
            row["actual_away"] = int(aws) if aws.is_integer() else aws
            row["actual_total"] = row["actual_home"] + row["actual_away"]
            picked = row.get("pick_abbr")
            winner = row.get("home_abbr") if hs > aws else (
                row.get("away_abbr") if aws > hs else "TIE")
            row["winner_result"] = (
                "PUSH" if winner == "TIE"
                else ("WIN" if picked == winner else "LOSS")
            )
            total_line = row.get("total_line")
            total_pick = row.get("total_pick")
            if total_line is not None and total_pick in ("OVER", "UNDER"):
                line = float(total_line)
                if row["actual_total"] == line:
                    row["total_result"] = "PUSH"
                elif total_pick == "OVER":
                    row["total_result"] = "WIN" if row["actual_total"] > line else "LOSS"
                else:
                    row["total_result"] = "WIN" if row["actual_total"] < line else "LOSS"
        except (TypeError, ValueError):
            all_final = False
        detail.append(row)
    return {
        "detail": detail, "any_game": bool(snapshot),
        "all_found": all_found, "all_final": all_final,
    }

def _nfl_gp_summary(detail: list) -> dict:
    def counts(key):
        return {v: sum(1 for r in detail if r.get(key) == v)
                for v in ("WIN", "LOSS", "PUSH")}
    w = counts("winner_result")
    t = counts("total_result")
    return {
        "winner_wins": w["WIN"], "winner_losses": w["LOSS"], "winner_pushes": w["PUSH"],
        "winner_rate": round(w["WIN"] / (w["WIN"] + w["LOSS"]) * 100, 1)
                      if w["WIN"] + w["LOSS"] else None,
        "total_wins": t["WIN"], "total_losses": t["LOSS"], "total_pushes": t["PUSH"],
        "total_rate": round(t["WIN"] / (t["WIN"] + t["LOSS"]) * 100, 1)
                    if t["WIN"] + t["LOSS"] else None,
    }

def _nfl_gp_record_payload() -> dict:
    daily = []
    for saved in _nfl_load_gp_snapshots():
        d = saved.get("date")
        detail = saved.get("detail") or []
        if not d:
            continue
        summary = _nfl_gp_summary(detail)
        daily.append({
            "date": d, "locked": bool(saved.get("locked")),
            "games": detail, **summary,
        })
    daily.sort(key=lambda x: x["date"], reverse=True)
    return {"daily": daily, "updated_at": datetime.utcnow().isoformat() + "Z"}

def _nfl_update_gp_ledger(include_date: str = "", system: str = "OLD"):
    """Grade unlocked official GP snapshots; historical replay never calls this."""
    today = _nfl_today()
    cfg = _nfl_store_config(system)
    for saved in _nfl_load_gp_snapshots(system):
        d = saved.get("date")
        if not d or d > today or (d == today and d != include_date) or saved.get("locked"):
            continue
        snapshot = saved.get("detail") or []
        if not isinstance(snapshot, list) or not snapshot:
            continue
        try:
            graded = _nfl_grade_gp_date(d, snapshot)
            if not graded.get("any_game"):
                continue
            summary = _nfl_gp_summary(graded["detail"])
            _nfl_sb_upsert("mpa_track_ledger", [{
                "app": cfg["app"], "date": d, "category": cfg["gp"],
                "side": "ALL",
                "wins": summary["winner_wins"], "losses": summary["winner_losses"],
                "locked": bool(graded.get("all_found") and graded.get("all_final")),
                "locked_at": (datetime.utcnow().isoformat() + "Z"
                              if graded.get("all_found") and graded.get("all_final")
                              else None),
                "detail": graded["detail"],
            }], on_conflict="app,date,category,side")
        except Exception as exc:
            print(f"[nfl_track] GP grade failed {d}: {exc}")

# ── Grading ───────────────────────────────────────────────────────────────────
def _nfl_grade_date(date_str: str, snap: list, box_override: dict = None) -> dict:
    """Grade every pick in snap against ESPN box scores.
    Groups by market+direction, ranks by score desc.
    Top _NFL_TRK_TOP per group -> main record; extras -> NFL Overflow."""
    from collections import defaultdict
    box = box_override if box_override is not None else _nfl_box_lookup(date_str)
    any_game = bool(box)
    all_final = any_game and all(v.get("final", False) for v in box.values())

    by_group: dict = defaultdict(list)
    for p in (snap or []):
        mk = p.get("market") or p.get("mkt") or ""
        if mk not in PROP_LABELS:
            continue
        direction = (p.get("pick") or "OVER").upper()
        by_group[(mk, direction)].append(p)
    for key in by_group:
        by_group[key].sort(key=lambda x: float(x.get("score") or 0), reverse=True)

    main_rows, ovf_rows, lock_best = [], [], {}
    for (mk, direction), ps in by_group.items():
        label = PROP_LABELS[mk]
        dir_word = "Over" if direction == "OVER" else "Under"
        cat = f"{label} ({dir_word})"
        for rank, p in enumerate(ps, 1):
            nk = (p.get("name") or "").lower().strip()
            st = (box or {}).get(nk, {})
            odds = p.get("over_odds") if direction == "OVER" else p.get("under_odds")
            line_raw = p.get("line") or p.get("realLine")
            result_val = actual = profit = None
            if st.get("final") and line_raw is not None:
                actual = st.get(mk)
                if actual is None and mk == "player_anytime_td":
                    actual = 0.0
                if actual is not None:
                    try:
                        fl = float(line_raw)
                        if actual == fl:
                            result_val = "PUSH"
                        elif direction == "OVER":
                            result_val = "WIN" if actual > fl else "LOSS"
                        else:
                            result_val = "WIN" if actual < fl else "LOSS"
                        if result_val and odds is not None:
                            profit = round(_nfl_american_profit(odds, _NFL_TRK_STAKE, result_val), 2)
                    except Exception:
                        pass
            row = {
                "name": p.get("name", ""), "team": p.get("team", ""),
                "category": cat, "side": direction, "market": mk,
                "line": line_raw, "odds": odds, "rank": rank,
                "result": result_val, "actual": actual, "profit": profit,
                "opening_line": p.get("openingLine"),
                "current_line": p.get("currentLine", p.get("realLine")),
                "line_move": p.get("lineMove"),
            }
            if p.get("system") == "NEW":
                row["system"] = "NEW"
                row["model_version"] = p.get("model_version", "NEW-v2-ewma-weather")
            if rank <= _NFL_TRK_TOP:
                main_rows.append(row)
            else:
                ovf_rows.append({**row, "pool": "NFL Overflow"})
            # Cross-market 80-100% Locks category
            lock_score = float(p.get("score") or p.get("dispScore") or 0)
            if lock_score >= 80:
                # Locks is a cross-market shortlist, not a duplicate copy of
                # every qualifying market. Keep one strongest option per player.
                lock_key = _norm(p.get("name") or "")
                lock_rank = (lock_score, abs(float(p.get("gap") or 0)), -rank)
                prior = lock_best.get(lock_key)
                if lock_key and (prior is None or lock_rank > prior[0]):
                    lock_best[lock_key] = (
                        lock_rank, {**row, "category": "80-100% Locks"})
    # Movement boards are official, isolated categories built from the same
    # already-qualified standard-line snapshot. They never use alternate lines.
    # Keep independent Top-10 lists for Over and Under; the two sections must
    # not compete for one combined 10-row cap.
    movement_by_side = {"OVER": {}, "UNDER": {}}
    for row in main_rows + ovf_rows:
        try:
            move = float(row.get("line_move"))
        except (TypeError, ValueError):
            continue
        if row.get("opening_line") is None or row.get("current_line") is None:
            continue
        side = str(row.get("side") or "").upper()
        if side == "OVER" and move > 0:
            category = "Biggest Over Line Movement"
        elif side == "UNDER" and move < 0:
            category = "Biggest Under Line Movement"
        else:
            continue
        key = (
            str(row.get("name") or "").strip().lower(),
            str(row.get("market") or "").strip().lower(),
            row.get("current_line"), side,
        )
        movement_by_side[side].setdefault(
            key, {**row, "category": category})
    movement = []
    for side in ("OVER", "UNDER"):
        rows = sorted(
            movement_by_side[side].values(),
            key=lambda x: abs(float(x.get("line_move") or 0)),
            reverse=True,
        )
        movement.extend(rows[:10])
    main_rows.extend(movement)

    lock_rows = [
        rec[1] for rec in sorted(
            lock_best.values(), key=lambda rec: rec[0], reverse=True)
    ]
    return {"any_game": any_game, "all_final": all_final,
            "main": main_rows, "overflow": ovf_rows, "locks": lock_rows}

def _nfl_aggregate_graded(graded: dict) -> dict:
    agg: dict = {}
    for row in graded.get("main", []) + graded.get("overflow", []) + graded.get("locks", []):
        if (_nfl_td_observation_only(row)
                or row.get("result") not in ("WIN", "LOSS")):
            continue
        cat  = row["category"]
        side = row.get("side", "OVER")
        rec  = agg.setdefault(cat, {}).setdefault(side, [0, 0])
        if row["result"] == "WIN":
            rec[0] += 1
        else:
            rec[1] += 1
    return agg

def _nfl_detail_graded(graded: dict, include_overflow: bool = True,
                       overflow_only: bool = False) -> list:
    out = []
    rows = []
    if not overflow_only:
        rows += graded.get("main", []) + graded.get("locks", [])
    if include_overflow or overflow_only:
        rows += graded.get("overflow", [])
    for row in rows:
        if row.get("result") not in ("WIN", "LOSS"):
            continue
        detail = {k: row.get(k) for k in (
            "name", "team", "category", "side", "market",
            "line", "odds", "rank", "result", "actual", "profit", "pool",
            "opening_line", "current_line", "line_move",
        )}
        detail["observation_only"] = _nfl_td_observation_only(row)
        out.append(detail)
    return out

def _nfl_box_from_stats_rows(rows) -> dict:
    """Normalize selected-week nfl-verse rows into the settlement box contract."""
    box = {}
    if rows is None:
        return box
    try:
        for _, row in rows.iterrows():
            raw_name = row.get("player_display_name", "")
            name = str(raw_name).lower().strip() if raw_name is not None else ""
            if not name or name == "nan":
                continue
            stats = box.setdefault(name, {"final": True})
            for market, col in PROP_TO_COL.items():
                val = row.get(col)
                try:
                    if val is None or val != val:
                        continue
                    num = float(val)
                except (TypeError, ValueError):
                    continue
                stats[market] = float(stats.get(market, 0)) + num
        return box
    except Exception as exc:
        print(f"[nfl_sim] nfl-verse grading box failed: {exc}")
        return {}

def _nfl_historical_replay_payload(result: dict, espn_games: list = None,
                                   replay_box: dict = None) -> dict:
    """Build a view-only Track Record payload for one completed historical date."""
    date_str = result.get("date") or ""
    graded = _nfl_grade_date(
        date_str, [
            {**pick, "observation_only": _nfl_td_observation_only(pick)}
            for pick in (result.get("picks") or [])
        ], box_override=replay_box)
    detail = _nfl_detail_graded(graded, include_overflow=False)
    overflow_detail = _nfl_detail_graded(graded, overflow_only=True)

    # Grade the display-only Game Predictor too, so a replay evaluates both
    # player props and the winner/total model without changing its live status.
    game_map = {
        (g.get("home_abbr"), g.get("away_abbr")): g
        for g in (espn_games or [])
    }
    gp_rows = []
    gp_daily_games = []
    for gp in result.get("game_predictions") or []:
        game = game_map.get((gp.get("home_abbr"), gp.get("away_abbr"))) or {}
        if not game.get("completed"):
            continue
        try:
            hs = float(game.get("home_score"))
            aws = float(game.get("away_score"))
        except (TypeError, ValueError):
            continue
        pick_home = bool(gp.get("pick_home"))
        picked = gp.get("home_abbr") if pick_home else gp.get("away_abbr")
        winner = gp.get("home_abbr") if hs > aws else (
            gp.get("away_abbr") if aws > hs else "TIE")
        win_result = "PUSH" if winner == "TIE" else ("WIN" if picked == winner else "LOSS")
        ml_odds = gp.get("home_ml_odds") if pick_home else gp.get("away_ml_odds")
        ml_book = gp.get("home_ml_book") if pick_home else gp.get("away_ml_book")
        total_result = None
        actual_total = hs + aws
        total_odds = None
        gp_rows.append({
            "name": f"{gp.get('away_abbr','')} @ {gp.get('home_abbr','')}",
            "team": picked, "category": "Game Predictor (Winner)",
            "side": "WIN", "market": "gp_winner", "line": None,
            "odds": ml_odds, "book": ml_book or "",
            "rank": len(gp_rows) + 1,
            "result": win_result, "actual": winner,
            "profit": round(_nfl_american_profit(
                ml_odds, _NFL_TRK_STAKE, win_result), 2
            ) if ml_odds is not None else None,
        })
        total_line = gp.get("total_line")
        total_side = gp.get("total_pick")
        if total_line is not None and total_side in ("OVER", "UNDER"):
            if actual_total == float(total_line):
                total_result = "PUSH"
            elif total_side == "OVER":
                total_result = "WIN" if actual_total > float(total_line) else "LOSS"
            else:
                total_result = "WIN" if actual_total < float(total_line) else "LOSS"
            total_odds = (
                gp.get("total_over_odds") if total_side == "OVER"
                else gp.get("total_under_odds")
            )
            total_book = (
                gp.get("total_over_book") if total_side == "OVER"
                else gp.get("total_under_book")
            )
            gp_rows.append({
                "name": f"{gp.get('away_abbr','')} @ {gp.get('home_abbr','')}",
                "team": "", "category": "Game Predictor (Total)",
                "side": total_side, "market": "gp_total",
                "line": total_line, "odds": total_odds,
                "book": total_book or "",
                "rank": len(gp_rows) + 1, "result": total_result,
                "actual": actual_total,
                "profit": round(_nfl_american_profit(
                    total_odds, _NFL_TRK_STAKE, total_result), 2
                ) if total_odds is not None else None,
            })
        gp_daily_games.append({
            "home_abbr": gp.get("home_abbr", ""), "away_abbr": gp.get("away_abbr", ""),
            "pick_abbr": picked, "pick_home": pick_home,
            "win_home": gp.get("win_home"), "win_away": gp.get("win_away"),
            "proj_home": gp.get("proj_home"), "proj_away": gp.get("proj_away"),
            "proj_total": gp.get("proj_total"), "total_line": total_line,
            "total_pick": total_side, "home_ml_odds": gp.get("home_ml_odds"),
            "away_ml_odds": gp.get("away_ml_odds"),
            "home_ml_book": gp.get("home_ml_book", ""),
            "away_ml_book": gp.get("away_ml_book", ""),
            "total_over_odds": gp.get("total_over_odds"),
            "total_under_odds": gp.get("total_under_odds"),
            "total_over_book": gp.get("total_over_book", ""),
            "total_under_book": gp.get("total_under_book", ""),
            "game_start": gp.get("game_start", ""),
            "actual_home": int(hs) if hs.is_integer() else hs,
            "actual_away": int(aws) if aws.is_integer() else aws,
            "actual_total": actual_total,
            "winner_result": win_result, "total_result": total_result,
        })
    # Winner/total results have their own Game Predictor record and must not
    # inflate the player-prop Track Record totals.
    gp_summary = _nfl_gp_summary(gp_daily_games)
    return {
        "dates": [{"date": date_str, "detail": detail}],
        "overflow_dates": [{"date": date_str, "detail": overflow_detail}],
        "stake": _NFL_TRK_STAKE,
        "historical": True,
        "game_predictor": {
            "daily": [{
                "date": date_str, "locked": True,
                "games": gp_daily_games, **gp_summary,
            }],
            "historical": True,
        },
        "notice": (
            "Historical Replay — reconstructed point-in-time results for review "
            "only; excluded from the official NFL Track Record."
        ),
    }

# ── Track ledger update ───────────────────────────────────────────────────────
_NFL_TRK_LOCK = _bt_th.Lock()

def _nfl_update_track_ledger(include_date: str = "", system: str = "OLD"):
    """Grade all saved pick snapshots for past dates not yet locked.
    Safe to call repeatedly — locked dates are skipped."""
    from datetime import date as _d
    today = _nfl_today()
    with _NFL_TRK_LOCK:
        cfg = _nfl_store_config(system)
        locked_rows = _nfl_sb_get("mpa_track_ledger", {
            "app": f"eq.{cfg['app']}", "category": f"eq.{cfg['ledger']}",
            "locked": "eq.true", "select": "date", "limit": "500",
        })
        locked = {r["date"] for r in (locked_rows or [])}
        upserts = []
        for d in _nfl_list_snap_dates(system):
            if d > today or (d == today and d != include_date) or d in locked:
                continue
            snap = _nfl_load_picks_snapshot(d, system)
            snap = _nfl_restore_td_observations_from_board(d, snap, system)
            if not snap:
                continue
            try:
                graded = _nfl_grade_date(d, snap)
            except Exception as e:
                print(f"[nfl_track] grade failed {d}: {e}")
                continue
            if not graded.get("any_game"):
                continue
            try:
                from datetime import date as _dd
                old_enough = (_dd.today() - _dd.fromisoformat(d)).days >= 2
            except Exception:
                old_enough = False
            if not graded.get("all_final") and not old_enough:
                continue   # wait for all scores to be final
            agg = _nfl_aggregate_graded(graded)
            det = _nfl_detail_graded(graded, include_overflow=False)
            overflow_det = _nfl_detail_graded(graded, overflow_only=True)
            upserts += [
                {"app": cfg["app"], "date": d, "category": cfg["ledger"], "side": "ALL",
                 "wins": 0, "losses": 0, "locked": True, "detail": agg},
                {"app": cfg["app"], "date": d, "category": cfg["detail"], "side": "ALL",
                 "wins": 0, "losses": 0, "locked": True, "detail": det},
                {"app": cfg["app"], "date": d, "category": cfg["overflow"], "side": "ALL",
                 "wins": 0, "losses": 0, "locked": True, "detail": overflow_det},
            ]
        if upserts:
            for i in range(0, len(upserts), 10):
                _nfl_sb_upsert("mpa_track_ledger", upserts[i:i+10], "app,date,category,side")
            print(f"[nfl_track] saved {len(upserts)//3} official dates into main and overflow records")
    try:
        _nfl_update_gp_ledger(include_date, system)
    except Exception as e:
        print(f"[nfl_track] GP background error: {e}")

def _nfl_trk_bg():
    try:
        _nfl_update_track_ledger()
    except Exception as e:
        print(f"[nfl_track] bg update error: {e}")

_bt_th.Thread(target=_nfl_trk_bg, daemon=True).start()


def _nfl_summarize_bets(bets: list) -> dict:
    cats: dict = {}
    tot_staked = tot_profit = 0.0
    w = l = pu = pend = 0
    for b in bets:
        res = b.get("result", "pending")
        try:
            stake = float(b.get("stake") or 0)
        except Exception:
            stake = 0.0
        c = cats.setdefault(b.get("category", "?"),
                            {"wins": 0, "losses": 0, "push": 0, "pending": 0,
                             "staked": 0.0, "profit": 0.0})
        if res == "WIN": w += 1; c["wins"] += 1
        elif res == "LOSS": l += 1; c["losses"] += 1
        elif res == "PUSH": pu += 1; c["push"] += 1
        else: pend += 1; c["pending"] += 1
        if res in ("WIN", "LOSS", "PUSH"):
            prof = float(b.get("profit") or 0)
            tot_staked += stake; c["staked"] += stake
            tot_profit += prof; c["profit"] += prof
    roi = (tot_profit / tot_staked * 100.0) if tot_staked > 0 else None
    ordered = _NFL_CAT_ORDER + [k for k in cats if k not in _NFL_CAT_ORDER]
    by_cat = []
    for cat in ordered:
        c = cats.get(cat)
        if not c:
            continue
        st = c["staked"]; pr = c["profit"]
        by_cat.append({"category": cat, "wins": c["wins"], "losses": c["losses"],
            "push": c["push"], "pending": c["pending"],
            "staked": round(st, 2), "profit": round(pr, 2),
            "roi": round(pr / st * 100, 1) if st > 0 else None})
    return {"wins": w, "losses": l, "push": pu, "pending": pend,
        "staked": round(tot_staked, 2), "profit": round(tot_profit, 2),
        "returned": round(tot_staked + tot_profit, 2),
        "roi": round(roi, 1) if roi is not None else None,
        "by_category": by_cat}


@app.get("/api/bets")
async def nfl_get_bets(request: Request, token: str = "", admin: str = "", settle: bool = True):
    tok = token or request.headers.get("Authorization", "").replace("Bearer ", "").strip()
    if not _nfl_bet_admin_ok(tok, admin):
        raise HTTPException(status_code=403, detail="Admin only")
    key = _nfl_bet_user_key(tok, admin)
    try:
        with _NFL_BET_LOCK:
            snapshot = _nfl_load_bets(key)
    except RuntimeError as exc:
        raise HTTPException(status_code=503, detail=str(exc))
    # Settle OFF-lock (see NBA): ESPN calls (now cached) must not hold _NFL_BET_LOCK.
    # Merge settled fields by id so a concurrently-added bet is never clobbered.
    if settle and _nfl_settle_batch(snapshot):
        # Apply ONLY bets settled to a terminal result this pass, and only onto a
        # still-pending on-disk bet — never write pending/None back and never flip an
        # already-terminal value (so a concurrent settle pass can't be clobbered).
        settled = {b.get("id"): b for b in snapshot
                   if b.get("id") and b.get("result") in ("WIN", "LOSS", "PUSH")}
        if settled:
            try:
                with _NFL_BET_LOCK:
                    current = _nfl_load_bets(key)
                    for b in current:
                        s = settled.get(b.get("id"))
                        if s and b.get("result") not in ("WIN", "LOSS", "PUSH"):
                            for f in ("result", "actual", "profit", "settled_at"):
                                b[f] = s.get(f)
                    _nfl_save_bets(key, current)
            except RuntimeError as exc:
                raise HTTPException(status_code=503, detail=str(exc))
    snapshot.sort(key=lambda b: (b.get("date", ""), b.get("placed_at", "")), reverse=True)
    return {"bets": snapshot, "summary": _nfl_summarize_bets(snapshot)}


@app.post("/api/bets")
async def nfl_add_bet(request: Request, token: str = "", admin: str = ""):
    tok = token or request.headers.get("Authorization", "").replace("Bearer ", "").strip()
    if not _nfl_bet_admin_ok(tok, admin):
        raise HTTPException(status_code=403, detail="Admin only")
    body = await request.json()
    try:
        stake = round(float(body.get("stake")), 2)
        odds = int(round(float(body.get("odds"))))
        line = float(body.get("line"))
    except Exception:
        raise HTTPException(status_code=400, detail="stake, odds and line must be numbers")
    if stake <= 0:
        raise HTTPException(status_code=400, detail="Bet size must be greater than 0")
    name = (body.get("name") or "").strip()
    market = (body.get("market") or "").strip()
    side = (body.get("side") or "OVER").strip().upper()
    if not name or market not in _NFL_BET_STAT_KEYS or side not in ("OVER", "UNDER"):
        raise HTTPException(status_code=400, detail="Invalid bet")
    bdate = (body.get("date") or _nfl_today()).strip()
    bet = {"id": _bt_uuid.uuid4().hex[:12], "date": bdate,
           "name": name, "pid": str(body.get("pid") or ""),
           "team": (body.get("team") or "").strip(),
           "opp": (body.get("opp") or "").strip(),
           "category": (body.get("category") or _NFL_STAT_LABEL.get(market, "?")).strip(),
           "side": side, "market": market,
           "stat_label": (body.get("stat_label") or _NFL_STAT_LABEL.get(market, "")).strip(),
           "line": line, "odds": odds, "stake": stake,
           "placed_at": (body.get("placed_at") or _nfl_today()),
           "result": "pending", "actual": None, "profit": None, "settled_at": None}
    try:
        _nfl_settle_bet(bet)
    except Exception:
        pass
    key = _nfl_bet_user_key(tok, admin)
    try:
        with _NFL_BET_LOCK:
            bets = _nfl_load_bets(key)
            bets.append(bet)
            _nfl_save_bets(key, bets)
    except RuntimeError as exc:
        raise HTTPException(status_code=503, detail=str(exc))
    return {"ok": True, "bet": bet}


@app.delete("/api/bets/{bet_id}")
async def nfl_delete_bet(bet_id: str, request: Request, token: str = "", admin: str = ""):
    tok = token or request.headers.get("Authorization", "").replace("Bearer ", "").strip()
    if not _nfl_bet_admin_ok(tok, admin):
        raise HTTPException(status_code=403, detail="Admin only")
    key = _nfl_bet_user_key(tok, admin)
    try:
        with _NFL_BET_LOCK:
            bets = _nfl_load_bets(key)
            new_bets = [b for b in bets if b.get("id") != bet_id]
            if len(new_bets) != len(bets):
                _nfl_save_bets(key, new_bets)
    except RuntimeError as exc:
        raise HTTPException(status_code=503, detail=str(exc))
    return {"ok": True}


@app.get("/api/bets/summary")
async def nfl_bets_summary(request: Request, token: str = "", admin: str = "", settle: bool = True):
    tok = token or request.headers.get("Authorization", "").replace("Bearer ", "").strip()
    if not _nfl_bet_admin_ok(tok, admin):
        raise HTTPException(status_code=403, detail="Admin only")
    key = _nfl_bet_user_key(tok, admin)
    try:
        with _NFL_BET_LOCK:
            bets = _nfl_load_bets(key)
            if settle and _nfl_settle_batch(bets):
                _nfl_save_bets(key, bets)
            snapshot = list(bets)
    except RuntimeError as exc:
        raise HTTPException(status_code=503, detail=str(exc))
    return {"sport": "NFL", "summary": _nfl_summarize_bets(snapshot)}


@app.get("/api/gp-record")
async def nfl_gp_record(grade: bool = False, date_str: str = "", system: str = "OLD"):
    """Standalone NFL Game Predictor winner and total record."""
    if grade:
        loop = asyncio.get_running_loop()
        await loop.run_in_executor(None, _nfl_update_gp_ledger, date_str, system)
    else:
        _bt_th.Thread(target=_nfl_update_gp_ledger, args=(date_str, system), daemon=True).start()
    if str(system).upper() != "NEW":
        return JSONResponse(_nfl_gp_record_payload())
    cfg = _nfl_store_config(system)
    daily = []
    for saved in _nfl_load_gp_snapshots(system):
        d = saved.get("date")
        if d:
            daily.append({"date": d, "locked": bool(saved.get("locked")),
                          "games": saved.get("detail") or [],
                          **_nfl_gp_summary(saved.get("detail") or [])})
    daily.sort(key=lambda x: x["date"], reverse=True)
    return JSONResponse({"daily": daily, "updated_at": datetime.utcnow().isoformat() + "Z",
                         "system": "NEW" if str(system).upper() == "NEW" else "OLD"})


@app.get("/api/track-record")
async def nfl_track_record(grade: bool = False, date_str: str = "", system: str = "OLD"):
    """NFL Track Record — all graded picks by date with W/L, ROI at $20/play."""
    if grade:
        loop = asyncio.get_running_loop()
        await loop.run_in_executor(None, _nfl_update_track_ledger, date_str, system)
    else:
        _bt_th.Thread(target=_nfl_update_track_ledger, args=("", system), daemon=True).start()
    cfg = _nfl_store_config(system)
    led_rows = _nfl_sb_get("mpa_track_ledger", {
        "app": f"eq.{cfg['app']}", "category": f"eq.{cfg['detail']}",
        "locked": "eq.true", "select": "date,detail", "limit": "365",
    })
    detail_by_date = {
        r["date"]: [
            {**row, "observation_only": _nfl_td_observation_only(row)}
            for row in (r.get("detail") or [])
        ]
        for r in (led_rows or [])
    }
    dates = sorted(detail_by_date.keys(), reverse=True)
    result = []
    for d in dates:
        det = detail_by_date[d]
        decided = [r for r in det if not _nfl_td_observation_only(r)
                   and r.get("result") in ("WIN","LOSS")
                   and r.get("category") not in _NFL_MOVEMENT_CATEGORIES]
        wins   = sum(1 for r in decided if r["result"] == "WIN")
        losses = len(decided) - wins
        priced = [r for r in decided if r.get("odds") is not None]
        net_pl = round(sum(r.get("profit") or 0 for r in priced), 2)
        staked = len(priced) * _NFL_TRK_STAKE
        roi    = round(net_pl / staked * 100, 1) if staked else None
        cats: dict = {}
        for r in [r for r in det if r.get("result") in ("WIN","LOSS")]:
            cat = r.get("category","?")
            e = cats.setdefault(cat, {"wins":0,"losses":0,"observations":0,
                                      "pl":0.0,"staked":0.0})
            if _nfl_td_observation_only(r):
                e["observations"] += 1
                continue
            if r["result"] == "WIN": e["wins"] += 1
            else: e["losses"] += 1
            if r.get("odds") is not None:
                e["pl"] = round(e["pl"] + (r.get("profit") or 0), 2)
                e["staked"] += _NFL_TRK_STAKE
        by_cat = []
        for cat, e in cats.items():
            total = e["wins"] + e["losses"]
            by_cat.append({
                "category": cat, "wins": e["wins"], "losses": e["losses"],
                "observations": e["observations"],
                "net_pl": e["pl"],
                "roi": round(e["pl"]/e["staked"]*100,1) if e["staked"] else None,
                "rate": round(e["wins"]/total*100,1) if total else None,
            })
        by_cat.sort(key=lambda x: (x.get("roi") or -999), reverse=True)
        result.append({
            "date": d, "wins": wins, "losses": losses,
            "net_pl": net_pl, "roi": roi,
            "by_cat": by_cat, "detail": det,
        })
    overflow_rows = _nfl_sb_get("mpa_track_ledger", {
        "app": f"eq.{cfg['app']}", "category": f"eq.{cfg['overflow']}",
        "locked": "eq.true", "select": "date,detail", "limit": "365",
    })
    overflow_dates = [
        {
            "date": r.get("date"),
            "detail": [
                {**row, "observation_only": _nfl_td_observation_only(row)}
                for row in (r.get("detail") or [])
            ],
        }
        for r in (overflow_rows or []) if r.get("date")
    ]
    overflow_dates.sort(key=lambda x: x["date"], reverse=True)

    historical_rows = _nfl_sb_get("mpa_track_ledger", {
        "app": f"eq.{cfg['app']}", "category": f"eq.{cfg['hist']}",
        "locked": "eq.true", "select": "date,detail", "limit": "730",
    })
    historical_dates, historical_overflow_dates, historical_gp_daily = [], [], []
    for saved in historical_rows or []:
        d = saved.get("date")
        payload = saved.get("detail") or {}
        if not d or not isinstance(payload, dict):
            continue
        historical_dates.append({
            "date": d,
            "detail": [
                {**row, "observation_only": _nfl_td_observation_only(row)}
                for row in (payload.get("props") or [])
            ],
        })
        historical_overflow_dates.append({
            "date": d,
            "detail": [
                {**row, "observation_only": _nfl_td_observation_only(row)}
                for row in (payload.get("overflow") or [])
            ],
        })
        gp = payload.get("game_predictor") or {}
        historical_gp_daily.extend(gp.get("daily") or [])
    historical_dates.sort(key=lambda x: x["date"], reverse=True)
    historical_overflow_dates.sort(key=lambda x: x["date"], reverse=True)
    gp_payload = _nfl_gp_record_payload()
    if str(system).upper() == "NEW":
        gp_payload = {"daily": [
            {"date": saved.get("date"), "locked": bool(saved.get("locked")),
             "games": saved.get("detail") or [],
             **_nfl_gp_summary(saved.get("detail") or [])}
            for saved in _nfl_load_gp_snapshots(system)
            if saved.get("date")
        ]}
    payload = {
        "dates": result, "stake": _NFL_TRK_STAKE,
        "game_predictor": gp_payload,
        "overflow_dates": overflow_dates,
        "historical_dates": historical_dates,
        "historical_overflow_dates": historical_overflow_dates,
        "historical_game_predictor": {"daily": historical_gp_daily},
    }
    if str(system).upper() == "NEW":
        payload["system"] = "NEW"
    return JSONResponse(payload)

# ── AI Coach Track Record (isolated namespace; never used by main/overflow) ───
def _nfl_coach_ledger_rows(app_name=_NFL_COACH_TRK_APP):
    return _nfl_sb_get("mpa_track_ledger", {"app": f"eq.{app_name}",
        "side": "eq.ALL", "select": "date,category,detail,locked", "limit": "1000"}) or []

def _nfl_coach_trusted_capture_source(date_str, raw, system: str = "OLD"):
    """Resolve the primary and side-specific pair from server-owned caches."""
    pools = []
    board = _new_cache_get(date_str) if str(system).upper() == "NEW" else _cache_get(date_str)
    if isinstance(board, dict):
        pools.extend(board.get("all") or board.get("picks") or [])
    alternates = _alt_coach_cache_get(
        date_str, system="NEW" if str(system).upper() == "NEW" else "OLD")
    if isinstance(alternates, dict):
        pools.extend(alternates.get("picks") or [])
    target_side = str(raw.get("side") or "").upper()
    target_market = _nfl_coach_market_key(raw.get("market"))
    try:
        target_line = float(raw.get("line"))
        target_odds = int(float(raw.get("odds")))
    except (TypeError, ValueError):
        return None
    for row in pools:
        row_side = str(row.get("pick") or row.get("side") or "").upper()
        row_market = _nfl_coach_market_key(
            row.get("market") or row.get("mkt") or row.get("label"))
        row_name = str(row.get("name") or row.get("player") or "")
        row_line = row.get("realLine", row.get("line"))
        row_odds = (
            row.get("realOdds") if target_side == "OVER"
            else row.get("realUnderOdds"))
        if row_odds is None:
            row_odds = row.get("odds")
        try:
            same_numbers = (
                abs(float(row_line) - target_line) < 1e-9
                and int(float(row_odds)) == target_odds)
        except (TypeError, ValueError):
            same_numbers = False
        if (
            _norm(row_name) == _norm(raw.get("player"))
            and str(row.get("game") or "") == str(raw.get("game") or "")
            and row_market == target_market
            and same_numbers
        ):
            return {"primary": dict(row)}
    return None

def _nfl_coach_capture_identity(row):
    try:
        return (
            _norm(str(row.get("player") or row.get("name") or "")),
            _nfl_coach_market_key(
                row.get("market") or row.get("market_label")),
            str(row.get("side") or row.get("pick") or "").upper(),
            round(float(row.get("line", row.get("realLine"))), 6),
            int(float(row.get("odds"))),
        )
    except (TypeError, ValueError):
        return None

def _nfl_coach_canonical_capture(date_str, category, filters=None, system: str = "OLD"):
    """Rebuild the complete current preset from server-owned cached picks."""
    if category == "alt_line_edge":
        source = _alt_coach_cache_get(
            date_str, system="NEW" if str(system).upper() == "NEW" else "OLD")
        if not isinstance(source, dict) or source.get("partial") or not source.get("authoritative", True):
            return []
        picks = ((source.get("picks") or source.get("all"))
                 if isinstance(source, dict) else [])
        candidates = _nfl_coach_filter_candidates(
            _nfl_coach_tracking_candidates(picks), filters)
        return _nfl_coach_hist_select(candidates, category, alternate=True)
    source = _new_cache_get(date_str) if str(system).upper() == "NEW" else _cache_get(date_str)
    picks = ((source.get("coach_candidates") or source.get("all")
              or source.get("picks") or [])
             if isinstance(source, dict) else [])
    candidates = _nfl_coach_filter_candidates(
        _nfl_coach_tracking_candidates(picks), filters)
    return _nfl_coach_hist_select(candidates, category)

def _nfl_grade_coach_ledger(system: str = "OLD"):
    cfg = _nfl_store_config(system)
    for saved in _nfl_coach_ledger_rows(cfg["coach"]):
        if saved.get("locked") or not isinstance(saved.get("detail"), list):
            continue
        try:
            current = saved
            for attempt in range(2):
                graded = _nfl_coach_grade_snapshot(
                    current["date"], current["detail"])
                terminal = bool(graded) and all(
                    r.get("result") in ("WIN","LOSS","PUSH","VOID")
                    for r in graded)
                # Pending rows remain untouched so grading cannot overwrite a
                # newer pre-kickoff capture with stale PENDING detail.
                if not terminal:
                    break
                counted = _nfl_coach_summary(graded)
                summary = {
                    "wins": counted["wins"],
                    "losses": counted["losses"],
                }
                if _nfl_sb_lock_coach_cas(current, graded, summary, cfg["coach"]):
                    break
                if attempt:
                    print("[nfl_coach_track] CAS retry lost for "
                          f"{current['date']} {current['category']}")
                    break
                latest = _nfl_sb_get("mpa_track_ledger", {
                    "app": f"eq.{cfg['coach']}",
                    "date": f"eq.{current['date']}",
                    "category": f"eq.{current['category']}",
                    "side": "eq.ALL",
                    "select": "date,category,detail,locked", "limit": "1",
                })
                if not latest or latest[0].get("locked"):
                    break
                current = latest[0]
        except Exception as exc: print(f"[nfl_coach_track] grade failed: {exc}")

@app.post("/api/nfl/coach-track/capture")
async def nfl_coach_track_capture(request: Request, token: str = ""):
    tok = token or request.headers.get("Authorization", "").replace("Bearer ", "").strip()
    if not _verify_hub_token(tok): raise HTTPException(401, "Subscription required — please log in via moneypicksarena.com")
    if not _SB_URL or not _SB_KEY: raise HTTPException(503, "AI Coach Track Record persistence is unavailable; nothing was saved.")
    body = await request.json()
    system = "NEW" if str(body.get("system") or "OLD").upper() == "NEW" else "OLD"
    cfg = _nfl_store_config(system)
    category = str(body.get("category") or "")
    date_str = str(body.get("date") or "")
    rows = body.get("rows")
    filters = body.get("filters")
    if filters is not None:
        if not isinstance(filters, dict):
            raise HTTPException(400, "Coach capture filters must be an object.")
        allowed_sides = {"OVER", "UNDER"}
        allowed_markets = set(PROP_LABELS.values())
        for key in ("sides", "markets", "games"):
            if not isinstance(filters.get(key), list):
                raise HTTPException(
                    400, f"Coach capture filters.{key} must be an array.")
        if not isinstance(filters.get("rookie_only", False), bool):
            raise HTTPException(
                400, "Coach capture filters.rookie_only must be true or false.")
        if (any(str(side).upper() not in allowed_sides
                for side in filters["sides"])
                or any(str(market) not in allowed_markets
                       for market in filters["markets"])
                or any(not isinstance(game, str) or "|" not in game
                       for game in filters["games"])):
            raise HTTPException(400, "Coach capture filters contain an invalid side, market, or game.")
        filters = {
            "sides": [str(side).upper() for side in filters["sides"]],
            # Display labels are intentionally exact and server-owned.
            "markets": list(filters["markets"]),
            "games": [_nfl_coach_game_key(
                *str(game).upper().split("|", 1)) for game in filters["games"]],
            "rookie_only": bool(filters.get("rookie_only")),
        }
    if category not in _NFL_COACH_CATS or not re.fullmatch(r"\d{4}-\d{2}-\d{2}", date_str) or not isinstance(rows, list) or not rows:
        raise HTTPException(400, "Invalid preset capture; no snapshot was saved.")
    canonical = _nfl_coach_canonical_capture(date_str, category, filters, system)
    canonical_ids = [_nfl_coach_capture_identity(row) for row in canonical]
    if not canonical_ids or any(item is None for item in canonical_ids):
        raise HTTPException(
            409,
            "Coach capture rejected: the server could not rebuild a complete "
            "current preset. Run Get Picks again.")
    # Always bank the complete, latest server-ranked preset.  The browser may
    # display the same valid rows in a different order or briefly hold an older
    # rendered array; neither should prevent official Coach tracking.
    rows = canonical
    existing = _nfl_sb_get("mpa_track_ledger", {"app":f"eq.{cfg['coach']}","date":f"eq.{date_str}","category":f"eq.{category}","side":"eq.ALL","select":"date,locked,locked_at,detail","limit":"1"})
    if existing and existing[0].get("locked"):
        return {"ok":True,"status":"locked",
                "message":"Results are locked; the final pregame snapshot cannot be changed."}
    now, frozen = datetime.now(timezone.utc), []
    if existing and any(
            (_nfl_coach_kickoff(row.get("game_start")) or now) <= now
            for row in (existing[0].get("detail") or [])):
        return {"ok":True,"status":"locked",
                "message":"This Coach category is frozen because one of its games has started."}
    for raw in rows:
        if not isinstance(raw, dict):
            raise HTTPException(400, "Coach capture rejected: invalid displayed row.")
        market = _nfl_coach_market_key(raw.get("market"))
        required = ("player","team","opponent","game","side","line","odds",
                    "model_probability","implied_probability","coach_edge")
        if not market or any(raw.get(k) in (None,"") for k in required) or str(raw["side"]).upper() not in ("OVER","UNDER"):
            raise HTTPException(400, "Coach capture rejected: each displayed row needs complete data.")
        try:
            trusted_source = _nfl_coach_trusted_capture_source(date_str, raw, system)
            if not isinstance(trusted_source, dict):
                raise ValueError(
                    "displayed recommendation is not present in server cache")
            trusted_primary = trusted_source["primary"]
            kickoff = _nfl_coach_kickoff(trusted_primary.get("game_start"))
            trusted_date = (
                kickoff.astimezone(ZoneInfo("America/New_York"))
                .strftime("%Y-%m-%d") if kickoff else "")
            if not kickoff or kickoff <= now or trusted_date != date_str:
                raise ValueError(
                    "server-cached recommendation is not pre-kickoff for this date")
            frozen.append({"player":str(raw["player"]),"team":str(raw["team"]),"opponent":str(raw["opponent"]),
                "game":str(raw["game"]),"game_start":kickoff.isoformat(),"market":market,"market_label":str(raw["market"]),"side":str(raw["side"]).upper(),
                "line":float(raw["line"]),"odds":int(float(raw["odds"])),
                "book":str(raw.get("book") or "OddsAPI"),
                "model_probability":float(raw["model_probability"]),"implied_probability":float(raw["implied_probability"]),
                "coach_edge":float(raw["coach_edge"]),
                "projection":(float(raw["projection"])
                              if raw.get("projection") not in (None, "") else None),
                "alternate":bool(raw.get("alternate")),
                "is_rookie":bool(trusted_primary.get("is_rookie")),
                "rookie_verified":bool(trusted_primary.get("rookie_verified")),
                "weather":dict(trusted_primary.get("weather") or {}),
                "weather_applied":bool(trusted_primary.get("weather_applied")),
                "weather_factor":trusted_primary.get("weather_factor"),
                "weather_base_projection":trusted_primary.get("weather_base_projection"),
                "weather_adjustment":trusted_primary.get("weather_adjustment"),
                "weather_severity":trusted_primary.get("weather_severity"),
                "weather_label":trusted_primary.get("weather_label", ""),
                "weather_summary":trusted_primary.get("weather_summary", ""),
                "weather_status":trusted_primary.get("weather_status", "UNAVAILABLE"),
                 "observation_only":_nfl_td_observation_only(raw),
                "captured_at":now.isoformat(),"result":"PENDING","actual":None,"units":None})
        except (TypeError, ValueError): raise HTTPException(400, "Coach capture rejected: invalid displayed play values.")
    # Recheck immediately before writing so a slow request cannot replace the
    # banked list after kickoff. Until then, each run replaces the prior run;
    # therefore the final run before kickoff is the official Coach snapshot.
    write_time = datetime.now(timezone.utc)
    kickoffs = [
        _nfl_coach_kickoff(row.get("game_start")) for row in frozen]
    safe_write_cutoff = write_time + timedelta(
        seconds=_NFL_COACH_CAPTURE_GUARD_SECONDS)
    if any(not kickoff or kickoff <= safe_write_cutoff for kickoff in kickoffs):
        raise HTTPException(
            400, "Coach capture rejected: kickoff is less than two minutes away "
                 "or passed before the snapshot was saved.")
    snapshot_deadline = min(kickoffs).isoformat()
    for row in frozen:
        row["snapshot_deadline"] = snapshot_deadline
    if existing and not existing[0].get("locked_at"):
        legacy_kickoffs = [
            _nfl_coach_kickoff(row.get("game_start"))
            for row in (existing[0].get("detail") or [])]
        legacy_deadline = min(
            (kickoff for kickoff in legacy_kickoffs if kickoff),
            default=min(kickoffs)).isoformat()
        _nfl_sb_backfill_coach_deadline(
            existing[0], legacy_deadline, cfg["coach"])
    save_state = _nfl_sb_save_latest_unlocked("mpa_track_ledger", {
        "app":cfg["coach"],"date":date_str,"category":category,
        "side":"ALL","wins":0,"losses":0,"locked":False,
        # While unlocked this is the database-filterable kickoff deadline.
        # Terminal grading replaces it with the actual lock timestamp.
        "locked_at":snapshot_deadline,"detail":frozen,
    }, now.isoformat())
    if save_state == "error":
        raise HTTPException(
            503, "AI Coach Track Record could not be persisted; nothing was saved.")
    if save_state == "refused":
        return {
            "ok":True, "status":"no_update",
            "message":(
                "No change: a newer pregame run is already banked or this "
                "category locked while the request was being saved."),
        }
    return {
        "ok":True, "status":save_state,
        "message":("Latest pregame Coach snapshot replaced the earlier run."
                   if save_state == "updated" else "Coach snapshot saved."),
    }

@app.get("/api/nfl/coach-track")
async def nfl_coach_track(request: Request, token: str = "", grade: bool = False,
                           source: str = "official", season: int = 0,
                           system: str = "OLD", date_str: str = ""):
    system = "NEW" if str(system).upper() == "NEW" else "OLD"
    tok = token or request.headers.get("Authorization", "").replace("Bearer ", "").strip()
    if not _verify_hub_token(tok):
        if system == "NEW":
            return JSONResponse({"detail":"Subscription required — please log in via moneypicksarena.com",
                                 "system":"NEW"}, status_code=401)
        raise HTTPException(401, "Subscription required — please log in via moneypicksarena.com")
    if not _SB_URL or not _SB_KEY:
        if system == "NEW":
            return JSONResponse({"detail":"AI Coach Track Record persistence is unavailable.",
                                 "system":"NEW"}, status_code=503)
        raise HTTPException(503, "AI Coach Track Record persistence is unavailable.")
    cfg = _nfl_store_config(system)
    historical = source == "historical"
    if grade and not historical:
        await asyncio.get_running_loop().run_in_executor(None, _nfl_grade_coach_ledger, system)
    grouped = {c:[] for c in _NFL_COACH_CATS}
    for saved in _nfl_coach_ledger_rows(
            cfg["coach_hist"] if historical else cfg["coach"]):
        if historical and season:
            start, end = f"{season}-08-01", f"{season + 1}-03-01"
            if not start <= str(saved.get("date") or "") < end:
                continue
        if saved.get("category") in grouped:
            for row in (saved.get("detail") or []):
                if not isinstance(row, dict):
                    continue
                clean = {
                    **row,
                    "date": saved.get("date"),
                    "category": saved.get("category"),
                    "observation_only": _nfl_td_observation_only(row),
                }
                clean.pop("paired_alternate", None)
                clean.pop("paired_alternates", None)
                grouped[saved["category"]].append(clean)
    if (not historical and re.fullmatch(r"\d{4}-\d{2}-\d{2}", date_str)
            and not any(row.get("date") == date_str
                        for row in grouped.get("td_scorers", []))):
        board = _nfl_load_board_snapshots(date_str, system) or {}
        source_rows = (
            list(board.get("all") or [])
            + list(board.get("picks") or [])
            + list(board.get("td_picks") or [])
        )
        recovered = _nfl_coach_hist_select(
            _nfl_coach_tracking_candidates(source_rows), "td_scorers")
        if recovered:
            recovered = (
                _nfl_coach_grade_snapshot(date_str, recovered)
                if grade else recovered
            )
            for row in recovered:
                clean = {
                    **row,
                    "date": date_str,
                    "category": "td_scorers",
                    "observation_only": True,
                    "recovered_from_pregame_board": True,
                }
                clean.pop("paired_alternate", None)
                clean.pop("paired_alternates", None)
                grouped["td_scorers"].append(clean)
    return {"stake":_NFL_TRK_STAKE,"source":"historical" if historical else "official",
            "season":season or None,
            "system":system,
            "categories":[{"category":c,"summary":_nfl_coach_summary(grouped[c]),"rows":grouped[c]} for c in _NFL_COACH_CATS]}

@app.post("/api/nfl/coach-track/grade")
async def nfl_coach_track_grade(request: Request, token: str = ""):
    tok = token or request.headers.get("Authorization", "").replace("Bearer ", "").strip()
    if not _verify_hub_token(tok): raise HTTPException(401, "Subscription required — please log in via moneypicksarena.com")
    if not _SB_URL or not _SB_KEY: raise HTTPException(503, "AI Coach Track Record persistence is unavailable.")
    body = await request.json() if request.headers.get("content-type","").startswith("application/json") else {}
    system = "NEW" if str(body.get("system") or "OLD").upper() == "NEW" else "OLD"
    await asyncio.get_running_loop().run_in_executor(None, _nfl_grade_coach_ledger, system)
    return {"ok": True}


@app.get("/", response_class=HTMLResponse)
async def index(admin: str = "", token: str = ""):
    today = datetime.now(ZoneInfo("America/New_York")).strftime("%Y-%m-%d")
    is_admin = (bool(admin) and admin == os.environ.get("INTERNAL_API_TOKEN", "__none__")) or _is_admin_token(token)
    js_flag = "true" if is_admin else "false"
    html = (
        HTML.replace("__TODAY__", today)
        .replace("__NFL_BASE_PATH__", json.dumps(os.environ.get("BASE_PATH", "").rstrip("/")))
        .replace("</head>", f"<script>window.IS_ADMIN = {js_flag};</script></head>", 1)
    )
    return HTMLResponse(html)

# ── HTML ───────────────────────────────────────────────────────────────────────
HTML = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>NFL Money Bombs &mdash; Money Picks Arena</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Playfair+Display:wght@400;700;900&family=Source+Sans+Pro:wght@300;400;600;700&display=swap" rel="stylesheet">
<style>
*{box-sizing:border-box;margin:0;padding:0}
html,body{max-width:100%;overflow-x:hidden}
img{max-width:100%;height:auto}
@media (max-width:1200px){table{display:block;width:100%;overflow-x:auto;-webkit-overflow-scrolling:touch;white-space:nowrap}}
@media (max-width:560px){table{font-size:12px}table th,table td{padding:6px 8px}}
body{background:#0f0f0f;color:#fff;font-family:'Source Sans Pro',sans-serif;min-height:100vh}
nav{position:fixed;top:0;width:100%;background:rgba(10,10,10,.95);backdrop-filter:blur(12px);border-bottom:1px solid #1c1c1c;z-index:100;padding:0 32px;height:80px;display:flex;align-items:center}
.logo{font-family:'Playfair Display',serif;font-size:36px;font-weight:900;color:#f59e0b;letter-spacing:.02em;line-height:1}
.logo span{color:#fff}
main{max-width:980px;margin:0 auto;padding:100px 20px 60px}
.hero{text-align:center;margin-bottom:32px}
.hero h1{font-family:'Playfair Display',serif;font-size:clamp(2rem,5vw,3rem);font-weight:900;margin-bottom:8px}
.hero h1 span{color:#f59e0b}
.hero p{color:#6b7280;font-size:14px;letter-spacing:.15em;text-transform:uppercase}
.card{background:#161616;border:1px solid #262626;border-radius:20px;padding:28px;margin-bottom:20px}
.run-card{text-align:center}
.run-card h2{font-family:'Playfair Display',serif;font-size:1.5rem;font-weight:700;color:#fff;margin-bottom:24px}
.date-row{display:flex;align-items:center;justify-content:center;gap:12px;margin-bottom:20px}
.date-row label{color:#9ca3af;font-weight:600;font-size:.85rem;letter-spacing:.15em;text-transform:uppercase}
.date-input{background:#0a0a0a;border:1px solid #2a2a2a;border-radius:10px;padding:11px 16px;color:#fff;font-size:14px;font-family:'Source Sans Pro',sans-serif;outline:none;transition:border .2s}
.date-input:focus{border-color:#f59e0b}
input[type=date]::-webkit-calendar-picker-indicator{filter:invert(1);opacity:.7;cursor:pointer}
.btn{background:#f59e0b;color:#000;font-weight:700;padding:12px 36px;border:none;border-radius:8px;font-size:15px;cursor:pointer;font-family:'Source Sans Pro',sans-serif;transition:all .2s}
.btn:hover{background:#fbbf24;transform:translateY(-1px);box-shadow:0 4px 20px rgba(245,158,11,.4)}
.btn:disabled{background:#2a2a2a;color:#4b5563;cursor:not-allowed;transform:none;box-shadow:none}
.status-msg{margin-top:14px;color:#6b7280;font-size:13px;min-height:20px}
.spinner{display:inline-block;width:13px;height:13px;border:2px solid rgba(245,158,11,.3);border-top-color:#f59e0b;border-radius:50%;animation:spin .7s linear infinite;margin-right:6px;vertical-align:middle}
@keyframes spin{to{transform:rotate(360deg)}}
footer{text-align:center;padding:32px 24px;color:#4b5563;font-size:.78rem;border-top:1px solid #1c1c1c;margin-top:24px;font-family:'Source Sans Pro',sans-serif}
.ft-logo{font-family:'Playfair Display',serif;color:#f59e0b;font-weight:700;font-size:.95rem;margin-bottom:6px}
.admin-only{display:none !important}
body.is-admin .admin-only{display:inline-block !important}
#parlayCard{display:none}
body.is-admin #parlayCard{display:block}
/* chips + sections + games */
.chips{display:grid;grid-template-columns:repeat(auto-fit,minmax(110px,1fr));gap:12px;margin-bottom:28px}
.chip{background:#161616;border:1px solid #262626;border-top:3px solid #f59e0b;border-radius:14px;padding:16px 10px;text-align:center}
.chip .val{font-size:1.8rem;font-weight:900;color:#f59e0b;font-family:'Playfair Display',serif}
.chip .lbl{font-size:.65rem;color:#6b7280;text-transform:uppercase;letter-spacing:.1em;margin-top:4px;font-weight:600}
.sec{display:flex;align-items:center;gap:12px;font-size:.94rem;font-weight:900;color:#fbbf24;text-transform:uppercase;letter-spacing:.13em;margin:30px 0 14px}
.sec::after{content:'';flex:1;height:3px;border-radius:999px;background:linear-gradient(90deg,#f59e0b,#fbbf24 72%,rgba(251,191,36,.2))}
.games{display:grid;grid-template-columns:repeat(auto-fill,minmax(170px,1fr));gap:10px;margin-bottom:24px}
.gcard{background:#161616;border:1px solid #262626;border-radius:14px;padding:14px;text-align:center;transition:border-color .2s}
.gcard:hover{border-color:#f59e0b}
.gcard .mu{font-size:1rem;font-weight:700;color:#fff}
.gcard .gt{font-size:.75rem;color:#6b7280;margin-top:5px}
/* shared text helpers */
.home{background:rgba(74,222,128,.08);color:#4ade80;padding:3px 8px;border-radius:4px;font-size:.74rem;font-weight:700;border:1px solid rgba(74,222,128,.2)}
.away{background:rgba(239,68,68,.08);color:#f87171;padding:3px 8px;border-radius:4px;font-size:.74rem;font-weight:700;border:1px solid rgba(239,68,68,.2)}
.gold{color:#f59e0b;font-weight:700}
.green{color:#4ade80;font-weight:700}
.red-txt{color:#f87171;font-weight:700}
.gray{color:#6b7280;font-size:.8rem}
.est{background:rgba(245,158,11,.08);color:#f59e0b;border:1px solid rgba(245,158,11,.2);padding:2px 8px;border-radius:4px;font-size:.78rem;font-weight:700}
.real-line{color:#4ade80;font-weight:800}
.odds-txt{color:#6b7280;font-size:.78rem}
.pname{font-weight:700;color:#fff}
.tbadge{background:#1f2937;color:#cbd5e1;padding:2px 7px;border-radius:5px;font-size:.72rem;font-weight:700}
.score{color:#f59e0b;font-weight:800}
.rk-num{color:#f59e0b;font-weight:900}
.rk-rest{color:#6b7280;font-weight:700}
.tag-sug{background:#065f46;color:#d1fae5;padding:2px 6px;border-radius:4px;font-size:.72rem;font-weight:700}
.tag-fade{background:#7f1d1d;color:#fecaca;padding:2px 6px;border-radius:4px;font-size:.72rem;font-weight:700}
.gap-pos{color:#10b981;font-weight:600}.gap-neg{color:#ef4444;font-weight:600}.gap-zero{color:#6b7280}
.err-box{background:rgba(239,68,68,.08);border:1px solid rgba(239,68,68,.2);border-radius:12px;padding:20px;text-align:center;color:#f87171;font-weight:700}
.no-picks{text-align:center;padding:50px;color:#4b5563}
.tbl-wrap{overflow-x:auto;border-radius:14px;border:1px solid #262626;margin-bottom:8px}
table{width:100%;border-collapse:collapse;font-size:.82rem;background:#161616}
thead tr{border-bottom:1px solid rgba(245,158,11,.2)}
th{padding:11px 12px;text-align:left;color:#f59e0b;font-size:.7rem;font-weight:700;text-transform:uppercase;letter-spacing:.1em;background:#1a1a1a;white-space:nowrap}
td{padding:9px 12px;border-bottom:1px solid #1c1c1c;white-space:nowrap}
tr:last-child td{border-bottom:none}
/* NBA-style trading cards */
.picks-grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(280px,1fr));gap:16px;margin-bottom:10px}
.pick-card{position:relative;background:linear-gradient(160deg,#1a1a1a,#121212);border:1px solid #2a2a2a;border-radius:18px;padding:18px 16px 14px;overflow:hidden;transition:border-color .2s,transform .2s}
.pick-card:hover{border-color:#f59e0b;transform:translateY(-2px)}
.pick-card.acc-rush,.pick-card.acc-rec,.pick-card.acc-pass,.pick-card.acc-recpt,
.pick-card.acc-td,.pick-card.acc-ptd,.pick-card.acc-def,.pick-card.acc-kick{border-top:4px solid #f59e0b}
.nfl-toolbar{display:flex;justify-content:flex-end;margin:0 0 14px}
#nflSearch{background:#111;color:#fff;border:1px solid #2a2a2a;border-radius:8px;padding:8px 14px;font-size:.9rem;outline:none;width:240px;max-width:60vw;font-family:'Source Sans Pro',sans-serif}
.sec-hdr{cursor:pointer;display:flex;align-items:center;justify-content:flex-start;user-select:none}
.sec-hdr>span:first-child{order:1;flex:0 1 auto}
.sec-hdr::after{order:2}
.sec-caret{order:3;font-size:1rem;color:#fbbf24;margin-left:2px}
.gcard{cursor:pointer}
.gc-hint{font-size:.62rem;color:#6b7280;margin-top:3px;text-transform:uppercase;letter-spacing:.08em}
.big-modal{max-width:680px;width:92%;max-height:86vh;overflow:auto}
.mk-hdr{font-size:.72rem;font-weight:800;color:#f59e0b;text-transform:uppercase;letter-spacing:.1em;margin:12px 0 6px}
.pl-row{display:flex;align-items:center;justify-content:space-between;gap:10px;padding:9px 12px;border:1px solid #1f1f1f;border-radius:9px;margin-bottom:6px;cursor:pointer;background:#0d0d0d}
.pl-row:hover{border-color:rgba(245,158,11,.4)}
.pl-row .nm{font-weight:700;color:#fff;font-size:.9rem}
.pl-row .mt{font-size:.72rem;color:#8a8f98}
.vsopp-row{display:flex;align-items:center;justify-content:space-between;font-size:.82rem;padding:5px 2px;border-bottom:1px solid #1a1a1a}
.pc-rank{position:absolute;top:10px;right:14px;font-family:'Playfair Display',serif;font-weight:900;font-size:1.6rem;color:rgba(245,158,11,.35)}
.pc-top{display:flex;align-items:center;gap:12px;margin-bottom:10px}
.hs-wrap{position:relative;width:58px;height:58px;border-radius:50%;flex:0 0 auto;background:#222;border:2px solid #333;overflow:visible;display:flex;align-items:center;justify-content:center}
.hs-img{width:100%;height:100%;object-fit:cover;position:absolute;inset:0;z-index:2;border-radius:50%}
.hs-ini{font-family:'Playfair Display',serif;font-weight:800;font-size:1.2rem;color:#9ca3af;z-index:1}
.pc-logo{width:22px;height:22px;position:absolute;bottom:-3px;right:-3px;z-index:3;background:#0f0f0f;border-radius:50%;padding:1px}
.pc-id{flex:1;min-width:0}
.pc-name{font-weight:800;color:#fff;font-size:1.02rem;line-height:1.15;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.pc-meta{font-size:.74rem;color:#9ca3af;margin-top:4px;display:flex;align-items:center;gap:6px;flex-wrap:wrap}
.pc-pos{display:inline-flex;align-items:center;justify-content:center;min-width:26px;padding:2px 6px;border:1px solid rgba(245,158,11,.48);border-radius:5px;background:rgba(245,158,11,.1);color:#fbbf24;font-size:.62rem;font-weight:900;letter-spacing:.04em}
.pc-mkt{display:inline-block;font-size:.6rem;font-weight:700;letter-spacing:.08em;text-transform:uppercase;color:#6b7280;margin-top:4px}
.pc-tagrow{min-height:1px;margin-bottom:8px}
.pc-line-row{display:flex;align-items:center;justify-content:space-between;background:#0e0e0e;border:1px solid #242424;border-radius:10px;padding:8px 12px;margin-bottom:10px}
.pc-line-row .ln{font-weight:900;color:#4ade80;font-size:1.05rem}
.pc-line-row .od{color:#6b7280;font-size:.76rem}
.pc-line-row .est{background:rgba(245,158,11,.08);color:#f59e0b;border:1px solid rgba(245,158,11,.2);padding:2px 8px;border-radius:5px;font-size:.82rem;font-weight:700}
.pc-stats{display:grid;grid-template-columns:1fr 1fr;gap:8px;margin-bottom:10px}
.pc-stat{background:#141414;border:1px solid #222;border-radius:9px;padding:8px;text-align:center}
.pc-stat .k{font-size:.56rem;color:#6b7280;text-transform:uppercase;letter-spacing:.04em;font-weight:700}
.pc-stat .v{font-weight:800;font-size:.92rem;margin-top:3px}
.pc-foot{display:flex;align-items:center;justify-content:space-between;gap:8px}
.pc-score{font-family:'Playfair Display',serif;font-weight:900;color:#f59e0b;font-size:1.15rem}
.pc-tap{background:none;border:1px solid #333;color:#9ca3af;border-radius:8px;padding:6px 10px;font-size:.7rem;font-weight:700;cursor:pointer;transition:all .2s}
.pc-tap:hover{border-color:#f59e0b;color:#f59e0b}
.uplays{background:#141414;border:1px solid #242424;border-radius:14px;padding:4px 4px;margin-bottom:10px}
.uprow{display:flex;align-items:center;justify-content:space-between;padding:9px 12px;border-bottom:1px solid #1c1c1c;cursor:pointer}
.uprow:last-child{border-bottom:none}
.uprow:hover{background:#1a1a1a}
.uprow .nm{font-weight:700;color:#fff;font-size:.82rem}
.uprow .mt{color:#6b7280;font-size:.72rem;margin-top:2px}
.special-wrap{display:grid;grid-template-columns:1fr 1fr;gap:14px;margin-bottom:10px}
@media(max-width:680px){.special-wrap{grid-template-columns:1fr}}
.sp-col{background:#141414;border:1px solid #242424;border-radius:14px;padding:14px}
.sp-col h4{font-size:.72rem;font-weight:800;color:#f59e0b;text-transform:uppercase;letter-spacing:.1em;margin-bottom:8px}
.sp-row{display:flex;align-items:center;justify-content:space-between;gap:8px;padding:8px 6px;border-bottom:1px solid #1c1c1c;cursor:pointer}
.sp-row:last-child{border-bottom:none}
.sp-row:hover{background:#1a1a1a}
.sp-row .nm{font-weight:700;color:#fff;font-size:.82rem}
.sp-row .mt{color:#6b7280;font-size:.72rem;margin-top:2px}
.lad-ov{position:fixed;inset:0;background:rgba(0,0,0,.72);z-index:200;display:flex;align-items:center;justify-content:center;padding:18px}
.lad-modal{background:#161616;border:1px solid #2a2a2a;border-radius:18px;max-width:460px;width:100%;max-height:86vh;overflow-y:auto;padding:22px}
.lad-modal h3{font-family:'Playfair Display',serif;color:#fff;font-size:1.25rem;margin-bottom:2px}
.lad-sub{color:#9ca3af;font-size:.8rem;margin-bottom:14px}
.lad-close{float:right;background:none;border:1px solid #333;color:#9ca3af;border-radius:8px;padding:4px 10px;cursor:pointer;font-weight:700}
.lad-glog{display:flex;flex-wrap:wrap;gap:6px;margin:8px 0 14px}
.glchip{background:#0e0e0e;border:1px solid #242424;border-radius:8px;padding:6px 8px;text-align:center;min-width:44px}
.glchip .d{font-size:.56rem;color:#6b7280}
.glchip .v{font-weight:800;font-size:.95rem;margin-top:2px;color:#e5e7eb}
.glchip.hit{border-color:rgba(74,222,128,.35)}
.glchip.hit .v{color:#4ade80}
.glchip.miss .v{color:#f87171}
.lad-stat{display:flex;justify-content:space-between;align-items:center;padding:8px 4px;border-bottom:1px solid #1c1c1c;font-size:.85rem}
.lad-stat:last-child{border-bottom:none}
.lad-stat .k{color:#9ca3af}
.lad-stat .v{font-weight:700}
.nfl-coach{border:1px solid rgba(56,189,248,.45)!important;background:linear-gradient(145deg,#101827,#0b1220)!important}
.nfl-coach-presets{display:flex;gap:7px;flex-wrap:wrap;margin:14px 0 10px}
.nfl-coach-preset{background:#111827;color:#cbd5e1;border:1px solid #334155;border-radius:999px;padding:7px 11px;font-size:.69rem;font-weight:900;cursor:pointer}
.nfl-coach-preset:hover{border-color:#38bdf8;color:#bae6fd}
.nfl-coach-filter-box{margin:10px 0 12px;padding:11px 12px;border:1px solid rgba(56,189,248,.28);border-radius:10px;background:rgba(7,13,24,.62)}
.nfl-coach-filter-head{display:flex;align-items:center;justify-content:space-between;gap:8px;flex-wrap:wrap}
.nfl-coach-filter-title{color:#7dd3fc;font-size:.65rem;font-weight:950;letter-spacing:.08em;text-transform:uppercase}
.nfl-coach-filter-help{color:#64748b;font-size:.64rem;line-height:1.4;margin-top:3px}
.nfl-coach-filter-row{display:flex;align-items:center;gap:7px;flex-wrap:wrap;margin-top:9px}
.nfl-coach-filter-label{display:inline-flex;align-items:center;gap:5px;color:#cbd5e1;font-size:.7rem;font-weight:800;cursor:pointer}
.nfl-coach-filter-label input{accent-color:#38bdf8}
.nfl-coach-filter-label.side-over input{accent-color:#4ade80}
.nfl-coach-filter-label.side-under input{accent-color:#f87171}
.nfl-coach-filter-actions{display:flex;gap:5px;flex-wrap:wrap}
.nfl-coach-filter-actions button{background:#1e293b;color:#cbd5e1;border:1px solid #334155;border-radius:6px;padding:4px 7px;font-size:.61rem;font-weight:900;cursor:pointer}
.nfl-coach-filter-actions button:hover{border-color:#38bdf8;color:#e0f2fe}
.nfl-coach-market-list{display:flex;gap:5px 10px;flex-wrap:wrap;margin-top:7px}
.nfl-coach-market-list .nfl-coach-filter-label{font-size:.67rem}
.nfl-coach-filter-quick{display:flex;gap:5px;flex-wrap:wrap;margin-top:8px}
.nfl-coach-filter-quick button{background:transparent;color:#7dd3fc;border:1px solid rgba(56,189,248,.28);border-radius:999px;padding:3px 7px;font-size:.59rem;font-weight:900;cursor:pointer}
.nfl-coach-filter-quick button:hover{background:rgba(56,189,248,.1);border-color:#38bdf8}
.nfl-coach-row{display:flex;gap:8px}
.nfl-coach-input{flex:1;min-width:0;background:#070d18;color:#fff;border:1px solid #334155;border-radius:11px;padding:12px 14px;font:inherit;font-size:.84rem}
.nfl-coach-send{background:#0284c7;color:#fff;border:0;border-radius:11px;padding:0 18px;font-weight:900;cursor:pointer}
.nfl-coach-answer{display:none;margin-top:14px;border-top:1px solid rgba(56,189,248,.25);padding-top:14px}
.nfl-coach-question{margin-left:auto;max-width:82%;background:#10243a;border:1px solid rgba(56,189,248,.3);border-radius:12px 12px 3px 12px;padding:9px 12px;color:#bae6fd;font-size:.75rem}
.nfl-coach-summary{margin:11px 0;color:#cbd5e1;font-size:.76rem;line-height:1.5}
.nfl-coach-play{margin-top:9px;background:#0b1220;border:1px solid rgba(56,189,248,.4);border-left:4px solid #38bdf8;border-radius:11px;padding:9px 12px;box-shadow:0 4px 11px rgba(0,0,0,.26)}
.nfl-coach-play>summary{display:flex;justify-content:space-between;align-items:center;gap:12px;list-style:none;cursor:pointer;color:#fff;font-size:.86rem;font-weight:900}
.nfl-coach-play>summary::-webkit-details-marker{display:none}
.nfl-coach-play>summary:after{content:"Expand";color:#38bdf8;font-size:.61rem;text-transform:uppercase}
.nfl-coach-play[open]>summary:after{content:"Collapse"}
.nfl-coach-ident{display:flex;align-items:center;gap:9px;min-width:0}
.nfl-coach-avatar{position:relative;width:36px;height:36px;flex:0 0 36px;border-radius:50%;background:#1e293b;border:1px solid #475569;display:flex;align-items:center;justify-content:center;color:#cbd5e1;font-size:.68rem;font-weight:950}
.nfl-coach-avatar>img:first-of-type{position:absolute;inset:0;width:100%;height:100%;object-fit:cover;border-radius:50%}
.nfl-coach-avatar .team-logo{position:absolute;right:-4px;bottom:-3px;width:16px;height:16px;object-fit:contain;background:#0b1220;border-radius:50%;padding:1px}
.nfl-coach-name{font-size:.94rem;font-weight:950;color:#fff}
.nfl-coach-meta{display:flex;gap:6px;align-items:center;flex-wrap:wrap;color:#a8b4c5;font-size:.67rem;margin-top:3px}
.nfl-coach-pos{color:#7dd3fc;border:1px solid rgba(56,189,248,.35);background:rgba(14,116,144,.14);border-radius:999px;padding:2px 6px;font-weight:950}
.nfl-coach-pickmeta{text-align:right;color:#f1f5f9;white-space:nowrap;font-size:.78rem;line-height:1.4}
.nfl-coach-copy{color:#94a3b8;font-size:.7rem;line-height:1.5;margin-top:8px}
.nfl-coach-stats{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:7px;margin-top:10px}
.nfl-coach-stat{background:#111827;border:1px solid #263449;border-radius:8px;padding:8px}
.nfl-coach-stat .k{color:#64748b;font-size:.56rem;font-weight:900;text-transform:uppercase}
.nfl-coach-stat .v{color:#f8fafc;font-size:.75rem;font-weight:900;margin-top:3px}
.nfl-coach-accord{margin-top:10px;border-top:1px solid #1e293b}
.nfl-coach-accord>details{border-bottom:1px solid #1e293b}
.nfl-coach-accord>details>summary{display:flex;justify-content:space-between;align-items:center;list-style:none;cursor:pointer;padding:11px 2px;color:#e2e8f0;font-size:.68rem;font-weight:950}
.nfl-coach-accord>details>summary::-webkit-details-marker{display:none}
.nfl-coach-accord>details>summary:after{content:"+";color:#38bdf8;font-size:.9rem}
.nfl-coach-accord>details[open]>summary:after{content:"−"}
.nfl-coach-accord-body{padding:0 2px 12px;color:#94a3b8;font-size:.67rem;line-height:1.5}
.nfl-coach-ratebar{height:4px;background:#1e293b;border-radius:99px;overflow:hidden;margin-top:8px}
.nfl-coach-ratebar span{display:block;height:100%;background:#38bdf8;border-radius:99px}
.nfl-coach-opp-history{min-width:0}
.nfl-coach-opp-history>summary{list-style:none;cursor:pointer}
.nfl-coach-opp-history>summary::-webkit-details-marker{display:none}
.nfl-coach-opp-history>summary .k{display:flex;align-items:center;justify-content:space-between;gap:8px}
.nfl-coach-opp-history>summary .k:after{content:"VIEW GAMES +";color:#38bdf8;font-size:.57rem;letter-spacing:.04em}
.nfl-coach-opp-history[open]>summary .k:after{content:"HIDE GAMES −"}
.nfl-coach-opp-history>summary:hover{border-color:#38bdf8;background:#101b2e}
.nfl-coach-opp-games{margin-top:7px;padding:8px;border:1px solid #24334d;border-radius:9px;background:#08111f}
.nfl-coach-opp-head{color:#94a3b8;font-size:.62rem;line-height:1.35;margin-bottom:6px}
.nfl-coach-opp-row{display:flex;align-items:center;justify-content:space-between;gap:8px;padding:5px 0;border-top:1px solid #17243a;font-size:.66rem}
.nfl-coach-opp-row:first-of-type{border-top:0}
.nfl-coach-opp-row .result{font-weight:800}
.nfl-coach-opp-row.hit .result{color:#4ade80}
.nfl-coach-opp-row.miss .result{color:#f87171}
.nfl-coach-opp-row.push .result{color:#fbbf24}
.nfl-coach-games{display:flex;gap:6px;flex-wrap:wrap;margin-top:10px}
.nfl-coach-game{min-width:48px;background:#0b1220;border:1px solid #263449;border-radius:7px;padding:6px;text-align:center}
.nfl-coach-game.hit{border-color:rgba(74,222,128,.45)}.nfl-coach-game.miss{border-color:rgba(248,113,113,.4)}
.nfl-coach-game .d{color:#64748b;font-size:.52rem}.nfl-coach-game .v{font-weight:950;margin-top:2px}.nfl-coach-game.hit .v{color:#4ade80}.nfl-coach-game.miss .v{color:#f87171}
@media(max-width:620px){.nfl-coach-row{display:block}.nfl-coach-send{width:100%;padding:11px;margin-top:8px}.nfl-coach-stats{grid-template-columns:repeat(2,minmax(0,1fr))}.nfl-coach-play>summary{align-items:flex-start}.nfl-coach-pickmeta{white-space:normal;text-align:left}.nfl-coach-play>summary:after{display:none}}
.pm-ov { background: rgba(0,0,0,0.85); backdrop-filter: blur(4px); padding: 16px; display: flex; align-items: center; justify-content: center; position: fixed; inset: 0; z-index: 200; }
.pm-modal { background: #0f1115; border: 1px solid #2a2e37; border-radius: 16px; max-width: 640px; width: 100%; max-height: 90vh; overflow-y: auto; padding: 0; box-shadow: 0 20px 40px rgba(0,0,0,0.6); position: relative; font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Helvetica, Arial, sans-serif; cursor: default; }
.pm-modal::-webkit-scrollbar { width: 6px; }
.pm-modal::-webkit-scrollbar-thumb { background: #333; border-radius: 3px; }
.pm-close { position: absolute; top: 16px; right: 16px; width: 32px; height: 32px; border-radius: 50%; background: #1a1d24; border: 1px solid #333842; color: #9ca3af; display: flex; align-items: center; justify-content: center; cursor: pointer; font-size: 14px; transition: all 0.2s; z-index: 10; padding: 0; }
.pm-close:hover { background: #2a2e37; color: #fff; }
.pm-header { padding: 24px 24px 20px; border-bottom: 1px solid #1f232b; background: linear-gradient(180deg, #161920 0%, #0f1115 100%); border-radius: 16px 16px 0 0; }
.pm-name { font-family: 'Playfair Display', serif; font-size: 1.6rem; font-weight: 800; color: #f8fafc; margin: 0 0 4px; padding-right: 30px; line-height: 1.2; }
.pm-sub { color: #94a3b8; font-size: 0.85rem; font-weight: 500; margin-bottom: 16px; letter-spacing: 0.02em; }
.pm-pick-row { display: flex; align-items: center; gap: 12px; flex-wrap: wrap; }
.pm-pick-badge { padding: 6px 12px; border-radius: 8px; font-size: 0.9rem; font-weight: 800; letter-spacing: 0.05em; text-transform: uppercase; }
.pm-pick-over { background: rgba(74,222,128,0.15); color: #4ade80; border: 1px solid rgba(74,222,128,0.3); }
.pm-pick-under { background: rgba(248,113,113,0.15); color: #f87171; border: 1px solid rgba(248,113,113,0.3); }
.pm-pick-book { color: #cbd5e1; font-size: 0.8rem; font-weight: 600; background: #1e222a; padding: 6px 10px; border-radius: 6px; border: 1px solid #2a2e37; }
.pm-body { padding: 20px 24px 24px; }
.pm-callout { border-radius: 10px; padding: 12px 14px; margin-bottom: 16px; }
.pm-callout-blue { background: rgba(56,189,248,0.06); border: 1px solid rgba(56,189,248,0.2); }
.pm-callout-amber { background: rgba(245,158,11,0.06); border: 1px solid rgba(245,158,11,0.2); }
.pm-co-title { font-size: 0.7rem; font-weight: 800; text-transform: uppercase; letter-spacing: 0.08em; margin-bottom: 4px; }
.pm-callout-blue .pm-co-title { color: #38bdf8; }
.pm-callout-amber .pm-co-title { color: #fbbf24; }
.pm-co-body { font-size: 0.8rem; color: #e2e8f0; line-height: 1.5; }
.pm-split-container { background: #14171d; border: 1px solid #232832; border-radius: 12px; margin-bottom: 20px; overflow: hidden; }
.pm-split-header { display: flex; align-items: center; justify-content: space-between; padding: 10px 14px; background: #1a1d24; border-bottom: 1px solid #232832; }
.pm-split-title { font-size: 0.75rem; font-weight: 700; color: #94a3b8; text-transform: uppercase; letter-spacing: 0.05em; }
.pm-split-line { font-size: 0.95rem; font-weight: 800; color: #f8fafc; }
.pm-split-grid { display: grid; grid-template-columns: 1fr 1fr; gap: 1px; background: #232832; }
.pm-split-card { background: #14171d; padding: 14px; position: relative; }
.pm-split-active { background: rgba(245,158,11,0.05); }
.pm-split-active::before { content: ''; position: absolute; top: 0; left: 0; right: 0; bottom: 0; border: 1px solid rgba(245,158,11,0.4); border-radius: inherit; pointer-events: none; }
.pm-split-venue { font-size: 0.7rem; font-weight: 800; color: #cbd5e1; margin-bottom: 6px; }
.pm-split-active .pm-split-venue { color: #fbbf24; }
.pm-split-val { font-size: 1.4rem; font-weight: 900; color: #fff; line-height: 1; margin-bottom: 4px; font-family: 'Playfair Display', serif; }
.pm-split-active .pm-split-val { color: #fbbf24; }
.pm-split-desc { font-size: 0.75rem; color: #94a3b8; line-height: 1.3; }
.pm-split-context { margin-top: 8px; padding-top: 8px; border-top: 1px solid #2a303a; color: #cbd5e1; font-size: .66rem; font-weight: 700; line-height: 1.45; }
.pm-split-sample { font-size: 0.65rem; color: #64748b; margin-top: 6px; font-weight: 600; text-transform: uppercase; }
.pm-split-badge { position: absolute; top: 12px; right: 12px; background: rgba(245,158,11,0.15); color: #fbbf24; font-size: 0.6rem; font-weight: 800; padding: 3px 6px; border-radius: 4px; border: 1px solid rgba(245,158,11,0.3); }
.pm-split-empty { font-size: 0.8rem; color: #94a3b8; background: #14171d; padding: 12px; border-radius: 8px; border: 1px solid #232832; margin-bottom: 20px; }
.pm-section { margin-bottom: 24px; }
.pm-sec-title { font-size: 0.75rem; font-weight: 800; color: #f8fafc; text-transform: uppercase; letter-spacing: 0.08em; margin-bottom: 12px; display: flex; align-items: center; justify-content: space-between; }
.pm-sec-hl { color: #64748b; font-size: 0.65rem; font-weight: 600; text-transform: none; letter-spacing: 0; }
.pm-sec-count { color: #94a3b8; font-weight: 600; }
.pm-sec-desc { font-size: 0.75rem; color: #94a3b8; margin: -6px 0 12px; }
.pm-glog { display: flex; flex-wrap: wrap; gap: 8px; }
.pm-glchip { background: #1a1d24; border: 1px solid #2a2e37; border-radius: 8px; padding: 8px 10px; text-align: center; min-width: 48px; transition: transform 0.1s; }
.pm-glchip:hover { transform: translateY(-1px); }
.pm-glchip .d { font-size: 0.6rem; color: #64748b; font-weight: 600; margin-bottom: 3px; }
.pm-glchip .v { font-weight: 800; font-size: 1.05rem; color: #e2e8f0; }
.pm-glchip.hit { border-color: rgba(74,222,128,0.4); background: rgba(74,222,128,0.05); }
.pm-glchip.hit .v { color: #4ade80; }
.pm-glchip.miss { border-color: rgba(248,113,113,0.3); background: rgba(248,113,113,0.05); }
.pm-glchip.miss .v { color: #f87171; }
.pm-gray { color: #64748b; font-size: 0.8rem; font-style: italic; }
.pm-vsopp-section { background: #12141a; border: 1px solid #232832; border-radius: 12px; padding: 16px; }
.pm-vsopp-section .pm-sec-title { margin-bottom: 8px; }
.pm-vsopp-summary { display: grid; grid-template-columns: repeat(3, 1fr); gap: 8px; margin-bottom: 14px; }
.pm-vo-card { padding: 10px; border-radius: 8px; text-align: center; }
.pm-vo-over { background: rgba(74,222,128,0.08); border: 1px solid rgba(74,222,128,0.25); }
.pm-vo-under { background: rgba(248,113,113,0.08); border: 1px solid rgba(248,113,113,0.25); }
.pm-vo-push { background: rgba(148,163,184,0.08); border: 1px solid rgba(148,163,184,0.25); }
.pm-vo-lbl { font-size: 0.65rem; font-weight: 800; margin-bottom: 4px; }
.pm-vo-over .pm-vo-lbl { color: #86efac; }
.pm-vo-under .pm-vo-lbl { color: #fca5a5; }
.pm-vo-push .pm-vo-lbl { color: #cbd5e1; }
.pm-vo-val { font-size: 1.1rem; font-weight: 900; }
.pm-vo-over .pm-vo-val { color: #4ade80; }
.pm-vo-under .pm-vo-val { color: #f87171; }
.pm-vo-push .pm-vo-val { color: #f8fafc; }
.pm-vo-val span { font-size: 0.7rem; font-weight: 600; opacity: 0.8; margin-left: 2px; }
.pm-vsopp-list { display: flex; flex-direction: column; }
.pm-vsopp-row { display: flex; align-items: center; justify-content: space-between; padding: 8px 4px; border-bottom: 1px solid #1f232b; }
.pm-vsopp-row:last-child { border-bottom: none; padding-bottom: 0; }
.pm-vo-date { font-size: 0.8rem; color: #94a3b8; }
.pm-vo-res { font-size: 0.85rem; font-weight: 800; }
.pm-res-over { color: #4ade80; }
.pm-res-under { color: #f87171; }
.pm-res-push { color: #cbd5e1; }
.pm-stats-section { margin-bottom: 0; }
.pm-stats-list { background: #12141a; border: 1px solid #232832; border-radius: 12px; overflow: hidden; }
.pm-stat { display: flex; align-items: center; justify-content: space-between; padding: 12px 16px; border-bottom: 1px solid #1f232b; }
.pm-stat:last-child { border-bottom: none; }
.pm-stat:nth-child(even) { background: rgba(255,255,255,0.01); }
.pm-stat .k { font-size: 0.8rem; color: #cbd5e1; font-weight: 700; line-height: 1.35; }
.pm-stat .v { font-size: 0.85rem; font-weight: 700; color: #f8fafc; text-align: right; max-width: 60%; line-height: 1.3; }
.pm-stat-note { display: block; margin-top: 3px; color: #64748b; font-size: .66rem; font-weight: 600; line-height: 1.35; }
.pm-stat .v .pm-stat-note { text-align: right; }
.pm-score-stat { background: rgba(245,158,11,0.08) !important; }
.pm-score-stat .k { color: #fbbf24; font-weight: 700; text-transform: uppercase; letter-spacing: 0.05em; }
.pm-gold { color: #fbbf24 !important; }
.pm-gold-bright { color: #f59e0b !important; font-size: 1.1rem !important; font-weight: 900 !important; }
.pm-text-green { color: #4ade80 !important; }
.pm-text-red { color: #f87171 !important; }
.pm-text-gray { color: #94a3b8 !important; }
@media (max-width: 480px) { .pm-header { padding: 20px 16px 16px; } .pm-body { padding: 16px 16px 20px; } .pm-split-card { padding: 12px 10px; } .pm-split-val { font-size: 1.25rem; } .pm-stat { padding: 10px 12px; } .pm-pick-badge { font-size: 0.8rem; padding: 5px 10px; } }
@media (max-width: 360px) { .pm-ov { padding: 8px; } .pm-split-grid { grid-template-columns: 1fr; } .pm-split-card { min-height: 92px; } }

</style>
</head>
<body>
<nav style="display:flex;justify-content:space-between;align-items:center"><div class="logo">Money <span>Picks</span> Arena</div><div style="display:flex;gap:8px;align-items:center"><button onclick="openNflGpRecord()" style="background:#6d28d9;color:#fff;border:none;border-radius:10px;padding:9px 16px;font-weight:800;font-size:.82rem;cursor:pointer;white-space:nowrap">&#128302; GP Record</button><button onclick="document.getElementById('nfl-track-section').scrollIntoView({behavior:'smooth'})" style="background:#065f46;color:#fff;border:none;border-radius:10px;padding:9px 16px;font-weight:800;font-size:.82rem;cursor:pointer;white-space:nowrap">&#128202; Track Record</button><button class="admin-only" onclick="openNflMyBets()" style="background:#0e7490;color:#fff;border:none;border-radius:10px;padding:9px 16px;font-weight:800;font-size:.82rem;cursor:pointer;white-space:nowrap">&#128176; My Bets</button></div></nav>
<style>
.nfl-bets-tbl{width:100%;border-collapse:collapse;font-size:.82rem}
.nfl-bets-tbl th{padding:7px 10px;text-align:left;font-size:.72rem;color:#9ca3af;font-weight:700;text-transform:uppercase;letter-spacing:.07em;border-bottom:1px solid #2a2a2a;white-space:nowrap}
.nfl-bets-tbl td{padding:8px 10px;border-bottom:1px solid #161616;vertical-align:middle;color:#e5e7eb}
.nfl-bets-tbl tr:last-child td{border-bottom:none}
.nfl-bets-tbl tr:hover td{background:rgba(255,255,255,.02)}
/* NFL Track Record */
 .nfl-trk-sum{background:linear-gradient(135deg,#172033,#111827);border:1px solid rgba(52,211,153,.18);border-radius:14px;padding:16px 18px;display:flex;flex-wrap:wrap;gap:18px;align-items:center;margin-bottom:16px}
 .nfl-trk-tbl{width:100%;border-collapse:collapse;font-size:.94rem;background:#101827}
 .nfl-trk-tbl thead tr{border-bottom:1px solid rgba(52,211,153,.28)}
 .nfl-trk-tbl th{padding:13px 14px;text-align:left;color:#6ee7b7;font-size:.74rem;font-weight:900;text-transform:uppercase;letter-spacing:.1em;background:#111c2e;white-space:nowrap}
 .nfl-trk-tbl td{padding:12px 14px;border-bottom:1px solid rgba(51,65,85,.55);white-space:nowrap;vertical-align:middle}
.nfl-trk-tbl tr:last-child td{border-bottom:none}
 .nfl-trk-tbl tr:hover td{background:rgba(56,189,248,.06)}
 .nfl-trk-compact{width:100%;table-layout:fixed}
 .nfl-trk-compact th,.nfl-trk-compact td{white-space:normal;overflow-wrap:anywhere;padding:10px 9px}
 .nfl-trk-compact .trk-date{width:11%}
 .nfl-trk-compact .trk-category{width:15%}
 .nfl-trk-compact .trk-player{width:18%}
 .nfl-trk-compact .trk-play{width:25%}
 .nfl-trk-compact .trk-odds{width:10%}
 .nfl-trk-compact .trk-actual{width:8%}
 .nfl-trk-compact .trk-result{width:13%}
 .nfl-trk-bar-wrap{width:96px;background:#1f2937;border-radius:999px;height:10px;overflow:hidden;display:inline-block;vertical-align:middle}
.nfl-trk-bar{height:100%;border-radius:4px}
 .nfl-trk-group{margin:0 0 18px;border:1px solid #263449;border-left:5px solid var(--trk-accent,#22d3ee);border-radius:16px;overflow:hidden;background:linear-gradient(145deg,rgba(15,23,42,.98),rgba(10,15,26,.98));box-shadow:0 8px 22px rgba(0,0,0,.18)}
.nfl-trk-group-head{display:flex;justify-content:space-between;align-items:center;gap:16px;flex-wrap:wrap;padding:16px 18px;background:linear-gradient(90deg,color-mix(in srgb,var(--trk-accent,#22d3ee) 15%,transparent),transparent);cursor:pointer;list-style:none}
.nfl-trk-group-head::-webkit-details-marker{display:none}
.nfl-trk-group[open]>.nfl-trk-group-head{border-bottom:1px solid rgba(148,163,184,.16)}
 .nfl-trk-group-title{display:flex;align-items:center;gap:10px;flex-wrap:wrap}
 .nfl-trk-group-kicker{font-size:.7rem;color:#94a3b8;text-transform:uppercase;letter-spacing:.14em;font-weight:900}
 .nfl-trk-group-name{font-size:1.12rem;color:#fff;font-weight:950;letter-spacing:.01em}
 .nfl-trk-group-side{font-size:.74rem;font-weight:950;letter-spacing:.1em;padding:5px 10px;border-radius:999px;color:var(--trk-accent,#67e8f9);border:1px solid color-mix(in srgb,var(--trk-accent,#67e8f9) 55%,transparent);background:color-mix(in srgb,var(--trk-accent,#67e8f9) 12%,transparent)}
 .nfl-trk-group-summary{display:flex;align-items:center;gap:14px;flex-wrap:wrap;color:#cbd5e1;font-size:.86rem;font-weight:800}
 .nfl-trk-group-rate{font-size:1.12rem;font-family:monospace;font-weight:950;color:var(--trk-accent,#67e8f9)}
 .nfl-trk-group-pl{font-family:monospace;font-weight:950}
.nfl-trk-group-toggle{display:inline-flex;align-items:center;justify-content:center;width:25px;height:25px;border:1px solid #475569;border-radius:7px;color:#e2e8f0;font-size:1rem;font-weight:900;line-height:1;background:#111827}
.nfl-trk-group-toggle:after{content:"+"}
.nfl-trk-group[open] .nfl-trk-group-toggle:after{content:"−"}
 .nfl-trk-table-scroll{overflow-x:auto}
 .nfl-trk-result{display:inline-block;min-width:68px;text-align:center;padding:5px 10px;border-radius:999px;font-size:.74rem;letter-spacing:.05em;font-weight:950}
 .nfl-trk-result.win{color:#86efac;background:rgba(34,197,94,.15);border:1px solid rgba(74,222,128,.35)}
 .nfl-trk-result.loss{color:#fca5a5;background:rgba(239,68,68,.15);border:1px solid rgba(248,113,113,.35)}
 .nfl-trk-result.push{color:#fde68a;background:rgba(234,179,8,.15);border:1px solid rgba(250,204,21,.35)}
 .nfl-trk-result.void{color:#cbd5e1;background:rgba(100,116,139,.15);border:1px solid rgba(148,163,184,.25)}
 .nfl-trk-result.pending{color:#cbd5e1;background:rgba(100,116,139,.15);border:1px solid rgba(148,163,184,.25)}
 .nfl-parlay-filters{display:grid;grid-template-columns:1fr 1fr;gap:10px;margin-top:14px;text-align:left}
 .nfl-parlay-filter-group{background:#101010;border:1px solid #292929;border-radius:11px;padding:11px}
.nfl-game-filter-dropdown>summary{display:flex;align-items:center;justify-content:space-between;gap:10px;list-style:none;cursor:pointer;color:#93c5fd;font-size:.68rem;font-weight:900;text-transform:uppercase;letter-spacing:.06em}
.nfl-game-filter-dropdown>summary::-webkit-details-marker{display:none}
.nfl-game-filter-dropdown>summary:after{content:"▼";color:#60a5fa;font-size:.62rem;transition:transform .15s ease}
.nfl-game-filter-dropdown[open]>summary:after{transform:rotate(180deg)}
.nfl-game-filter-summary{margin-left:auto;color:#9ca3af;font-size:.62rem;font-weight:800;letter-spacing:0;text-transform:none}
.nfl-game-filter-panel{padding-top:11px;margin-top:9px;border-top:1px solid #252525}
.nfl-game-filter-panel .nfl-parlay-filter-actions{display:flex;justify-content:flex-end;margin-bottom:9px}
 .nfl-parlay-filter-head{display:flex;align-items:center;justify-content:space-between;gap:8px;margin-bottom:8px}
 .nfl-parlay-filter-title{color:#e5e7eb;font-size:.72rem;font-weight:950;letter-spacing:.05em;text-transform:uppercase}
 .nfl-parlay-filter-actions{display:flex;gap:5px}
 .nfl-parlay-filter-actions button{background:#1f2937;color:#cbd5e1;border:1px solid #374151;border-radius:6px;padding:4px 7px;font-size:.6rem;font-weight:900;cursor:pointer}
 .nfl-parlay-filter-actions button:hover{border-color:#f59e0b;color:#fbbf24}
 .nfl-parlay-cat-list{display:grid;grid-template-columns:1fr;gap:5px;max-height:190px;overflow:auto;padding-right:3px}
 .nfl-game-filter-list{display:grid;grid-template-columns:repeat(auto-fit,minmax(125px,1fr));gap:6px;max-height:150px;overflow:auto;padding-right:3px}
 .nfl-parlay-cat{display:flex;align-items:flex-start;gap:7px;color:#9ca3af;font-size:.67rem;line-height:1.3;cursor:pointer}
 .nfl-parlay-cat input{accent-color:#f59e0b;margin-top:1px}
 .nfl-parlay-cat-empty{color:#64748b;font-size:.65rem;line-height:1.4}
 .nfl-parlay-source{display:inline-block;margin-left:6px;padding:2px 5px;border-radius:5px;font-size:.54rem;font-weight:950;letter-spacing:.04em;vertical-align:1px}
 .nfl-parlay-source.normal{color:#93c5fd;background:rgba(59,130,246,.15)}
 .nfl-parlay-source.coach{color:#86efac;background:rgba(34,197,94,.15)}
 .nfl-td-card{display:none;max-width:960px;margin:0 auto 16px;border-color:rgba(250,204,21,.42)!important;background:radial-gradient(circle at top right,rgba(250,204,21,.08),transparent 38%),#151515!important}
 .nfl-td-head{display:flex;justify-content:space-between;align-items:flex-start;gap:14px;flex-wrap:wrap}
 .nfl-td-kicker{color:#facc15;font-size:.64rem;font-weight:950;letter-spacing:.13em;text-transform:uppercase}
 .nfl-td-title{font-family:'Playfair Display',serif;color:#fff;font-size:1.4rem;margin-top:4px}
 .nfl-td-sub{color:#94a3b8;font-size:.74rem;line-height:1.5;margin-top:5px;max-width:720px}
 .nfl-td-count{color:#fde68a;background:rgba(250,204,21,.1);border:1px solid rgba(250,204,21,.3);border-radius:999px;padding:6px 11px;font-size:.68rem;font-weight:950}
  .nfl-td-controls{display:flex;align-items:flex-end;justify-content:flex-end;gap:8px;flex-wrap:wrap}
  .nfl-td-game-label{display:flex;flex-direction:column;gap:4px;color:#a3a38d;font-size:.56rem;font-weight:900;letter-spacing:.08em;text-transform:uppercase;text-align:left}
  .nfl-td-game-select{min-width:170px;max-width:240px;background:#11110d;color:#fff;border:1px solid rgba(250,204,21,.35);border-radius:8px;padding:7px 9px;font-size:.7rem;font-weight:800}
 .nfl-td-table-wrap{overflow-x:auto;margin-top:14px;border:1px solid #2d2d22;border-radius:12px}
 .nfl-td-table{width:100%;border-collapse:collapse;min-width:790px;font-size:.72rem}
 .nfl-td-table th{background:#11110d;color:#a3a38d;text-align:left;padding:9px 10px;font-size:.58rem;text-transform:uppercase;letter-spacing:.07em}
 .nfl-td-table td{padding:11px 10px;border-top:1px solid #29291f;color:#e5e7eb;vertical-align:middle}
 .nfl-td-player{appearance:none;background:none;border:0;padding:0;color:#fff;font:inherit;font-weight:950;cursor:pointer;text-align:left}
 .nfl-td-player:hover,.nfl-td-player:focus-visible{color:#facc15;outline:none}
 .nfl-td-rank{display:inline-flex;width:24px;height:24px;align-items:center;justify-content:center;border-radius:50%;background:rgba(250,204,21,.12);color:#fde68a;font-weight:950}
 .nfl-td-prob{color:#86efac;font-weight:950;font-family:monospace}
 .nfl-td-edge{color:#4ade80;font-weight:950;font-family:monospace}
 .nfl-td-method{margin-top:10px;color:#6b7280;font-size:.64rem;line-height:1.45}
 .nfl-gp-filters{display:grid;grid-template-columns:minmax(130px,160px) minmax(110px,140px) minmax(0,1fr);gap:10px;align-items:end;margin-bottom:14px}
 .nfl-gp-filter{display:flex;flex-direction:column;gap:6px;min-width:0;color:#9ca3af;font-size:.72rem;font-weight:800;text-transform:uppercase;letter-spacing:.09em}
 .nfl-gp-filter .date-input{display:block;width:100%;max-width:100%;min-width:0;box-sizing:border-box}
   .nfl-gp-grid{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));align-items:stretch;gap:16px;padding:4px 0}
   .nfl-gp-game{position:relative;display:flex;flex-direction:column;overflow:hidden;background:linear-gradient(180deg,#13161f 0%,#0b0e14 100%);border:1px solid #1e293b;border-radius:12px;cursor:pointer;box-shadow:0 8px 24px rgba(0,0,0,.4);transition:transform .2s ease,border-color .2s ease,box-shadow .2s ease;min-width:0}
  .nfl-gp-game:hover{transform:translateY(-2px);border-color:#3b82f6;box-shadow:0 12px 32px rgba(0,0,0,.5)}
  .nfl-gp-game:focus-visible{outline:2px solid #8b5cf6;outline-offset:2px}
  .nfl-gp-head{display:flex;align-items:flex-start;justify-content:space-between;gap:12px;padding:14px 16px;border-bottom:1px solid rgba(255,255,255,.04);background:rgba(255,255,255,.02)}
  .nfl-gp-matchup{color:#f8fafc;font-size:1.05rem;font-weight:900;letter-spacing:-.02em}
  .nfl-gp-date{display:block;color:#94a3b8;font-size:.65rem;margin-top:4px;font-weight:700;text-transform:uppercase;letter-spacing:.04em}
  .nfl-gp-badges{display:flex;flex-direction:column;align-items:flex-end;gap:5px}
  .nfl-gp-badge{border-radius:4px;padding:3px 7px;color:#fff;font-size:.58rem;font-weight:800;letter-spacing:.04em;white-space:nowrap;box-shadow:0 2px 4px rgba(0,0,0,.25)}
  .nfl-gp-teams{display:flex;flex-direction:column;gap:12px;padding:16px}
  .nfl-gp-team{position:relative;display:grid;grid-template-columns:40px minmax(0,1fr) 60px;grid-template-rows:auto auto auto;gap:4px 10px;align-items:center}
  .nfl-gp-logo{width:40px;height:40px;object-fit:contain;grid-row:1/3;filter:drop-shadow(0 2px 4px rgba(0,0,0,.4))}
  .nfl-gp-abbr{color:#cbd5e1;font-size:1rem;font-weight:800;line-height:1.1;grid-column:2;grid-row:1}
  .nfl-gp-team.pick .nfl-gp-abbr{color:#fff}
  .nfl-gp-sp{color:#64748b;font-size:.62rem;grid-column:2;grid-row:2;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;font-weight:600;margin-top:2px}
  .nfl-gp-ranks{display:flex;gap:4px;align-items:center}
  .nfl-gp-rank{font-size:.55rem;padding:2px 5px;border-radius:4px;background:#0f172a;color:#94a3b8;font-weight:800;letter-spacing:.03em;border:1px solid #1e293b}
  .nfl-gp-rank.off{color:#93c5fd;background:rgba(59,130,246,.1);border-color:rgba(59,130,246,.2)}
  .nfl-gp-rank.def{color:#86efac;background:rgba(34,197,94,.1);border-color:rgba(34,197,94,.2)}
  .nfl-gp-win-box{grid-column:3;grid-row:1/3;display:flex;flex-direction:column;align-items:flex-end;justify-content:center}
  .nfl-gp-win{color:#cbd5e1;font-size:1.1rem;font-weight:900;line-height:1}
  .nfl-gp-win small{display:block;color:#64748b;font-size:.52rem;letter-spacing:.05em;text-transform:uppercase;margin-top:4px;font-weight:800;text-align:right}
  .nfl-gp-team.pick .nfl-gp-win{color:#4ade80}
  .nfl-gp-team.pick .nfl-gp-win small{color:#22c55e}
  .nfl-gp-barline{grid-column:1/-1;grid-row:3;width:100%;min-width:0;margin-top:6px}
  .nfl-gp-bar{height:8px;width:100%;border-radius:4px;background:#0f172a;overflow:hidden;box-shadow:inset 0 1px 2px rgba(0,0,0,.6)}
  .nfl-gp-bar>span{display:block;height:100%;border-radius:4px;transition:width .4s ease}
  .nfl-gp-callouts{display:grid;grid-template-columns:1fr 1fr;gap:12px;padding:0 16px 16px;margin-top:auto}
  .nfl-gp-callout{min-width:0;border-left:2px solid #334155;padding-left:10px}
  .nfl-gp-callout .k{color:#64748b;font-size:.56rem;font-weight:800;letter-spacing:.06em;text-transform:uppercase}
  .nfl-gp-callout .v{color:#e2e8f0;font-size:.76rem;font-weight:700;margin-top:5px;line-height:1.4}
  .nfl-gp-why{padding:14px 16px;background:rgba(0,0,0,.2);border-top:1px solid #1e293b;color:#94a3b8;font-size:.7rem;line-height:1.5}
  .nfl-gp-why-title{display:flex;align-items:center;gap:6px;color:#818cf8;font-weight:900;font-size:.62rem;letter-spacing:.06em;text-transform:uppercase;margin-bottom:8px}
  .nfl-gp-why-title::before{content:'';display:block;width:4px;height:4px;background:#818cf8;border-radius:50%}
  .nfl-gp-why ul{margin:0;padding-left:0;list-style:none;display:flex;flex-direction:column;gap:6px}
  .nfl-gp-why li{position:relative;padding-left:12px}
  .nfl-gp-why li::before{content:'';position:absolute;left:0;top:6px;width:4px;height:1px;background:#475569}
  @media(max-width:1100px){.nfl-gp-grid{grid-template-columns:repeat(2,minmax(0,1fr))}}
  @media(max-width:650px){.nfl-gp-grid{grid-template-columns:1fr}.nfl-gp-game{border-radius:10px}}
  .nfl-gp-track{margin:0;border-top:1px solid #1e293b;background:#070d1a}
  .nfl-gp-track summary{list-style:none;cursor:pointer;padding:8px 12px;color:#a78bfa;font-size:.62rem;font-weight:900;letter-spacing:.07em}
  .nfl-gp-track summary::-webkit-details-marker{display:none}
  .nfl-gp-track summary:after{content:'Show';float:right;color:#64748b}
  .nfl-gp-track[open] summary:after{content:'Hide'}
  .nfl-gp-track-body{border-top:1px solid #111c2e}
  .nfl-games-jump{cursor:pointer;border-color:rgba(245,158,11,.55)!important;background:linear-gradient(145deg,rgba(245,158,11,.16),rgba(17,24,39,.8))!important}
  .nfl-games-jump .val,.nfl-games-jump .lbl{color:#fbbf24!important}
  .nfl-by-game{margin-top:20px;border:1px solid rgba(245,158,11,.35);border-radius:16px;background:linear-gradient(145deg,rgba(120,53,15,.12),rgba(15,23,42,.72));overflow:hidden;scroll-margin-top:16px}
  .nfl-by-game-head{padding:16px 18px;border-bottom:1px solid rgba(245,158,11,.2);display:flex;justify-content:space-between;align-items:center;gap:12px;flex-wrap:wrap}
  .nfl-by-game-title{color:#fbbf24;font-size:1.05rem;font-weight:950}
  .nfl-by-game-sub{color:#94a3b8;font-size:.7rem;margin-top:4px}
  .nfl-by-game-count{color:#fde68a;background:rgba(245,158,11,.12);border:1px solid rgba(245,158,11,.3);border-radius:999px;padding:5px 10px;font-size:.66rem;font-weight:900}
  .nfl-by-game-list{padding:12px}
  .nfl-game-group{margin-bottom:8px;border:1px solid #263244;border-radius:12px;background:#0a1120;overflow:hidden}
  .nfl-game-group:last-child{margin-bottom:0}
  .nfl-game-group summary{list-style:none;display:flex;align-items:center;justify-content:space-between;gap:10px;padding:12px 14px;cursor:pointer;color:#f8fafc;font-size:.82rem;font-weight:900}
  .nfl-game-group summary::-webkit-details-marker{display:none}
  .nfl-game-group summary:hover{background:rgba(124,58,237,.1)}
  .nfl-game-group summary:after{content:'Show picks';color:#a78bfa;font-size:.62rem;font-weight:900}
  .nfl-game-group[open] summary:after{content:'Hide picks'}
  .nfl-game-group-meta{display:flex;align-items:center;gap:8px;color:#94a3b8;font-size:.63rem;font-weight:750}
  .nfl-game-pick-count{color:#fbbf24;background:rgba(245,158,11,.1);border-radius:999px;padding:3px 8px;font-weight:900}
  .nfl-game-group-body{border-top:1px solid #263244;padding:5px 12px 10px}
 @media(max-width:620px){.nfl-parlay-filters{grid-template-columns:1fr}}
 @media(max-width:680px){
    .nfl-gp-game{width:100%;max-width:100%;min-width:0;border-radius:12px}.nfl-gp-head{align-items:flex-start}.nfl-gp-team{grid-template-columns:36px minmax(0,1fr) 52px;gap:4px 8px}.nfl-gp-logo{width:36px;height:36px}.nfl-gp-callouts{grid-template-columns:1fr}.nfl-game-group summary{align-items:flex-start}.nfl-game-group-meta{flex-direction:column;align-items:flex-end}
   .nfl-gp-filters{grid-template-columns:minmax(0,1fr) minmax(0,1fr)}
   .nfl-gp-filter-date{grid-column:1/-1}
   .nfl-trk-group-head{padding:14px}.nfl-trk-group-name{font-size:1.02rem}.nfl-trk-tbl{font-size:.88rem}.nfl-trk-tbl th{font-size:.68rem;padding:11px}.nfl-trk-tbl td{padding:11px 12px}
   .nfl-trk-compact,.nfl-trk-compact tbody,.nfl-trk-compact tr,.nfl-trk-compact td{display:block;width:100%}
   .nfl-trk-compact thead{display:none}
   .nfl-trk-compact tr{padding:9px 11px;border-bottom:1px solid rgba(51,65,85,.65)}
   .nfl-trk-compact td{display:grid;grid-template-columns:92px minmax(0,1fr);gap:9px;border:0;padding:5px 0!important}
   .nfl-trk-compact td:before{content:attr(data-label);color:#64748b;font-size:.66rem;font-weight:900;text-transform:uppercase;letter-spacing:.08em}
 }
</style>
<div id="nfl-mybets-card" style="display:none;max-width:960px;margin:18px auto 0;padding:0 16px">
  <div class="card" style="padding:20px 22px">
    <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:6px">
      <h2 style="font-family:'Playfair Display',serif;font-size:1.4rem;font-weight:700;color:#fff">&#128176; My Bets</h2>
      <button onclick="document.getElementById(&#39;nfl-mybets-card&#39;).style.display=&#39;none&#39;" style="background:#1f2937;border:none;color:#9ca3af;border-radius:8px;padding:8px 11px;font-size:.9rem;cursor:pointer">&#215;</button>
    </div>
    <div id="nfl-mybets-body"><p style="color:#9ca3af;font-size:.85rem">Loading&#8230;</p></div>
  </div>
</div>
<main>
  <div class="hero">
    <h1>NFL <span>Money Bombs</span></h1>
    <p>NFL Daily &amp; Weekly Picks</p>
  </div>
  <div class="card run-card">
    <h2>Run NFL Picks</h2>
    <div class="date-row">
      <label>Date</label>
      <input type="date" id="datePicker" class="date-input" value="__TODAY__" onchange="if(typeof _nflPerfectParlayInvalidate==='function')_nflPerfectParlayInvalidate('date')">
      <label for="nflSystem" style="margin-left:8px">System</label>
      <select id="nflSystem" class="date-input" onchange="_nflSystemChanged()" style="min-width:130px">
        <option value="OLD" selected>OLD</option>
        <option value="NEW">NEW</option>
      </select>
      <select id="runScope" class="date-input" onchange="_nflRunScopeChanged()" style="min-width:190px">
        <option value="day">Selected day only</option>
        <option value="week">Full week · Wed–Tue</option>
      </select>
    </div>
    <div id="runScopeHint" style="color:#6b7280;font-size:.72rem;margin:-5px 0 14px">Runs only the selected calendar date.</div>
    <button class="btn" id="getBtn" onclick="getPicks()">🎯 Get Picks</button>
    <button class="btn" id="lastSeasonBtn" onclick="openNflLastSeason()" style="margin-left:10px;background:#6d28d9;color:#fff">📚 View Last Season</button>
    <button class="btn admin-only" id="runBtn" onclick="runPicks()" style="margin-left:10px">Run Picks</button>
    <div class="status-msg" id="statusMsg"></div>
    <div id="nflSystemBadge" style="display:inline-block;margin-top:5px;color:#fbbf24;font-size:.72rem;font-weight:900;letter-spacing:.08em">SYSTEM: OLD</div>
  </div>
  <div class="card" id="parlayCard" style="text-align:center;max-width:600px;margin:0 auto 16px">
    <h2 style="font-family:'Playfair Display',serif;font-size:1.3rem;font-weight:700;color:#fff;margin-bottom:6px">🎰 Auto Parlay Builder <span style="font-size:.7rem;color:#777;font-family:sans-serif">admin only</span></h2>
    <p style="font-size:.74rem;color:#888;margin-bottom:14px">Best available legs from the loaded board — priced odds combined</p>
    <div style="display:flex;gap:10px;justify-content:center;align-items:center;flex-wrap:wrap">
      <label style="color:#9ca3af;font-size:.85rem;font-weight:600">Legs
        <select id="parlayLegs" style="background:#1a1a1a;color:#fff;border:1px solid #333;border-radius:8px;padding:8px 12px;font-size:.9rem;font-weight:700;margin-left:6px">
          <option>2</option><option selected>3</option><option>4</option><option>5</option><option>6</option><option>7</option><option>8</option><option>9</option><option>10</option>
        </select>
      </label>
      <button class="btn" onclick="buildParlay()">Build Best Parlay</button>
      <button class="btn" onclick="generateParlay()" style="background:#1f2937;color:#fff">🎲 Generate New</button>
    </div>
    <div style="display:flex;gap:8px;justify-content:center;align-items:center;flex-wrap:wrap;margin-top:13px">
      <span style="color:#9ca3af;font-size:.72rem;font-weight:900;text-transform:uppercase;letter-spacing:.08em">Odds</span>
      <button type="button" id="nflParlayOddsAll" aria-pressed="true" onclick="_nflParlaySetOddsMode('all')" style="background:#f59e0b;color:#111827;border:1px solid #f59e0b;border-radius:8px;padding:7px 12px;font-size:.75rem;font-weight:900;cursor:pointer">All Odds</button>
      <button type="button" id="nflParlayOddsPlus" aria-pressed="false" onclick="_nflParlaySetOddsMode('plus')" style="background:#1f2937;color:#e5e7eb;border:1px solid #374151;border-radius:8px;padding:7px 12px;font-size:.75rem;font-weight:900;cursor:pointer">+ Odds</button>
      <button type="button" id="nflParlayOddsMinus" aria-pressed="false" onclick="_nflParlaySetOddsMode('minus')" style="background:#1f2937;color:#e5e7eb;border:1px solid #374151;border-radius:8px;padding:7px 12px;font-size:.75rem;font-weight:900;cursor:pointer">− Odds</button>
    </div>
    <div class="nfl-parlay-filters">
      <details class="nfl-parlay-filter-group nfl-game-filter-dropdown" style="grid-column:1/-1;border-color:rgba(59,130,246,.35)">
        <summary><span>Choose Games</span><span id="nflParlayGamesSummary" class="nfl-game-filter-summary">Run picks to load games</span></summary>
        <div class="nfl-game-filter-panel">
          <div class="nfl-parlay-filter-actions"><button type="button" onclick="_nflGameSetAll('parlay',true)">All</button><button type="button" onclick="_nflGameSetAll('parlay',false)">None</button></div>
          <div id="nflParlayGames" class="nfl-game-filter-list"><div class="nfl-parlay-cat-empty">Run today&#39;s picks to load games.</div></div>
        </div>
      </details>
      <div class="nfl-parlay-filter-group">
        <div class="nfl-parlay-filter-head"><div class="nfl-parlay-filter-title">Normal Plays</div><div class="nfl-parlay-filter-actions"><button type="button" onclick="_nflParlaySetAll('normal',true)">All</button><button type="button" onclick="_nflParlaySetAll('normal',false)">None</button></div></div>
        <div id="nflParlayNormalCats" class="nfl-parlay-cat-list"><div class="nfl-parlay-cat-empty">Run today&#39;s picks to load categories.</div></div>
      </div>
      <div class="nfl-parlay-filter-group" style="border-color:rgba(34,197,94,.3)">
        <div class="nfl-parlay-filter-head"><div class="nfl-parlay-filter-title" style="color:#86efac">Coach Edge Plays</div><div class="nfl-parlay-filter-actions"><button type="button" onclick="_nflParlaySetAll('coach',true)">All</button><button type="button" onclick="_nflParlaySetAll('coach',false)">None</button></div></div>
        <div id="nflParlayCoachCats" class="nfl-parlay-cat-list"><div class="nfl-parlay-cat-empty">Run today&#39;s picks to load positive-edge categories.</div></div>
      </div>
    </div>
    <div id="parlayResult" style="margin-top:16px;text-align:left"></div>
  </div>
  <div class="card nfl-coach" id="nflCoachCard" style="max-width:960px;margin:0 auto 16px">
    <div style="display:flex;justify-content:space-between;gap:12px;flex-wrap:wrap">
       <div><div style="color:#38bdf8;font-size:.66rem;font-weight:900;letter-spacing:.12em;text-transform:uppercase">Grounded NFL analysis</div>
       <h2 style="font-family:'Playfair Display',serif;color:#fff;font-size:1.35rem;margin-top:4px">The Edge Coach · NFL Props Analyst</h2>
       <div style="color:#94a3b8;font-size:.76rem;margin-top:5px">Find safer sportsbook sides or scan every supported market for positive Coach Edge. Choose Over, Under, categories, and games above.</div></div>
      <div><button onclick="openNflCoachTrack()" style="width:100%;background:#0e7490;color:#fff;border:0;border-radius:8px;padding:8px 11px;font-weight:900;font-size:.7rem;cursor:pointer">AI Coach Track Record</button><button onclick="showNflPerfectParlayBuilder()" style="width:100%;margin-top:8px;background:linear-gradient(135deg,#0369a1,#7c3aed);color:#fff;border:1px solid rgba(125,211,252,.5);border-radius:8px;padding:8px 10px;font-size:.7rem;font-weight:950;cursor:pointer;white-space:nowrap;box-shadow:0 4px 14px rgba(124,58,237,.22)">&#10024; Perfect Parlay</button><div style="color:#86efac;border:1px solid rgba(74,222,128,.35);border-radius:999px;padding:5px 9px;height:max-content;font-size:.62rem;font-weight:900;margin-top:6px">NO INVENTED PLAYS</div></div>
    </div>
    <div class="nfl-coach-presets">
      <button class="nfl-coach-preset" onclick="askNflCoachPreset('Show every play with a 100% App Hit Rate','app_hit_rate_100')" style="border-color:#22c55e;color:#bbf7d0">100% App Hit Rate</button>
      <button class="nfl-coach-preset" onclick="askNflCoachPreset('Show me the safest bets','safest_bets')">Safest bets</button>
      <button class="nfl-coach-preset" onclick="askNflCoachPreset('Show the best positive Coach Edge plays','coach_edge')">Coach Edge</button>
       <button class="nfl-coach-preset" onclick="askNflMovementCoach('OVER')" style="border-color:#22c55e;color:#bbf7d0">Biggest Over Line Movement</button>
       <button class="nfl-coach-preset" onclick="askNflMovementCoach('UNDER')" style="border-color:#f87171;color:#fecaca">Biggest Under Line Movement</button>
      <button class="nfl-coach-preset" id="nflAltCoachBtn" onclick="askNflAltCoach()" style="border-color:#f59e0b;color:#fde68a">Best Alt-Line Edge Plays · Top 10</button>
      <button class="nfl-coach-preset" onclick="askNflCoachPreset('Show the best passing plays','passing')">Passing</button>
      <button class="nfl-coach-preset" onclick="askNflCoachPreset('Show the best rushing plays','rushing')">Rushing</button>
      <button class="nfl-coach-preset" onclick="askNflCoachPreset('Show the best receiving plays','receiving')">Receiving</button>
      <button class="nfl-coach-preset" onclick="askNflCoachPreset('Show the best defensive player prop plays','defense')">Best Defense Plays</button>
      <button class="nfl-coach-preset" onclick="askNflCoachPreset('Show the best kicker prop plays','kicking')">Best Kicker Plays</button>
      <button class="nfl-coach-preset" onclick="askNflTdCoach()" style="border-color:#eab308;color:#fde68a">TD Scorers · Top 10</button>
      <button class="nfl-coach-preset" onclick="askNflCoachPreset('Show the best under plays','best_unders')">Best unders</button>
    </div>
     <div class="nfl-coach-filter-box" id="nflCoachFilterBox">
       <div class="nfl-coach-filter-head">
         <div><div class="nfl-coach-filter-title">Coach sides, rookies &amp; market categories</div>
         <div class="nfl-coach-filter-help">Rookie combines with any selected category—for example Rookie + Receptions—and applies before Coach ranking, distinct-player dedupe, and the Top 10 cap. Rookie status uses ESPN roster experience. Genuine sportsbook quotes only.</div></div>
         <div class="nfl-coach-filter-actions"><button type="button" onclick="_nflCoachSetSides(true)">All sides</button><button type="button" onclick="_nflCoachSetSides(false)">No sides</button></div>
       </div>
       <div class="nfl-coach-filter-row" aria-label="Coach sides">
         <span style="color:#64748b;font-size:.62rem;font-weight:900;text-transform:uppercase;letter-spacing:.08em">Sides</span>
         <label class="nfl-coach-filter-label side-over"><input type="checkbox" class="nfl-coach-side-choice" data-side="OVER" checked onchange="_nflCoachSelectionChanged()"> OVER</label>
         <label class="nfl-coach-filter-label side-under"><input type="checkbox" class="nfl-coach-side-choice" data-side="UNDER" checked onchange="_nflCoachSelectionChanged()"> UNDER</label>
         <label class="nfl-coach-filter-label" style="border-color:#a78bfa;color:#ddd6fe"><input type="checkbox" id="nflCoachRookieOnly" class="nfl-coach-rookie-choice" onchange="_nflCoachSelectionChanged()"> ROOKIE</label>
       </div>
       <div class="nfl-coach-filter-row">
         <div style="display:flex;align-items:center;gap:8px;flex-wrap:wrap;width:100%">
           <span style="color:#64748b;font-size:.62rem;font-weight:900;text-transform:uppercase;letter-spacing:.08em">Markets</span>
           <div class="nfl-coach-filter-actions"><button type="button" onclick="_nflCoachSetMarkets(true)">All categories</button><button type="button" onclick="_nflCoachSetMarkets(false)">No categories</button></div>
         </div>
         <div id="nflCoachMarkets" class="nfl-coach-market-list" aria-label="Coach market categories"></div>
         <div id="nflCoachMarketQuick" class="nfl-coach-filter-quick" aria-label="Coach market shortcuts"></div>
       </div>
     </div>
    <details class="nfl-parlay-filter-group nfl-game-filter-dropdown" style="margin:10px 0 12px;border-color:rgba(56,189,248,.35)">
      <summary><span style="color:#7dd3fc">Choose Games for Coach</span><span id="nflCoachGamesSummary" class="nfl-game-filter-summary">Run picks to load games</span></summary>
      <div class="nfl-game-filter-panel">
        <div class="nfl-parlay-filter-actions"><button type="button" onclick="_nflGameSetAll('coach',true)">All</button><button type="button" onclick="_nflGameSetAll('coach',false)">None</button></div>
        <div id="nflCoachGames" class="nfl-game-filter-list"><div class="nfl-parlay-cat-empty">Run today&#39;s picks to load games.</div></div>
      </div>
    </details>
    <div class="nfl-coach-row">
      <input id="nflCoachInput" class="nfl-coach-input" placeholder="Example: Safest rushing unders from -300 to -150" onkeydown="if(event.key==='Enter')askNflCoach()"/>
      <button class="nfl-coach-send" onclick="askNflCoach()">Analyze</button>
    </div>
     <div style="color:#64748b;font-size:.65rem;line-height:1.45;margin-top:8px">Requires a loaded NFL board and genuine sportsbook prices. Safest Bets ranks the selected sides by implied probability; Coach Edge equals app probability minus sportsbook-implied probability. Filters stay active for every preset, including TD and alternate-line Top 10.</div>
    <div id="nflCoachAnswer" class="nfl-coach-answer"></div>
    <div id="nflCoachCaptureStatus" style="min-height:1.2em;margin-top:8px;color:#94a3b8;font-size:.7rem"></div>
  </div>
  <div id="nfl-coach-track-section" class="card" style="display:none;max-width:960px;margin:0 auto 16px;padding:20px 22px">
    <div style="margin-bottom:14px">
      <h2 style="font-family:'Playfair Display',serif;font-size:1.4rem;font-weight:700;color:#fff">&#128202; NFL AI Coach Track Record <span id="nflCoachSystemBadge" style="color:#fbbf24;font-size:.7rem">SYSTEM: OLD</span></h2>
       <div style="color:#7c8aa0;font-size:.76rem;margin-top:4px">Write-once pre-kickoff recommendations from all Coach presets. Kept separate from the main, Overflow, Game Predictor, and historical records.</div>
    </div>
    <div style="display:flex;align-items:center;gap:10px;flex-wrap:wrap;margin-bottom:14px">
      <label style="color:#9ca3af;font-size:.78rem;font-weight:700;text-transform:uppercase;letter-spacing:.1em">Record</label>
      <select id="nflCoachTrkSource" class="date-input" onchange="_nflCoachTrackAwaitingSelection()">
        <option value="official">Official Coach</option>
        <option value="historical">Historical Edge Coach</option>
      </select>
      <label style="color:#9ca3af;font-size:.78rem;font-weight:700;text-transform:uppercase;letter-spacing:.1em">Period</label>
      <select id="nflCoachTrkPeriod" class="date-input" onchange="renderNflCoachTrack()">
        <option value="day">Day</option>
        <option value="week">Week</option>
        <option value="month">Month</option>
        <option value="season">Season</option>
        <option value="all">All Time</option>
      </select>
      <label style="color:#9ca3af;font-size:.78rem;font-weight:700;text-transform:uppercase;letter-spacing:.1em">Date</label>
      <input type="date" id="nflCoachTrkDate" class="date-input" value="__TODAY__" style="width:auto" onchange="_nflCoachTrkDayName();_nflCoachTrackAwaitingSelection()">
      <span id="nflCoachTrkDayName" style="color:#34d399;font-weight:700;font-size:.9rem"></span>
      <label style="color:#9ca3af;font-size:.78rem;font-weight:700;text-transform:uppercase;letter-spacing:.1em">Bet $</label>
      <input type="number" id="nflCoachTrkStake" class="date-input" value="20" min="0.01" step="0.01" style="width:105px" oninput="renderNflCoachTrack()">
      <button onclick="loadNflCoachTrack()" style="background:#065f46;color:#fff;border:none;border-radius:8px;padding:8px 14px;font-weight:700;cursor:pointer;font-size:.82rem">&#8635; Get Results</button>
      <button id="nflCoachTrkBtnCat" onclick="nflCoachTrkSetTab('cat')" style="background:#065f46;color:#fff;border:none;border-radius:8px;padding:8px 14px;font-weight:700;cursor:pointer;font-size:.82rem">By Category</button>
      <button id="nflCoachTrkBtnList" onclick="nflCoachTrkSetTab('list')" style="background:#1f2937;color:#fff;border:none;border-radius:8px;padding:8px 14px;font-weight:700;cursor:pointer;font-size:.82rem">Full List</button>
    </div>
    <div id="nflCoachTrackSummary"></div>
    <div id="nflCoachTrackBody"></div>
  </div>
  <div id="nfl-gp-card" style="display:none;max-width:1500px;margin:18px auto 0;padding:0 16px">
    <div style="display:flex;align-items:center;gap:8px;font-size:1.05rem;font-weight:900;color:#a78bfa;margin-bottom:6px;letter-spacing:0.02em"><svg width="18" height="18" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" style="color:#a78bfa"><path d="M21.54 15H17a2 2 0 0 0-2 2v4.54"/><path d="M7 3.34V5a3 3 0 0 0 3 3v0a2 2 0 0 1 2 2v0c0 1.1.9 2 2 2v0a2 2 0 0 0 2-2c0-1.1.9-2 2-2h3.17"/><path d="M11 21.95V18a2 2 0 0 0-2-2v0a2 2 0 0 1-2-2v-1a2 2 0 0 0-2-2H2.05"/><circle cx="12" cy="12" r="10"/></svg> GAME PREDICTOR &#8212; TODAY&#39;S WINNERS</div>
    <div style="font-size:.72rem;color:#64748b;margin-bottom:14px">Model blends recent L5 form, last completed season offense/defense, home-field advantage, and venue-aware results from the last five head-to-head meetings. Tap a game for the full breakdown.</div>
    <div id="nfl-gp-body"></div>
  </div>
  <div id="nfl-td-predictor-card" class="card nfl-td-card">
    <div class="nfl-td-head">
      <div><div class="nfl-td-kicker">Touchdown Intelligence</div><h2 class="nfl-td-title">Anytime TD Predictor</h2>
      <div class="nfl-td-sub">Touchdown scorers ranked by their strongest displayed hit-rate signal. Model probability and sportsbook value edge remain visible as separate checks.</div></div>
      <div class="nfl-td-controls"><label class="nfl-td-game-label">Pick Game<select id="nflTdGameSelect" class="nfl-td-game-select" onchange="_renderNflTdPredictor((window._nflState||{}).d||{})"><option value="">All Games</option></select></label><div id="nflTdPredictorCount" class="nfl-td-count"></div></div>
    </div>
    <div id="nflTdPositionFilters" role="group" aria-label="Filter Anytime TD scorers by position" style="display:flex;gap:7px;flex-wrap:wrap;margin:13px 0 2px"></div>
    <div id="nfl-td-predictor-body"></div>
  </div>
  <div id="results"></div>
</main>
<footer>
  <div class="ft-logo">Money Picks Arena</div>
  <div>NFL Money Bombs &middot; Player Props &middot; Daily Picks</div>
  <div style="margin-top:8px;font-size:.7rem">For entertainment only. Not a betting service. Must be 18+. Please gamble responsibly.</div>
</footer>
<div id="nfl-track-section" style="max-width:960px;margin:18px auto 0;padding:0 16px 40px">
  <div id="nfl-gp-record-section" class="card" style="padding:20px 22px;border-color:#4c1d95">
    <div style="display:flex;justify-content:space-between;align-items:flex-start;gap:12px;flex-wrap:wrap;margin-bottom:12px">
      <div>
        <h2 style="font-family:'Playfair Display',serif;font-size:1.4rem;font-weight:700;color:#fff;display:flex;align-items:center;gap:8px"><svg width="22" height="22" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" style="color:#a78bfa"><path d="M21.54 15H17a2 2 0 0 0-2 2v4.54"/><path d="M7 3.34V5a3 3 0 0 0 3 3v0a2 2 0 0 1 2 2v0c0 1.1.9 2 2 2v0a2 2 0 0 0 2-2c0-1.1.9-2 2-2h3.17"/><path d="M11 21.95V18a2 2 0 0 0-2-2v0a2 2 0 0 1-2-2v-1a2 2 0 0 0-2-2H2.05"/><circle cx="12" cy="12" r="10"/></svg> NFL Game Predictor Record <span style="color:#fbbf24;font-size:.7rem;font-family:sans-serif">SYSTEM: SELECTED</span></h2>
        <div style="color:#7c8aa0;font-size:.76rem;margin-top:4px">Official pre-game forecasts tracked separately for game winners and point totals.</div>
      </div>
      <button onclick="loadNflGpRecord()" style="background:#6d28d9;color:#fff;border:none;border-radius:8px;padding:8px 14px;font-weight:700;cursor:pointer;font-size:.82rem">&#8635; Get Results</button>
    </div>
    <div class="nfl-gp-filters">
      <label class="nfl-gp-filter">Season
        <select id="nflGpSeason" class="date-input" onchange="_nflGpControlChanged('season')"></select>
      </label>
      <label class="nfl-gp-filter">Week
        <select id="nflGpWeek" class="date-input" onchange="_nflGpControlChanged('week')"></select>
      </label>
      <label class="nfl-gp-filter nfl-gp-filter-date">Game Date
        <select id="nflGpDate" class="date-input" onchange="renderNflGpRecord()"></select>
      </label>
      <label class="nfl-gp-filter">Bet Amount
        <input id="nflGpStake" class="date-input" type="number" min="0.01" step="0.01" value="20" oninput="_nflGpStakeChanged()" style="width:110px">
      </label>
    </div>
    <div id="nflGpTrkSummary"></div>
    <div id="nflGpTrkBody"></div>
  </div>
  <div class="card" style="padding:20px 22px">
    <div style="margin-bottom:14px">
      <h2 style="font-family:'Playfair Display',serif;font-size:1.4rem;font-weight:700;color:#fff">&#128202; NFL Track Record <span id="nflTrackSystemBadge" style="color:#fbbf24;font-size:.7rem">SYSTEM: OLD</span></h2>
      <div style="color:#7c8aa0;font-size:.76rem;margin-top:4px">Top 10 picks per category. Historical Analysis remains separate from the official pre-game record.</div>
    </div>
    <div style="display:flex;align-items:center;gap:10px;flex-wrap:wrap;margin-bottom:14px">
      <label style="color:#9ca3af;font-size:.78rem;font-weight:700;text-transform:uppercase;letter-spacing:.1em">Record</label>
      <select id="nflTrkSource" class="date-input" onchange="nflTrkSourceChanged()">
        <option value="official">Official</option>
        <option value="historical">Historical Analysis</option>
      </select>
      <label style="color:#9ca3af;font-size:.78rem;font-weight:700;text-transform:uppercase;letter-spacing:.1em">Period</label>
      <select id="nflTrkPeriod" class="date-input" onchange="renderNflTrackDay()">
        <option value="day">Day</option>
        <option value="week">Week</option>
        <option value="month">Month</option>
        <option value="season">Season</option>
        <option value="all">All Time</option>
      </select>
      <label style="color:#9ca3af;font-size:.78rem;font-weight:700;text-transform:uppercase;letter-spacing:.1em">Date</label>
      <input type="date" id="nflTrkDate" class="date-input" style="width:auto" onchange="_nflTrkDayName();renderNflTrackDay()">
      <span id="nflTrkDayName" style="color:#34d399;font-weight:700;font-size:.9rem"></span>
      <label style="color:#9ca3af;font-size:.78rem;font-weight:700;text-transform:uppercase;letter-spacing:.1em">Bet $</label>
      <input type="number" id="nflTrkStake" class="date-input" value="20" min="0.01" step="0.01" style="width:105px" oninput="renderNflTrackDay()">
      <button onclick="loadNflTrackRecord()" style="background:#065f46;color:#fff;border:none;border-radius:8px;padding:8px 14px;font-weight:700;cursor:pointer;font-size:.82rem">&#8635; Get Results</button>
      <button id="nflTrkBtnCat" onclick="nflTrkSetTab('cat')" style="background:#065f46;color:#fff;border:none;border-radius:8px;padding:8px 14px;font-weight:700;cursor:pointer;font-size:.82rem">By Category</button>
      <button id="nflTrkBtnList" onclick="nflTrkSetTab('list')" style="background:#1f2937;color:#fff;border:none;border-radius:8px;padding:8px 14px;font-weight:700;cursor:pointer;font-size:.82rem">Full List</button>
    </div>
    <div id="nflTrkSummary"></div>
    <div id="nflTrkBody"></div>
  </div>
  <div class="card" style="padding:20px 22px;border-color:#92400e">
    <div style="margin-bottom:14px">
      <h2 style="font-family:'Playfair Display',serif;font-size:1.4rem;font-weight:700;color:#fff">&#128200; NFL Overflow Track Record <span id="nflOverflowSystemBadge" style="color:#fbbf24;font-size:.7rem">SYSTEM: OLD</span></h2>
      <div style="color:#9a7b63;font-size:.76rem;margin-top:4px">Ranks 11+ tracked separately from each category&#39;s Top 10 picks.</div>
    </div>
    <div style="display:flex;align-items:center;gap:10px;flex-wrap:wrap;margin-bottom:14px">
      <label style="color:#9ca3af;font-size:.78rem;font-weight:700;text-transform:uppercase;letter-spacing:.1em">Record</label>
      <select id="nflOvfSource" class="date-input" onchange="renderNflOverflowDay()">
        <option value="official">Official</option>
        <option value="historical">Historical Analysis</option>
      </select>
      <label style="color:#9ca3af;font-size:.78rem;font-weight:700;text-transform:uppercase;letter-spacing:.1em">Period</label>
      <select id="nflOvfPeriod" class="date-input" onchange="renderNflOverflowDay()">
        <option value="day">Day</option>
        <option value="week">Week</option>
        <option value="month">Month</option>
        <option value="season">Season</option>
        <option value="all">All Time</option>
      </select>
      <label style="color:#9ca3af;font-size:.78rem;font-weight:700;text-transform:uppercase;letter-spacing:.1em">Date</label>
      <input type="date" id="nflOvfDate" class="date-input" style="width:auto" onchange="_nflOvfDayName();renderNflOverflowDay()">
      <span id="nflOvfDayName" style="color:#f59e0b;font-weight:700;font-size:.9rem"></span>
      <label style="color:#9ca3af;font-size:.78rem;font-weight:700;text-transform:uppercase;letter-spacing:.1em">Bet $</label>
      <input type="number" id="nflOvfStake" class="date-input" value="20" min="0.01" step="0.01" style="width:105px" oninput="renderNflOverflowDay()">
      <button onclick="loadNflOverflowRecord()" style="background:#92400e;color:#fff;border:none;border-radius:8px;padding:8px 14px;font-weight:700;cursor:pointer;font-size:.82rem">&#8635; Get Results</button>
      <button id="nflOvfBtnCat" onclick="nflOvfSetTab('cat')" style="background:#92400e;color:#fff;border:none;border-radius:8px;padding:8px 14px;font-weight:700;cursor:pointer;font-size:.82rem">By Category</button>
      <button id="nflOvfBtnList" onclick="nflOvfSetTab('list')" style="background:#1f2937;color:#fff;border:none;border-radius:8px;padding:8px 14px;font-weight:700;cursor:pointer;font-size:.82rem">Full List</button>
    </div>
    <div id="nflOvfSummary"></div>
    <div id="nflOvfBody"><p style="color:#94a3b8">Select the record, period, and date, then click Get Results.</p></div>
  </div>
</div>
<script>

window.NFL_BASE_PATH=__NFL_BASE_PATH__;
if(window.NFL_BASE_PATH){
  (function(){
    var nativeFetch=window.fetch.bind(window);
    window.fetch=function(resource,options){
      if(typeof resource==='string'&&resource.indexOf('/api/')===0){
        resource=window.NFL_BASE_PATH+resource;
      }
      return nativeFetch(resource,options);
    };
  })();
}

var _nflKey='__mpa_token';
var _nflParams=new URLSearchParams(window.location.search);
var _nflUrlTok=_nflParams.get('token');
if(_nflUrlTok){localStorage.setItem(_nflKey,_nflUrlTok);window.history.replaceState({},'',window.location.pathname);}
var _nflTok=localStorage.getItem(_nflKey)||'';
if(!_nflTok){window.location.href='https://moneypicksarena.com';}
var _nflAdminParam=_nflParams.get('admin')||'';
function _applyAdmin(){if(window.IS_ADMIN){document.body&&document.body.classList.add('is-admin');}else{if(_nflTok){fetch('/api/whoami?token='+encodeURIComponent(_nflTok)).then(function(r){return r.json();}).then(function(d){if(d&&d.is_admin){window.IS_ADMIN=true;document.body&&document.body.classList.add('is-admin');}}).catch(function(){});}}}
if(document.readyState==='loading'){document.addEventListener('DOMContentLoaded',_applyAdmin);}else{_applyAdmin();}

// ===== Admin Auto Parlay Builder (NFL) =====
function _amToDec(a){var s=String(a==null?'':a).replace('+','').trim();var n=parseFloat(s);if(!n||isNaN(n))return null;return n>0?1+n/100:1+100/Math.abs(n);}
function _decToAm(d){if(!d||d<=1)return null;return d>=2?'+'+Math.round((d-1)*100):'-'+Math.round(100/(d-1));}
function _fmtOdds(o){if(o==null||o==='')return null;var s=String(o).trim();if(!s||s==='0')return null;return (s.charAt(0)==='-'||s.charAt(0)==='+')?s:'+'+s;}
function _floorOk(odds){if(odds==null||odds==='')return true;var a=parseFloat(odds);if(isNaN(a)||a===0)return true;return a>=-1000;}
function _legScore(c){return (c.hasOdds?1:0)*1e9+(c.rate||0)*1e4+(c.dec?Math.min(c.dec,11)*100:0);}
function _nflLeg(p){
  var dir=(p.pick==='O'||p.pick==='OVER')?'OVER':(p.pick==='U'||p.pick==='UNDER')?'UNDER':p.pick;
  var line=(p.realLine!=null?p.realLine:(p.dispLine!=null?p.dispLine:0));
  var rate=(p.vsLineRate||p.rateB||p.rateA||p.dispScore||0);
  var odds=(dir==='OVER')?p.realOdds:(dir==='UNDER')?p.realUnderOdds:null;var dec=_amToDec(odds);
  return {player:p.name,team:p.team||'',opp:p.opponent||'',market:p.mkt||p.label||'',dir:dir,line:line,rate:Math.round(rate||0),odds:odds,book:_nflSideBook(p,dir),dec:dec,hasOdds:!!dec,source:'normal',detail:p};
}
function _nflParlayCatKey(c){return String(c.market||'NFL Prop')+'|'+String(c.dir||'');}
function _nflParlayCatLabel(c){return String(c.market||'NFL Prop')+(c.dir?' · '+c.dir:'');}
window.__NFL_GAME_FILTERS__={parlay:{},coach:{}};
function _nflGameKey(team,opp){
  return [String(team||'').toUpperCase(),String(opp||'').toUpperCase()].sort().join('|');
}
function _nflLoadedGames(){
  var d=(window._nflState||{}).d||{},seen={},games=[];
  (d.games||[]).forEach(function(g){
    var away=String(g.away_abbr||g.away_team||'').toUpperCase();
    var home=String(g.home_abbr||g.home_team||'').toUpperCase();
    var key=_nflGameKey(away,home);
    if(!away||!home||seen[key])return;
    seen[key]=1;games.push({key:key,label:away+' @ '+home});
  });
  if(!games.length){
    (d.all||[]).forEach(function(p){
      var team=String(p.team||'').toUpperCase(),opp=String(p.opponent||p.opp||'').toUpperCase();
      var key=_nflGameKey(team,opp);
      if(!team||!opp||seen[key])return;
      seen[key]=1;games.push({key:key,label:team+' vs '+opp});
    });
  }
  return games.sort(function(a,b){return a.label.localeCompare(b.label);});
}
function _nflGameFilterOn(scope,team,opp){
  var group=(window.__NFL_GAME_FILTERS__||{})[scope]||{};
  return group[_nflGameKey(team,opp)]!==false;
}
function _nflGameSync(scope){
  var group=window.__NFL_GAME_FILTERS__[scope]||(window.__NFL_GAME_FILTERS__[scope]={});
  document.querySelectorAll('.nfl-game-choice[data-scope="'+scope+'"]').forEach(function(cb){
    group[decodeURIComponent(cb.getAttribute('data-key')||'')]=!!cb.checked;
  });
  _nflGameFilterSummary(scope);
}
function _nflGameSetAll(scope,on){
  document.querySelectorAll('.nfl-game-choice[data-scope="'+scope+'"]').forEach(function(cb){cb.checked=!!on;});
  _nflGameSync(scope);
}
function _nflGameFilterActive(scope){
  var games=_nflLoadedGames();
  return games.some(function(g){return !_nflGameFilterOn(scope,g.key.split('|')[0],g.key.split('|')[1]);});
}
function _nflGameFilterSummary(scope){
  var games=_nflLoadedGames(),selected=games.filter(function(g){
    return _nflGameFilterOn(scope,g.key.split('|')[0],g.key.split('|')[1]);
  }).length;
  var id=scope==='coach'?'nflCoachGamesSummary':'nflParlayGamesSummary';
  var el=document.getElementById(id);if(!el)return;
  if(!games.length)el.textContent='Run picks to load games';
  else if(selected===games.length)el.textContent='All '+games.length+' selected';
  else if(selected===0)el.textContent='None selected';
  else el.textContent=selected+' of '+games.length+' selected';
}
var _NFL_COACH_FILTER_STORAGE='nfl_coach_ui_filters_v3';
function _nflCoachReadFilterPrefs(){
  try{
    var raw=localStorage.getItem(_NFL_COACH_FILTER_STORAGE),saved=raw?JSON.parse(raw):null;
    if(saved&&Array.isArray(saved.sides)&&Array.isArray(saved.markets))return saved;
  }catch(e){}
  return {sides:['OVER','UNDER'],markets:null,rookieOnly:false};
}
window.__NFL_COACH_FILTER_PREFS__=_nflCoachReadFilterPrefs();
function _nflCoachSaveFilterPrefs(){
  var sides=[],markets=[],sideNodes=document.querySelectorAll('.nfl-coach-side-choice'),marketNodes=document.querySelectorAll('.nfl-coach-market-choice');
  sideNodes.forEach(function(cb){if(cb.checked)sides.push(String(cb.getAttribute('data-side')||'').toUpperCase());});
  marketNodes.forEach(function(cb){if(cb.checked)markets.push(decodeURIComponent(cb.getAttribute('data-market')||''));});
  var rookie=document.getElementById('nflCoachRookieOnly');
  window.__NFL_COACH_FILTER_PREFS__={sides:sides,markets:markets,rookieOnly:!!(rookie&&rookie.checked)};
  try{localStorage.setItem(_NFL_COACH_FILTER_STORAGE,JSON.stringify(window.__NFL_COACH_FILTER_PREFS__));}catch(e){}
}
function _nflCoachSelectionChanged(){_nflCoachSaveFilterPrefs();}
function _nflCoachSetSides(on){
  document.querySelectorAll('.nfl-coach-side-choice').forEach(function(cb){cb.checked=!!on;});
  _nflCoachSelectionChanged();
}
function _nflCoachSetMarkets(on){
  document.querySelectorAll('.nfl-coach-market-choice').forEach(function(cb){cb.checked=!!on;});
  _nflCoachSelectionChanged();
}
function _nflCoachOnlyMarket(label){
  document.querySelectorAll('.nfl-coach-market-choice').forEach(function(cb){
    cb.checked=decodeURIComponent(cb.getAttribute('data-market')||'')===String(label);
  });
  _nflCoachSelectionChanged();
}
function _nflCoachSetMarketFamily(family){
  document.querySelectorAll('.nfl-coach-market-choice').forEach(function(cb){
    var label=decodeURIComponent(cb.getAttribute('data-market')||'');
    cb.checked=_nflCoachFamily(label)===family;
  });
  _nflCoachSelectionChanged();
}
function _nflCoachRenderMarketFilters(){
  var box=document.getElementById('nflCoachMarkets'),quick=document.getElementById('nflCoachMarketQuick');
  if(!box||typeof _MORDER==='undefined')return;
  var labels=_MORDER.slice(),prefs=window.__NFL_COACH_FILTER_PREFS__||{},savedMarkets=Array.isArray(prefs.markets)?prefs.markets:null;
  var savedSides=Array.isArray(prefs.sides)?prefs.sides:null;
  document.querySelectorAll('.nfl-coach-side-choice').forEach(function(cb){
    cb.checked=savedSides===null||savedSides.indexOf(String(cb.getAttribute('data-side')||'').toUpperCase())>=0;
  });
  var rookie=document.getElementById('nflCoachRookieOnly');
  if(rookie)rookie.checked=prefs.rookieOnly===true;
  box.innerHTML=labels.map(function(label){
    var checked=savedMarkets===null||savedMarkets.indexOf(label)>=0;
    return '<label class="nfl-coach-filter-label"><input type="checkbox" class="nfl-coach-market-choice" data-market="'+encodeURIComponent(label)+'"'+(checked?' checked':'')+' onchange="_nflCoachSelectionChanged()"> '+_esc(label)+'</label>';
  }).join('');
  if(quick){
    quick.innerHTML='<span style="color:#64748b;font-size:.6rem;font-weight:900;align-self:center">ONE-CLICK EXACT:</span>'
      +labels.map(function(label){return '<button type="button" title="Show only '+_esc(label)+'" onclick="_nflCoachOnlyMarket(\\''+label+'\\')">'+_esc(label)+'</button>';}).join('')
      +'<button type="button" onclick="_nflCoachSetMarketFamily(\\'pass\\')">Passing family</button>'
      +'<button type="button" onclick="_nflCoachSetMarketFamily(\\'rush\\')">Rushing family</button>'
      +'<button type="button" onclick="_nflCoachSetMarketFamily(\\'rec\\')">Receiving family</button>'
      +'<button type="button" onclick="_nflCoachSetMarketFamily(\\'def\\')">Defense family</button>'
      +'<button type="button" onclick="_nflCoachSetMarketFamily(\\'kick\\')">Kicker family</button>'
      +'<button type="button" onclick="_nflCoachSetMarketFamily(\\'td\\')">TD family</button>';
  }
}
function _nflCoachSelectedSides(){
  var nodes=document.querySelectorAll('.nfl-coach-side-choice'),out=[];
  nodes.forEach(function(cb){if(cb.checked)out.push(String(cb.getAttribute('data-side')||'').toUpperCase());});
  return out;
}
function _nflCoachSelectedMarkets(){
  var nodes=document.querySelectorAll('.nfl-coach-market-choice'),out=[];
  nodes.forEach(function(cb){if(cb.checked)out.push(decodeURIComponent(cb.getAttribute('data-market')||''));});
  return out;
}
function _nflCoachVisibleProps(props){
  var markets=_nflCoachSelectedMarkets();
  var rookie=document.getElementById('nflCoachRookieOnly'),rookieOnly=!!(rookie&&rookie.checked);
  return (props||[]).filter(function(p){
    return markets.indexOf(String(p.market||''))>=0&&(!rookieOnly||p.isRookie===true);
  });
}
function _nflCoachFilterPayload(){
  _nflGameSync('coach');
  var games=_nflLoadedGames(),selected=games.filter(function(g){
    return _nflGameFilterOn('coach',g.key.split('|')[0],g.key.split('|')[1]);
  }).map(function(g){return g.key;});
  var rookie=document.getElementById('nflCoachRookieOnly');
  return {sides:_nflCoachSelectedSides(),markets:_nflCoachSelectedMarkets(),games:selected,rookie_only:!!(rookie&&rookie.checked)};
}
function _nflGameFilterHtml(scope){
  var games=_nflLoadedGames(),group=(window.__NFL_GAME_FILTERS__||{})[scope]||{};
  if(!games.length)return '<div class="nfl-parlay-cat-empty">Run today&#39;s picks to load games.</div>';
  return games.map(function(g){
    return '<label class="nfl-parlay-cat"><input class="nfl-game-choice" type="checkbox" data-scope="'+scope+'" data-key="'+encodeURIComponent(g.key)+'"'
      +(group[g.key]!==false?' checked':'')+' onchange="_nflGameSync(\\''+scope+'\\')"> <span>'+_esc(g.label)+'</span></label>';
  }).join('');
}
function _renderNflGameFilters(){
  var parlay=document.getElementById('nflParlayGames'),coach=document.getElementById('nflCoachGames');
  if(parlay)parlay.innerHTML=_nflGameFilterHtml('parlay');
  if(coach)coach.innerHTML=_nflGameFilterHtml('coach');
  _nflGameFilterSummary('parlay');
  _nflGameFilterSummary('coach');
}
function _nflNormalParlayCandidates(){
  var plays=window.__NFL_PLAYS__||[],out=[];
  plays.forEach(function(p){
    if(!p||!p.name||!p.pick)return;
    if(p.score==null||p.score<55)return;
    var c=_nflLeg(p);
    if(!c.dir)return;
    if(!_floorOk(c.odds))return;
    out.push(c);
  });
  return out;
}
function _nflCoachParlayCandidates(){
  if(typeof _nflCoachProps!=='function'||typeof _nflCoachSafest!=='function')return [];
  function leg(p){
    var dec=_amToDec(p.odds);
    return {player:p.player,team:p.team||'',opp:p.opponent||'',market:p.market||'NFL Prop',
      dir:p.side,line:p.line,rate:Math.round(p.appProb||0),odds:p.odds,dec:dec,hasOdds:!!dec,
      book:p.book||'Sportsbook line',edge:Number(p.edge||0),isAlternate:!!p.isAlternate,
      source:'coach',coachCats:[],detail:p.source||null,coachDetail:p};
  }
  function select(rows,sorter,limit){
    var seen={};
    return rows.slice().sort(sorter).filter(function(p){
      var key=String(p.player||'').trim().toLowerCase();
      if(!key||seen[key])return false;seen[key]=1;return true;
    }).slice(0,limit||5);
  }
  var allCoach=_nflCoachSafest(_nflCoachProps()).filter(function(p){
    return _nflGameFilterOn('parlay',p.team,p.opponent);
  });
  var positive=allCoach.filter(function(p){return p.edge>0;});
  var byEdge=function(a,b){return b.edge-a.edge||b.appProb-a.appProb;};
  var bySafe=function(a,b){return b.implied-a.implied||b.appProb-a.appProb;};
  var byProbability=function(a,b){return b.appProb-a.appProb||b.edge-a.edge;};
  var pools={
    safest_bets:select(positive,bySafe,5),
    coach_edge:select(positive,byEdge,5),
    passing:select(positive.filter(function(p){return _nflCoachFamily(p.market)==='pass';}),byEdge,5),
    rushing:select(positive.filter(function(p){return _nflCoachFamily(p.market)==='rush';}),byEdge,5),
    receiving:select(positive.filter(function(p){return _nflCoachFamily(p.market)==='rec';}),byEdge,5),
    defense:select(positive.filter(function(p){return _nflCoachFamily(p.market)==='def';}),byEdge,5),
    kicking:select(positive.filter(function(p){return _nflCoachFamily(p.market)==='kick';}),byEdge,5),
    td_scorers:select(allCoach.filter(function(p){return _nflCoachFamily(p.market)==='td'&&p.side==='OVER';}),byProbability,10),
    best_unders:select(positive.filter(function(p){return p.side==='UNDER';}),byEdge,5),
    alt_line_edge:((window.__NFL_ALT_PARLAY_DATE__===((document.getElementById('datePicker')||{}).value||window.__NFL_DATE__||''))
      ?(window.__NFL_ALT_PARLAY_CANDIDATES__||[]):[]).filter(function(p){
      return p&&_nflGameFilterOn('parlay',p.team,p.opponent)
        &&p.odds!=null&&p.odds>=-1000&&p.edge>0&&p.appProb>=85&&p.implied>=70;
    }).slice(0,10)
  },merged={};
  Object.keys(pools).forEach(function(cat){
    pools[cat].forEach(function(p){
      var c=leg(p),key=[c.player,c.market,c.dir,c.line,c.odds].join('|');
      if(!c.player||!c.dir||!_floorOk(c.odds))return;
      if(!merged[key])merged[key]=c;
      if(merged[key].coachCats.indexOf(cat)<0)merged[key].coachCats.push(cat);
    });
  });
  return Object.keys(merged).map(function(key){return merged[key];});
}
var _NFL_PARLAY_COACH_CATS=[
  {key:'safest_bets',label:'Safest Bets'},
  {key:'coach_edge',label:'Coach Edge'},
  {key:'alt_line_edge',label:'Best Alt-Line Edge Plays · Top 10'},
  {key:'passing',label:'Passing'},
  {key:'rushing',label:'Rushing'},
  {key:'receiving',label:'Receiving'},
  {key:'defense',label:'Best Defense Plays'},
  {key:'kicking',label:'Best Kicker Plays'},
  {key:'td_scorers',label:'TD Scorers'},
  {key:'best_unders',label:'Best Unders'}
  ,{key:'coach_over_movement',label:'Biggest Over Line Movement'}
  ,{key:'coach_under_movement',label:'Biggest Under Line Movement'}
];
window.__NFL_PARLAY_FILTERS__={normal:{},coach:{}};
window.__NFL_PARLAY_ODDS_MODE__='all';
function _nflParlaySetOddsMode(mode){
  window.__NFL_PARLAY_ODDS_MODE__=(mode==='plus'||mode==='minus')?mode:'all';
  [['all','nflParlayOddsAll'],['plus','nflParlayOddsPlus'],['minus','nflParlayOddsMinus']].forEach(function(item){
    var active=window.__NFL_PARLAY_ODDS_MODE__===item[0],btn=document.getElementById(item[1]);
    if(!btn)return;
    btn.style.background=active?'#f59e0b':'#1f2937';
    btn.style.color=active?'#111827':'#e5e7eb';
    btn.style.borderColor=active?'#f59e0b':'#374151';
    btn.setAttribute('aria-pressed',active?'true':'false');
  });
  closeParlay();
}
function _nflParlayOddsAllowed(odds){
  var mode=window.__NFL_PARLAY_ODDS_MODE__||'all',value=parseFloat(odds);
  if(mode==='all')return true;
  if(!isFinite(value)||value===0)return false;
  return mode==='plus'?value>0:value<0;
}
function _nflParlayFilterOn(source,key){
  var group=(window.__NFL_PARLAY_FILTERS__||{})[source]||{};
  return group[key]!==false;
}
function _nflParlaySyncFilters(){
  document.querySelectorAll('.nfl-parlay-cat input[data-source]').forEach(function(cb){
    var source=cb.getAttribute('data-source'),key=decodeURIComponent(cb.getAttribute('data-key')||'');
    if(!window.__NFL_PARLAY_FILTERS__[source])window.__NFL_PARLAY_FILTERS__[source]={};
    window.__NFL_PARLAY_FILTERS__[source][key]=!!cb.checked;
  });
}
function _nflParlaySetAll(source,on){
  document.querySelectorAll('.nfl-parlay-cat input[data-source="'+source+'"]').forEach(function(cb){cb.checked=!!on;});
  _nflParlaySyncFilters();
}
function _nflParlayCategoryHtml(source,cands){
  if(source==='coach'){
    return _NFL_PARLAY_COACH_CATS.map(function(cat){
      return '<label class="nfl-parlay-cat"><input type="checkbox" data-source="coach" data-key="'+encodeURIComponent(cat.key)+'"'+(_nflParlayFilterOn('coach',cat.key)?' checked':'')+' onchange="_nflParlaySyncFilters()"> <span>'+_esc(cat.label)+'</span></label>';
    }).join('');
  }
  var seen={},cats=[];
  (cands||[]).forEach(function(c){var key=_nflParlayCatKey(c);if(!seen[key]){seen[key]=1;cats.push({key:key,label:_nflParlayCatLabel(c)});}});
  cats.sort(function(a,b){return a.label.localeCompare(b.label);});
  if(!cats.length)return '<div class="nfl-parlay-cat-empty">'+(source==='coach'?'No positive Coach Edge categories are available on this loaded board.':'No qualifying normal categories are available.')+'</div>';
  return cats.map(function(cat){
    return '<label class="nfl-parlay-cat"><input type="checkbox" data-source="'+source+'" data-key="'+encodeURIComponent(cat.key)+'"'+(_nflParlayFilterOn(source,cat.key)?' checked':'')+' onchange="_nflParlaySyncFilters()"> <span>'+_esc(cat.label)+'</span></label>';
  }).join('');
}
function _renderNflParlayFilters(){
  var normal=document.getElementById('nflParlayNormalCats'),coach=document.getElementById('nflParlayCoachCats');
  _renderNflGameFilters();
  if(normal)normal.innerHTML=_nflParlayCategoryHtml('normal',_nflNormalParlayCandidates());
  if(coach)coach.innerHTML=_nflParlayCategoryHtml('coach',_nflCoachParlayCandidates());
}
function _parlayPool(){
  _nflParlaySyncFilters();
  var combined=_nflNormalParlayCandidates().concat(_nflCoachParlayCandidates()).filter(function(c){
    if(!_nflGameFilterOn('parlay',c.team,c.opp))return false;
    if(!_nflParlayOddsAllowed(c.odds))return false;
    if(c.source==='coach'){
      return (c.coachCats||[]).some(function(cat){return _nflParlayFilterOn('coach',cat);});
    }
    return _nflParlayFilterOn('normal',_nflParlayCatKey(c));
  }),byP={};
  combined.forEach(function(c){
    var cur=byP[c.player];
    if(!cur||_legScore(c)>_legScore(cur))byP[c.player]=c;
  });
  return Object.keys(byP).map(function(k){return byP[k];}).sort(function(a,b){return _legScore(b)-_legScore(a);});
}
function _shuffle(a){for(var i=a.length-1;i>0;i--){var j=Math.floor(Math.random()*(i+1));var t=a[i];a[i]=a[j];a[j]=t;}return a;}
function closeParlay(){var o=document.getElementById('parlayResult');if(o)o.innerHTML='';}
function buildParlay(){_renderParlay(false);}
function generateParlay(){_renderParlay(true);}
function _renderParlay(randomize){
  var sel=document.getElementById('parlayLegs');
  var n=parseInt(sel?sel.value:'3',10)||3;
  var out=document.getElementById('parlayResult');
  if(!out)return;
  var cands=_parlayPool();
  if(!cands.length){out.innerHTML='<div style="color:#888;padding:10px">No qualifying plays match the selected games and categories.</div>';return;}
  if(cands.length<n){out.innerHTML='<div style="color:#f87171;padding:10px">Only '+cands.length+' qualifying play'+(cands.length!==1?'s':'')+' on the board. Pick a smaller parlay.</div>';return;}
  function _pick(ordered,avoid){var used={},picked=[],i,c;for(i=0;i<ordered.length&&picked.length<n;i++){c=ordered[i];if(used[c.player])continue;if(avoid&&avoid[c.player])continue;used[c.player]=1;picked.push(c);}for(i=0;i<ordered.length&&picked.length<n;i++){c=ordered[i];if(used[c.player])continue;used[c.player]=1;picked.push(c);}return picked;}
  var legs;
  if(randomize){var avoid=null;if(window._lastParlay&&window._lastParlay.length){avoid={};window._lastParlay.forEach(function(pl){avoid[pl]=1;});}legs=_pick(_shuffle(cands.slice()),avoid).sort(function(a,b){return _legScore(b)-_legScore(a);});}
  else{legs=_pick(cands.slice(),null);}
  window._lastParlay=legs.map(function(l){return l.player;});
  window._nflParlayLegs=legs;
  window._nflParlayMode=randomize?'RANDOM MIX':'TOP PLAYS';
  _paintNflParlay();
}
function _paintNflParlay(){
  var out=document.getElementById('parlayResult');
  if(!out)return;
  var legs=window._nflParlayLegs||[],n=legs.length;
  var dec=1,priced=0,missing=0;
  legs.forEach(function(l){if(l.dec){dec*=l.dec;priced++;}else{missing++;}});
  var am=priced?_decToAm(dec):null;var payout=priced?(100*dec):null;
  var dirColor=function(d){return d==='OVER'?'#4ade80':d==='UNDER'?'#f87171':'#9ca3af';};
  var rows=legs.map(function(l,i){var fo=_fmtOdds(l.odds);return '<div role="button" tabindex="0" onclick="_openNflParlayLeg('+i+')" onkeydown="if(event.key===\\'Enter\\'||event.key===\\' \\'){event.preventDefault();_openNflParlayLeg('+i+')}" title="Open player matchup details" style="display:flex;justify-content:space-between;align-items:center;gap:10px;padding:10px 12px;border-bottom:1px solid #1a1a1a;cursor:pointer">'
    +'<div style="min-width:0">'
    +'<div style="font-weight:800;color:#fff;font-size:.85rem">'+(i+1)+'. '+l.player+' <span style="color:#777;font-size:.7rem">'+l.team+(l.opp?(' vs '+l.opp):'')+'</span><span class="nfl-parlay-source '+(l.source==='coach'?'coach':'normal')+'">'+(l.source==='coach'?'COACH EDGE':'NORMAL')+'</span></div>'
    +'<div style="color:#999;font-size:.72rem;margin-top:2px">'+l.market+(l.line!=null?(' · line '+l.line):'')+(l.rate?(' · '+l.rate+'% hit'):'')+'</div>'
    +'</div>'
    +'<div style="display:flex;align-items:center;gap:8px;white-space:nowrap">'
    +'<div style="text-align:right">'
    +'<div style="color:'+dirColor(l.dir)+';font-weight:900;font-size:.8rem">'+l.dir+'</div>'
    +'<div style="color:#f59e0b;font-size:.72rem;font-weight:800">'+(fo||'odds N/A')+' · '+_esc(l.book||'Book unavailable')+'</div>'
    +'</div>'
    +'<button id="nflrep'+i+'" onclick="event.stopPropagation();_replaceNflParlayLeg('+i+')" title="Swap this leg for another play" style="background:#1e3a8a;color:#bfdbfe;border:1px solid #1d4ed8;border-radius:7px;padding:4px 9px;font-size:.85rem;cursor:pointer;font-weight:800;line-height:1;flex-shrink:0">&#8635;</button>'
    +'</div></div>';}).join('');
  var header='<div style="display:flex;justify-content:space-between;align-items:center;padding:8px 12px;border-bottom:1px solid #262626;background:#121212">'
    +'<span style="font-weight:800;color:#ccc;font-size:.74rem">'+(window._nflParlayMode||'TOP PLAYS')+'</span>'
    +'<span onclick="closeParlay()" title="Close" style="cursor:pointer;color:#888;font-weight:900;font-size:1.15rem;line-height:1;padding:0 6px">×</span></div>';
  var summary='<div style="display:flex;justify-content:space-between;align-items:center;padding:12px;background:linear-gradient(135deg,rgba(245,158,11,.12),rgba(245,158,11,.02));border-top:1px solid #262626">'
    +'<div style="font-weight:900;color:#f59e0b">'+n+'-LEG PARLAY</div>'
    +'<div style="text-align:right">'+(am?('<div style="font-weight:900;color:#4ade80;font-size:1.05rem">'+am+'</div><div style="color:#999;font-size:.7rem">$100 → $'+payout.toFixed(2)+(missing?(' · '+priced+'/'+n+' legs priced'):'')+'</div>'):('<div style="color:#888;font-size:.78rem">No book odds available for these legs</div>'))+'</div>'
    +'</div>';
  out.innerHTML='<div style="background:#0e0e0e;border:1px solid #262626;border-radius:12px;overflow:hidden">'+header+rows+summary+'</div>';
}
function _openNflParlayLeg(idx){
  var leg=(window._nflParlayLegs||[])[idx];if(!leg)return;
  if(leg.source==='coach'&&leg.coachDetail&&typeof _nflCoachAccordions==='function'){
    var p=leg.coachDetail;
    var why='<div style="background:rgba(34,197,94,.08);border:1px solid rgba(34,197,94,.25);border-radius:10px;padding:11px 12px;margin:10px 0 14px;color:#cbd5e1;font-size:.78rem;line-height:1.5">'
      +'<b style="color:#86efac">Why this parlay leg:</b> This was a positive Coach Edge candidate that passed your game, category, and odds filters. '
      +'Model probability is <b>'+Number(p.appProb||0).toFixed(1)+'%</b>, sportsbook-implied probability is <b>'+Number(p.implied||0).toFixed(1)+'%</b>, and Coach Edge is <b>'+_nflCoachSigned(Number(p.edge||0))+' points</b>.'
      +'</div>';
    _openModal(_esc(p.player),_esc(p.market)+' · '+_esc(p.team)+' vs '+_esc(p.opponent)+' · '+p.side+' '+p.line+' · '+_nflCoachOdds(p.odds)+' · '+_esc(p.book||'Sportsbook line'),why+_nflCoachAccordions(p));
    return;
  }
  if(leg.detail){
    var key='nfl_parlay_'+idx;
    var detail=Object.assign({},leg.detail,{
      pick:leg.dir,dispLine:leg.line,realLine:leg.line,
      parlayWhy:'Selected after your game, category, and odds filters as one of the strongest remaining eligible plays. Displayed ranking rate: '+Number(leg.rate||0).toFixed(0)+'%.'
    });
    window.__NFLLAD__[key]=detail;
    openNflLadder(key);
  }
}
function _replaceNflParlayLeg(idx){
  var legs=window._nflParlayLegs;
  if(!legs||!legs[idx])return;
  var current=legs[idx],used={};
  legs.forEach(function(l,i){if(i!==idx)used[l.player]=1;});
  var pool=_parlayPool().filter(function(c){
    return c.player!==current.player&&!used[c.player];
  });
  if(!pool.length){_flashNoNflSwap(idx);return;}
  legs[idx]=pool[Math.floor(Math.random()*pool.length)];
  window._lastParlay=legs.map(function(l){return l.player;});
  _paintNflParlay();
}
function _flashNoNflSwap(idx){
  var b=document.getElementById('nflrep'+idx);
  if(!b)return;
  var old=b.innerHTML;
  b.innerHTML='none';b.style.background='#374151';b.style.color='#9ca3af';
  setTimeout(function(){b.innerHTML=old;b.style.background='#1e3a8a';b.style.color='#bfdbfe';},1000);
}

var jobId=null, pollTimer=null, _pollBusy=false;
var _nflSystemGeneration=0,_nflPollSeq=0,_nflPicksSeq=0,
    _nflCoachTrackLoadSeq=0,_nflGpRecordLoadSeq=0,_nflHistoryLoadSeq=0,
    _nflHistSeasonLoadSeq=0,_nflActiveControllers=[];
function _nflRequestCurrent(generation,system){
  return generation===_nflSystemGeneration&&system===_nflSystem();
}
function _nflTrackController(controller){
  if(controller)_nflActiveControllers.push(controller);
  return controller;
}
function _nflUntrackController(controller){
  var i=_nflActiveControllers.indexOf(controller);
  if(i>=0)_nflActiveControllers.splice(i,1);
}
function _nflRestoreRunButton(){
  var btn=document.getElementById('runBtn');
  if(btn){btn.disabled=false;btn.textContent='Run Picks';}
}
function _nflSystem(){
  var el=document.getElementById('nflSystem');
  return el&&el.value==='NEW'?'NEW':'OLD';
}
function _nflSystemChanged(){
  if(typeof _nflPerfectParlayInvalidate==='function')_nflPerfectParlayInvalidate('system');
  var s=_nflSystem(),badge=document.getElementById('nflSystemBadge');
  if(badge){badge.textContent='SYSTEM: '+s;badge.style.color=s==='NEW'?'#67e8f9':'#fbbf24';}
  ['nflCoachSystemBadge','nflTrackSystemBadge','nflOverflowSystemBadge'].forEach(function(id){
    var b=document.getElementById(id);if(b){b.textContent='SYSTEM: '+s;b.style.color=s==='NEW'?'#67e8f9':'#fbbf24';}
  });
  var status=document.getElementById('statusMsg');
  if(status)status.textContent=s==='NEW'?'NEW model selected — isolated cache and record.':'OLD model selected — legacy behavior.';
  _nflSystemGeneration++;
  _nflPollSeq++;_nflPicksSeq++;_nflCoachTrackLoadSeq++;
  _nflGpRecordLoadSeq++;_nflHistoryLoadSeq++;_nflHistSeasonLoadSeq++;
  _nflTrkLoadSeq++;_nflOvfLoadSeq++;
  window.__NFL_ALT_COACH_SEQ__=(window.__NFL_ALT_COACH_SEQ__||0)+1;
  _nflRestoreRunButton();
  _nflActiveControllers.splice(0).forEach(function(c){try{c.abort();}catch(e){}});
  clearInterval(pollTimer);pollTimer=null;jobId=null;
  window.__NFL_COACH_VIEW_SEQ__=(window.__NFL_COACH_VIEW_SEQ__||0)+1;
  window.__NFL_COACH_CAPTURE_SEQ__=(window.__NFL_COACH_CAPTURE_SEQ__||0)+1;
  if(window.__NFL_ALT_COACH_RUN__){
    window.__NFL_ALT_COACH_RUN__.cancelled=true;
    try{window.__NFL_ALT_COACH_RUN__.requestController.abort();}catch(e){}
  }
  window._nflState=null;window.__NFL_PLAYS__=[];window.__NFLLAD__={};
  window.__NFL_GP__=[];window.__NFL_GP_BET__={};window.__NFL_BET_SRC__={};
  window.__NFL_ALT_PARLAY_CANDIDATES__=[];window.__NFL_ALT_PARLAY_DATE__='';
  window.__NFL_LAST_ALT_COACH__=[];window.__NFL_LAST_ALT_COACH_DATE__='';
  window.__NFL_MYBETS__=null;window._lastParlay=null;window._nflParlayLegs=[];
  _nflCoachTrackData=null;_nflTrkData=null;_nflOvfData=null;
  _nflTrkReplayDate='';_nflCoachTrackTabMode='cat';_nflTrkTabMode='cat';_nflOvfTabMode='cat';
  ['results','nflBody','nflCoachAnswer','nflCoachCaptureStatus','nflCoachTrackSummary',
   'nflCoachTrackBody','nflTrkSummary','nflTrkBody','nflOvfSummary','nflOvfBody',
   'nflGpTrkSummary','nflGpTrkBody','parlayResult','nflMyBetsBody',
   'nflHistoricalBody'].forEach(function(id){
     var el=document.getElementById(id);if(el)el.innerHTML='';
   });
  ['nfl-gp-modal','nfl-bet-modal','nfl-ladder-modal'].forEach(function(id){
    var el=document.getElementById(id);if(el)el.style.display='none';
  });
  ['nflTrkSource','nflOvfSource','nflCoachTrkSource'].forEach(function(id){
    var el=document.getElementById(id);if(el)el.value='official';
  });
  if(typeof _nflCoachTrackAwaitingSelection==='function')_nflCoachTrackAwaitingSelection();
  if(typeof _nflCoachRender==='function')_nflCoachRender('',[],0,'edge',false);
  if(typeof closeParlay==='function')closeParlay();
}

function _nflRunScope(){
  var el=document.getElementById('runScope');
  return el&&el.value==='week'?'week':'day';
}
function _nflTodayLocal(){
  var d=new Date(),y=d.getFullYear(),m=String(d.getMonth()+1).padStart(2,'0'),day=String(d.getDate()).padStart(2,'0');
  return y+'-'+m+'-'+day;
}
function _nflRunScopeChanged(){
  if(typeof _nflPerfectParlayInvalidate==='function')_nflPerfectParlayInvalidate('scope');
  var hint=document.getElementById('runScopeHint'),week=_nflRunScope()==='week';
  if(hint)hint.textContent=week
    ?'Runs the NFL week containing this date: Wednesday through Tuesday, including Monday Night Football.'
    :'Runs only the selected calendar date.';
}

async function runPicks(){
  if(document.getElementById('runBtn').disabled)return;
  var date=document.getElementById('datePicker').value;
  var scope=_nflRunScope();
  if(!date){alert('Please select a date');return;}
  var requestedSystem=_nflSystem(),requestGeneration=_nflSystemGeneration,
      requestSeq=++_nflPicksSeq,requestController=_nflTrackController(new AbortController());
  var btn=document.getElementById('runBtn');
  var status=document.getElementById('statusMsg');
  btn.disabled=true;
  btn.innerHTML='<span class="spinner"></span>Running...';
  status.innerHTML='<span class="spinner"></span>'+(scope==='week'
    ?'Running the full Wednesday–Tuesday NFL week...'
    :'Fetching prop lines and loading NFL stats...');
  document.getElementById('results').innerHTML='';
  try{
    const r=await fetch('/api/run',{method:'POST',headers:{'Content-Type':'application/json'},
      signal:requestController.signal,
      body:JSON.stringify({date:date,scope:scope,system:requestedSystem,token:_nflTok})});
    const d=await r.json();
    if(requestSeq!==_nflPicksSeq||!_nflRequestCurrent(requestGeneration,requestedSystem)){
      _nflRestoreRunButton();return;
    }
    if(!r.ok || !d.job_id)throw new Error(d.detail||d.error||'Could not start run');
    jobId=d.job_id;
    _pollFails=0;
    clearInterval(pollTimer);
    pollTimer=setInterval(pollJob,2500);
  }catch(e){
    if(requestSeq!==_nflPicksSeq||!_nflRequestCurrent(requestGeneration,requestedSystem)){
      _nflRestoreRunButton();return;
    }
    status.textContent='Error: '+e.message;
    btn.disabled=false;btn.textContent='Run Picks';
  }finally{_nflUntrackController(requestController);}
}

var _pollFails=0;
async function pollJob(){
  if(!jobId || _pollBusy)return;
  _pollBusy=true;
  var requestedSystem=_nflSystem(),requestGeneration=_nflSystemGeneration,
      requestSeq=++_nflPollSeq;
  const controller=new AbortController();
  _nflTrackController(controller);
  let requestTimer=setTimeout(()=>controller.abort(),15000);
  var pollPhase='status';
  try{
    const r=await fetch('/api/run/'+jobId+'?status_only=true',{signal:controller.signal,cache:'no-store'});
    if(requestSeq!==_nflPollSeq||!_nflRequestCurrent(requestGeneration,requestedSystem)){
      _nflRestoreRunButton();return;
    }
    if(!r.ok){
      // 404 = job gone (server restarted mid-run); stop and tell user
      if(r.status===404){
        clearInterval(pollTimer);
        document.getElementById('statusMsg').textContent='Server restarted mid-run — please try again.';
        document.getElementById('runBtn').disabled=false;
        document.getElementById('runBtn').textContent='Run Picks';
        return;
      }
      throw new Error('Status request failed: HTTP '+r.status);
    }
    let d=await r.json();
    if(d.status==='done'){
      pollPhase='download';
      clearTimeout(requestTimer);
      requestTimer=setTimeout(()=>controller.abort(),60000);
      document.getElementById('statusMsg').textContent='Analysis complete — downloading saved results…';
      const resultResponse=await fetch('/api/run/'+jobId,{signal:controller.signal,cache:'no-store'});
      if(!resultResponse.ok)throw new Error('Completed results: HTTP '+resultResponse.status);
      d=await resultResponse.json();
    }
    if(requestSeq!==_nflPollSeq||!_nflRequestCurrent(requestGeneration,requestedSystem)
       ||(d.result&&String(d.result.system||'OLD')!==requestedSystem)){
      _nflRestoreRunButton();return;
    }
    _pollFails=0;
    if(d.status==='done'){
      pollPhase='display';
      clearInterval(pollTimer);
      renderResults(d.result);
      if(d.result&&d.result.historicalTrackRecord){
        _nflTrkReplayDate=d.result.date||'';
        _nflTrkData=d.result.historicalTrackRecord;
        var replaySource=document.getElementById('nflTrkSource');
        if(replaySource) replaySource.value='historical';
        var replayDate=document.getElementById('nflTrkDate');
        if(replayDate) replayDate.value=d.result.date||'';
        _nflTrkDayName();
        renderNflTrackDay();
        renderNflGpRecord();
      }
      document.getElementById('runBtn').disabled=false;
      document.getElementById('runBtn').textContent='Run Picks';
      document.getElementById('statusMsg').textContent=
        d.result&&d.result.week_mode
          ?'Full NFL week loaded. The scheduled opening snapshot was saved only for the eligible game date: Wednesday→Thursday, Friday→Sunday, or Saturday→Monday.'
          :
        d.result&&d.result.historicalTrackRecord
          ?'HISTORICAL REPLAY — this run excludes the selected date from model inputs and is excluded from the official Track Record.'
          :d.result&&d.result.official_tracking===false
          ?'VIEW ONLY — this run was not captured before every kickoff and is excluded from the official Track Record.'
          :'Official pre-game snapshot saved for Track Record grading.';
    }else if(d.status==='error'){
      clearInterval(pollTimer);
      document.getElementById('statusMsg').textContent='Error: '+(d.error||'Unknown error');
      document.getElementById('runBtn').disabled=false;
      document.getElementById('runBtn').textContent='Run Picks';
    }else{
      var prog=(d.progress||'Analyzing player histories...').replace(/</g,'&lt;');
      document.getElementById('statusMsg').innerHTML='<span class="spinner"></span>'+prog;
    }
  }catch(e){
    if(requestSeq!==_nflPollSeq||!_nflRequestCurrent(requestGeneration,requestedSystem)){
      _nflRestoreRunButton();return;
    }
    if(pollPhase==='display'){
      clearInterval(pollTimer);pollTimer=null;
      _nflRestoreRunButton();
      document.getElementById('statusMsg').textContent='Analysis completed, but displaying the board failed: '+(e.message||String(e))+'. Results remain saved; use Get Picks.';
      console.error('NFL result display failed',e);
      return;
    }
    // A long full-week job can briefly miss status requests while the service
    // is under load. Never abandon the known server job on a transient network
    // error; only a confirmed 404 above means the job was lost to a restart.
    _pollFails++;
    if(_pollFails<5){
      document.getElementById('statusMsg').textContent='Waiting for server status — retry '+_pollFails+'/5. The last progress update may be stale.';
    }else{
      document.getElementById('statusMsg').textContent='Retrying '+pollPhase+' for the same job — attempt '+_pollFails+'. '+(e.name==='AbortError'?'Request timed out.':(e.message||String(e)))+' No new analysis has been started.';
    }
  }finally{
    clearTimeout(requestTimer);
    _nflUntrackController(controller);
    _pollBusy=false;
  }
}

// Get Picks loads today's saved board, or builds a view-only replay for a past date.
async function getPicks(){
  var date=document.getElementById('datePicker').value;
  var scope=_nflRunScope();
  if(!date){alert('Please select a date');return;}
  var requestedSystem=_nflSystem(),requestGeneration=_nflSystemGeneration,
      requestSeq=++_nflPicksSeq,requestController=_nflTrackController(new AbortController());
  var btn=document.getElementById('getBtn');
  var status=document.getElementById('statusMsg');
  var orig=btn.textContent;
  var isHistorical=scope==='day'&&date<_nflTodayLocal();
  btn.disabled=true;
  btn.innerHTML='<span class="spinner"></span>'+(isHistorical?'Replaying...':'Loading...');
  status.innerHTML='<span class="spinner"></span>'+(scope==='week'
    ?'Loading saved Wednesday–Tuesday boards...'
    :isHistorical
    ?'Building point-in-time picks and grading the historical results...'
    :'Loading saved picks...');
  document.getElementById('results').innerHTML='';
  try{
    var url=isHistorical
       ?'/api/picks?target_date='+encodeURIComponent(date)+'&simulate=true&system='+encodeURIComponent(requestedSystem)+'&token='+encodeURIComponent(_nflTok)
       :'/api/cached?target_date='+encodeURIComponent(date)+'&scope='+encodeURIComponent(scope)+'&system='+encodeURIComponent(requestedSystem)+'&token='+encodeURIComponent(_nflTok);
    var r=await fetch(url,{signal:requestController.signal,cache:'no-store'});
    if(requestSeq!==_nflPicksSeq||!_nflRequestCurrent(requestGeneration,requestedSystem))return;
    if(r.status===404){
      var missing=await r.json().catch(function(){return{};});
      status.textContent=missing.detail||('No saved '+requestedSystem+' picks for '+date+'.');
      return;
    }
    if(!r.ok){
      var er=await r.json().catch(function(){return{};});
      throw new Error(er.detail||('Server error '+r.status));
    }
    var d=await r.json();
    if(requestSeq!==_nflPicksSeq||!_nflRequestCurrent(requestGeneration,requestedSystem)
       ||String(d.system||'OLD')!==requestedSystem)return;
    if(d.error) throw new Error(d.error);
    renderResults(d);
    if(isHistorical&&d.historicalTrackRecord){
      _nflTrkReplayDate=date;
      _nflTrkData=d.historicalTrackRecord;
      var replaySource=document.getElementById('nflTrkSource');
      if(replaySource) replaySource.value='historical';
      var trkDate=document.getElementById('nflTrkDate');
      if(trkDate)trkDate.value=date;
      _nflTrkDayName();
      renderNflTrackDay();
      renderNflGpRecord();
      document.getElementById('nfl-gp-record-section').scrollIntoView({behavior:'smooth',block:'start'});
    }
    status.textContent=isHistorical
      ?'HISTORICAL REPLAY — picks and results reconstructed for '+date+'; not added to the official record'
       :(d.saved_board?'Loaded saved '+requestedSystem+' picks for '+date+' — saved prices, not a fresh odds update.':'');
  }catch(e){
    if(requestSeq!==_nflPicksSeq||!_nflRequestCurrent(requestGeneration,requestedSystem))return;
    status.textContent='Error: '+e.message;
  }finally{
    _nflUntrackController(requestController);
    btn.disabled=false; btn.textContent=orig;
  }
}

// ===== NBA-style cards (NFL) =====
window.__NFLLAD__ = window.__NFLLAD__ || {};
var _MORDER=['Pass Yds','Pass TDs','Completions','Pass Att','INT Thrown','Rush Yds','RB Total Yds','Rush Att','Rec Yds','Receptions','Anytime TD','Tackles+Ast','Sacks','Def INT','Kick Pts','FG Made'];
var _MLBL={'Pass Yds':'Pass','Pass TDs':'Pass TD','Completions':'Comp','Pass Att':'Att','INT Thrown':'INT','Rush Yds':'Rush','RB Total Yds':'Total Yds','Rush Att':'Carries','Rec Yds':'Rec','Receptions':'Recept','Anytime TD':'TD','Tackles+Ast':'Tkl','Sacks':'Sacks','Def INT':'D INT','Kick Pts':'K Pts','FG Made':'FG'};
_nflCoachRenderMarketFilters();

function _nflGameDone(p){
  var s=p&&p.game_start; if(!s) return false;
  var t=new Date(s).getTime(); if(!t||isNaN(t)) return false;
  // A saved board is a betting view: once a game kicks off its picks are no
  // longer actionable, while later-game snapshots remain available.
  if(window._nflState&&window._nflState.d&&window._nflState.d.week_mode)
    return Date.now() >= t;
  // Only auto-hide finished games on TODAY'S live slate. When browsing a
  // past date every game is long over — show ALL picks (historical review).
  var d=new Date(t), now=new Date();
  if(d.toDateString()!==now.toDateString()) return false;
  return Date.now() >= t;
}
function rateClass(r){ return r >= 70 ? 'green' : r >= 55 ? 'gold' : 'red-txt'; }
function _initials(name){
  var parts=String(name||'').trim().split(/\s+/);
  if(!parts.length||!parts[0]) return '?';
  if(parts.length===1) return parts[0].slice(0,2).toUpperCase();
  return (parts[0][0]+parts[parts.length-1][0]).toUpperCase();
}
function _accFor(mkt){
  if(mkt==='Rush Yds'||mkt==='RB Total Yds'||mkt==='Rush Att') return 'acc-rush';
  if(mkt==='Rec Yds') return 'acc-rec';
  if(mkt==='Pass Yds'||mkt==='Completions'||mkt==='Pass Att'||mkt==='INT Thrown') return 'acc-pass';
  if(mkt==='Receptions') return 'acc-recpt';
  if(mkt==='Anytime TD') return 'acc-td';
  if(mkt==='Pass TDs') return 'acc-ptd';
  if(mkt==='Tackles+Ast'||mkt==='Sacks'||mkt==='Def INT') return 'acc-def';
  if(mkt==='Kick Pts'||mkt==='FG Made') return 'acc-kick';
  return 'acc-pass';
}
function _mIcon(mkt){
  if(mkt==='Rush Yds') return '🏈';
  if(mkt==='RB Total Yds') return '🏈';
  if(mkt==='Rush Att') return '🏃';
  if(mkt==='Rec Yds') return '🙌';
  if(mkt==='Pass Yds') return '🎯';
  if(mkt==='Completions') return '✅';
  if(mkt==='Pass Att') return '📨';
  if(mkt==='INT Thrown') return '🛑';
  if(mkt==='Receptions') return '🧤';
  if(mkt==='Anytime TD') return '🏆';
  if(mkt==='Pass TDs') return '💣';
  if(mkt==='Tackles+Ast') return '🛡️';
  if(mkt==='Sacks') return '💥';
  if(mkt==='Def INT') return '🧲';
  if(mkt==='Kick Pts') return '🦵';
  if(mkt==='FG Made') return '🥅';
  return '🏈';
}
function _logoAbbr(t){
  var m={'LA':'lar','LAR':'lar','LAC':'lac','WAS':'wsh','WSH':'wsh','JAC':'jax','JAX':'jax','OAK':'lv','LV':'lv','SD':'lac','STL':'lar'};
  var k=String(t||'').toUpperCase();
  return (m[k]||k.toLowerCase());
}
function _ladKey(p){ return 'flad_'+p.pid+'_'+String(p.mkt||'').replace(/[^a-z]/gi,''); }
function _rateHtml(rate,hits,tot){
  if(!tot) return '<span class="gray">—</span>';
  var n=Number(rate),valid=isFinite(n),pct=valid?n.toFixed(1)+'%':'--';
  var sample=(hits==null||hits===''||!isFinite(Number(hits)))
    ?tot+' games'
    :Math.round(Number(hits))+'/'+tot;
  return '<span class="'+(valid?rateClass(n):'gray')+'">'+sample+' ('+pct+')</span>';
}
function fmtTag(t){
  if(t==='SUGGESTED') return '<span class="tag-sug">⭐ PICK</span>';
  if(t==='FADE')      return '<span class="tag-fade">⚠ FADE</span>';
  return '';
}
function fmtGap(g){
  if(g===null||g===undefined) return '<span class="gap-zero">—</span>';
  var cls = g>0?'gap-pos':(g<0?'gap-neg':'gap-zero');
  var sign = g>0?'+':'';
  return '<span class="'+cls+'">'+sign+g+'</span>';
}
function _nflSideOdds(p,side){
  side=side||(p&&p.pick)||'OVER';
  if(side==='UNDER') return p&&p.realUnderOdds!=null?p.realUnderOdds:null;
  return p&&p.realOdds!=null?p.realOdds:null;
}
function _nflSideBook(p,side){
  side=side||(p&&p.pick)||'OVER';
  return String((side==='UNDER'?(p&&p.under_book):(p&&p.over_book))||'Book unavailable');
}
function _nflIsRoiFocusPick(p){
  var odds=_nflSideOdds(p,'UNDER');
  return !!p&&p.pick==='UNDER'&&odds!=null&&Number(odds)>=-150;
}
function fmtVsLine(p){
  if(p.realLine==null||!p.vsLineTotal) return '<span class="gray">—</span>';
  var n=Number(p.vsLineRate),valid=isFinite(n);
  var sample=(p.vsLineHits==null||p.vsLineHits===''||!isFinite(Number(p.vsLineHits)))
    ?p.vsLineTotal+' games'
    :Math.round(Number(p.vsLineHits))+'/'+p.vsLineTotal;
  return '<span class="'+(valid?rateClass(n):'gray')+'">'+sample+' ('+(valid?n.toFixed(1)+'%':'--')+')</span>';
}
function _nflOppVenueLabel(p){
  var side=String((p&&p.pick)||'PICK').toUpperCase();
  return side+' vs '+String((p&&p.opponent)||'Opponent')+' · all meetings';
}
function _nflRecentVenueLabel(p){
  var side=String((p&&p.pick)||'PICK').toUpperCase();
  if(p&&p.homeRoad==='R')return side+' · L10 Away';
  if(p&&p.homeRoad==='H')return side+' · L10 Home';
  return side+' · L10 H/A';
}
function _nflDefenseSplitHtml(p){
  var statLabels={
    player_pass_yds:'passing yards',player_pass_tds:'passing TDs',
    player_pass_completions:'completions',player_pass_attempts:'pass attempts',
    player_pass_interceptions:'interceptions thrown',
    player_rush_yds:'rushing yards',player_rush_attempts:'carries',
    player_rush_reception_yds:'rushing + receiving yards',
    player_reception_yds:'receiving yards',player_receptions:'receptions',
    player_anytime_td:'rushing + receiving TDs'
  };
  var m=_esc(statLabels[String(p&&p.market||'')]||String(p&&p.mkt||'stat').replace(/Yds/gi,'yards').toLowerCase());
  var pg=_esc(String(p&&p.defPositionGroup||p&&p.positionGroup||p&&p.position||'position').toUpperCase());
  var o=_esc((p&&p.opponent)||'Opponent');
  var line=p&&p.realLine!=null?p.realLine:p.dispLine;
   if(p&&p.defSchemaVersion!==2&&p.defSchemaVersion!==3){
    return '<div class="pm-split-empty">Legacy/unverified defensive allowance — this frozen saved board was not recomputed.</div>';
  }
  if(!p||(p.defHomeAllowed==null&&p.defAwayAllowed==null)){
    return '<div class="pm-split-empty">Sportsbook line: <strong style="color:#f8fafc">'+line+'</strong> &middot; '+_esc(p&&p.defUnavailable||('Exact '+m+' allowed to '+pg+'s by opponent venue is unavailable; neutral adjustment.'))+'</div>';
  }
  var hA=p.defenseVenue==='HOME';
  var aA=p.defenseVenue==='AWAY';
  var isPassTd=String(p&&p.market||'')==='player_pass_tds';
  var overNeed=isPassTd?Math.floor(Number(line))+1:null;
  var underMax=isPassTd?Math.ceil(Number(line))-1:null;
  function tdLineContext(avg){
    if(!isPassTd||avg==null||!isFinite(Number(avg)))return '';
    var gap=Math.abs(overNeed-Number(avg)).toFixed(1);
    var relation=Number(avg)<overNeed?'below':'above';
    return '<div class="pm-split-context">OVER needs '+overNeed+'+ &middot; UNDER wins at '+underMax+' or fewer<br>Average is '+gap+' '+relation+' the '+overNeed+'-TD OVER requirement</div>';
  }
  return '<div class="pm-split-container">'
    +'<div class="pm-split-header"><span class="pm-split-title">Team positional totals · vs '+pg+' · '+m+'</span><span class="pm-split-line">Line '+line+'</span></div>'
    +'<div class="pm-split-empty">Defense venue shown below is opposite the player offense venue. '+_esc(p.defSourceWindow||'Two-season point-in-time sample')+'. Not a personal scoring probability.</div>'
    +'<div class="pm-split-grid">'
    +'<div class="pm-split-card '+(hA?'pm-split-active':'')+'"><div class="pm-split-venue">'+o+' HOME</div><div class="pm-split-val">'+(p.defHomeAllowed!=null?p.defHomeAllowed:'—')+'</div><div class="pm-split-desc">'+m+' to '+pg+'s per game</div>'+tdLineContext(p.defHomeAllowed)+'<div class="pm-split-sample">'+(p.defHomeSample!=null?p.defHomeSample:0)+' completed games</div>'+(hA?'<div class="pm-split-badge">USED TODAY · OFFENSE AWAY</div>':'')+'</div>'
    +'<div class="pm-split-card '+(aA?'pm-split-active':'')+'"><div class="pm-split-venue">'+o+' AWAY</div><div class="pm-split-val">'+(p.defAwayAllowed!=null?p.defAwayAllowed:'—')+'</div><div class="pm-split-desc">'+m+' to '+pg+'s per game</div>'+tdLineContext(p.defAwayAllowed)+'<div class="pm-split-sample">'+(p.defAwaySample!=null?p.defAwaySample:0)+' completed games</div>'+(aA?'<div class="pm-split-badge">USED TODAY · OFFENSE HOME</div>':'')+'</div>'
    +'</div></div>';
}
function _nflOffenseContextHtml(p){
  var pos=String(p&&p.positionGroup||p&&p.position||'').toUpperCase();
  if(!p||!['QB','RB','WR','TE'].includes(pos))return '';
  var vals=[p.contextPositionTDAvg,p.contextOffenseTDAvg,p.contextPositionYardsAvg,p.contextOffenseYardsAvg];
  if(vals.every(function(v){return v==null;}))
    return '<div class="pm-split-empty">Offensive defense context unavailable; no probability or pick change.</div>';
  var venue=String(p.contextVenue||'').toUpperCase(), opp=_esc(p.opponent||'Opponent');
  function card(title,key,unit){
    var h=p[key+'HomeAvg'], a=p[key+'AwayAvg'];
    return '<div class="pm-split-card '+(venue?'pm-split-active':'')+'"><div class="pm-split-venue">'+title+'</div><div class="pm-split-val">HOME '+(h!=null?h:'—')+' · AWAY '+(a!=null?a:'—')+'</div><div class="pm-split-desc">'+unit+'</div><div class="pm-split-sample">HOME '+(p[key+'HomeSample']||0)+' · AWAY '+(p[key+'AwaySample']||0)+' completed games</div>'+(venue?'<div class="pm-split-badge">USED TODAY · '+venue+'</div>':'')+'</div>';
  }
  return '<div class="pm-split-container"><div class="pm-split-header"><span class="pm-split-title">Opponent offense context · '+opp+' '+_esc(venue)+'</span><span class="pm-split-line">Display only</span></div><div class="pm-split-empty">Used today: opposing defense '+_esc(venue)+' · '+_esc(p.contextSourceWindow||'two-season point-in-time sample')+'. Not a personal probability.</div><div class="pm-split-grid">'
    +card(pos+' TDs allowed','contextPositionTD','rushing + receiving TDs to '+pos)
    +card('Entire offense TDs allowed','contextOffenseTD','all rushing + receiving TDs; no passing TDs')
    +card(pos+' yards allowed','contextPositionYards',pos==='QB'?'passing yards':pos==='RB'?'rushing + receiving scrimmage yards':'receiving yards')
    +card('Entire offense total yards','contextOffenseYards','team passing + rushing yards; no receiving double-count')
    +'</div></div>';
}
function nflCard(p,i){
  var key=_ladKey(p); window.__NFLLAD__[key]=p;
  var ha=p.homeRoad==='H';
  var hasHA=(p.homeRoad==='H'||p.homeRoad==='R');
  var head=p.head||'';
  var logo='https://a.espncdn.com/i/teamlogos/nfl/500/'+_logoAbbr(p.team)+'.png';
  var shownOdds=_nflSideOdds(p);
  var shownBook=_nflSideBook(p);
  var lineHtml=(p.realLine!=null)
    ? `<span class="ln">${p.dispLine}</span> <span class="od">${shownOdds!=null?shownOdds:''} · ${_esc(shownBook)}</span>`
    : `<span class="est">~${p.dispLine}</span>`;
  var lastStat=(p.realLine!=null&&p.vsLineTotal)
    ? `<div class="pc-stat"><div class="k">vs Book L10</div><div class="v ${rateClass(p.vsLineRate)}">${p.vsLineHits}/${p.vsLineTotal} (${p.vsLineRate}%)</div></div>`
    : `<div class="pc-stat"><div class="k">Under L10</div><div class="v ${rateClass(p.underRate)}">${p.underHits}/${p.underTotal} (${p.underRate}%)</div></div>`;
  var haBadge=hasHA?`<span class="${ha?'home':'away'}">${ha?'HOME':'AWAY'}</span>`:'';
  var pos=String(p.position||p.roster_position||'').toUpperCase().trim();
  var posBadge=pos?`<span class="pc-pos">${_esc(pos)}</span>`:'';
  var systemBadge=p.system==='NEW'?'<span style="color:#67e8f9;font-weight:900">NEW</span>':'';
  var sparseBadge=p.sparseStatus?`<span style="color:#fbbf24;font-weight:900">${_esc(p.sparseStatus)}</span>`:'';
  var defChip='';
  if(p.defRank&&p.defAdj){
    var dcol=p.defAdj>0?'#4ade80':'#f87171';
    defChip='<div style="font-size:.62rem;font-weight:800;color:'+dcol+';margin-top:2px">vs #'+p.defRank+' '+(p.defLbl||'D')+' · '+(p.defAdj>0?'+':'')+p.defAdj+'% projection'+(p.defAllowed!=null?' · '+p.defAllowed+' allowed':'')+'</div>';
  }
  var roleChip=p.role?'<div style="font-size:.62rem;font-weight:800;color:#93c5fd;margin-top:2px">'+_esc(p.role)+(p.teamOptionRank!=null?' · team receiving option #'+p.teamOptionRank:'')+' · '+Math.round(Number(p.roleConfidence||0)*100)+'% role confidence</div>':'';
  var riskStatus=String(p.roleRiskStatus||'').toUpperCase();
  var riskChip=(riskStatus==='WATCH'||riskStatus==='AVOID')
    ?'<div style="margin-top:5px;padding:5px 7px;border-radius:6px;border:1px solid '+(riskStatus==='AVOID'?'rgba(248,113,113,.55)':'rgba(251,191,36,.5)')+';background:'+(riskStatus==='AVOID'?'rgba(127,29,29,.18)':'rgba(120,80,0,.15)')+';color:'+(riskStatus==='AVOID'?'#fca5a5':'#fde68a')+';font-size:.62rem;font-weight:900">ROLE '+riskStatus+' · '+_esc((p.roleRiskReasons||[])[0]||'Review expected usage')+'</div>'
    :'';
  return `
   <div class="pick-card ${_accFor(p.mkt)}">
     <div class="pc-rank">${i}</div>
     <div class="pc-top">
       <div class="hs-wrap"><span class="hs-ini">${_initials(p.name)}</span>
         <img class="hs-img" src="${head}" onerror="this.style.display='none'"/>
         <img class="pc-logo" src="${logo}" onerror="this.style.display='none'"/>
       </div>
       <div class="pc-id">
         <div class="pc-name">${p.name}</div>
           <div class="pc-meta">${systemBadge} ${sparseBadge} ${posBadge}${p.team} vs ${p.opponent} ${haBadge}${p.slate_date?' · '+p.slate_date:''}</div>
         <div class="pc-mkt">${p.mkt||''} · ${p.pick||''}</div>
         ${roleChip}
          ${riskChip}
         ${defChip}
       </div>
     </div>
     <div class="pc-tagrow">${fmtTag(p.tag)}</div>
      <div class="pc-line-row"><span>${lineHtml}</span><span class="od">Odds / Book</span></div>
      ${p.lineMovementAvailable&&p.openingLine!=null?`<div style="font-size:.68rem;color:#fbbf24;margin-top:5px;font-weight:800">Opening ${p.openingLine} → Current ${p.currentLine} (${Number(p.lineMove)>=0?'+':''}${Number(p.lineMove).toFixed(2)} pts)</div>`:''}
     <div class="pc-stats">
       <div class="pc-stat"><div class="k">${_esc(_nflOppVenueLabel(p))}</div><div class="v">${_rateHtml(p.rateA,p.hitsA,p.totA)}</div></div>
       <div class="pc-stat"><div class="k">${_esc(_nflRecentVenueLabel(p))}</div><div class="v">${_rateHtml(p.rateB,p.hitsB,p.totB)}</div></div>
       <div class="pc-stat"><div class="k">Avg</div><div class="v gold">${p.avg}</div></div>
       ${lastStat}
     </div>
     <div class="pc-foot"><span class="pc-score">${p.dispScore}</span>
       <span style="display:flex;gap:6px">${_nflBetBtn(p)}<button class="pc-tap" onclick="openNflLadder('${key}')">📊 Game Log</button></span></div>
   </div>`;
}
function nflCardGrid(picks,startRank){
  if(!picks||!picks.length) return '<div class="no-picks">No qualifying picks for this market.</div>';
   startRank=(startRank==null?1:startRank);
   return '<div class="picks-grid">'+picks.map(function(p,i){return nflCard(p,startRank+i);}).join('')+'</div>';
}
function _nflRoleRiskBoard(rows){
  var allSeen={},allPlayers=(rows||[]).filter(function(p){
    var key=String(p.name||'').toLowerCase().replace(/[^a-z0-9]/g,'');
    if(!key||allSeen[key])return false;allSeen[key]=1;return true;
  });
  var unverified=allPlayers.filter(function(p){
    return String(p.roleRiskStatus||'UNVERIFIED').toUpperCase()==='UNVERIFIED';
  }).length;
  var seen={},players=(rows||[]).filter(function(p){
    var status=String(p.roleRiskStatus||'').toUpperCase();
    if(status!=='WATCH'&&status!=='AVOID')return false;
    var key=String(p.name||'').toLowerCase().replace(/[^a-z0-9]/g,'');
    if(!key||seen[key])return false;seen[key]=1;return true;
  }).sort(function(a,b){
    var ar=String(a.roleRiskStatus).toUpperCase()==='AVOID'?0:1;
    var br=String(b.roleRiskStatus).toUpperCase()==='AVOID'?0:1;
    return ar-br||String(a.name).localeCompare(String(b.name));
  });
  if(!players.length){
    var neutral=unverified
      ?unverified+' player'+(unverified===1?'':'s')+' could not be verified on the current ESPN roster/depth feed.'
      :'No verified depth, injury, suspension, or recent-snap warning was found for the loaded players.';
    return '<details style="margin:14px 0;border:1px solid #334155;border-radius:12px;background:#0b1220;overflow:hidden"><summary style="cursor:pointer;padding:12px 15px;color:#93c5fd;font-weight:950">Pregame Role Risk Monitor · No flagged players</summary><div style="padding:0 15px 12px;color:#94a3b8;font-size:.7rem;line-height:1.45">'+neutral+'</div></details>';
  }
  var body=players.map(function(p){
    var key=_ladKey(p);window.__NFLLAD__[key]=p;
    var status=String(p.roleRiskStatus||'WATCH').toUpperCase();
    var color=status==='AVOID'?'#fca5a5':'#fde68a';
    var depth=p.depthRank!=null?_esc(p.depthPosition||p.position)+' '+p.depthRank:'Depth unavailable';
    var snap=p.recentSnapPct!=null?Number(p.recentSnapPct).toFixed(0)+'% recent snaps':'Snap trend unavailable';
    return '<button onclick="openNflLadder(&#39;'+key+'&#39;)" style="width:100%;display:grid;grid-template-columns:minmax(120px,1.1fr) minmax(90px,.7fr) minmax(180px,2fr);gap:10px;align-items:center;text-align:left;background:#0b1220;border:1px solid #334155;border-radius:8px;padding:9px 11px;color:#e2e8f0;cursor:pointer">'
      +'<span><b style="color:#fff">'+_esc(p.name)+'</b><br><small style="color:#94a3b8">'+_esc(p.team)+' · '+_esc(p.position||'')+'</small></span>'
      +'<span style="color:'+color+';font-weight:900">'+status+'<br><small>'+depth+'</small></span>'
      +'<span style="font-size:.68rem;color:#cbd5e1">'+_esc((p.roleRiskReasons||[]).join(' · ')||'Review role')+'<br><small style="color:#64748b">'+snap+'</small></span></button>';
  }).join('');
  return '<details open style="margin:14px 0;border:1px solid rgba(251,191,36,.42);border-radius:12px;background:rgba(120,80,0,.08);overflow:hidden">'
    +'<summary style="cursor:pointer;padding:12px 15px;color:#fde68a;font-weight:950">⚠ Pregame Role Risk Monitor · '+players.length+' player'+(players.length===1?'':'s')+'</summary>'
    +'<div style="padding:0 12px 12px;display:grid;gap:7px"><div style="color:#cbd5e1;font-size:.7rem;line-height:1.45">AVOID players are excluded from Locks, Coach Edge, and Perfect Parlay. WATCH players remain eligible with reduced confidence. Click a player for depth, snap, injury, and source details.</div>'+body+'</div></details>';
}
function _spRow(p){
  var key=_ladKey(p); window.__NFLLAD__[key]=p;
  var best=Math.max(p.rateA||0,p.rateB||0);
  return `<div class="sp-row" onclick="openNflLadder('${key}')"><div><div class="nm">${p.name}</div><div class="mt">${p.team} vs ${p.opponent} · ${p.dispLine} ${p.pick||''} · ${_esc(_nflSideBook(p))}</div></div><div class="${rateClass(best)}" style="font-weight:800">${best}%</div></div>`;
}
function _edge(p){ var g=(p.gap==null?0:p.gap); return (p.pick==='UNDER')?(-g):g; }
function _collapseSec(id,title,inner,open){
  var disp=open?'block':'none'; var car=open?'▾':'▸';
  return '<div class="sec sec-hdr" onclick="_secToggle(&#39;'+id+'&#39;)"><span>'+title+'</span>'+
         '<span class="sec-caret" id="car_'+id+'">'+car+'</span></div>'+
         '<div id="sec_'+id+'" style="display:'+disp+'">'+inner+'</div>';
}
function _nflMovementBoard(picks,side){
  var rows=(picks||[]).filter(function(p){
    var move=Number(p.lineMove);
    return !_nflGameDone(p)&&p.lineMovementAvailable&&p.realLine!=null
      &&p.pick===side&&isFinite(move)&&((side==='OVER'&&move>0)||(side==='UNDER'&&move<0));
  });
  var seen={};
  rows=rows.filter(function(p){
    var key=[p.name||p.player,p.market||p.mkt,p.realLine,side].join('|').toLowerCase();
    if(seen[key])return false;seen[key]=1;return true;
  }).sort(function(a,b){return Math.abs(Number(b.lineMove))-Math.abs(Number(a.lineMove));}).slice(0,10);
  if(!rows.length)return '<div class="no-picks" style="padding:24px">No qualifying opening-to-current line moves captured yet.</div>';
  return '<div style="padding:10px 0 4px;color:#94a3b8;font-size:.76rem;line-height:1.45">A '+side+' line move shows the sportsbook changed the required line after opening. It can reflect market action or a changed expectation, but it is not a guarantee. The current number is the number you must bet.</div>'+nflCardGrid(rows,1);
}
function _secToggle(id){
  var el=document.getElementById('sec_'+id); var c=document.getElementById('car_'+id);
  if(!el) return; var hidden=el.style.display==='none';
  el.style.display=hidden?'block':'none'; if(c) c.textContent=hidden?'▾':'▸';
}
function _playRow(p){
  var key=_ladKey(p); window.__NFLLAD__[key]=p;
  var best=Math.max(p.rateA||0,p.rateB||0);
  var sub=p.team+' vs '+p.opponent+' · '+(p.mkt||p.label)+' · '+p.dispLine+' '+(p.pick||'')+' · '+_nflSideBook(p);
  return '<div class="pl-row" onclick="openNflLadder(&#39;'+key+'&#39;)">'+
         '<div><div class="nm">'+p.name+'</div><div class="mt">'+sub+'</div></div>'+
         '<div class="'+rateClass(best)+'" style="font-weight:800">'+best+'%</div></div>';
}
function _openModal(title,sub,body){
  var html='<div class="lad-modal big-modal" onclick="event.stopPropagation()">'+
    '<button class="lad-close" onclick="_closeModal()">✕</button>'+
    '<h3>'+title+'</h3><div class="lad-sub">'+sub+'</div>'+body+'</div>';
  var ov=document.createElement('div'); ov.className='lad-ov'; ov.id='nflModalOv';
  ov.onclick=_closeModal; ov.innerHTML=html; document.body.appendChild(ov);
}
function _closeModal(){var o=document.getElementById('nflModalOv'); if(o)o.remove();}
function _nflWeatherHtml(w){
  if(!w||w.status!=='OK')return '';
  var k=w.kickoff||{}, rain=k.precipitation_probability!=null?String(Math.round(k.precipitation_probability))+'% precip':'';
  var amt=k.precipitation_in!=null?Number(k.precipitation_in).toFixed(2)+' in':'';
  var wind=k.wind_mph!=null?Math.round(k.wind_mph)+' mph wind':'';
  var gust=k.gust_mph!=null?Math.round(k.gust_mph)+' mph gusts':'';
  var vals=[w.label||'Weather',k.temperature_f!=null?Math.round(k.temperature_f)+'°F':'',rain,amt,wind,gust].filter(Boolean).join(' · ');
  return '<div style="margin:10px 0;padding:9px 11px;border:1px solid rgba(251,191,36,.28);border-radius:9px;background:rgba(120,80,0,.12);color:#fde68a;font-size:.68rem;font-weight:800">⚠ WEATHER · '+_esc(vals)+'<span style="display:block;color:#cbd5e1;font-weight:600;margin-top:3px">'+_esc(w.summary||'')+'</span></div>';
}
function _nflPlayerWeatherHtml(p){
  if(!p||p.weatherStatus!=='OK'||!p.weatherApplied)return '';
  var effect=Number(p.weatherAdjustment||0), sign=effect>0?'+':'';
  return '<div style="margin:9px 0;padding:8px 10px;border:1px solid rgba(251,191,36,.22);border-radius:8px;background:rgba(120,80,0,.1);color:#fde68a;font-size:.68rem;font-weight:800">Weather model · '+_esc(p.weatherLabel||'')+' · '+sign+effect+' projection'+(p.weatherSummary?'<span style="display:block;color:#cbd5e1;font-weight:600;margin-top:3px">'+_esc(p.weatherSummary)+'</span>':'')+'</div>';
}
function _gameModal(gi){
  var st=window._nflState||{}; var g=((st.d||{}).games||[])[gi]; if(!g) return;
  var gk=g.game; var mu=(g.away_abbr||g.away_team||'?')+' @ '+(g.home_abbr||g.home_team||'?');
  var plays=(st.all||[]).filter(function(p){return p.game===gk;});
  var body='';
  _MORDER.forEach(function(m){
    var mp=plays.filter(function(p){return (p.mkt||p.label)===m;}).sort(function(a,b){return _edge(b)-_edge(a);});
    if(!mp.length) return;
    body+='<div class="mk-hdr">'+_mIcon(m)+' '+m+'</div>'+mp.map(_playRow).join('');
  });
  if(!body) body='<div class="mt" style="color:#6b7280;padding:10px">No plays for this game.</div>';
  _openModal(mu, ((st.d||{}).date||'')+' · tap any play for its game log', _nflWeatherHtml(g.weather)+body);
}
function _marketModal(m){
  var st=window._nflState||{};
  var plays=(st.all||[]).filter(function(p){return (p.mkt||p.label)===m;}).sort(function(a,b){return _edge(b)-_edge(a);});
  var body=plays.length?plays.map(_playRow).join(''):'<div class="mt" style="color:#6b7280;padding:10px">No plays.</div>';
  _openModal(_mIcon(m)+' '+m, plays.length+' plays · tap any play for its game log', body);
}
function _nflJumpToGames(){
  var el=document.getElementById('nfl-by-game-section');
  if(!el)return;
  el.scrollIntoView({behavior:'smooth',block:'start'});
  el.setAttribute('data-highlight','1');
  el.style.boxShadow='0 0 0 3px rgba(245,158,11,.28),0 18px 45px rgba(0,0,0,.32)';
  setTimeout(function(){el.style.boxShadow='';el.removeAttribute('data-highlight');},1400);
}
function _underBox(picks){
  // Sort best rate first, then keep only 1 play per player (their best)
  var sorted=(picks||[]).filter(function(p){return p.underTotal>=2 && p.underRate>=60;})
      .sort(function(a,b){return b.underRate-a.underRate||b.underTotal-a.underTotal;});
  var seen={}; var u=[];
  sorted.forEach(function(p){var nm=(p.name||'').toLowerCase();if(!seen[nm]){seen[nm]=true;u.push(p);}});
  u=u.slice(0,10);
  if(!u.length) return '';
  var rows=u.map(function(p){
    var key=_ladKey(p); window.__NFLLAD__[key]=p;
    return `<div class="uprow" onclick="openNflLadder('${key}')"><div><div class="nm">${p.name}</div><div class="mt">${p.team} vs ${p.opponent} · ${p.mkt} · under ${p.underLine} · ${_esc(_nflSideBook(p,'UNDER'))}</div></div><div class="${rateClass(p.underRate)}" style="font-weight:800">${p.underHits}/${p.underTotal} (${p.underRate}%)</div></div>`;
  }).join('');
  return '<div class="uplays">'+rows+'</div>';
}
function openNflLadder(key){
  var p=window.__NFLLAD__[key]; if(!p) return;
  var line=p.dispLine;
  var pickSide=String(p.pick||'PICK').toUpperCase();
  var venueScope=p.homeRoad==='R'?'away games':(p.homeRoad==='H'?'home games':'games at all venues');
  var statName=_esc(p.mkt||p.label||'stat');
  function detailedRate(hits,total,rate,scope,side){
    var h=Number(hits||0),t=Number(total||0),r=Number(rate);
    side=String(side||pickSide).toUpperCase();
    if(!t||!isFinite(r))return '<span class="gray">No qualifying games</span>';
    return '<span class="'+rateClass(r)+'">'+h+'/'+t+' ('+r.toFixed(1)+'%)'
      +'<span class="pm-stat-note">'+h+' of '+t+' '+scope+' finished '+side.toLowerCase()+' '+line+'</span></span>';
  }
  var chips=(p.glog||[]).map(function(g){
    var hit=p.pick==='UNDER'?g.v<line:g.v>line; var cls=hit?'hit':'miss';
    var od=g.o?(' &middot; '+g.o):'';
    return '<div class="pm-glchip '+cls+'"><div class="d">'+g.d+od+'</div><div class="v">'+g.v+'</div></div>';
  }).join('');
  if(!chips) chips='<span class="pm-gray">No game log available.</span>';
  
  var vslRow=(p.realLine!=null&&p.vsLineTotal)
    ? '<div class="pm-stat"><span class="k">'+pickSide+' '+p.realLine+' &middot; Last 10 all venues<span class="pm-stat-note">Most recent games, regardless of HOME/AWAY</span></span><span class="v">'+detailedRate(p.vsLineHits,p.vsLineTotal,p.vsLineRate,'recent games')+'</span></div>'
    : '';
    
  var vol=(p.vsOppLog||[]);
  var voHtml='';
  if(vol.length){
    var oppOver=0,oppUnder=0,oppPush=0;
    vol.forEach(function(g){
      var v=Number(g.v);
      if(v>line)oppOver++;else if(v<line)oppUnder++;else oppPush++;
    });
    var oppPct=function(n){return vol.length?(n/vol.length*100).toFixed(1):'0.0';};
    voHtml='<div class="pm-section pm-vsopp-section">'
      +'<div class="pm-sec-title">History vs '+_esc(p.opponent)+' <span class="pm-sec-count">('+vol.length+' meetings)</span></div>'
      +'<div class="pm-sec-desc">Past results compared against today&rsquo;s line of <strong style="color:#f8fafc">'+line+'</strong>.</div>'
      +'<div class="pm-vsopp-summary">'
      +'<div class="pm-vo-card pm-vo-over"><div class="pm-vo-lbl">OVER '+line+'</div><div class="pm-vo-val">'+oppOver+'/'+vol.length+' <span>'+oppPct(oppOver)+'%</span></div></div>'
      +'<div class="pm-vo-card pm-vo-under"><div class="pm-vo-lbl">UNDER '+line+'</div><div class="pm-vo-val">'+oppUnder+'/'+vol.length+' <span>'+oppPct(oppUnder)+'%</span></div></div>'
      +'<div class="pm-vo-card pm-vo-push"><div class="pm-vo-lbl">PUSH</div><div class="pm-vo-val">'+oppPush+'/'+vol.length+'</div></div>'
      +'</div><div class="pm-vsopp-list">';
    voHtml+=vol.map(function(g){
      var v=Number(g.v),result=v>line?'OVER':(v<line?'UNDER':'PUSH');
      var cls=result==='OVER'?'pm-res-over':(result==='UNDER'?'pm-res-under':'pm-res-push');
      var venue=g.ha?(' &middot; '+_esc(g.ha)):'';
      return '<div class="pm-vsopp-row"><span class="pm-vo-date">'+_esc(g.d)+venue+'</span><span class="pm-vo-res '+cls+'">'+g.v+' &middot; '+result+'</span></div>';
    }).join('');
    voHtml+='</div></div>';
  }

  var parlayWhy=p.parlayWhy
    ?'<div class="pm-callout pm-callout-blue"><div class="pm-co-title">Why this parlay leg</div><div class="pm-co-body">'+_esc(p.parlayWhy)+'</div></div>'
    :'';
  var historyRule=p.historyLockReason
    ?'<div class="pm-callout pm-callout-amber"><div class="pm-co-title">Pick-side rule</div><div class="pm-co-body">'+_esc(p.historyLockReason)+'. The small defense adjustment cannot reverse this side.</div></div>'
    :'';

  var roleHtml = p.role
    ? '<div class="pm-stat"><span class="k">Role / opportunity<span class="pm-stat-note">Recent usage plus current ESPN offensive depth chart when available</span></span><span class="v">'+_esc(p.role)+(p.teamOptionRank!=null?' &middot; Option #'+p.teamOptionRank:'')+(p.depthRank!=null?' &middot; ESPN '+_esc(p.depthPosition||p.position)+' '+p.depthRank:'')+' ('+Math.round(Number(p.roleConfidence||0)*100)+'% conf)</span></div>'
    : '';
  var roleRiskStatus=String(p.roleRiskStatus||'').toUpperCase();
  var roleRiskHtml=(roleRiskStatus&&roleRiskStatus!=='CLEAR'&&roleRiskStatus!=='UNVERIFIED')
    ?'<div class="pm-callout '+(roleRiskStatus==='AVOID'?'pm-callout-amber':'pm-callout-blue')+'"><div class="pm-co-title">Role Risk · '+_esc(roleRiskStatus)+'</div><div class="pm-co-body">'+_esc((p.roleRiskReasons||[]).join(' · ')||'Reduced-role evidence requires review')+(p.recentSnapPct!=null?'<br>Recent offense snaps: '+Number(p.recentSnapPct).toFixed(0)+'%'+(p.priorSnapPct!=null?' vs prior '+Number(p.priorSnapPct).toFixed(0)+'%':''):'')+'<br><span style="color:#94a3b8">Source: '+_esc(p.roleRiskSource||'ESPN roster')+'</span></div></div>'
    :'';
    
  var probHtml = (p.baseProbability!=null||p.adjustedProbability!=null)
    ? '<div class="pm-stat"><span class="k">Base &rarr; adjusted probability<span class="pm-stat-note">Base blends opponent history and recent venue form; adjusted adds role, defense and verified injury effects</span></span><span class="v">'+(p.baseProbability!=null?Number(p.baseProbability).toFixed(1):'—')+'% &rarr; '+(p.adjustedProbability!=null?Number(p.adjustedProbability).toFixed(1):'—')+'%</span></div>'
    : '';
    
  var defHtml = (p.defRank!=null&&p.defAdj!=null)
    ? '<div class="pm-stat"><span class="k">Opponent defense &middot; #'+p.defRank+' '+_esc(p.defLbl||'D')+'<span class="pm-stat-note">Venue-specific adjustment to the player projection; negative lowers the projected stat</span></span><span class="v '+(p.defAdj>0?'pm-text-green':(p.defAdj<0?'pm-text-red':'pm-text-gray'))+'">'+(p.defAdj>0?'+':'')+p.defAdj+'% nudge</span></div>'
    : '';

  var splitHtml = (p.realLine!=null||p.dispLine!=null) ? _nflDefenseSplitHtml(p) : '';
  splitHtml += _nflOffenseContextHtml(p);

  var pickCls = pickSide === 'UNDER' ? 'pm-pick-under' : 'pm-pick-over';

  var html='<div class="pm-modal" onclick="event.stopPropagation()">'
    +'<button class="pm-close" onclick="closeNflLadder()"><svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round"><line x1="18" y1="6" x2="6" y2="18"></line><line x1="6" y1="6" x2="18" y2="18"></line></svg></button>'
    +'<div class="pm-header">'
    +'<h3 class="pm-name">'+p.name+'</h3>'
    +'<div class="pm-sub">'+p.mkt+' &middot; '+p.team+' vs '+p.opponent+'</div>'
    +'<div class="pm-pick-row">'
    +'<div class="pm-pick-badge '+pickCls+'">'+pickSide+' '+line+'</div>'
    +'<div class="pm-pick-book">'+_esc(_nflSideBook(p))+'</div>'
    +'</div>'
    +'</div>'
    +'<div class="pm-body">'
    +_nflPlayerWeatherHtml(p)
     +roleRiskHtml
    +parlayWhy
    +historyRule
    +splitHtml
    +'<div class="pm-section">'
    +'<div class="pm-sec-title">Recent Games <span class="pm-sec-hl">(Green = '+(pickSide==='UNDER'?'under':'over')+' line)</span></div>'
    +'<div class="pm-glog">'+chips+'</div>'
    +'</div>'
    +voHtml
    +'<div class="pm-section pm-stats-section">'
    +'<div class="pm-sec-title">Matchup Stats</div>'
    +'<div class="pm-stats-list">'
    +'<div class="pm-stat"><span class="k">'+pickSide+' vs '+_esc(p.opponent)+' &middot; All meetings<span class="pm-stat-note">Every available career meeting, all venues</span></span><span class="v">'+detailedRate(p.hitsA,p.totA,p.rateA,'meetings')+'</span></div>'
    +'<div class="pm-stat"><span class="k">'+pickSide+' '+line+' &middot; Recent '+venueScope+'<span class="pm-stat-note">Up to 10 '+venueScope+' before today</span></span><span class="v">'+detailedRate(p.hitsB,p.totB,p.rateB,venueScope)+'</span></div>'
    +vslRow
    +'<div class="pm-stat"><span class="k">UNDER '+line+' &middot; Recent '+venueScope+'<span class="pm-stat-note">Dedicated downside rate for the same venue sample</span></span><span class="v">'+detailedRate(p.underHits,p.underTotal,p.underRate,venueScope,'UNDER')+'</span></div>'
    +'<div class="pm-stat"><span class="k">Average &middot; Recent '+venueScope+'<span class="pm-stat-note">Arithmetic average across '+Number(p.totB||0)+' available '+venueScope+'</span></span><span class="v pm-gold">'+p.avg+'<span class="pm-stat-note">'+statName+' per game</span></span></div>'
    +defHtml
    +roleHtml
    +probHtml
    +'<div class="pm-stat pm-score-stat"><span class="k">Final model score<span class="pm-stat-note">Confidence for the printed '+pickSide+' pick after all adjustments</span></span><span class="v pm-gold-bright">'+p.dispScore+'</span></div>'
    +'</div>'
    +'</div>'
    +'</div>'
    +'</div>';
    
  var ov=document.createElement('div');
  ov.className='pm-ov'; ov.id='nflLadOv'; ov.onclick=closeNflLadder;
  ov.innerHTML=html;
  document.body.appendChild(ov);
}
function closeNflLadder(){var o=document.getElementById('nflLadOv');if(o)o.remove();}

function buildNormTable(picks, startNum){
  var thead = '<thead><tr><th>#</th><th>PLAYER</th><th>TEAM</th><th>OPP</th><th>H/A</th>' +
    '<th>BOOK</th><th>AVG vs OPP</th><th>AVG L10 H/A</th><th>HITS BOOK L10</th>' +
    '<th>GAP vs BOOK</th><th>vs OPP all meetings</th><th>L10 H/A</th><th>SCORE</th><th>PICK</th><th>TAG</th></tr></thead>';
  var rows = '';
  picks.forEach(function(p, i){
    var hasHA=(p.homeRoad==='H'||p.homeRoad==='R');
    var ha = p.homeRoad === 'H';
    var num = startNum + i;
    rows += '<tr>' +
      '<td>' + (startNum === 1 ? '<span class="rk-num">' + num + '</span>' : '<span class="rk-rest">' + num + '</span>') + '</td>' +
      '<td><span class="pname">' + p.name + '</span></td>' +
      '<td><span class="tbadge">' + p.team + '</span></td>' +
      '<td><span class="tbadge">' + p.opponent + '</span></td>' +
      '<td>' + (hasHA ? '<span class="' + (ha ? 'home' : 'away') + '">' + (ha ? 'HOME' : 'AWAY') + '</span>' : '<span class="gray">—</span>') + '</td>' +
      '<td>' + (p.realLine!=null ? '<span class="real-line">' + p.dispLine + '</span> <span class="odds-txt">' + (_nflSideOdds(p)!=null?_nflSideOdds(p):'') + '</span><br><small class="gray">' + _esc(_nflSideBook(p)) + '</small>' : '<span class="est">~' + p.dispLine + '</span>') + '</td>' +
      '<td><span class="gold">' + p.avgA + '</span></td>' +
      '<td><span class="gold">' + p.avg + '</span></td>' +
      '<td>' + fmtVsLine(p) + '</td>' +
      '<td>' + fmtGap(p.gap) + '</td>' +
      '<td>' + _rateHtml(p.rateA,p.hitsA,p.totA) + '</td>' +
      '<td>' + _rateHtml(p.rateB,p.hitsB,p.totB) + '</td>' +
      '<td><span class="score">' + p.dispScore + '</span></td>' +
      '<td>' + (p.pick||'') + '</td>' +
      '<td>' + fmtTag(p.tag) + '</td>' +
      '</tr>';
  });
  return '<div class="tbl-wrap"><table>' + thead + '<tbody>' + rows + '</tbody></table></div>';
}

// ── NFL Game Predictor ────────────────────────────────────────────────────────
function _nflGpConfClr(c){return({STRONG:'#7c3aed',MODERATE:'#2563eb',LEAN:'#64748b'})[c]||'#64748b';}
function _nflGpFix(v){return(v==null||v==='')?'&#8212;':(Math.round(Number(v)*10)/10).toFixed(1);}
function _nflGpBetPanel(g,idx){
  var _gd=g.slate_date||window.__NFL_DATE__||'';
  var _ha=g.home_abbr||'',_aa=g.away_abbr||'';
  window.__NFL_GP_BET__=window.__NFL_GP_BET__||{};
  var n=0;
  function _od(v){return v!=null?(v>0?'+'+v:''+v):'&#8212;';}
  function _regML(abbr,side,odds,book,sfx){
    var k='nfgpml'+idx+sfx; window.__NFL_GP_BET__[k]={
      name:_aa+' @ '+_ha+' \u2014 '+abbr+' to Win',team:abbr,opp:(side==='HOME'?_aa:_ha),
      category:'Game Predictor',side:side,stat_key:'gp_winner',stat_label:'to Win',
      line:null,odds:odds,book:book||'',home_abbr:_ha,away_abbr:_aa,date:_gd}; return k;
  }
  function _regTot(dir,odds,book,sfx){
    var k='nfgptl'+idx+sfx; window.__NFL_GP_BET__[k]={
      name:_aa+' @ '+_ha+' '+dir+' '+g.total_line,team:_aa+'@'+_ha,opp:'',
      category:'Game Predictor',side:dir,stat_key:'gp_total',stat_label:'Point Total',
      line:g.total_line,odds:odds,book:book||'',home_abbr:_ha,away_abbr:_aa,date:_gd}; return k;
  }
  function _row(label,od,book,k,isPick){
    if(od==null||!k) return '';
    var star=isPick?'&#9733; ':''; var lc=isPick?'#e9d5ff':'#94a3b8';
    return '<div style="display:flex;align-items:center;gap:6px;padding:5px 12px;border-top:1px solid #111c2e">'
      +'<div style="flex:1;font-size:.7rem;font-weight:800;color:'+lc+'">'+star+label+'</div>'
      +'<div style="font-family:monospace;font-size:.7rem;font-weight:700;color:#fbbf24;min-width:36px;text-align:right">'+_od(od)+'<br><small style="color:#64748b">'+_esc(book||'Book unavailable')+'</small></div>'
      +'<button onclick="event.stopPropagation();_nflGpBetForm(&#39;'+k+'&#39;)" style="background:#1a1740;color:#a5b4fc;border:none;border-radius:5px 0 0 5px;padding:4px 9px;font-size:.65rem;font-weight:800;cursor:pointer;white-space:nowrap">Track</button>'
      +'</div>';
  }
  var rows='';
  if(g.away_ml_odds!=null) rows+=_row(_aa+' ML',g.away_ml_odds,g.away_ml_book,_regML(_aa,'AWAY',g.away_ml_odds,g.away_ml_book,'a'),!g.pick_home);
  if(g.home_ml_odds!=null) rows+=_row(_ha+' ML',g.home_ml_odds,g.home_ml_book,_regML(_ha,'HOME',g.home_ml_odds,g.home_ml_book,'h'),g.pick_home);
  if(g.total_line!=null){
    if(g.total_over_odds!=null) rows+=_row('OVER '+g.total_line,g.total_over_odds,g.total_over_book,_regTot('OVER',g.total_over_odds,g.total_over_book,'o'),g.total_pick==='OVER');
    if(g.total_under_odds!=null) rows+=_row('UNDER '+g.total_line,g.total_under_odds,g.total_under_book,_regTot('UNDER',g.total_under_odds,g.total_under_book,'u'),g.total_pick==='UNDER');
  }
  if(!rows) return '';
  return '<details class="nfl-gp-track">'
    +'<summary>TRACK SPORTSBOOK LINES &#183; &#9733; MODEL PICK</summary>'
    +'<div class="nfl-gp-track-body">'+rows+'</div></details>';
}
function _nflGpCard(g,i){
  var cc=_nflGpConfClr(g.conf);
  function teamRow(abbr,sp,proj,win,isPick,book,offRank,defRank){
    var barClr=isPick?'#22c55e':'#ef4444';
    var logo='https://a.espncdn.com/i/teamlogos/nfl/500/'+_logoAbbr(abbr)+'.png';
    return '<div class="nfl-gp-team'+(isPick?' pick':'')+'">'
      +'<img class="nfl-gp-logo" src="'+_esc(logo)+'" alt="" onerror="this.style.visibility=\\'hidden\\'"/>'
      +'<div class="nfl-gp-abbr">'+_esc(abbr)+'</div>'
      +'<div class="nfl-gp-sp">'+_esc(sp||'Starter TBD')+' &middot; '+_esc(book||'N/A')+'<div class="nfl-gp-ranks"><span class="nfl-gp-rank off">OFF #'+(offRank||'—')+'</span><span class="nfl-gp-rank def">DEF #'+(defRank||'—')+'</span></div></div>'
      +'<div class="nfl-gp-win-box"><div class="nfl-gp-win">'+win+'%<small>Win</small></div></div>'
      +'<div class="nfl-gp-barline"><div class="nfl-gp-bar"><span style="width:'+win+'%;background:'+barClr+'"></span></div></div>'
      +'</div>';
  }
  var drivers=(g.drivers||[]).slice(0,3).map(function(d){return '<li>'+_esc(d)+'</li>';}).join('');
  var vb=g.value_flag?('<span class="nfl-gp-badge" style="background:#166534;color:#4ade80">VALUE +'+g.mkt_edge+'%</span>'):'';
  var totValue='',totalBook='';
  if(g.total_line==null){
    totValue='Proj '+_nflGpFix(g.proj_total)+' &middot; no book line';
  } else {
    var ov=g.total_pick==='OVER'; var ec=(g.total_edge>0?'+':'')+_nflGpFix(g.total_edge);
    totalBook=ov?g.total_over_book:g.total_under_book;
    totValue='<span style="color:'+(ov?'#4ade80':'#fca5a5')+'">'+g.total_pick+' '+_nflGpFix(g.total_line)+'</span> &middot; proj '+_nflGpFix(g.proj_total)+' &middot; '+ec+' pts<br><span style="color:#64748b;font-size:.65rem;font-weight:600">'+_esc(totalBook||'Book unavailable')+'</span>';
  }
  var mktValue='No moneyline edge';
  if(g.mkt_edge!=null){
    var mp=(g.pick_home?g.mkt_home_pct:g.mkt_away_pct), md=(g.pick_home?g.win_home:g.win_away);
    var sign=(g.mkt_edge>0?'+':'');
    mktValue='<span style="color:#818cf8">'+_esc(g.pick_abbr)+' '+md+'%</span> vs mkt '+mp+'%<br><span style="color:'+(g.mkt_edge>0?'#4ade80':g.mkt_edge<0?'#f87171':'#64748b')+';font-size:.65rem;font-weight:600">'+sign+g.mkt_edge+'% edge</span>';
  }
  return '<div class="nfl-gp-game" role="button" tabindex="0" onclick="_openNflGamePred('+i+')" onkeydown="if(event.key===\\'Enter\\'||event.key===\\' \\'){event.preventDefault();_openNflGamePred('+i+')}">'
    +'<div class="nfl-gp-head"><div><div class="nfl-gp-matchup">'+_esc(g.away_abbr)+' @ '+_esc(g.home_abbr)+'</div><span class="nfl-gp-date">'+_esc(g.slate_date||'Today')+'</span></div>'
    +'<div class="nfl-gp-badges">'+vb
    +'<span class="nfl-gp-badge" style="background:'+cc+'">'+_esc(g.conf)+'</span>'
    +'<span class="nfl-gp-badge" style="background:#4f46e5">PICK '+_esc(g.pick_abbr)+'</span></div></div>'
    +'<div class="nfl-gp-teams">'
    +teamRow(g.away_abbr,g.away_sp,g.proj_away,g.win_away,!g.pick_home,g.away_ml_book,g.away_off_rank,g.away_def_rank)
    +teamRow(g.home_abbr,g.home_sp,g.proj_home,g.win_home,g.pick_home,g.home_ml_book,g.home_off_rank,g.home_def_rank)
    +'</div><div class="nfl-gp-callouts"><div class="nfl-gp-callout"><div class="k">Point total</div><div class="v">'+totValue+'</div></div>'
    +'<div class="nfl-gp-callout"><div class="k">Winner value</div><div class="v">'+mktValue+'</div></div></div>'
    +'<div class="nfl-gp-why"><div class="nfl-gp-why-title">Why This Pick</div><ul>'+drivers+'</ul></div>'
    +_nflGpBetPanel(g,i)
    +'</div>';
}
function _nflGpHistoryRow(m,home,away){
  var winner=m.winner==='TIE'?'TIE':(m.winner||'—');
  var venueSide=(m.home_abbr===home?home+' HOME':home+' AWAY')+' · '+
    (m.home_abbr===away?away+' HOME':away+' AWAY');
  var score=_esc(m.away_abbr)+' '+m.away_score+' — '+_esc(m.home_abbr)+' '+m.home_score;
  var total=(Number(m.home_score)||0)+(Number(m.away_score)||0);
  var type=m.season_type==='POST'?'PLAYOFF':'REG';
  return '<div style="padding:13px 0;border-top:1px solid #1e293b">'
    +'<div style="display:flex;justify-content:space-between;gap:8px;align-items:center;flex-wrap:wrap">'
    +'<span style="font-size:.72rem;font-weight:900;color:#e2e8f0">'+_esc(m.date_label||m.date||'—')+'</span>'
    +'<span style="font-size:.58rem;padding:3px 7px;border-radius:5px;background:'+(type==='PLAYOFF'?'rgba(167,139,250,.18)':'rgba(148,163,184,.12)')+';color:'+(type==='PLAYOFF'?'#c4b5fd':'#94a3b8')+';font-weight:900;letter-spacing:.05em">'+type+'</span></div>'
    +'<div style="display:flex;justify-content:space-between;gap:8px;margin-top:7px;font-size:.76rem;align-items:center">'
    +'<span style="color:#4ade80;font-weight:900">'+_esc(winner)+'</span>'
    +'<span style="color:#fbbf24;font-weight:900;font-family:monospace">'+score+' <small style="color:#94a3b8;font-family:inherit">TOTAL '+total+'</small></span></div>'
    +'<div style="margin-top:5px;color:#94a3b8;font-size:.64rem">'+_esc(venueSide)+' · '+_esc(m.venue||'Stadium unavailable')
    +(m.city_state?' · '+_esc(m.city_state):'')+'</div>'
    +'</div>';
}
function _nflGpLoadHistory(g){
  var box=document.getElementById('nfl-gp-history'); if(!box) return;
  var home=g.home_abbr||'',away=g.away_abbr||'';
  var requestedSystem=_nflSystem(),requestGeneration=_nflSystemGeneration,
      requestSeq=++_nflHistoryLoadSeq,
      requestController=_nflTrackController(new AbortController());
  var key=away+'@'+home;
  box.dataset.key=key;
  fetch('/api/nfl/game-history?home='+encodeURIComponent(home)+'&away='+encodeURIComponent(away)
    +'&before='+encodeURIComponent(window.__NFL_DATE__||'')
    +'&system='+encodeURIComponent(requestedSystem),{signal:requestController.signal})
    .then(function(r){return r.json();})
    .then(function(d){
      _nflUntrackController(requestController);
      if(requestSeq!==_nflHistoryLoadSeq||!_nflRequestCurrent(requestGeneration,requestedSystem))return;
      if(box.dataset.key!==key) return;
      if(d.error){box.innerHTML='<div style="color:#f87171">'+_esc(d.error)+'</div>';return;}
      var games=d.games||[];
      if(!games.length){
        box.innerHTML='<div style="color:#64748b">No completed meetings found in the available schedule history.</div>';
        return;
      }
       var winsHome=0,winsAway=0,ties=0,totalSum=0,exactVenue=0;
       games.forEach(function(m){
         if(m.winner===home)winsHome++; else if(m.winner===away)winsAway++; else ties++;
         totalSum+=(Number(m.home_score)||0)+(Number(m.away_score)||0);
         if(m.home_abbr===home)exactVenue++;
       });
       var avgTotal=games.length?(totalSum/games.length).toFixed(1):'—';
       box.innerHTML='<div style="font-size:.68rem;color:#c4b5fd;font-weight:900;letter-spacing:.08em;margin-bottom:10px;text-transform:uppercase">Last '+games.length+' meetings · display only</div>'
         +'<div style="display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:7px;margin-bottom:10px">'
         +'<div style="background:#111827;border:1px solid #243047;border-radius:8px;padding:9px"><div style="font-size:.58rem;color:#64748b;font-weight:800">SERIES WINS</div><div style="margin-top:3px;color:#e2e8f0;font-weight:900">'+_esc(home)+' '+winsHome+' · '+_esc(away)+' '+winsAway+(ties?' · '+ties+' TIE':'')+'</div></div>'
         +'<div style="background:#111827;border:1px solid #243047;border-radius:8px;padding:9px"><div style="font-size:.58rem;color:#64748b;font-weight:800">AVG COMBINED</div><div style="margin-top:3px;color:#fbbf24;font-weight:900">'+avgTotal+' PTS</div></div>'
         +'<div style="background:#111827;border:1px solid #243047;border-radius:8px;padding:9px"><div style="font-size:.58rem;color:#64748b;font-weight:800">VENUE SPLIT</div><div style="margin-top:3px;color:#c4b5fd;font-weight:900">'+exactVenue+' EXACT HOME</div></div></div>'
         +games.map(function(m){return _nflGpHistoryRow(m,home,away);}).join('');
    })
    .catch(function(){
      _nflUntrackController(requestController);
      if(!_nflRequestCurrent(requestGeneration,requestedSystem))return;
      if(box.dataset.key===key)box.innerHTML='<div style="color:#f87171">Could not load matchup history. Try again.</div>';
    });
}
function _openNflGamePred(i){
  var gp=(window.__NFL_GP__||[])[i]; if(!gp) return;
  var ov=document.getElementById('nfl-gp-modal');
  if(!ov){
    ov=document.createElement('div');ov.id='nfl-gp-modal';
    ov.style.cssText='position:fixed;inset:0;background:rgba(0,0,0,.85);backdrop-filter:blur(6px);-webkit-backdrop-filter:blur(6px);z-index:10000;display:flex;align-items:center;justify-content:center;padding:20px;overflow:hidden;box-sizing:border-box';
    ov.onclick=function(e){if(e.target===ov)ov.style.display='none';};
    document.body.appendChild(ov);
  }
  ov.style.display='flex';
  ov.innerHTML='<div style="margin:auto;background:#09090b;border:1px solid #27272a;border-radius:16px;padding:24px;color:#94a3b8;font-size:.85rem;font-weight:700">Loading game breakdown...</div>';
  try{
  function val(v,fix){return v==null||v===''?'—':(fix?_nflGpFix(v):_esc(v));}
  function team(abbr,sp,proj,win,pick,off,def,ml){
    var c=pick?'#22c55e':'#ef4444',logo='https://a.espncdn.com/i/teamlogos/nfl/500/'+_logoAbbr(abbr)+'.png';
    return '<div style="min-width:0;flex:1 1 260px;background:linear-gradient(145deg,'+(pick?'rgba(34,197,94,.12)':'rgba(239,68,68,.07)')+',rgba(15,23,42,.45));border:1px solid '+(pick?'rgba(34,197,94,.45)':'rgba(239,68,68,.3)')+';border-radius:14px;padding:16px;box-sizing:border-box">'
      +'<div style="display:flex;align-items:center;gap:11px"><img src="'+_esc(logo)+'" style="width:42px;height:42px;object-fit:contain" alt="" onerror="this.style.visibility=&#39;hidden&#39;"/><div style="min-width:0"><div style="font-size:1.25rem;font-weight:950;color:#fff">'+_esc(abbr)+'</div><div style="font-size:.65rem;color:#94a3b8;white-space:nowrap;overflow:hidden;text-overflow:ellipsis">'+_esc(sp||'Starter unavailable')+'</div></div><span style="margin-left:auto;font-size:.58rem;color:'+c+';font-weight:900">'+(pick?'MODEL WINNER':'CHALLENGER')+'</span></div>'
      +'<div style="display:flex;gap:6px;margin-top:13px;flex-wrap:wrap"><span style="padding:4px 7px;border-radius:5px;background:#172033;color:#93c5fd;font-size:.6rem;font-weight:800">OFF #'+val(off)+'</span><span style="padding:4px 7px;border-radius:5px;background:#172033;color:#86efac;font-size:.6rem;font-weight:800">DEF #'+val(def)+'</span><span style="padding:4px 7px;border-radius:5px;background:#172033;color:#fbbf24;font-size:.6rem;font-weight:800">ML '+val(ml)+'</span></div>'
      +'<div style="display:flex;justify-content:space-between;align-items:end;margin-top:16px"><div><div style="font-size:.58rem;color:#64748b;font-weight:800;letter-spacing:.08em">PROJECTED POINTS</div><div style="font-size:2.25rem;line-height:1;color:#fff;font-weight:950">'+val(proj,true)+'</div></div><div style="text-align:right"><div style="font-size:1.3rem;color:'+c+';font-weight:950">'+val(win)+'%</div><div style="font-size:.58rem;color:#94a3b8;font-weight:800">WIN PROBABILITY</div></div></div>'
      +'<div style="height:8px;border-radius:5px;background:#172033;overflow:hidden;margin-top:12px"><div style="height:100%;width:'+Math.max(0,Math.min(100,Number(win)||0))+'%;background:'+c+';border-radius:5px"></div></div></div>';
  }
  var pick=_esc(gp.pick_abbr||'—'), modelWin=gp.pick_home?gp.win_home:gp.win_away;
  var totalLine=gp.total_line!=null?_nflGpFix(gp.total_line):'—',projTotal=val(gp.proj_total,true);
  var totalCall=gp.total_pick?gp.total_pick+' '+totalLine:'No total call';
  var totalEdge=gp.total_edge!=null?((gp.total_edge>0?'+':'')+_nflGpFix(gp.total_edge)+' pts'):'—';
  var market=gp.mkt_edge!=null?((gp.mkt_edge>0?'+':'')+gp.mkt_edge+'% '+(gp.value_flag?'value':'edge')):'No market edge';
  var marketColor=gp.mkt_edge>0?'#4ade80':gp.mkt_edge<0?'#f87171':'#94a3b8';
  var tile=function(label,a,b){return '<div style="background:#111827;border:1px solid #243047;border-radius:9px;padding:11px;min-width:0"><div style="font-size:.57rem;color:#64748b;font-weight:900;letter-spacing:.07em;text-transform:uppercase">'+label+'</div><div style="margin-top:5px;color:#e2e8f0;font-size:.72rem;font-weight:800;line-height:1.5">'+a+' <span style="color:#64748b">·</span> '+b+'</div></div>';};
  var inputs=tile('Recent L5 adjusted',_esc(gp.away_abbr)+' '+val(gp.recent_away,true),_esc(gp.home_abbr)+' '+val(gp.recent_home,true))
    +tile('Last-season anchor',_esc(String(gp.reference_season||'Last season').toUpperCase()),_esc(gp.away_abbr)+' '+val(gp.last_away,true)+' · '+_esc(gp.home_abbr)+' '+val(gp.last_home,true))
    +tile('Blended stats baseline','45% L5 / 55% season',_esc(gp.away_abbr)+' '+val(gp.stat_away,true)+' · '+_esc(gp.home_abbr)+' '+val(gp.stat_home,true))
    +tile('Exact venue split',_esc(gp.away_abbr)+' AWAY '+val(gp.away_venue_off_pts,true),_esc(gp.home_abbr)+' HOME '+val(gp.home_venue_off_pts,true))
    +tile('H2H blend',val(gp.h2h_weight_pct,true)+'% adjustment',val(gp.h2h_exact_venue_games)+' exact · '+val(gp.h2h_reversed_venue_games)+' reversed');
  var drivers=(gp.drivers||[]).map(function(d){return '<li style="display:flex;gap:9px;align-items:flex-start;margin:0 0 9px;color:#cbd5e1"><span style="width:6px;height:6px;border-radius:50%;background:#818cf8;margin-top:6px;flex:none"></span><span>'+_esc(d)+'</span></li>';}).join('');
  if(!drivers)drivers='<li style="color:#64748b;list-style:none">No model drivers were supplied.</li>';
  var marketBlock=gp.mkt_edge!=null?'<div style="display:grid;grid-template-columns:repeat(auto-fit,minmax(120px,1fr));gap:8px">'+tile('Model probability',val(modelWin)+'%','on '+pick)+tile('No-vig market',val(gp.pick_home?gp.mkt_home_pct:gp.mkt_away_pct)+'%','derived from book')+tile('Moneyline',val(gp.pick_home?gp.home_ml_odds:gp.away_ml_odds),_esc(gp.pick_home?gp.home_ml_book:gp.away_ml_book))+ '</div>':'<div style="color:#64748b;font-size:.75rem">No moneyline market data was supplied for this game.</div>';
  ov.innerHTML='<div style="background:#080b12;border:1px solid #26334a;border-radius:20px;max-width:920px;width:100%;max-height:calc(100vh - 28px);overflow-y:auto;overflow-x:hidden;box-sizing:border-box;margin:auto;padding:clamp(16px,3vw,28px);box-shadow:0 28px 100px rgba(0,0,0,.85);position:relative">'
    +'<button onclick="document.getElementById(&#39;nfl-gp-modal&#39;).style.display=&#39;none&#39;" aria-label="Close" style="position:absolute;top:18px;right:18px;width:34px;height:34px;border-radius:9px;background:#172033;border:1px solid #334155;color:#cbd5e1;font-size:1.1rem;cursor:pointer">X</button>'
    +'<div style="font-size:.6rem;color:#818cf8;font-weight:900;letter-spacing:.14em">MONEY PICKS ARENA · NFL GAME PREDICTOR</div><div style="display:flex;align-items:start;gap:12px;margin-top:8px;padding-right:42px"><div style="min-width:0"><div style="font-size:clamp(1.5rem,4vw,2.2rem);font-weight:950;color:#fff;letter-spacing:-.04em">'+_esc(gp.away_abbr)+' <span style="color:#64748b">@</span> '+_esc(gp.home_abbr)+'</div><div style="font-size:.72rem;color:#94a3b8;margin-top:5px">'+_esc(gp.slate_date||'Date unavailable')+' · Blended matchup model</div></div><div style="margin-left:auto;white-space:nowrap;background:rgba(34,197,94,.14);border:1px solid rgba(34,197,94,.4);color:#4ade80;border-radius:8px;padding:7px 10px;font-size:.65rem;font-weight:900">'+(gp.value_flag?'VALUE ':'PICK ') +pick+'</div></div>'
     +_nflWeatherHtml(gp.weather)
     +'<div style="margin-top:20px;display:flex;flex-wrap:wrap;gap:12px">'+team(gp.away_abbr,gp.away_sp,gp.proj_away,gp.win_away,!gp.pick_home,gp.away_off_rank,gp.away_def_rank,gp.away_ml_odds)+team(gp.home_abbr,gp.home_sp,gp.proj_home,gp.win_home,gp.pick_home,gp.home_off_rank,gp.home_def_rank,gp.home_ml_odds)+'</div>'
    +'<div style="margin-top:14px;background:linear-gradient(90deg,rgba(129,140,248,.16),rgba(34,197,94,.1));border:1px solid #334155;border-radius:12px;padding:15px"><div style="font-size:.58rem;color:#a5b4fc;font-weight:900;letter-spacing:.1em">MODEL VERDICT</div><div style="display:flex;flex-wrap:wrap;gap:18px;align-items:end;margin-top:7px"><div><div style="font-size:.62rem;color:#94a3b8">PROJECTED FINAL</div><strong style="font-size:1.5rem;color:#fff">'+_esc(gp.away_abbr)+' '+val(gp.proj_away,true)+' — '+_esc(gp.home_abbr)+' '+val(gp.proj_home,true)+'</strong></div><div><div style="font-size:.62rem;color:#94a3b8">WINNER</div><strong style="font-size:1.15rem;color:#4ade80">'+pick+' · '+val(modelWin)+'%</strong></div><div><div style="font-size:.62rem;color:#94a3b8">TOTAL</div><strong style="font-size:1.05rem;color:#fbbf24">'+totalCall+' · '+totalEdge+'</strong><div style="font-size:.62rem;color:#94a3b8">Model '+projTotal+' vs book '+totalLine+'</div></div></div></div>'
    +'<section style="margin-top:18px"><div style="font-size:.62rem;color:#a78bfa;font-weight:900;letter-spacing:.12em;margin-bottom:9px">MARKET VALUE</div>'+marketBlock+'<div style="margin-top:10px;color:'+marketColor+';font-weight:900;font-size:.82rem">'+market+'</div></section>'
    +'<section style="margin-top:18px"><div style="font-size:.62rem;color:#a78bfa;font-weight:900;letter-spacing:.12em;margin-bottom:9px">MODEL INPUTS</div><div style="display:grid;grid-template-columns:repeat(auto-fit,minmax(190px,1fr));gap:8px">'+inputs+'</div></section>'
    +'<section style="margin-top:18px;background:#0d1422;border:1px solid #1e2b40;border-radius:12px;padding:15px"><div style="font-size:.62rem;color:#a78bfa;font-weight:900;letter-spacing:.12em;margin-bottom:11px">WHY THIS PICK</div><ul style="padding:0;margin:0;list-style:none">'+drivers+'</ul></section>'
    +'<div id="nfl-gp-history" style="margin-top:18px;background:#0d1422;border:1px solid #1e2b40;border-radius:12px;padding:15px;font-size:.75rem;color:#94a3b8"><div style="color:#64748b;text-align:center;font-weight:700">Loading last five meetings...</div></div>'
    +'<div style="color:#475569;font-size:.6rem;margin-top:16px;text-align:center;text-transform:uppercase;letter-spacing:.08em;font-weight:800">Display only · Not tracked · No additional sportsbook requests</div></div>';
  _nflGpLoadHistory(gp);
  }catch(err){
    console.error('Game Predictor breakdown failed',err);
    ov.innerHTML='<div style="margin:auto;background:#09090b;border:1px solid #ef4444;border-radius:16px;max-width:520px;padding:24px;color:#e2e8f0">'
      +'<div style="font-weight:900;color:#f87171;margin-bottom:8px">Game breakdown could not open</div>'
      +'<div style="font-size:.82rem;color:#94a3b8">Close this window and try the card again.</div>'
      +'<button onclick="document.getElementById(&#39;nfl-gp-modal&#39;).style.display=&#39;none&#39;" style="margin-top:16px;background:#1e293b;border:0;border-radius:8px;padding:9px 14px;color:#fff;font-weight:800;cursor:pointer">Close</button></div>';
  }
}
function _nflGpBetForm(key){
  var src=(window.__NFL_GP_BET__||{})[key]; if(!src) return;
  window.__NFL_BET_CUR__=src;
  var ov=document.getElementById('nfl-bet-modal');
  if(!ov){
    ov=document.createElement('div');ov.id='nfl-bet-modal';
    ov.style.cssText='position:fixed;inset:0;background:rgba(0,0,0,.82);z-index:10001;display:flex;align-items:center;justify-content:center;padding:16px';
    ov.onclick=function(e){if(e.target===ov)ov.style.display='none';};
    document.body.appendChild(ov);
  }
  var pickTxt=src.side+(src.line!=null?' '+src.line:'')+' '+(src.stat_label||'');
  ov.innerHTML=`<div style="background:#161616;border:1px solid #0e7490;border-radius:16px;max-width:360px;width:100%;padding:22px;box-shadow:0 20px 60px rgba(0,0,0,.7)">
    <div style="font-weight:900;color:#e2e8f0;font-size:1rem;margin-bottom:4px">Track Game Predictor Bet</div>
    <div style="color:#7c3aed;font-weight:800;font-size:.85rem;margin-bottom:14px">${_esc(src.name)}</div>
    <div style="background:#0a1120;border-radius:8px;padding:10px 12px;margin-bottom:14px;font-size:.8rem;color:#94a3b8">
      Pick: <b style="color:#e2e8f0">${_esc(pickTxt)}</b>
    </div>
    <label style="font-size:.72rem;color:#9ca3af;font-weight:600">Odds (American)
      <input id="nfl-gp-bet-odds" type="number" value="${src.odds!=null?src.odds:''}" style="display:block;width:100%;margin-top:5px;background:#0b0b0b;border:1px solid #333;border-radius:8px;padding:9px 11px;color:#fbbf24;font-family:monospace;font-weight:700;font-size:.95rem">
    </label>
    <label style="font-size:.72rem;color:#9ca3af;font-weight:600;margin-top:10px;display:block">Bet size ($)
      <input id="nfl-gp-bet-stake" type="number" min="0" step="0.01" placeholder="e.g. 50" style="display:block;width:100%;margin-top:5px;background:#0b0b0b;border:1px solid #333;border-radius:8px;padding:9px 11px;color:#fff;font-weight:700;font-size:.95rem">
    </label>
    <div id="nfl-gp-bet-msg" style="font-size:.76rem;color:#f87171;min-height:1em;margin-top:6px"></div>
    <div style="display:flex;gap:10px;margin-top:14px">
      <button onclick="document.getElementById('nfl-bet-modal').style.display='none'" style="flex:1;background:#1e293b;color:#94a3b8;border:none;border-radius:9px;padding:11px;font-weight:800;cursor:pointer">Cancel</button>
      <button onclick="_nflGpSaveBet()" style="flex:2;background:#0e7490;color:#fff;border:none;border-radius:9px;padding:11px;font-weight:800;cursor:pointer;font-size:.92rem">Log Bet</button>
    </div>
  </div>`;
  ov.style.display='flex';
}
function _nflGpSaveBet(){
  var src=window.__NFL_BET_CUR__; if(!src) return;
  var odds=parseFloat(document.getElementById('nfl-gp-bet-odds').value);
  var stake=parseFloat(document.getElementById('nfl-gp-bet-stake').value);
  var msg=document.getElementById('nfl-gp-bet-msg');
  if(isNaN(odds)||isNaN(stake)||stake<=0){if(msg)msg.textContent='Enter valid odds and stake.';return;}
  var payload=Object.assign({},src,{odds:odds,stake:stake,date_placed:src.date||window.__NFL_DATE__||''});
  fetch('/api/nfl/bet',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(payload)})
    .then(function(r){return r.json();})
    .then(function(r){
      document.getElementById('nfl-bet-modal').style.display='none';
      _nflToast('Bet logged!');
    }).catch(function(){if(msg)msg.textContent='Failed to save. Try again.';});
}
function _renderNflGamePredictor(d){
  var card=document.getElementById('nfl-gp-card');
  if(!card) return;
  var gp=(d&&d.game_predictions)||[];
  if(!gp.length){card.style.display='none';return;}
  window.__NFL_GP__=gp;
  card.style.display='';
  var html='<div class="nfl-gp-grid">';
  for(var i=0;i<gp.length;i++) html+=_nflGpCard(gp[i],i);
  html+='</div>';
  document.getElementById('nfl-gp-body').innerHTML=html;
}
function _nflCoachNum(v){
  if(v==null||v==='')return null;
  var n=Number(String(v).replace('+','').trim());
  return isFinite(n)&&n!==0?n:null;
}
function _nflCoachImplied(v){
  var n=_nflCoachNum(v);if(n==null)return null;
  return n<0?(-n/(-n+100)*100):(100/(n+100)*100);
}
function _nflCoachOdds(v){var n=Number(v);return n>0?'+'+n:String(n);}
function _nflCoachSigned(v){var n=Number(v||0);return (n>=0?'+':'')+n.toFixed(2);}
function _nflCoachProps(sourceCandidates){
  var d=(window._nflState||{}).d||{},seen={},out=[];
  // Coach categories must scan the complete analyzed slate. `d.picks` is the
  // reduced board list and can omit an otherwise valid priced market family.
  // An explicitly present but empty coach_candidates array must not shadow the
  // populated full slate.
  var source=Array.isArray(sourceCandidates)?sourceCandidates:
    (Array.isArray(d.coach_candidates)&&d.coach_candidates.length?d.coach_candidates:
      (Array.isArray(d.all)&&d.all.length?d.all:(d.picks||[])));
  source.forEach(function(p){
    if(p.coachEligible===false || p.availabilityVerified===false
       ||p.betQualified===false||p.roleRiskBlockPremium===true)return;
    // The live API only serves the current result cache for 15 minutes. Do not
    // apply a second browser-clock/per-row timestamp gate: old-format rows or a
    // page left open can otherwise erase every Coach candidate after loading.
    var side=String(p.pick||'OVER').toUpperCase();
    var odds=_nflSideOdds(p,side),implied=_nflCoachImplied(odds);
    var line=p.realLine!=null?p.realLine:p.dispLine;
    var prob=Number(p.dispScore!=null?p.dispScore:p.score);
    if(line==null||implied==null||!isFinite(prob)||prob<=0)return;
    var key=String(p.pid||p.name)+'|'+String(p.mkt||p.label)+'|'+side+'|'+line+'|'+odds;
    if(seen[key])return;seen[key]=1;
    out.push({
      player:p.name||'',position:p.position||p.roster_position||'',team:p.team||'',opponent:p.opponent||p.opp||'',
      market:p.mkt||p.label||'NFL Prop',side:side,line:Number(line),odds:Number(odds),
      oppositeOdds:_nflSideOdds(p,side==='OVER'?'UNDER':'OVER'),
      appProb:Math.max(0,Math.min(100,prob)),implied:implied,
      projection:p.projAvg!=null?Number(p.projAvg):(p.avg!=null?Number(p.avg):null),
      recentRate:Number(p.vsLineRate||p.rateB||0),recentHits:Number(p.vsLineHits||p.hitsB||0),
      recentTotal:Number(p.vsLineTotal||p.totB||0),oppRate:Number(p.rateA||0),
      oppHits:Number(p.hitsA||0),oppTotal:Number(p.totA||0),book:side==='UNDER'?(p.under_book||''):(p.over_book||''),
      isAlternate:!!p.isAlternate,game_start:p.game_start||'',
      isRookie:p.isRookie===true,rookieVerified:p.rookieVerified===true,
       openingLine:p.openingLine,currentLine:p.currentLine!=null?p.currentLine:p.realLine,
       lineMove:p.lineMove,lineMovementAvailable:!!p.lineMovementAvailable,
        slate_date:p.slate_date||'',source:p
    });
  });
  out.forEach(function(p){p.edge=p.appProb-p.implied;});
  return out;
}
function _nflCoachSafest(props){
  var seen={},out=[];
  (props||[]).forEach(function(p){var k=p.player+'|'+p.market+'|'+p.side+'|'+p.line+'|'+p.odds;if(!seen[k]){seen[k]=1;out.push(p);}});
  (props||[]).forEach(function(p){
    if(_nflCoachFamily(p.market)==='td')return;
    var odds=_nflCoachNum(p.oppositeOdds);if(odds==null)return;
    var side=p.side==='OVER'?'UNDER':'OVER',k=p.player+'|'+p.market+'|'+side+'|'+p.line+'|'+odds;
    if(seen[k])return;seen[k]=1;
    var q=Object.assign({},p,{side:side,odds:odds,oppositeOdds:p.odds,implied:_nflCoachImplied(odds),
      appProb:Math.max(0,Math.min(100,100-p.appProb)),
      recentRate:p.recentTotal?Math.max(0,100-p.recentRate):0,
      recentHits:p.recentTotal?Math.max(0,p.recentTotal-p.recentHits):0,
      oppRate:p.oppTotal?Math.max(0,100-p.oppRate):0,
      oppHits:p.oppTotal?Math.max(0,p.oppTotal-p.oppHits):0,
      book:side==='UNDER'?(p.source.under_book||''):(p.source.over_book||'')});
    q.edge=q.appProb-q.implied;out.push(q);
  });
  return out;
}
function _nflCoachParse(question,props){
  var q=String(question||'').toLowerCase(),words=' '+q.replace(/[^a-z0-9]+/g,' ').replace(/ +/g,' ').trim()+' ';
  var f={mode:'edge',limit:10,side:'',market:'',marketExact:'',players:[],teams:[],minOdds:null,maxOdds:null,onePerCategory:false};
  if(q.indexOf('safe')>=0||q.indexOf('most likely')>=0||q.indexOf('highest probability')>=0)f.mode='safe';
  if(/(?:each|every|all)\\s+(?:available\\s+)?(?:market\\s+)?categor/.test(q)
      ||/(?:each|every|all)\\s+(?:available\\s+)?market/.test(q)){
    f.onePerCategory=true;
  }
  var top=words.match(/ top +([0-9]{1,2}) /);if(top)f.limit=Math.max(1,Math.min(10,Number(top[1])));
  if(words.indexOf(' under ')>=0)f.side='UNDER';else if(words.indexOf(' over ')>=0)f.side='OVER';
  var exactMarkets=[
    {label:'RB Total Yds',terms:['rushing and receiving yards','rushing plus receiving yards','rush and receiving yards','rush plus receiving yards','rush receiving yards','rush rec yards','combined yards','total yards']},
    {label:'Completions',terms:['qb completions','qb completion','quarterback completions','quarterback completion','pass completions','pass completion','passing completions','passing completion','completions']},
    {label:'Pass Att',terms:['qb attempts','qb attempt','quarterback attempts','quarterback attempt','pass attempts','pass attempt','passing attempts','passing attempt']},
    {label:'Pass Yds',terms:['passing yards','passing yard','passing yds','passing yd','pass yards','pass yard','pass yds','pass yd']},
    {label:'Pass TDs',terms:['passing touchdowns','passing touchdown','passing tds','passing td','pass touchdowns','pass touchdown','pass tds','pass td']},
    {label:'INT Thrown',terms:['interceptions thrown','interception thrown','passing interceptions','passing interception','qb interceptions','qb interception','pass ints','pass int']},
    {label:'Rush Att',terms:['rushing attempts','rushing attempt','rush attempts','rush attempt','carries']},
    {label:'Rush Yds',terms:['rushing yards','rushing yard','rushing yds','rushing yd','rush yards','rush yard','rush yds','rush yd']},
    {label:'Rec Yds',terms:['receiving yards','receiving yard','receiving yds','receiving yd','reception yards','reception yard','rec yards','rec yard','rec yds','rec yd']},
    {label:'Receptions',terms:['receptions','reception','catches','catch']},
    {label:'Anytime TD',terms:['anytime touchdowns','anytime touchdown','anytime tds','anytime td','td scorers','td scorer']},
    {label:'Tackles+Ast',terms:['tackles assists','tackles assist','tackles plus assists','tackles+assists','tackle assists','tackle assist','total tackles']},
    {label:'Sacks',terms:['player sacks','player sack','defensive sacks','defensive sack','sacks','sack']},
    {label:'Def INT',terms:['defensive interceptions','defensive interception','defender interceptions','defender interception','def ints','def int']},
    {label:'Kick Pts',terms:['kicking points','kicking point','kicker points','kicker point','kick points','kick point']},
    {label:'FG Made',terms:['field goals made','field goal made','field goals','field goal','fgs made','fg made']}
  ];
  exactMarkets.some(function(def){
    if(def.terms.some(function(term){return q.indexOf(term)>=0;})){f.marketExact=def.label;return true;}
    return false;
  });
  var markets=[['passing','pass'],['pass ','pass'],['quarterback','pass'],[' qb ','pass'],
    ['rushing','rush'],['rush ','rush'],['running back','rush'],[' rb ','rush'],
    ['receiving','rec'],['reception','rec'],['receiver','rec'],[' wr ','rec'],[' tight end','rec'],[' te ','rec'],
    ['touchdown','td'],[' td','td'],['tackle','def'],['sack','def'],['defensive','def'],['defense','def'],
    ['kicker','kick'],['kicking','kick'],['field goal','kick']];
  markets.some(function(x){if(q.indexOf(x[0])>=0){f.market=x[1];return true;}return false;});
  var neg=q.match(/-[0-9]{2,4}/g)||[];if(neg.length>=2){var ns=neg.slice(0,2).map(Number);f.minOdds=Math.min.apply(null,ns);f.maxOdds=Math.max.apply(null,ns);}
  props.forEach(function(p){
    var n=String(p.player||'').toLowerCase();if(n&&q.indexOf(n)>=0&&f.players.indexOf(n)<0)f.players.push(n);
    [p.team,p.opponent].forEach(function(t){var x=String(t||'').toLowerCase();if(x&&q.indexOf(x)>=0&&f.teams.indexOf(x)<0)f.teams.push(x);});
  });
  return f;
}
function _nflCoachFamily(m){
  m=String(m||'').toLowerCase();
  if(m.indexOf('rb total yds')>=0)return 'rush';
  if(m.indexOf('pass')>=0||m.indexOf('completion')>=0||m.indexOf('int thrown')>=0)return 'pass';
  if(m.indexOf('rush')>=0)return 'rush';
  if(m.indexOf('rec')>=0)return 'rec';
  if(m.indexOf('touchdown')>=0||m.indexOf('anytime td')>=0)return 'td';
  if(m.indexOf('tackle')>=0||m.indexOf('sack')>=0||m.indexOf('def int')>=0)return 'def';
  if(m.indexOf('kick')>=0||m.indexOf('fg made')>=0)return 'kick';
  return '';
}
function _nflCoachHit(side,value,line){
  var v=Number(value),l=Number(line);if(!isFinite(v)||!isFinite(l)||v===l)return null;
  return side==='UNDER'?v<l:v>l;
}
function _nflCoachLogRate(p,count){
  var games=(p.source.glog||[]).slice(0,count),hits=0,total=0;
  games.forEach(function(g){var hit=_nflCoachHit(p.side,g.v,p.line);if(hit==null)return;total++;if(hit)hits++;});
  return {hits:hits,total:total,rate:total?(hits/total*100):null};
}
function _nflCoachRateTile(label,rate,hits,total){
  var shown=rate!=null&&Number(total)>0,pct=shown?Math.max(0,Math.min(100,Number(rate))):0;
  return '<div class="nfl-coach-stat"><div class="k">'+_esc(label)+'</div><div class="v">'+(shown?Number(rate).toFixed(0)+'% · '+hits+'/'+total:'N/A')+'</div><div class="nfl-coach-ratebar"><span style="width:'+pct+'%"></span></div></div>';
}
function _nflCoachOppHistory(p,rate,hits,total){
  var s=p.source||{},games=s.vsOppLog||[],shown=rate!=null&&Number(total)>0;
  var pct=shown?Math.max(0,Math.min(100,Number(rate))):0;
  var line=Number(p.line),over=0,under=0,push=0;
  games.forEach(function(g){var v=Number(g.v);if(v>line)over++;else if(v<line)under++;else push++;});
  var rows=games.length?games.map(function(g){
    var v=Number(g.v),result=v>line?'OVER':(v<line?'UNDER':'PUSH');
    var cls=result==='PUSH'?'push':(result===p.side?'hit':'miss');
    var venue=g.ha?(' · '+_esc(g.ha)):'';
    return '<div class="nfl-coach-opp-row '+cls+'"><span>'+_esc(g.d)+venue+'</span><span><b>'+v.toFixed(1)+'</b> <span class="result">'+result+'</span></span></div>';
  }).join(''):'<div class="nfl-coach-opp-head">No game-by-game opponent history is available.</div>';
  return '<details class="nfl-coach-opp-history">'
    +'<summary class="nfl-coach-stat" title="View every '+_esc(p.market)+' game against '+_esc(p.opponent)+'">'
    +'<div class="k">vs '+_esc(p.opponent)+' · all meetings</div><div class="v">'+(games.length?'OVER '+over+'/'+games.length+' · UNDER '+under+'/'+games.length+(push?' · PUSH '+push:''):'N/A')+'</div>'
    +'<div class="nfl-coach-ratebar"><span style="width:'+pct+'%"></span></div></summary>'
    +'<div class="nfl-coach-opp-games"><div class="nfl-coach-opp-head">'+_esc(p.player)+' vs '+_esc(p.opponent)
    +' · every result compared with today’s '+_esc(p.market)+' line of '+line.toFixed(1)+'</div>'+rows+'</div></details>';
}
function _nflCoachRateTiles(p){
  var s=p.source||{},l5=_nflCoachLogRate(p,5),l10=_nflCoachLogRate(p,10);
  var venueRate=p.side==='UNDER'?(s.totB?100-Number(s.rateB||0):null):Number(s.rateB);
  var venueHits=p.side==='UNDER'?Math.max(0,Number(s.totB||0)-Number(s.hitsB||0)):Number(s.hitsB||0);
  var bookRate=p.side==='UNDER'?(s.vsLineTotal?100-Number(s.vsLineRate||0):null):Number(s.vsLineRate);
  var bookHits=p.side==='UNDER'?Math.max(0,Number(s.vsLineTotal||0)-Number(s.vsLineHits||0)):Number(s.vsLineHits||0);
  var oppRate=p.side==='UNDER'?(s.totA?100-Number(s.rateA||0):null):Number(s.rateA);
  var oppHits=p.side==='UNDER'?Math.max(0,Number(s.totA||0)-Number(s.hitsA||0)):Number(s.hitsA||0);
  var oppositeRate=l10.total?100-l10.rate:null,oppositeHits=l10.total-l10.hits;
  return '<div class="nfl-coach-stats">'
    +_nflCoachRateTile('L5',l5.rate,l5.hits,l5.total)
    +_nflCoachRateTile('L10',l10.rate,l10.hits,l10.total)
    +_nflCoachRateTile(s.homeRoad==='H'?'Home split':(s.homeRoad==='R'?'Away split':'Venue split'),venueRate,venueHits,s.totB)
    +_nflCoachRateTile('vs Book Line',bookRate,bookHits,s.vsLineTotal)
    +_nflCoachOppHistory(p,oppRate,oppHits,s.totA)
    +_nflCoachRateTile(p.side==='OVER'?'Under L10':'Over L10',oppositeRate,oppositeHits,l10.total)
    +'</div>';
}
function _nflCoachGameTiles(p){
  var games=(p.source.glog||[]).slice(0,10);
  if(!games.length)return '<div style="margin-top:9px">No game-by-game log is available.</div>';
  return '<div class="nfl-coach-games">'+games.map(function(g){
    var hit=_nflCoachHit(p.side,g.v,p.line),cls=hit==null?'':(hit?'hit':'miss');
    return '<div class="nfl-coach-game '+cls+'"><div class="d">'+_esc(g.d)+(g.o?' · '+_esc(g.o):'')+'</div><div class="v">'+Number(g.v).toFixed(1)+'</div></div>';
  }).join('')+'</div>';
}
function _nflCoachLineMovement(p){
  var s=p.source||{};
  if(!s.lineMovementAvailable||s.openingLine==null||s.currentLine==null){
    return '<div>No scheduled opening line is stored for this exact player and market. Use Full Week on Wednesday for Thursday games, Friday for Sunday games, or Saturday for Monday games; then Run Picks on game day for the comparison.</div>';
  }
  var open=Number(s.openingLine),current=Number(s.currentLine),move=Number(s.lineMove||0);
  var direction=move>0?'UP':(move<0?'DOWN':'UNCHANGED');
  var color=move===0?'#9ca3af':'#fbbf24';
  var impact=move===0
    ?'The book line has not moved.'
    :(move>0
      ?(p.side==='OVER'?'The higher line makes this Over harder to clear.':'The higher line gives this Under more room.')
      :(p.side==='OVER'?'The lower line makes this Over easier to clear.':'The lower line gives this Under less room.'));
  var openOdds=s.openingOdds!=null?_nflCoachOdds(s.openingOdds):'N/A';
  var captured=s.lineOpenCapturedAt?new Date(s.lineOpenCapturedAt).toLocaleString():'scheduled opening run';
  return '<div class="nfl-coach-stats">'
    +'<div class="nfl-coach-stat"><div class="k">Weekly opening line</div><div class="v">'+open+'</div></div>'
    +'<div class="nfl-coach-stat"><div class="k">Current game-day line</div><div class="v">'+current+'</div></div>'
    +'<div class="nfl-coach-stat"><div class="k">Line move</div><div class="v" style="color:'+color+'">'+direction+' '+_nflCoachSigned(move)+' pts</div></div>'
    +'<div class="nfl-coach-stat"><div class="k">Selected-side odds</div><div class="v">'+openOdds+' → '+_nflCoachOdds(p.odds)+'</div></div>'
    +'</div><div style="margin-top:9px;color:#cbd5e1">'+impact+'</div>'
    +'<div style="margin-top:7px;color:#6b7280;font-size:.68rem">Opening snapshot: '+_esc(captured)+'. Line movement can reflect betting pressure, injuries, limits, or sportsbook adjustment; it does not by itself prove whether public or sharp bettors caused the move.</div>';
}
function _nflCoachAccordions(p){
  var s=p.source||{},opp=_nflCoachNum(p.oppositeOdds),oppImp=opp!=null?_nflCoachImplied(opp):null;
  var other=p.side==='OVER'?'UNDER':'OVER',projection=p.projection!=null&&isFinite(p.projection)?p.projection.toFixed(2):'N/A';
  var avg=s.avg!=null&&isFinite(Number(s.avg))?Number(s.avg).toFixed(2):'N/A';
  var gap=p.projection!=null&&isFinite(p.projection)?Number(p.projection)-Number(p.line):null;
  var venue=s.homeRoad==='H'?'Home':(s.homeRoad==='R'?'Away':'N/A');
  var def=(s.defRank!=null?('#'+s.defRank+' '+_esc(s.defLbl||'defense')):'N/A');
  var defAdj=s.defAdj!=null?((Number(s.defAdj)>=0?'+':'')+Number(s.defAdj).toFixed(1)+'%'):'N/A';
  var gameTime=s.game_start?new Date(s.game_start).toLocaleString():'N/A';
  var injuryStatus=_esc(s.injuryStatus||'UNVERIFIED');
  var injuryColor=s.injuryStatus==='ACTIVE'?'#4ade80':(s.injuryStatus==='OUT'||s.injuryStatus==='DOUBTFUL'?'#f87171':'#fbbf24');
  var baseProjection=s.baseProjAvg!=null&&isFinite(Number(s.baseProjAvg))?Number(s.baseProjAvg).toFixed(2):projection;
  var injuryAdj=s.injuryAdj!=null&&isFinite(Number(s.injuryAdj))?((Number(s.injuryAdj)>=0?'+':'')+Number(s.injuryAdj).toFixed(2)):'0.00';
  var injuryReasons=(s.injuryOpportunityReasons||[]);
  var injuryText=injuryReasons.length?injuryReasons.map(function(r){return _esc(r.player)+' ('+_esc(r.status)+') '+(Number(r.bump_pct)>=0?'+':'')+Number(r.bump_pct).toFixed(1)+'% opportunity';}).join('<br>'):'No same-position teammate adjustment.';
  var injuryUpdated=s.injuryUpdatedAt?new Date(s.injuryUpdatedAt).toLocaleString():'N/A';
  var quoteUpdated=s.quoteFetchedAt?new Date(s.quoteFetchedAt).toLocaleString():'N/A';
  return '<div class="nfl-coach-accord">'
    +'<details><summary>Odds Comparison</summary><div class="nfl-coach-accord-body"><div class="nfl-coach-stats">'
    +'<div class="nfl-coach-stat"><div class="k">Selected side</div><div class="v">'+p.side+' '+_nflCoachOdds(p.odds)+' · '+p.implied.toFixed(1)+'% implied</div></div>'
    +'<div class="nfl-coach-stat"><div class="k">Other side</div><div class="v">'+(opp!=null?other+' '+_nflCoachOdds(opp)+' · '+oppImp.toFixed(1)+'% implied':'N/A')+'</div></div>'
    +'<div class="nfl-coach-stat"><div class="k">Source</div><div class="v">'+_esc(p.book||'Sportsbook line')+'</div></div>'
    +'<div class="nfl-coach-stat"><div class="k">Quote checked</div><div class="v">'+_esc(quoteUpdated)+'</div></div>'
    +'</div><div style="margin-top:7px">Only genuine prices from a sportsbook response refreshed within 15 minutes are eligible for live Coach rankings.</div></div></details>'
    +'<details><summary>Hit Rate Chart</summary><div class="nfl-coach-accord-body">'+_nflCoachRateTiles(p)+_nflCoachGameTiles(p)+'</div></details>'
    +'<details><summary>Line Movement</summary><div class="nfl-coach-accord-body">'+_nflCoachLineMovement(p)+'</div></details>'
    +'<details><summary>Key Stats</summary><div class="nfl-coach-accord-body"><div class="nfl-coach-stats">'
    +'<div class="nfl-coach-stat"><div class="k">Projection</div><div class="v">'+projection+'</div></div>'
    +'<div class="nfl-coach-stat"><div class="k">Base projection</div><div class="v">'+baseProjection+'</div></div>'
    +'<div class="nfl-coach-stat"><div class="k">Injury adjustment</div><div class="v">'+injuryAdj+'</div></div>'
    +'<div class="nfl-coach-stat"><div class="k">Recent average</div><div class="v">'+avg+'</div></div>'
    +'<div class="nfl-coach-stat"><div class="k">Projection gap</div><div class="v">'+(gap!=null?_nflCoachSigned(gap):'N/A')+'</div></div>'
    +'<div class="nfl-coach-stat"><div class="k">App probability</div><div class="v">'+p.appProb.toFixed(1)+'%</div></div>'
    +'<div class="nfl-coach-stat"><div class="k">Implied probability</div><div class="v">'+p.implied.toFixed(1)+'%</div></div>'
    +'<div class="nfl-coach-stat"><div class="k">Coach Edge</div><div class="v" style="color:'+(p.edge>=0?'#4ade80':'#f87171')+'">'+_nflCoachSigned(p.edge)+' pts</div></div>'
    +'</div></div></details>'
    +'<details><summary>Player &amp; Team Stats</summary><div class="nfl-coach-accord-body"><div class="nfl-coach-stats">'
    +'<div class="nfl-coach-stat"><div class="k">Matchup</div><div class="v">'+_esc(p.team)+' vs '+_esc(p.opponent)+'</div></div>'
    +'<div class="nfl-coach-stat"><div class="k">Venue</div><div class="v">'+venue+'</div></div>'
    +'<div class="nfl-coach-stat"><div class="k">Opponent defense</div><div class="v">'+def+'</div></div>'
    +'<div class="nfl-coach-stat"><div class="k">Defense ranking factor</div><div class="v">'+defAdj+'</div></div>'
    +'<div class="nfl-coach-stat"><div class="k">Recent games</div><div class="v">'+(s.glog||[]).length+'</div></div>'
    +'<div class="nfl-coach-stat"><div class="k">Game time</div><div class="v">'+_esc(gameTime)+'</div></div>'
    +'<div class="nfl-coach-stat"><div class="k">Player injury status</div><div class="v" style="color:'+injuryColor+'">'+injuryStatus+'</div></div>'
    +'<div class="nfl-coach-stat"><div class="k">Status checked</div><div class="v">'+_esc(injuryUpdated)+'</div></div>'
    +'</div><div style="margin-top:9px;color:#cbd5e1">'+injuryText+'</div>'
    +(s.injuryNote?'<div style="margin-top:7px;color:#94a3b8">'+_esc(s.injuryNote)+'</div>':'')
    +'</div></details></div>';
}
var __nflPerfectParlayPool=[],__nflPerfectParlayLegs=[],__nflPerfectParlayBoard=null;
var __nflPerfectParlayStake=100,__nflPerfectParlayNotice='',__nflPerfectParlayBoardSeq=0;
var __nflPerfectParlaySettings={legs:3,categories:[],side:'ALL'};
function _nflPerfectParlayInvalidate(reason){
  __nflPerfectParlayBoardSeq++;
  __nflPerfectParlayPool=[];__nflPerfectParlayLegs=[];__nflPerfectParlayBoard=null;
  __nflPerfectParlayNotice=reason?'The loaded board, date, scope, or system changed. Build a new parlay.':'';
}
function _nflPerfectParlayCommit(html){
  var el=document.getElementById('nflCoachAnswer');
  if(el){el.innerHTML=html;el.style.display='block';}
}
function _nflPerfectParlayPlayerKey(x){
  return String((x&&x.player)||'').toLowerCase().replace(/[^a-z0-9]/g,'');
}
function _nflPerfectParlayBoardSignature(){
  var d=(window._nflState||{}).d||{},dp=document.getElementById('datePicker');
  return [String((dp&&dp.value)||''),_nflRunScope(),_nflSystem(),
    String(d.anchor_date||d.date||''),d.week_mode?'week':'day',String(__nflPerfectParlayBoardSeq)].join('|');
}
function _nflPerfectParlayCurrent(){
  var ok=!!(__nflPerfectParlayBoard&&window._nflState&&
    __nflPerfectParlayBoard.state===window._nflState&&
    __nflPerfectParlayBoard.signature===_nflPerfectParlayBoardSignature()&&
    !__nflPerfectParlayPool.some(function(p){return _nflGameDone(p.source);}));
  if(!ok){
    var note=document.getElementById('nflPerfectParlayNotice');
    if(note)note.textContent='The loaded board, date, scope, or system changed. Build a new parlay from the current displayed picks.';
  }
  return ok;
}
function _nflPerfectParlayEligibleRows(side){
  var d=(window._nflState||{}).d||{},displayed=Array.isArray(d.picks)?d.picks:[],wanted=side||'ALL';
  return _nflCoachProps(displayed).filter(function(p){
    var src=p.source||{},book=p.book||'',sourceMarket=String(src.sourceMarket||src.market||'');
    if(wanted!=='ALL'&&p.side!==wanted)return false;
    if(p.side!=='OVER'&&p.side!=='UNDER')return false;
    if(p.isAlternate||src.isAlternate||/_alternate$/i.test(sourceMarket))return false;
    if(!book||src.realLine==null||p.line==null||!isFinite(Number(p.line))||Number(src.realLine)!==Number(p.line))return false;
    if(!isFinite(Number(p.odds))||Number(p.odds)<-1000||Number(p.odds)===0)return false;
    if(!isFinite(Number(p.appProb))||!isFinite(Number(p.implied))||Number(p.edge)<=0)return false;
    if(_nflGameDone(src))return false;
    p.slate_date=p.slate_date||src.slate_date||(!d.week_mode?d.date:'')||'';
    if(!p.slate_date)return false;
    return true;
  });
}
function setNflPerfectParlayCategories(on){
  document.querySelectorAll('input[name="nflPerfectParlayCat"]:not(:disabled)').forEach(function(cb){cb.checked=!!on;});
}
function showNflPerfectParlayBuilder(){
  var saved=__nflPerfectParlaySettings||{},savedLegs=Math.max(2,Math.min(10,Number(saved.legs)||3));
  var side=saved.side||'ALL',eligible=_nflPerfectParlayEligibleRows('ALL'),counts={};
  eligible.forEach(function(p){counts[String(p.market||'')]=(counts[String(p.market||'')]||0)+1;});
  var selected=(saved.categories&&saved.categories.length)?saved.categories.slice():_MORDER.slice();
  var cats=_MORDER.map(function(label){
    var count=counts[label]||0,checked=selected.indexOf(label)>=0,disabled=!count;
    return '<label style="display:flex;align-items:center;gap:6px;padding:7px 9px;background:'+(checked&&!disabled?'rgba(14,165,233,.14)':'#020617')+';border:1px solid '+(checked&&!disabled?'#0ea5e9':'#334155')+';border-radius:7px;color:'+(disabled?'#475569':'#e2e8f0')+';font-size:.68rem;font-weight:800;cursor:'+(disabled?'not-allowed':'pointer')+'"><input type="checkbox" name="nflPerfectParlayCat" value="'+_esc(label)+'"'+(checked&&!disabled?' checked':'')+(disabled?' disabled':'')+' style="accent-color:#0ea5e9"> '+_esc(label)+' <span style="color:#64748b">('+count+')</span></label>';
  }).join('');
  var sizes='';for(var i=2;i<=10;i++)sizes+='<option value="'+i+'"'+(i===savedLegs?' selected':'')+'>'+i+' legs</option>';
  var field='margin-top:5px;min-width:150px;background:#020617;color:#fff;border:1px solid #475569;border-radius:7px;padding:9px 10px;font-weight:800';
  _nflPerfectParlayCommit('<div><div class="nfl-coach-question">&#10024; Perfect Parlay</div>'
    +'<div class="nfl-coach-summary">Build a display-only parlay from the currently loaded NFL market boards. Legs require the exact displayed player, standard market, side, line, slate date, sportsbook, and price; alternate or borrowed quotes never qualify.</div>'
    +'<div style="margin-top:12px;padding:12px;background:#0f172a;border:1px solid #334155;border-radius:10px">'
    +'<div style="display:flex;justify-content:space-between;gap:8px;align-items:center;flex-wrap:wrap;margin-bottom:8px"><b style="color:#94a3b8;font-size:.68rem">CATEGORIES — SELECT ONE OR MORE</b><span><button onclick="setNflPerfectParlayCategories(true)" style="background:#1e293b;color:#bae6fd;border:1px solid #334155;border-radius:6px;padding:5px 8px;font-weight:800;cursor:pointer">Select all</button> <button onclick="setNflPerfectParlayCategories(false)" style="background:#1e293b;color:#94a3b8;border:1px solid #334155;border-radius:6px;padding:5px 8px;font-weight:800;cursor:pointer">Clear</button></span></div>'
    +'<div style="display:flex;flex-wrap:wrap;gap:7px">'+cats+'</div>'
    +'<div style="display:flex;align-items:end;gap:9px;flex-wrap:wrap;margin-top:13px">'
    +'<label style="color:#94a3b8;font-size:.68rem;font-weight:800">PARLAY SIZE<br><select id="nflPerfectParlayLegCount" style="'+field+'">'+sizes+'</select></label>'
    +'<label style="color:#94a3b8;font-size:.68rem;font-weight:800">SIDE<br><select id="nflPerfectParlaySide" style="'+field+'"><option value="ALL"'+(side==='ALL'?' selected':'')+'>Best available</option><option value="OVER"'+(side==='OVER'?' selected':'')+'>Overs only</option><option value="UNDER"'+(side==='UNDER'?' selected':'')+'>Unders only</option></select></label>'
    +'<button onclick="buildNflPerfectParlay()" style="background:linear-gradient(135deg,#0284c7,#7c3aed);color:#fff;border:0;border-radius:8px;padding:10px 15px;font-weight:950;cursor:pointer">BUILD PERFECT PARLAY</button></div></div></div>');
}
function _nflPerfectParlayAmerican(decimalOdds){
  var d=Number(decimalOdds);if(!isFinite(d)||d<=1)return 'N/A';
  var a=d>=2?(d-1)*100:-100/(d-1),r=Math.round(a);return (r>0?'+':'')+r;
}
function changeNflPerfectParlayLeg(index){
  if(!_nflPerfectParlayCurrent())return;
  var legs=__nflPerfectParlayLegs,pool=__nflPerfectParlayPool,current=legs[index];if(!current)return;
  var used={};legs.forEach(function(x,i){if(i!==index)used[_nflPerfectParlayPlayerKey(x)]=1;});
  var start=pool.indexOf(current),currentKey=_nflPerfectParlayPlayerKey(current);
  for(var step=1;step<=pool.length;step++){
    var next=pool[(Math.max(0,start)+step)%pool.length],key=_nflPerfectParlayPlayerKey(next);
    if(key!==currentKey&&!used[key]){
      legs[index]=next;__nflPerfectParlayNotice='Leg replaced. Combined odds and estimated payout updated.';
      renderNflPerfectParlay();return;
    }
  }
}
function generateNewNflPerfectParlay(){
  if(!_nflPerfectParlayCurrent())return;
  var legs=__nflPerfectParlayLegs,pool=__nflPerfectParlayPool,used={};
  legs.forEach(function(x){used[_nflPerfectParlayPlayerKey(x)]=1;});
  var fresh=pool.filter(function(x){return !used[_nflPerfectParlayPlayerKey(x)];});
  if(!fresh.length){__nflPerfectParlayNotice='No unused qualifying player remains. Edit categories, side, or leg count for more options.';renderNflPerfectParlay();return;}
  var next=fresh.slice(0,legs.length),rotated=legs.slice(1).concat(legs.slice(0,1));
  next=next.concat(rotated.slice(0,legs.length-next.length));
  var replacements=Math.min(fresh.length,legs.length);
  __nflPerfectParlayLegs=next;
  __nflPerfectParlayNotice=replacements===legs.length?'New parlay: every player was replaced using the same approved pool.':replacements+' fresh player'+(replacements===1?'':'s')+' included; '+(legs.length-replacements)+' retained because only '+pool.length+' unique qualifying players are available.';
  renderNflPerfectParlay();
}
function updateNflPerfectParlayStake(input){
  var stake=Number(input.value),valid=input.value.trim()!==''&&isFinite(stake)&&stake>0,combined=1;
  input.setCustomValidity(valid?'':'Enter a stake greater than zero.');
  __nflPerfectParlayLegs.forEach(function(x){combined*=Number(_amToDec(x.odds)||1);});
  if(valid)__nflPerfectParlayStake=stake;
  var profit=document.getElementById('nflPerfectParlayProfit'),ret=document.getElementById('nflPerfectParlayReturn');
  if(profit)profit.textContent=valid?'$'+(stake*(combined-1)).toFixed(2):'—';
  if(ret)ret.textContent=valid?'$'+(stake*combined).toFixed(2):'—';
}
function openNflPerfectParlayDetail(index){
  var p=__nflPerfectParlayLegs[index];if(!p||!_nflPerfectParlayCurrent())return;
  var why='<div style="background:rgba(14,165,233,.08);border:1px solid rgba(14,165,233,.3);border-radius:10px;padding:11px 12px;margin:10px 0 14px;color:#cbd5e1;font-size:.78rem;line-height:1.5"><b style="color:#7dd3fc">Why this leg:</b> Exact displayed standard-line pick with '+Number(p.appProb).toFixed(1)+'% app probability, '+Number(p.implied).toFixed(1)+'% implied probability, and '+_nflCoachSigned(p.edge)+' Coach Edge points.</div>';
  _openModal(_esc(p.player),_esc(p.market)+' · '+_esc(p.team)+' vs '+_esc(p.opponent)+' · '+_esc(p.side)+' '+_esc(String(p.line))+' · '+_esc(_nflCoachOdds(p.odds))+' · '+_esc(p.book),why+_nflCoachAccordions(p));
}
function renderNflPerfectParlay(){
  var legs=__nflPerfectParlayLegs||[];if(!legs.length)return;
  var combined=1,used={},hundred=0;
  legs.forEach(function(p){combined*=Number(_amToDec(p.odds)||1);used[_nflPerfectParlayPlayerKey(p)]=1;if(Number(p.appProb)>=99.95)hundred++;});
  var fresh=__nflPerfectParlayPool.filter(function(p){return !used[_nflPerfectParlayPlayerKey(p)];}).length;
  var rows=legs.map(function(p,i){
    var key=_nflPerfectParlayPlayerKey(p),canSwap=__nflPerfectParlayPool.some(function(x){var k=_nflPerfectParlayPlayerKey(x);return k!==key&&!used[k];});
    return '<tr><td style="padding:9px;border-top:1px solid #263244">'+(i+1)+'</td><td style="padding:9px;border-top:1px solid #263244"><button onclick="openNflPerfectParlayDetail('+i+')" style="background:none;border:0;color:#fff;text-decoration:underline;text-decoration-style:dotted;font-weight:900;cursor:pointer;padding:0">'+_esc(p.player)+'</button><br><small style="color:#64748b">'+_esc(p.team)+' vs '+_esc(p.opponent)+(p.slate_date?' · '+_esc(p.slate_date):'')+(Number(p.appProb)>=99.95?' · 100% APP PLAY':'')+'</small></td>'
      +'<td style="padding:9px;border-top:1px solid #263244">'+_esc(p.market)+'<br><b style="color:'+(p.side==='OVER'?'#4ade80':'#f87171')+'">'+_esc(p.side)+' '+_esc(String(p.line))+'</b></td><td style="padding:9px;border-top:1px solid #263244">'+_esc(_nflCoachOdds(p.odds))+'<br><small style="color:#64748b">'+_esc(p.book)+'</small></td>'
      +'<td style="padding:9px;border-top:1px solid #263244;font-weight:900;color:'+(Number(p.appProb)>=99.95?'#fbbf24':'#e5e7eb')+'">'+Number(p.appProb).toFixed(1)+'%</td><td style="padding:9px;border-top:1px solid #263244;color:#4ade80;font-weight:900">+'+Number(p.edge).toFixed(2)+' pts</td>'
      +'<td style="padding:9px;border-top:1px solid #263244;text-align:center">'+(canSwap?'<button aria-label="Change '+_esc(p.player)+' leg" onclick="changeNflPerfectParlayLeg('+i+')" style="width:32px;height:32px;border-radius:50%;background:#1e3a8a;color:#bfdbfe;border:1px solid #3b82f6;font-size:1rem;font-weight:900;cursor:pointer">&#8635;</button>':'<span style="color:#475569">&#8212;</span>')+'</td></tr>';
  }).join('');
  var stake=__nflPerfectParlayStake,settings=__nflPerfectParlaySettings,labels=(settings.categories||[]).join(', ');
  var hundredNote=hundred?hundred+' exact 100% app-probability play'+(hundred===1?' is':'s are')+' included.':'No exact 100% play is available in these legs; all selections still have positive Coach Edge.';
  var newDisabled=!fresh,button='<button onclick="generateNewNflPerfectParlay()"'+(newDisabled?' disabled':'')+' style="background:linear-gradient(135deg,#0284c7,#7c3aed);color:#fff;border:1px solid #7dd3fc;border-radius:8px;padding:10px 14px;font-weight:900;cursor:'+(newDisabled?'not-allowed':'pointer')+';opacity:'+(newDisabled?'.5':'1')+'">&#8635; Generate New</button>';
  _nflPerfectParlayCommit('<div><div style="display:flex;justify-content:space-between;gap:10px;align-items:center;flex-wrap:wrap"><div class="nfl-coach-question">&#10024; Perfect Parlay · '+legs.length+' Legs</div>'+button+'</div>'
    +'<div style="margin-top:11px;padding:11px 12px;background:linear-gradient(135deg,rgba(2,132,199,.16),rgba(124,58,237,.16));border:1px solid rgba(125,211,252,.35);border-radius:10px;color:#e5e7eb;font-size:.74rem;line-height:1.5">'+hundredNote+' Every leg is from the loaded displayed NFL boards, uses one player once, and is display-only.<br><b style="color:#bae6fd">'+_esc(labels)+' · '+_esc(settings.side==='ALL'?'Best available side':settings.side+' only')+'</b>'
    +'<div style="display:flex;flex-wrap:wrap;gap:18px;align-items:center;margin-top:12px;padding-top:12px;border-top:1px solid #475569"><div><small style="color:#94a3b8">COMBINED ODDS</small><br><b style="color:#fbbf24;font-size:1.25rem">'+_nflPerfectParlayAmerican(combined)+'</b><br><small style="color:#94a3b8">'+combined.toFixed(2)+' decimal</small></div><label style="color:#cbd5e1;font-size:.7rem">BET AMOUNT ($)<br><input type="number" min="0.01" step="0.01" value="'+stake+'" oninput="updateNflPerfectParlayStake(this)" style="margin-top:5px;width:105px;padding:9px;background:#020617;border:1px solid #64748b;border-radius:7px;color:#fff;font-size:1rem"></label><div><small style="color:#94a3b8">POTENTIAL PROFIT</small><br><b id="nflPerfectParlayProfit" style="color:#4ade80;font-size:1.25rem">$'+(stake*(combined-1)).toFixed(2)+'</b></div><div><small style="color:#94a3b8">TOTAL RETURN · INCLUDES STAKE</small><br><b id="nflPerfectParlayReturn" style="color:#fff;font-size:1.25rem">$'+(stake*combined).toFixed(2)+'</b></div></div></div>'
    +'<div id="nflPerfectParlayNotice" role="status" aria-live="polite" style="margin:10px 0;color:#cbd5e1;font-size:.72rem">'+_esc(__nflPerfectParlayNotice||(__nflPerfectParlayPool.length+' unique qualifying players · '+fresh+' unused alternatives. Generate New maximizes fresh players.'))+'</div>'
    +'<div style="overflow-x:auto;border:1px solid #263244;border-radius:10px"><table style="width:100%;min-width:900px;border-collapse:collapse;color:#e5e7eb;font-size:.7rem"><thead><tr style="background:#111827;color:#94a3b8;text-align:left"><th style="padding:9px">#</th><th style="padding:9px">Player</th><th style="padding:9px">Play</th><th style="padding:9px">Odds</th><th style="padding:9px">App Prob</th><th style="padding:9px">Coach Edge</th><th style="padding:9px">Change Leg</th></tr></thead><tbody>'+rows+'</tbody></table></div>'
    +'<div style="display:flex;gap:8px;flex-wrap:wrap;margin-top:12px">'+button+'<button onclick="showNflPerfectParlayBuilder()" style="background:#1e293b;color:#fff;border:1px solid #475569;border-radius:8px;padding:10px 14px;font-weight:900;cursor:pointer">Edit parlay options</button></div><div style="margin-top:10px;color:#94a3b8;font-size:.65rem;line-height:1.5">Estimated payout if every leg wins. Prices can come from different books, so a sportsbook may offer different combined odds. App probabilities are not guarantees. Perfect Parlay never writes to tracking or saved picks.</div></div>');
}
function buildNflPerfectParlay(){
  var countEl=document.getElementById('nflPerfectParlayLegCount'),sideEl=document.getElementById('nflPerfectParlaySide');
  var requested=Math.max(2,Math.min(10,parseInt((countEl&&countEl.value)||'3',10)||3));
  var categories=Array.prototype.slice.call(document.querySelectorAll('input[name="nflPerfectParlayCat"]:checked')).map(function(cb){return cb.value;});
  var side=(sideEl&&sideEl.value)||'ALL';
  __nflPerfectParlaySettings={legs:requested,categories:categories.slice(),side:side};
  if(!categories.length){_nflPerfectParlayCommit('<div><div class="nfl-coach-question">&#10024; Perfect Parlay</div><div class="nfl-coach-summary">Select at least one category before building.</div><button onclick="showNflPerfectParlayBuilder()" style="background:#1e293b;color:#fff;border:1px solid #475569;border-radius:8px;padding:9px 12px;font-weight:900;cursor:pointer">Edit parlay options</button></div>');return;}
  var d=(window._nflState||{}).d,dp=document.getElementById('datePicker'),selectedDate=String((dp&&dp.value)||'');
  if(!d||!Array.isArray(d.picks)||!d.picks.length||String(d.anchor_date||d.date||'')!==selectedDate||String(d.system||'OLD')!==_nflSystem()||(d.week_mode?'week':'day')!==_nflRunScope()){
    _nflPerfectParlayCommit('<div><div class="nfl-coach-question">&#10024; Perfect Parlay · '+requested+' Legs</div><div class="nfl-coach-summary">Load the displayed NFL picks for '+_esc(selectedDate||'your selected date')+' first. Full-week boards use each row’s own slate date.</div></div>');return;
  }
  var raw=_nflPerfectParlayEligibleRows(side).filter(function(p){return categories.indexOf(String(p.market||''))>=0;}),byPlayer={};
  raw.forEach(function(p){
    var key=_nflPerfectParlayPlayerKey(p),old=byPlayer[key];if(!key)return;
    if(!old||p.appProb>old.appProb||(p.appProb===old.appProb&&p.edge>old.edge))byPlayer[key]=p;
  });
  var pool=Object.keys(byPlayer).map(function(k){return byPlayer[k];});
  pool.sort(function(a,b){return b.appProb-a.appProb||b.edge-a.edge||String(a.player).localeCompare(String(b.player));});
  if(pool.length<requested){
    _nflPerfectParlayCommit('<div><div class="nfl-coach-question">&#10024; Perfect Parlay · '+requested+' Legs</div><div class="nfl-coach-summary">Only '+pool.length+' unique player'+(pool.length===1?'':'s')+' from the currently displayed boards qualify with an exact genuine standard-line price of -1000 or better and positive Coach Edge. Choose fewer legs or broaden the filters.</div><button onclick="showNflPerfectParlayBuilder()" style="background:#1e293b;color:#fff;border:1px solid #475569;border-radius:8px;padding:9px 12px;font-weight:900;cursor:pointer">Edit parlay options</button></div>');return;
  }
  __nflPerfectParlayPool=pool.slice();__nflPerfectParlayLegs=pool.slice(0,requested);__nflPerfectParlayNotice='';
  __nflPerfectParlayBoard={state:window._nflState,signature:_nflPerfectParlayBoardSignature()};
  renderNflPerfectParlay();
}
function _nflCoachRender(question,rows,total,mode,isAlternate){
  var el=document.getElementById('nflCoachAnswer');if(!el)return;
  el.style.display='block';
  var summary=mode==='movement_over'
    ?'A positive Over line move means the sportsbook raised the required number after opening. That often reflects market action or a higher expectation, but it is not a guarantee—and the higher current number is harder to clear.'
    :mode==='movement_under'
    ?'A negative Under line move means the sportsbook lowered the required number after opening. That often reflects market action or a lower expectation, but it is not a guarantee—and the lower current number is harder for an Under.'
    :mode==='hundred'
    ?'Every displayed Coach-eligible NFL play with an exact 100.0% app hit rate is shown. This category is not capped at 10 and does not remove additional markets from the same player.'
    :mode==='td_probability'
    ?'I ranked every genuine Anytime TD OVER price from the complete analyzed slate by app touchdown probability and kept the Top 10. Positive Coach Edge is not required; implied probability and Coach Edge remain visible for context.'
    :mode==='safe'
    ?'I checked the selected sides across '+total+' priced NFL candidates and ranked these by sportsbook-implied win probability. Safer favorites can require substantially more risk for a smaller return.'
    :(isAlternate
      ?'I checked '+total+' genuine alternate-line candidates for the safer-value sweet spot. Every result is priced -1000 or better, has at least 85% app probability, at least 70% sportsbook-implied probability, and positive Coach Edge; each player can appear once per qualifying market, using that player-market’s largest-edge line, with a maximum of 10 plays.'
      :'I checked '+total+' priced NFL board plays and ranked the matching positive Coach Edge results. Coach Edge is probability edge, not guaranteed monetary profit.');
  if(!rows.length){el.innerHTML='<div class="nfl-coach-question">'+_esc(question)+'</div><div class="nfl-coach-summary">'+(mode==='hundred'?'No loaded Coach-eligible NFL play currently has an exact 100.0% app hit rate.':(mode.indexOf('movement_')===0?'No qualifying opening-to-current line moves captured yet.':'No loaded priced NFL prop matched that request.'))+'</div>';return;}
  var cards=rows.map(function(p,i){
    var s=p.source||{},head=_esc(s.head||''),logo='https://a.espncdn.com/i/teamlogos/nfl/500/'+_logoAbbr(p.team)+'.png';
    var venue=s.homeRoad==='H'?'HOME':(s.homeRoad==='R'?'AWAY':'');
    var status=String(s.injuryStatus||'UNVERIFIED'),statusColor=status==='ACTIVE'?'#4ade80':'#fbbf24';
    return '<details class="nfl-coach-play"><summary><span class="nfl-coach-ident"><span class="nfl-coach-avatar">'+_esc(_initials(p.player))
      +(head?'<img src="'+head+'" alt="" onerror="this.style.display=\\'none\\'"/>':'')
      +'<img class="team-logo" src="'+_esc(logo)+'" alt="" onerror="this.style.display=\\'none\\'"/></span>'
      +'<span><span class="nfl-coach-name">'+(i+1)+'. '+_esc(p.player)+'</span><span class="nfl-coach-meta">'
      +(p.position?'<span class="nfl-coach-pos">'+_esc(p.position)+'</span>':'')
      +(p.isRookie?'<span style="color:#ddd6fe;border:1px solid #7c3aed;border-radius:999px;padding:1px 5px;font-weight:900">ROOKIE</span>':'')
      +'<span style="color:'+statusColor+';font-weight:800">'+_esc(status)+'</span>'
      +'<span>'+_esc(p.team)+' vs '+_esc(p.opponent)+'</span>'+(venue?'<span>· '+venue+'</span>':'')+(p.slate_date?'<span>· '+_esc(p.slate_date)+'</span>':'')+'</span></span></span>'
      +'<span class="nfl-coach-pickmeta">'+_esc(p.market)+(p.isAlternate?' · <b style="color:#fbbf24">ALT LINE</b>':'')+'<br><b style="color:'+(p.side==='OVER'?'#4ade80':'#f87171')+'">'+p.side+' '+p.line+' · '+_nflCoachOdds(p.odds)+'</b><br><small style="color:#94a3b8">'+_esc(p.book||'Book unavailable')+'</small></span></summary>'
      +'<div class="nfl-coach-copy">'+(mode==='safe'?'<b style="color:#fbbf24">Safety rank: '+p.implied.toFixed(1)+'% sportsbook-implied.</b> ':'')
      +'App probability '+p.appProb.toFixed(1)+'% vs '+p.implied.toFixed(1)+'% implied = <b style="color:'+(p.edge>=0?'#4ade80':'#f87171')+'">'+_nflCoachSigned(p.edge)+' Coach Edge points</b>.'
      +(mode.indexOf('movement_')===0&&p.lineMove!=null?' <span style="color:#fbbf24">Opening '+p.openingLine+' → current '+p.currentLine+' ('+(p.lineMove>=0?'+':'')+Number(p.lineMove).toFixed(2)+')</span>':'')+'</div>'
     +_nflCoachAccordions(p)+'</details>';
  }).join('');
  el.innerHTML='<div class="nfl-coach-question">'+_esc(question)+'</div><div class="nfl-coach-summary">'+summary+'</div>'+cards;
}
function _nflCoachCapture(category,rows){
  var status=document.getElementById('nflCoachCaptureStatus'),dp=document.getElementById('datePicker'),token=localStorage.getItem('__mpa_token')||'';
  var requestedSystem=_nflSystem(),requestGeneration=_nflSystemGeneration;
  var captureSeq=(window.__NFL_COACH_CAPTURE_SEQ__||0)+1;
  window.__NFL_COACH_CAPTURE_SEQ__=captureSeq;
  if(!rows||!rows.length){if(status)status.textContent='Nothing saved: no qualifying displayed plays.';return;}
  var fallback=(dp&&dp.value)||window.__NFL_DATE__||'',groups={};
  rows.forEach(function(p){
    var ds=p.slate_date||fallback;
    if(!groups[ds])groups[ds]=[];
     groups[ds].push({player:p.player,team:p.team,opponent:p.opponent,game:(p.source&&p.source.game)||'',game_start:p.game_start,market:p.market,side:p.side,line:p.line,odds:p.odds,book:p.book,model_probability:p.appProb,implied_probability:p.implied,coach_edge:p.edge,projection:p.projection,alternate:p.isAlternate,opening_line:p.openingLine,current_line:p.currentLine,line_move:p.lineMove,line_movement_available:p.lineMovementAvailable});
  });
  if(status)status.textContent='Saving displayed snapshot by game date…';
  var filters=_nflCoachFilterPayload();
  var requests=Object.keys(groups).map(function(ds){
    var payload={category:category,date:ds,rows:groups[ds],filters:filters,system:_nflSystem()};
    return fetch('/api/nfl/coach-track/capture?token='+encodeURIComponent(token),{method:'POST',headers:{'Content-Type':'application/json','Authorization':token?'Bearer '+token:''},body:JSON.stringify(payload)}).then(function(r){return r.json().then(function(x){if(!r.ok)throw new Error(x.detail||'Save failed');return x;});});
  });
  Promise.all(requests).then(function(results){if(status&&window.__NFL_COACH_CAPTURE_SEQ__===captureSeq&&_nflRequestCurrent(requestGeneration,requestedSystem)){var changed=results.filter(function(x){return x.status==='saved'||x.status==='updated';}).length,refused=results.length-changed,updated=results.some(function(x){return x.status==='updated';});status.style.color=refused?'#fbbf24':'#86efac';status.textContent=changed?((updated?'Updated latest pregame':'Saved')+' '+changed+' game-date snapshot'+(changed===1?'':'s')+'. The final run before kickoff is banked.'+(refused?' '+refused+' date was already frozen or newer.':'')):('No snapshot changed: '+results.map(function(x){return x.message||x.status;}).join(' '));}}).catch(function(e){if(status&&window.__NFL_COACH_CAPTURE_SEQ__===captureSeq&&_nflRequestCurrent(requestGeneration,requestedSystem)){status.style.color='#f87171';status.textContent='Not saved: '+e.message;}});
}
function _nflCoachTrackedCategory(category){
  var rookie=document.getElementById('nflCoachRookieOnly');
  return rookie&&rookie.checked?'rookie_plays':category;
}
function askNflCoachPreset(q,category){
  var input=document.getElementById('nflCoachInput');if(input)input.value=q;
  var shown=askNflCoach();
  _nflCoachCapture(_nflCoachTrackedCategory(category),shown);
  return shown;
}
function askNflMovementCoach(side){
  var category=side==='OVER'?'coach_over_movement':'coach_under_movement';
  var q=side==='OVER'?'Show the biggest positive Over line movement plays':'Show the biggest negative Under line movement plays';
  var input=document.getElementById('nflCoachInput');if(input)input.value=q;
  var selectedSides=_nflCoachSelectedSides();
  var props=_nflCoachVisibleProps(_nflCoachProps()),rows=props.filter(function(p){
    return selectedSides.indexOf(p.side)>=0&&_nflGameFilterOn('coach',p.team,p.opponent)
      &&!p.isAlternate&&!p.alternate&&p.lineMovementAvailable&&p.edge>0&&((side==='OVER'&&p.side==='OVER'&&Number(p.lineMove)>0)||(side==='UNDER'&&p.side==='UNDER'&&Number(p.lineMove)<0));
  }).sort(function(a,b){return Math.abs(Number(b.lineMove))-Math.abs(Number(a.lineMove));}).slice(0,10);
  _nflCoachRender(q,rows,props.length,side==='OVER'?'movement_over':'movement_under',false);
  _nflCoachCapture(_nflCoachTrackedCategory(category),rows);
  return rows;
}
function askNflTdCoach(){
  var q='Show the Top 10 Anytime TD scorers by app probability';
  var input=document.getElementById('nflCoachInput');if(input)input.value=q;
  var props=_nflCoachVisibleProps(_nflCoachProps());
  var selectedSides=_nflCoachSelectedSides(),seen={};
  var shown=props.filter(function(p){
    return p.side==='OVER'&&selectedSides.indexOf('OVER')>=0
      &&_nflCoachFamily(p.market)==='td'
      &&_nflGameFilterOn('coach',p.team,p.opponent);
  }).sort(function(a,b){
    return b.appProb-a.appProb||b.edge-a.edge;
  }).filter(function(p){
    var key=String(p.player||'').trim().toLowerCase();
    if(!key||seen[key])return false;
    seen[key]=1;return true;
  }).slice(0,10);
  _nflCoachRender(q,shown,props.length,'td_probability',false);
  _nflCoachCapture('td_scorers',shown);
  return shown;
}
async function askNflAltCoach(){
  var btn=document.getElementById('nflAltCoachBtn'),answer=document.getElementById('nflCoachAnswer'),captureStatus=document.getElementById('nflCoachCaptureStatus');
  var active=window.__NFL_ALT_COACH_RUN__;
  if(active){
    active.cancelled=true;
    if(active.requestController)active.requestController.abort();
    if(answer&&(window.__NFL_COACH_VIEW_SEQ__||0)===active.viewSeq){answer.style.display='block';answer.innerHTML='<div class="nfl-coach-summary">Alternate-line polling cancelled. The shared background scan continues; no cancelled result was shown or captured. Click again to check it.</div>';}
    if(captureStatus){captureStatus.textContent='Polling cancelled; the shared alternate scan continues in the background.';captureStatus.style.color='#fbbf24';}
    if(btn){btn.disabled=false;btn.textContent='Best Alt-Line Edge Plays · Top 10';}
    return;
  }
  var oldText=btn?btn.textContent:'Best Alt-Line Edge Plays · Top 10';
  var dateEl=document.getElementById('datePicker');
  var date=(dateEl&&dateEl.value)||window.__NFL_DATE__||'';
  var run={date:date,system:_nflSystem(),generation:_nflSystemGeneration,
    seq:(window.__NFL_ALT_COACH_SEQ__||0)+1,cancelled:false,requestController:null,
    deadline:Date.now()+10*60*1000};
  run.viewSeq=window.__NFL_COACH_VIEW_SEQ__||0;
  window.__NFL_ALT_COACH_SEQ__=run.seq;
  window.__NFL_ALT_COACH_RUN__=run;
  window.__NFL_COACH_CAPTURE_SEQ__=(window.__NFL_COACH_CAPTURE_SEQ__||0)+1;
  if(captureStatus){captureStatus.textContent='';captureStatus.style.color='';}
  if(btn){btn.disabled=false;btn.textContent='Cancel alternate-line scan';}
  var lastAlt=(window.__NFL_LAST_ALT_COACH_DATE__===date&&Array.isArray(window.__NFL_LAST_ALT_COACH__))
    ?window.__NFL_LAST_ALT_COACH__: [];
  if(answer&&!lastAlt.length){answer.style.display='block';answer.innerHTML='<div class="nfl-coach-summary">Fetching genuine sportsbook alternate-line ladders. A cold scan can take several minutes; it will continue in the background if the first request times out. Click the button again to cancel.</div>';}
  function ensureCurrent(skipDeadline){
    if(run.cancelled)throw {kind:'cancelled',name:'AltCancelled'};
    if(window.__NFL_ALT_COACH_RUN__!==run)throw {kind:'stale',name:'AltStale'};
    if((window.__NFL_COACH_VIEW_SEQ__||0)!==run.viewSeq)throw {kind:'stale-view',name:'AltStaleView'};
    if(!_nflRequestCurrent(run.generation,run.system))throw {kind:'stale-system',name:'AltStaleSystem'};
    var currentDate=(document.getElementById('datePicker')||{}).value||window.__NFL_DATE__||'';
    if(currentDate!==date)throw {kind:'stale-date',name:'AltStaleDate'};
    if(!skipDeadline&&Date.now()>run.deadline)throw {kind:'timeout',name:'AltTimeout'};
  }
  function waitForPoll(){
    return new Promise(function(resolve){setTimeout(resolve,2500);});
  }
  try{
    var token=localStorage.getItem('__mpa_token')||'';
    var res,data;
    while(true){
      ensureCurrent();
      var requestController=new AbortController(),requestTimer=setTimeout(function(){requestController.abort();},12000);
      run.requestController=requestController;
      try{
        res=await fetch('/api/nfl/coach-alternates?date_str='+encodeURIComponent(date)+'&system='+encodeURIComponent(run.system)+'&token='+encodeURIComponent(token),{signal:requestController.signal,cache:'no-store'});
        data=await res.json();
        data=data||{};
      }catch(requestError){
        if(run.cancelled)throw {kind:'cancelled',name:'AltCancelled'};
        if(requestError&&requestError.name==='AbortError'){
          if(Date.now()>run.deadline)throw {kind:'timeout',name:'AltTimeout'};
          if(captureStatus){captureStatus.textContent='Alternate scan did not answer yet — retrying in 2.5 seconds…';captureStatus.style.color='#fbbf24';}
          await waitForPoll();
          continue;
        }
        throw requestError;
      }finally{
        clearTimeout(requestTimer);
        if(run.requestController===requestController)run.requestController=null;
      }
      ensureCurrent();
      if(data&&data.date&&String(data.date)!==String(date))throw {kind:'stale-date',name:'AltStaleDate'};
      if(data&&String(data.system||'OLD')!==run.system)throw {kind:'stale-system',name:'AltStaleSystem'};
      if(res.status!==202||!data.pending)break;
      if(captureStatus){captureStatus.textContent='Alternate scan still running — checking again automatically…';captureStatus.style.color='#fbbf24';}
      await waitForPoll();
    }
    if(!res.ok||data.error)throw new Error(data.detail||data.error||('HTTP '+res.status));
    ensureCurrent();
    var partial=!!(data.stale||data.partial||data.complete===false||String(data.warning||'').trim());
    var altProps=_nflCoachProps(data.picks||[]);
    window.__NFL_LAST_ALT_COACH__=partial?window.__NFL_LAST_ALT_COACH__:(data.picks||[]).slice();
    window.__NFL_LAST_ALT_COACH_DATE__=partial?window.__NFL_LAST_ALT_COACH_DATE__:date;
    var input=document.getElementById('nflCoachInput');
    if(input)input.value='Show the top 10 safe-value alternate-line plays priced -1000 or better, at 85% model probability and 70% book probability or better';
    var shown=askNflCoach({props:altProps,alternate:true});
    run.viewSeq=window.__NFL_COACH_VIEW_SEQ__||run.viewSeq;
    window.__NFL_ALT_PARLAY_CANDIDATES__=shown.slice();
    window.__NFL_ALT_PARLAY_DATE__=date;
    _renderNflParlayFilters();
    if(partial){
      if(captureStatus){captureStatus.textContent='Warning: '+(data.warning||'This alternate result is stale or partial.')+' Nothing was captured.';captureStatus.style.color='#fbbf24';}
    }else{
      _nflCoachCapture(_nflCoachTrackedCategory('alt_line_edge'),shown);
    }
  }catch(e){
    var kind=e&&e.kind||'',msg=kind==='cancelled'
      ?'Alternate-line polling cancelled. The shared background scan continues; no result was captured.'
      :kind==='timeout'
        ?'The alternate-line scan did not finish before the client wait window. The shared background scan continues; try again shortly.'
      :(kind==='stale-date'||kind==='stale-view'||kind==='stale-system')
          ?'The selected date changed or a newer Coach request replaced this scan. The late result was discarded.'
          :(e&&e.message||'Alternate-line scan failed.');
    if(kind!=='cancelled'&&kind!=='stale-date'&&kind!=='stale-view'&&lastAlt.length&&window.__NFL_ALT_COACH_RUN__===run){
      ensureCurrent(true);
      var fallbackShown=askNflCoach({props:_nflCoachProps(lastAlt),alternate:true});
      run.viewSeq=window.__NFL_COACH_VIEW_SEQ__||run.viewSeq;
      window.__NFL_ALT_PARLAY_CANDIDATES__=fallbackShown.slice();
      window.__NFL_ALT_PARLAY_DATE__=date;
      _renderNflParlayFilters();
      if(captureStatus){captureStatus.textContent=msg+' Showing the last successful result for '+date+'; it is stale fallback and was not captured.';captureStatus.style.color='#fbbf24';}
    }else if(answer&&(window.__NFL_COACH_VIEW_SEQ__||0)===run.viewSeq)answer.innerHTML='<div class="nfl-coach-summary" style="color:'+(kind==='cancelled'?'#fbbf24':'#f87171')+'">'+_esc(msg)+'</div>';
  }finally{
    if(window.__NFL_ALT_COACH_RUN__===run)delete window.__NFL_ALT_COACH_RUN__;
    if(btn){btn.disabled=false;btn.textContent=oldText;}
  }
}
function askNflCoach(options){
  options=options||{};
  window.__NFL_COACH_VIEW_SEQ__=(window.__NFL_COACH_VIEW_SEQ__||0)+1;
  var input=document.getElementById('nflCoachInput'),question=String(input&&input.value||'').trim();if(!question){if(input)input.focus();return;}
  var props=Array.isArray(options.props)?options.props:_nflCoachProps();
  props=_nflCoachVisibleProps(props);
  var exactHundred=/100(?:\\.0)?\\s*%?\\s*(?:app\\s*)?(?:hit\\s*rate|probability)/i.test(question);
  if(!props.length){_nflCoachRender(question,[],0,exactHundred?'hundred':'edge',options.alternate===true);return [];}
  var f=_nflCoachParse(question,props),candidates=_nflCoachSafest(props);
  var selectedSides=_nflCoachSelectedSides();
  candidates=candidates.filter(function(p){return selectedSides.indexOf(String(p.side||'').toUpperCase())>=0;});
  if(!options.ignoreGames){
    candidates=candidates.filter(function(p){return _nflGameFilterOn('coach',p.team,p.opponent);});
  }
  if(options.limit!=null)f.limit=Number(options.limit)||f.limit;
  var rows=candidates.filter(function(p){
    if(exactHundred&&Math.abs(Number(p.appProb)-100)>0.05)return false;
    if(exactHundred&&p.isAlternate)return false;
    if(!exactHundred&&f.mode!=='safe'&&p.edge<=0)return false;
    if(options.alternate&&p.appProb<85)return false;
    if(options.alternate&&p.implied<70)return false;
    if(options.alternate&&(p.odds==null||p.odds<-1000))return false;
    if(f.side&&p.side!==f.side)return false;
    if(f.marketExact&&String(p.market)!==f.marketExact)return false;
    if(f.market&&_nflCoachFamily(p.market)!==f.market)return false;
    if(f.minOdds!=null&&(p.odds<f.minOdds||p.odds>f.maxOdds))return false;
    if(f.players.length&&f.players.indexOf(String(p.player).toLowerCase())<0)return false;
    if(f.teams.length&&f.teams.indexOf(String(p.team).toLowerCase())<0&&f.teams.indexOf(String(p.opponent).toLowerCase())<0)return false;
    return true;
  });
  rows.sort(options.alternate
    ?function(a,b){return b.edge-a.edge||b.appProb-a.appProb;}
    :(f.mode==='safe'
      ?function(a,b){return b.implied-a.implied||b.appProb-a.appProb;}
      :function(a,b){return b.edge-a.edge||b.appProb-a.appProb;}));
  if(exactHundred){
    rows.sort(function(a,b){return b.edge-a.edge||b.appProb-a.appProb||String(a.market||'').localeCompare(String(b.market||''));});
    var hundredSeen={};
    rows=rows.filter(function(p){
      var key=String(p.player||'').trim().toLowerCase();
      if(!key||hundredSeen[key])return false;
      hundredSeen[key]=1;return true;
    });
    _nflCoachRender(question,rows,candidates.length,'hundred',false);
    return rows;
  }
  if(f.onePerCategory){
    var seenCategories={},categoryRows=[];
    rows.forEach(function(p){
      var category=String(p.market||'NFL Prop');
      if(seenCategories[category])return;
      seenCategories[category]=1;
      categoryRows.push(p);
    });
    _nflCoachRender(question,categoryRows,candidates.length,f.mode,options.alternate===true);
    return categoryRows;
  }
  var seenPlayers={};
  rows=rows.filter(function(p){
    var key=String(p.player||'').trim().toLowerCase()
      +(options.alternate?'|'+String(p.market||'').trim().toLowerCase():'');
    if(!key||seenPlayers[key])return false;
    seenPlayers[key]=1;return true;
  });
  var shown=rows.slice(0,f.limit);_nflCoachRender(question,shown,candidates.length,f.mode,options.alternate===true);return shown;
}
var _nflCoachTrackData=null,_nflCoachTrackTabMode='cat';
var _NFL_COACH_TRACK_LABELS={
  app_hit_rate_100:'100% App Hit Rate',safest_bets:'Safest Bets',coach_edge:'Coach Edge',
  alt_line_edge:'Best Alt-Line Edge Plays',passing:'Passing',
  rushing:'Rushing',receiving:'Receiving',defense:'Best Defense Plays',
   kicking:'Best Kicker Plays',td_scorers:'TD Scorers',best_unders:'Best Unders',
   rookie_plays:'Rookie Plays',
   coach_over_movement:'Biggest Over Line Movement',coach_under_movement:'Biggest Under Line Movement'
};
function _nflCoachTrackLabel(category){return _NFL_COACH_TRACK_LABELS[category]||String(category||'Coach').replace(/_/g,' ');}
function _nflCoachTrkStake(){
  var el=document.getElementById('nflCoachTrkStake'),n=parseFloat(el&&el.value);
  return isFinite(n)&&n>0?n:20;
}
function _nflCoachTrkDayName(){
  var dp=document.getElementById('nflCoachTrkDate'),dn=document.getElementById('nflCoachTrkDayName');
  if(!dp||!dn)return;
  try{var days=['Sunday','Monday','Tuesday','Wednesday','Thursday','Friday','Saturday'];
    dn.textContent=days[new Date(dp.value+'T12:00:00').getDay()];}catch(e){dn.textContent='';}
}
function nflCoachTrkSetTab(tab){
  _nflCoachTrackTabMode=tab==='list'?'list':'cat';
  var bc=document.getElementById('nflCoachTrkBtnCat'),bl=document.getElementById('nflCoachTrkBtnList');
  if(bc)bc.style.background=_nflCoachTrackTabMode==='cat'?'#065f46':'#1f2937';
  if(bl)bl.style.background=_nflCoachTrackTabMode==='list'?'#065f46':'#1f2937';
  renderNflCoachTrack();
}
function _nflCoachTrackAwaitingSelection(){
  _nflCoachTrackData=null;
  var sum=document.getElementById('nflCoachTrackSummary'),out=document.getElementById('nflCoachTrackBody');
  if(sum)sum.innerHTML='';
  if(out)out.innerHTML='<p style="color:#94a3b8">Select the record, period, and date, then click Get Results.</p>';
}
function openNflCoachTrack(){
  var e=document.getElementById('nfl-coach-track-section');
  if(e){e.style.display='block';e.scrollIntoView({behavior:'smooth',block:'center'});}
  _nflCoachTrkDayName();
  _nflCoachTrackAwaitingSelection();
}
function loadNflCoachTrack(){
  var out=document.getElementById('nflCoachTrackBody'),token=localStorage.getItem('__mpa_token')||'';if(out)out.innerHTML='<p style="color:#94a3b8">Loading Coach record…</p>';
  var requestedSystem=_nflSystem(),requestGeneration=_nflSystemGeneration,
      requestSeq=++_nflCoachTrackLoadSeq,
      requestController=_nflTrackController(new AbortController());
  var source=(document.getElementById('nflCoachTrkSource')||{}).value||'official';
  var selected=(document.getElementById('nflCoachTrkDate')||{}).value||'';
  var y=selected?Number(selected.slice(0,4)):new Date().getFullYear();
  var m=selected?Number(selected.slice(5,7)):(new Date().getMonth()+1);
  var season=m>=9?y:y-1;
  fetch('/api/nfl/coach-track?grade=true&source='+encodeURIComponent(source)+'&season='+encodeURIComponent(season)+'&date_str='+encodeURIComponent(selected)+'&system='+encodeURIComponent(requestedSystem)+'&token='+encodeURIComponent(token),{headers:{'Authorization':token?'Bearer '+token:''},signal:requestController.signal}).then(function(r){return r.json().then(function(x){if(!r.ok)throw new Error(x.detail||'Could not load');return x;});}).then(function(x){
    _nflUntrackController(requestController);
    if(requestSeq!==_nflCoachTrackLoadSeq||!_nflRequestCurrent(requestGeneration,requestedSystem)
       ||String(x.system||'OLD')!==requestedSystem)return;
    _nflCoachTrackData=x;renderNflCoachTrack();
  }).catch(function(e){
    _nflUntrackController(requestController);
    if(requestSeq!==_nflCoachTrackLoadSeq||!_nflRequestCurrent(requestGeneration,requestedSystem))return;
    if(out)out.innerHTML='<p style="color:#f87171">'+_esc(e.message)+'</p>';
  });
}
function _nflCoachTrackRows(){
  var rows=[];
  ((_nflCoachTrackData&&_nflCoachTrackData.categories)||[]).forEach(function(item){
    (item.rows||[]).forEach(function(r){rows.push(Object.assign({},r,{
      category:item.category,category_label:_nflCoachTrackLabel(item.category),
      record_date:r.date||''
    }));});
  });
  return rows;
}
function _nflCoachTrackSelectedRows(){
  var dp=document.getElementById('nflCoachTrkDate'),periodEl=document.getElementById('nflCoachTrkPeriod');
  var selected=dp?dp.value:'',period=periodEl?periodEl.value:'day';
  return _nflCoachTrackRows().filter(function(r){
    if(period==='all')return true;
    if(period==='season')return _nflSeasonKey(r.record_date)===_nflSeasonKey(selected);
    if(period==='month')return String(r.record_date).slice(0,7)===String(selected).slice(0,7);
    if(period==='week')return _nflWeekKey(r.record_date)===_nflWeekKey(selected);
    return r.record_date===selected;
  });
}
function _nflCoachTrackProfit(r,stake){
  if(r.observation_only||!(r.result==='WIN'||r.result==='LOSS')||r.odds==null)return null;
  return _nflTrkProfit(r,stake);
}
function _nflCoachTrackSummary(rows,stake,label){
  var sum=document.getElementById('nflCoachTrackSummary');if(!sum)return;
  var counted=rows.filter(function(r){return !r.observation_only;});
  var observations=rows.length-counted.length;
  var wins=counted.filter(function(r){return r.result==='WIN';}).length;
  var losses=counted.filter(function(r){return r.result==='LOSS';}).length;
  var pushes=counted.filter(function(r){return r.result==='PUSH';}).length;
  var voids=counted.filter(function(r){return r.result==='VOID';}).length;
  var pending=counted.length-wins-losses-pushes-voids;
  var graded=wins+losses,priced=counted.filter(function(r){return (r.result==='WIN'||r.result==='LOSS')&&r.odds!=null;});
  var net=priced.reduce(function(v,r){return v+(_nflCoachTrackProfit(r,stake)||0);},0);
  var roi=priced.length?net/(priced.length*stake)*100:null,rate=graded?wins/graded*100:null;
  var color=net>=0?'#4ade80':'#f87171';
  if(!rows.length){sum.innerHTML='<p style="color:#9ca3af;padding:12px;text-align:center">No AI Coach recommendations for '+_esc(label)+'.</p>';return;}
  sum.innerHTML='<div class="nfl-trk-sum">'
    +'<span style="color:#9ca3af;font-size:.78rem;font-weight:800">'+_esc(label)+'</span>'
    +'<span style="font-size:1.05rem;font-weight:900;color:#fff"><span style="color:#4ade80">'+wins+'</span>/<span style="color:#f87171">'+graded+'</span>'
    +(rate!=null?' <span style="color:#9ca3af;font-size:.85rem;font-weight:600">('+rate.toFixed(1)+'%)</span>':'')+'</span>'
    +(pushes?'<span style="color:#fbbf24;font-weight:800">'+pushes+' PUSH</span>':'')
    +(voids?'<span style="color:#94a3b8;font-weight:800">'+voids+' VOID</span>':'')
    +(pending?'<span style="color:#fbbf24;font-weight:800">'+pending+' pending</span>':'')
    +(observations?'<span style="color:#fbbf24;font-weight:800">'+observations+' TD observation'+(observations===1?'':'s')+'</span>':'')
     +'<span style="font-family:monospace;font-weight:800;color:'+color+'">Primary Net '+(net>=0?'+$':'-$')+Math.abs(net).toFixed(0)+'</span>'
    +(roi!=null?'<span style="font-family:monospace;font-weight:700;color:'+color+'">ROI '+(roi>=0?'+':'')+roi.toFixed(1)+'%</span>':'')
    +'<span style="color:#6b7280;font-size:.8rem">$'+stake+'/play · ROI uses WIN/LOSS priced plays only</span></div>';
}
function _nflCoachTrackCategoryHtml(rows,stake){
  var categories=Object.keys(_NFL_COACH_TRACK_LABELS);
  return categories.map(function(category){
    var list=rows.filter(function(r){return r.category===category;});
    var counted=list.filter(function(r){return !r.observation_only;}),observations=list.length-counted.length;
    var w=counted.filter(function(r){return r.result==='WIN';}).length;
    var l=counted.filter(function(r){return r.result==='LOSS';}).length,p=counted.filter(function(r){return r.result==='PUSH';}).length;
    var v=counted.filter(function(r){return r.result==='VOID';}).length,pending=counted.length-w-l-p-v;
    var graded=w+l,rate=graded?w/graded*100:null,priced=counted.filter(function(r){return (r.result==='WIN'||r.result==='LOSS')&&r.odds!=null;});
    var net=priced.reduce(function(total,r){return total+(_nflCoachTrackProfit(r,stake)||0);},0);
    var roi=priced.length?net/(priced.length*stake)*100:null,color=net>=0?'#4ade80':'#f87171';
    var meta=w+'W · '+l+'L'+(p?' · '+p+'P':'')+(v?' · '+v+'V':'')+(pending?' · '+pending+' pending':'')+(observations?' · '+observations+' observations':'');
    return '<details class="nfl-trk-group" style="--trk-accent:#22d3ee">'
      +'<summary class="nfl-trk-group-head"><div class="nfl-trk-group-title">'
      +'<span class="nfl-trk-group-kicker">Coach Category</span><span class="nfl-trk-group-name">'+_esc(_nflCoachTrackLabel(category))+'</span></div>'
      +'<div class="nfl-trk-group-summary"><span>'+meta+'</span><span class="nfl-trk-group-rate">'+(rate==null?'—':rate.toFixed(1)+'%')+'</span>'
      +'<span class="nfl-trk-group-pl" style="color:'+color+'">'+(net>=0?'+$':'-$')+Math.abs(net).toFixed(0)+'</span>'
       +'<span style="color:'+color+'">'+(roi==null?'—':(roi>=0?'+':'')+roi.toFixed(1)+'% ROI')+'</span>'
       +'<span class="nfl-trk-group-toggle" aria-hidden="true"></span></div></summary>'
        +_nflCoachTrackRowsTable(list,stake,false)+'</details>';
  }).join('');
}
function _nflCoachTrackRowsTable(rows,stake,showCategory){
  if(!rows.length)return '';
  var sorted=rows.slice().sort(function(a,b){return String(b.record_date).localeCompare(String(a.record_date))||Object.keys(_NFL_COACH_TRACK_LABELS).indexOf(a.category)-Object.keys(_NFL_COACH_TRACK_LABELS).indexOf(b.category)||String(a.player).localeCompare(String(b.player));});
  var body=sorted.map(function(r){
    var result=(r.result||'PENDING').toUpperCase(),profit=_nflCoachTrackProfit(r,stake),edge=Number(r.coach_edge);
     var metrics='<small style="display:block;color:#94a3b8;margin-top:4px">Model '+Number(r.model_probability||0).toFixed(1)+'% · Implied '+Number(r.implied_probability||0).toFixed(1)+'% · <b style="color:'+(edge>=0?'#4ade80':'#f87171')+'">'+(edge>=0?'+':'')+edge.toFixed(2)+' pts</b></small>';
    return '<tr><td class="trk-date" data-label="Date" style="color:#94a3b8;font-family:monospace">'+_esc(r.record_date||'')+'</td>'
      +(showCategory?'<td class="trk-category" data-label="Category" style="color:#7dd3fc;font-weight:900">'+_esc(r.category_label)+'</td>':'')
      +'<td class="trk-player" data-label="Player" style="color:#fff;font-weight:900">'+_esc(r.player||'')+'<br><small style="color:#94a3b8">'+_esc(r.team||'')+' vs '+_esc(r.opponent||'')+'</small></td>'
      +'<td class="trk-play" data-label="Play" style="color:#e2e8f0;font-weight:800">'+_esc(r.market_label||r.market||'')+'<br>'+_esc((r.side||'')+' '+r.line)+metrics+'</td>'
       +'<td class="trk-odds" data-label="Odds / Book" style="font-family:monospace">'+_nflCoachOdds(r.odds)+'<br><small style="color:#94a3b8">'+_esc(r.book||'')+'</small></td>'
       +'<td class="trk-actual" data-label="Actual" style="color:#cbd5e1">'+(r.actual==null?'—':_esc(String(r.actual)))+'</td>'
       +'<td class="trk-result" data-label="Result / P&L"><span class="nfl-trk-result '+result.toLowerCase()+'">'+_esc(result)+'</span><br><small style="font-family:monospace;font-weight:900;color:'+(r.observation_only?'#fbbf24':profit==null?'#94a3b8':profit>=0?'#4ade80':'#f87171')+'">'+(r.observation_only?'OBSERVATION':profit==null?'—':(profit>=0?'+$':'-$')+Math.abs(profit).toFixed(2))+'</small></td></tr>';
  }).join('');
  return '<div class="nfl-trk-table-scroll"><table class="nfl-trk-tbl nfl-trk-compact"><thead><tr><th class="trk-date">Date</th>'
    +(showCategory?'<th class="trk-category">Coach Category</th>':'')+'<th class="trk-player">Player</th><th class="trk-play">Play / Probabilities</th><th class="trk-odds">Odds / Book</th><th class="trk-actual">Actual</th><th class="trk-result">Result / P&L</th></tr></thead><tbody>'+body+'</tbody></table></div>';
}
function _nflCoachTrackListHtml(rows,stake){
  return _nflCoachTrackCategoryHtml(rows,stake);
}
function renderNflCoachTrack(){
  var out=document.getElementById('nflCoachTrackBody');if(!out||!_nflCoachTrackData)return;
  var dp=document.getElementById('nflCoachTrkDate'),periodEl=document.getElementById('nflCoachTrkPeriod');
  var selected=dp?dp.value:'',period=periodEl?periodEl.value:'day',rows=_nflCoachTrackSelectedRows(),stake=_nflCoachTrkStake();
  var label=_nflTrkPeriodLabel(selected,period);
  _nflCoachTrackSummary(rows,stake,label);
  out.innerHTML=rows.length
    ?(_nflCoachTrackTabMode==='cat'?_nflCoachTrackCategoryHtml(rows,stake):_nflCoachTrackListHtml(rows,stake))
    :'';
}
var _nflTdPosition='ALL';
function _nflTdPositionOf(p){
  var pos=String((p&&p.position)||(p&&p.roster_position)||'').toUpperCase();
  return pos==='FB'||pos==='HB'?'RB':pos;
}
function setNflTdPosition(pos){
  pos=String(pos||'ALL').toUpperCase();
  _nflTdPosition=['ALL','QB','RB','WR','TE'].indexOf(pos)>=0?pos:'ALL';
  _renderNflTdPredictor((window._nflState||{}).d||{});
}
function _nflTdPositionButtons(source){
  var box=document.getElementById('nflTdPositionFilters');if(!box)return;
  var counts={ALL:source.length,QB:0,RB:0,WR:0,TE:0};
  source.forEach(function(p){var pos=_nflTdPositionOf(p);if(counts[pos]!=null)counts[pos]++;});
  box.innerHTML=['ALL','QB','RB','WR','TE'].map(function(pos){
    var active=_nflTdPosition===pos,disabled=pos!=='ALL'&&!counts[pos];
    return '<button type="button" aria-pressed="'+(active?'true':'false')+'" onclick="setNflTdPosition(\\''+pos+'\\')"'+(disabled?' disabled':'')+' style="padding:7px 13px;border-radius:999px;border:1px solid '+(active?'#fbbf24':'#3f3f32')+';background:'+(active?'rgba(245,158,11,.2)':'#151510')+';color:'+(disabled?'#57574c':active?'#fde68a':'#d6d3c5')+';font-size:.68rem;font-weight:900;cursor:'+(disabled?'not-allowed':'pointer')+';opacity:'+(disabled?'.55':'1')+'">'+(pos==='ALL'?'ALL':pos)+' <span style="color:'+(active?'#fbbf24':'#77776a')+'">'+counts[pos]+'</span></button>';
  }).join('');
}
function _renderNflTdPredictor(d){
  var card=document.getElementById('nfl-td-predictor-card'),body=document.getElementById('nfl-td-predictor-body');
  if(!card||!body)return;
  var gameSelect=document.getElementById('nflTdGameSelect'),games=_nflLoadedGames();
  if(gameSelect){
    var selectedValue=gameSelect.value||'';
    gameSelect.innerHTML='<option value="">All Games</option>'+games.map(function(g){return '<option value="'+_esc(g.key)+'">'+_esc(g.label)+'</option>';}).join('');
    gameSelect.value=games.some(function(g){return g.key===selectedValue;})?selectedValue:'';
  }
  var selectedGame=gameSelect?gameSelect.value:'';
  var source=((d&&d.all)||[]).filter(function(p){
    var isNew=String(p.system||'').toUpperCase()==='NEW'||p.model_version==='NEW-v2-ewma-weather';
    return p.market==='player_anytime_td'&&p.pick==='OVER'
      &&p.realOdds!=null&&(isNew||Number(p.vsLineTotal||p.totB||0)>=5)
      &&p.coachEligible!==false&&p.availabilityVerified!==false;
  });
  var available=source.filter(function(p){
    return !_nflGameDone(p)&&(!selectedGame||_nflGameKey(p.team,p.opponent||p.opp)===selectedGame);
  });
  _nflTdPositionButtons(available);
  var rows=available.filter(function(p){
    return _nflTdPosition==='ALL'||_nflTdPositionOf(p)===_nflTdPosition;
  }).slice().sort(function(a,b){
    var br=Math.max(Number(b.rateA||0),Number(b.rateB||0),Number(b.vsLineRate||0));
    var ar=Math.max(Number(a.rateA||0),Number(a.rateB||0),Number(a.vsLineRate||0));
    return br-ar||Number(b.score||b.dispScore||0)-Number(a.score||a.dispScore||0)
      ||Number(b.valueEdge||0)-Number(a.valueEdge||0);
  }).slice(0,selectedGame?5:10);
  if(!rows.length){
    if(!source.length){card.style.display='none';body.innerHTML='';return;}
    card.style.display='block';
    var emptyCount=document.getElementById('nflTdPredictorCount');
    if(emptyCount)emptyCount.textContent=(selectedGame?'TOP 5':'TOP 10')+' · 0 '+(_nflTdPosition==='ALL'?'':' '+_nflTdPosition)+' SCORERS';
    body.innerHTML='<div style="margin-top:14px;border:1px solid #2d2d22;border-radius:12px;padding:18px;text-align:center;color:#a3a38d;font-size:.76rem">No '+(_nflTdPosition==='ALL'?'':_esc(_nflTdPosition)+' ')+'priced Anytime TD scorer with enough recent history is available'+(selectedGame?' for this matchup':'')+'.</div>';
    return;
  }
  card.style.display='block';
  var count=document.getElementById('nflTdPredictorCount');
  if(count)count.textContent=(selectedGame?'TOP 5 · ':'TOP 10 · ')+rows.length+(_nflTdPosition==='ALL'?'':' '+_nflTdPosition)+' SCORER'+(rows.length===1?'':'S');
  var table=rows.map(function(p,i){
    var key=_ladKey(p);window.__NFLLAD__[key]=p;
    var odds=_nflSideOdds(p,'OVER'),implied=_nflCoachImplied(odds);
    var prob=Number(p.score!=null?p.score:p.dispScore||0);
    var rankRate=Math.max(Number(p.rateA||0),Number(p.rateB||0),Number(p.vsLineRate||0));
    var edge=p.valueEdge!=null?Number(p.valueEdge):(implied==null?null:prob-implied);
    var recent=p.vsLineTotal?Number(p.vsLineHits||0)+'/'+Number(p.vsLineTotal||0)+' ('+Number(p.vsLineRate||0).toFixed(0)+'%)':'—';
    var versus=p.totA?Number(p.hitsA||0)+'/'+Number(p.totA||0)+' ('+Number(p.rateA||0).toFixed(0)+'%)':'—';
    var defense=p.defRank!=null?'#'+p.defRank+' '+_esc(p.defLbl||'defense'):(p.defLbl?_esc(p.defLbl):'—');
    return '<tr><td><span class="nfl-td-rank">'+(i+1)+'</span></td>'
      +'<td><button type="button" class="nfl-td-player" onclick="openNflLadder(\\''+key+'\\')">'+_esc(p.name)+'</button><br><small style="color:#6b7280">'+_esc(p.team||'')+' vs '+_esc(p.opponent||'')+(p.slate_date?' · '+_esc(p.slate_date):'')+'</small></td>'
      +'<td style="font-weight:900;color:#fde68a">OVER 0.5 TD</td>'
      +'<td style="font-family:monospace;color:#fbbf24;font-weight:900">'+(_fmtOdds(odds)||'—')+'<br><small style="color:#6b7280">'+_esc(p.over_book||'')+'</small></td>'
      +'<td class="nfl-td-prob">'+rankRate.toFixed(0)+'%</td>'
      +'<td>'+(implied==null?'—':implied.toFixed(1)+'%')+'</td>'
      +'<td style="font-family:monospace;font-weight:900;color:#c4b5fd">'+prob.toFixed(1)+'%</td>'
      +'<td class="nfl-td-edge">'+(edge==null?'—':(edge>=0?'+':'')+edge.toFixed(1)+' pts')+'</td>'
      +'<td>'+recent+'</td><td>'+versus+'</td><td>'+defense+'</td></tr>';
  }).join('');
  body.innerHTML='<div class="nfl-td-table-wrap"><table class="nfl-td-table"><thead><tr><th>#</th><th>Player</th><th>Play</th><th>Best Odds</th><th>Rank Rate</th><th>Implied</th><th>Model Prob</th><th>Value Edge</th><th>L10 vs Line</th><th>Vs Opponent</th><th>Opponent Defense</th></tr></thead><tbody>'+table+'</tbody></table></div>'
    +'<div class="nfl-td-method">Rank Rate is the strongest displayed hit rate from the player’s recent, venue, book-line, or opponent sample, matching the percentage used in the game’s Anytime TD list. Model Prob remains the calibrated walk-forward probability, and Value Edge remains Model Prob minus sportsbook break-even. Players require a genuine Anytime TD price and at least five recent games. Passing touchdowns never count—only rushing or receiving touchdowns settle this market. Click any player for the full game log.</div>';
}
function renderResults(d){
  var res=document.getElementById('results');
  if(typeof _nflPerfectParlayInvalidate==='function')_nflPerfectParlayInvalidate('board');
  if(!d){ res.innerHTML=''; return; }
  if(d.error){
    var failed=(d.skipped_matchups||[]);
    var failedDetail=failed.length?('<div style="font-size:13px;color:#fbbf24;margin-top:8px;font-weight:700">Skipped matchups: '+failed.map(_esc).join(', ')+'</div>'):'';
    res.innerHTML='<div class="err-box">'+_esc(d.error)+failedDetail+'<div style="font-size:13px;color:#9ca3af;margin-top:6px;font-weight:400">NFL season runs September through February</div></div>';
    return;
  }
  window._nflState={d:d, all:(d.all||[])};
  var systemBadge=document.getElementById('nflSystemBadge');
  if(systemBadge){systemBadge.textContent='SYSTEM: '+(d.system||_nflSystem());systemBadge.style.color=(d.system||_nflSystem())==='NEW'?'#67e8f9':'#fbbf24';}
  window.__NFL_PLAYS__=d.all||[];
  window.__NFL_DATE__=d.anchor_date||d.date||'';
  _renderNflParlayFilters();
  var weekNotice=d.week_notice?('<div style="margin-bottom:10px;padding:11px 14px;border:1px solid '+(d.incomplete?'#b45309':'#6d28d9')+';background:'+(d.incomplete?'rgba(180,83,9,.16)':'rgba(109,40,217,.12)')+';border-radius:10px;color:'+(d.incomplete?'#fde68a':'#ddd6fe')+';font-size:.82rem;font-weight:'+(d.incomplete?'700':'400')+'">'+_esc(d.week_notice)+'</div>'):'';
  var note=d.data_note?('<div style="margin-bottom:10px;padding:11px 14px;border:1px solid #24506b;background:#0b2230;border-radius:10px;color:#9bd5f5;font-size:.82rem">'+d.data_note+'</div>'):'';
  var warn=d.data_warning?('<div class="err-box" style="margin-bottom:10px">'+d.data_warning+'</div>'):'';
  var legacyWarn=d.defense_legacy_warning?('<div class="err-box" style="margin-bottom:10px">'+_esc(d.defense_legacy_warning)+'</div>'):'';
  var skipped=(d.skipped_matchups||[]);
  var completenessWarn=skipped.length?('<div class="err-box" style="margin-bottom:10px"><strong>Incomplete sportsbook slate:</strong> no player props were loaded for '+skipped.map(_esc).join(', ')+'. These matchups were skipped after the sportsbook request timed out or failed.</div>'):'';
  res.innerHTML=weekNotice+completenessWarn+legacyWarn+note+warn+'<div class="nfl-toolbar"><input id="nflSearch" type="text" placeholder="Search player…" oninput="_nflPaint(this.value)"/></div><div id="nflBody"></div>';
  _renderNflGamePredictor(d);
  _renderNflTdPredictor(d);
  _nflPaint('');
}

// Paints chips/games/special/cards into #nflBody. Re-runs on every search
// keystroke with a name filter; the search box itself lives outside #nflBody so
// it keeps focus. All category sections are open by default.
function _nflPaint(q){
  var st=window._nflState||{}; var d=st.d; if(!d) return;
  q=(q||'').toLowerCase().trim();
  var expand=true;
  var picks=(d.picks||[]);
  if(q) picks=picks.filter(function(p){return (p.name||'').toLowerCase().indexOf(q)>=0;});
  var byM={}; _MORDER.forEach(function(m){byM[m]=[];});
  picks.forEach(function(p){ var m=p.mkt||p.label; if(!byM[m]) byM[m]=[]; byM[m].push(p); });
  // Rank within each market by cushion (avg vs line, in the pick's direction) so
  // cheap 1.5 lines no longer automatically outrank tougher higher lines.
  Object.keys(byM).forEach(function(m){ byM[m].sort(function(a,b){return _edge(b)-_edge(a);}); });
  st.byM=byM;
  var allF=(d.all||[]);

  var h='';
  h+=_nflRoleRiskBoard(allF);

  // Chips (market chips are tappable -> all plays for that market)
  h+='<div class="chips">';
  h+='<div class="chip nfl-games-jump" role="button" tabindex="0" onclick="_nflJumpToGames()" onkeydown="if(event.key===\\'Enter\\'||event.key===\\' \\'){event.preventDefault();_nflJumpToGames()}"><div class="val">'+((d.games||[]).length)+'</div><div class="lbl">View Games</div></div>';
  _MORDER.forEach(function(m){ if(byM[m]&&byM[m].length){ h+='<div class="chip" style="cursor:pointer" onclick="_marketModal(&#39;'+m+'&#39;)"><div class="val">'+byM[m].length+'</div><div class="lbl">'+(_MLBL[m]||m)+'</div></div>'; }});
  h+='</div>';

  // ROI Focus keeps every existing market board below, but promotes the
  // conservative slice that finished positive in the saved 2025 replay:
  // UNDER picks with a real price of -150 or better.
  var roiFocus=picks.filter(function(p){
    return !_nflGameDone(p)&&_nflIsRoiFocusPick(p);
  }).sort(function(a,b){
    return Number(b.score||b.dispScore||0)-Number(a.score||a.dispScore||0)
      ||_edge(b)-_edge(a);
  }).filter(function(p){
    // ROI Focus is a concentrated board: keep only the highest-ranked
    // qualifying market for each player. Their other markets remain on the
    // normal boards below.
    var key=String(p.name||p.player||'').trim().toLowerCase();
    if(!key)return false;
    if(this[key])return false;
    this[key]=true;
    return true;
  },{});
  if(roiFocus.length){
    var focusTop=roiFocus.slice(0,10),focusMore=roiFocus.slice(10);
    var focusBody=nflCardGrid(focusTop,1);
    if(focusMore.length){
      focusBody+='<details style="margin:14px 16px 16px">'
        +'<summary style="cursor:pointer;list-style:none;text-align:center;padding:10px 14px;border:1px solid rgba(52,211,153,.4);border-radius:10px;background:rgba(52,211,153,.08);color:#6ee7b7;font-weight:800;font-size:.8rem">'
        +'Show '+focusMore.length+' more ROI Focus pick'+(focusMore.length!==1?'s':'')+'</summary>'
        +'<div style="margin-top:14px">'+nflCardGrid(focusMore,11)+'</div></details>';
    }
    h+='<div style="background:linear-gradient(135deg,rgba(6,95,70,.22),rgba(15,23,42,.8));border:1px solid rgba(52,211,153,.48);border-radius:14px;margin:14px 0;overflow:hidden">'
      +'<div style="padding:13px 16px;border-bottom:1px solid rgba(52,211,153,.2)">'
      +'<div style="display:flex;align-items:center;justify-content:space-between;gap:10px;flex-wrap:wrap">'
      +'<div><div style="font-weight:900;font-size:1rem;color:#6ee7b7">ROI Focus</div>'
      +'<div style="font-size:.72rem;color:#a7f3d0;margin-top:3px">UNDER picks priced -150 or better — the positive-ROI slice in the saved 2025 replay. Past results do not guarantee future profit.</div></div>'
      +'<div style="background:rgba(52,211,153,.14);border:1px solid rgba(52,211,153,.35);border-radius:20px;padding:4px 12px;color:#6ee7b7;font-size:.75rem;font-weight:900">'+roiFocus.length+(d.week_mode?' this week':' today')+'</div>'
      +'</div></div>'+focusBody+'</div>';
  }

  // ── 🔒 80–100% Locks — every tracked sample hit at 80%+ ─────────────────
  var lockPicks=(d.all||[]).filter(function(p){
    return !_nflGameDone(p) && p.betQualified!==false
      && p.roleRiskBlockPremium!==true
      && Number(p.score||p.dispScore)>=80 && p.pick;
  });
  if(q) lockPicks=lockPicks.filter(function(p){return (p.name||'').toLowerCase().indexOf(q)>=0;});
  lockPicks.sort(function(a,b){
    var sa=Number(b.score||b.dispScore||0),sb=Number(a.score||a.dispScore||0);
    if(sa!==sb) return sa-sb;
    var ga=Math.abs(Number(a.gap||0)),gb=Math.abs(Number(b.gap||0));
    if(ga!==gb) return gb-ga;
    var ai=_MORDER.indexOf(a.mkt||a.label),bi=_MORDER.indexOf(b.mkt||b.label);
    return ai-bi||(a.name||'').localeCompare(b.name||'');
  });
  var lockSeen={};
  lockPicks=lockPicks.filter(function(p){
    var key=String(p.name||'').trim().toLowerCase().replace(/[^a-z0-9]+/g,'');
    if(!key||lockSeen[key])return false;
    lockSeen[key]=1;return true;
  });
  if(lockPicks.length){
     var lockTop=lockPicks.slice(0,20), lockMore=lockPicks.slice(20);
     var lockBody=nflCardGrid(lockTop,1);
     if(lockMore.length){
       lockBody+='<details style="margin:14px 16px 16px">'
         +'<summary style="cursor:pointer;list-style:none;display:flex;align-items:center;justify-content:center;gap:8px;padding:10px 14px;border:1px solid rgba(245,158,11,.45);border-radius:10px;background:rgba(245,158,11,.08);color:#fbbf24;font-weight:800;font-size:.8rem">'
         +'&#9654; Show '+lockMore.length+' more lock'+(lockMore.length!==1?'s':'')+' (ranks 21+)'
         +'</summary>'
         +'<div style="margin-top:14px">'+nflCardGrid(lockMore,21)+'</div>'
         +'</details>';
     }
    h+='<div style="background:linear-gradient(135deg,rgba(245,158,11,.1),rgba(74,222,128,.05));border:1px solid rgba(245,158,11,.4);border-radius:14px;margin-bottom:14px;overflow:hidden">'
      +'<div style="display:flex;align-items:center;gap:10px;padding:12px 16px;cursor:pointer;user-select:none" onclick="_secToggle(&#39;lock8100&#39;)">'
      +'<span style="font-size:1.4rem;flex-shrink:0">&#128274;</span>'
      +'<div style="flex:1;min-width:0">'
      +'<div style="font-weight:900;font-size:1rem;color:#f59e0b;letter-spacing:.03em">80–100% Locks</div>'
      +'<div style="font-size:.72rem;color:#9ca3af;margin-top:2px">All tracked samples hit at 80%+ across all markets — sorted highest % first</div>'
      +'</div>'
      +'<div style="background:rgba(245,158,11,.2);border:1px solid rgba(245,158,11,.5);border-radius:20px;padding:3px 12px;font-size:.73rem;font-weight:900;color:#f59e0b;flex-shrink:0">'+lockPicks.length+' lock'+(lockPicks.length!==1?'s':'')+'</div>'
      +'<span id="car_lock8100" style="color:#f59e0b;font-size:1rem;flex-shrink:0">&#9660;</span>'
      +'</div>'
       +'<div id="sec_lock8100">'+lockBody+'</div>'
      +'</div>';
  }

  // Card grids per market — separate OVER and UNDER boards, each top 10 + overflow.
  // Finished games (kickoff + 4h elapsed) drop off the board.
  var hasCards=false;
  h+=_collapseSec('biggest_over_movement','⬆ Biggest Over Line Movement',_nflMovementBoard(picks,'OVER'),true);
  h+=_collapseSec('biggest_under_movement','⬇ Biggest Under Line Movement',_nflMovementBoard(picks,'UNDER'),true);
  _MORDER.forEach(function(m,i){
    var all=(byM[m]||[]).filter(function(p){return !_nflGameDone(p);});
    var overs =all.filter(function(p){return p.pick==='OVER';});
    var unders=all.filter(function(p){return p.pick==='UNDER';});
    if(!overs.length&&!unders.length) return;
    hasCards=true;
    if(overs.length){
      var og=overs.slice(0,10), ofov=overs.slice(10,20);
      h+=_collapseSec('mkt_ov_'+i, '⬆ '+_mIcon(m)+' Top 10 '+m+' — OVERS', nflCardGrid(og), true);
      if(ofov.length) h+=_collapseSec('ovf_ov_'+i, '⬆ '+m+' OVERS — Overflow ('+ofov.length+' more)', nflCardGrid(ofov), false);
    }
    if(unders.length){
      var ug=unders.slice(0,10), ufov=unders.slice(10,20);
      h+=_collapseSec('mkt_un_'+i, '⬇ '+_mIcon(m)+' Top 10 '+m+' — UNDERS', nflCardGrid(ug), true);
      if(ufov.length) h+=_collapseSec('ovf_un_'+i, '⬇ '+m+' UNDERS — Overflow ('+ufov.length+' more)', nflCardGrid(ufov), false);
    }
  });
  if(!hasCards){
    h+='<div class="no-picks">No qualifying picks'+(q?' for "'+q+'"':' for '+(d.date||'today'))+'.</div>';
  }

  // Existing matchup tiles belong after the market boards. Each tile opens
  // the complete game-picks modal, so no second by-game accordion is needed.
  if((d.games||[]).length){
    h+='<div id="nfl-by-game-section"><div class="sec">- Games -- '+(d.date||'')+'</div><div class="games">';
    d.games.forEach(function(g,gi){
      var mu=(g.away_abbr||g.away_team||'?')+' @ '+(g.home_abbr||g.home_team||'?');
      var day=g.slate_date?'<div style="color:#a78bfa;font-size:.64rem;font-weight:900;margin-bottom:3px">'+g.slate_date+'</div>':'';
      h+='<div class="gcard" onclick="_gameModal('+gi+')">'+day+'<div class="mu">'+mu+'</div><div class="gc-hint">tap for plays</div></div>';
    });
    h+='</div></div>';
  }

  document.getElementById('nflBody').innerHTML=h;
}

function nflToggle(n){
  var el=document.getElementById('nfltoggle_'+n);
  var btn=document.getElementById('nfltoggle_btn_'+n);
  if(!el) return;
  var hidden=el.style.display==='none';
  el.style.display=hidden?'block':'none';
  if(btn) btn.textContent=hidden?'Collapse':'Expand';
}
// ── My Bets ──────────────────────────────────────────────────────────────────
function _nflEsc(s){return(s||'').replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;');}
function _esc(s){return _nflEsc(s==null?'':String(s));}
function _nflMoney(v){var n=Number(v)||0;return(n>=0?'$':'\u2212$')+Math.abs(n).toFixed(2);}
function _nflBetAuthQS(){
  var tok=localStorage.getItem('__mpa_token')||'';
  var adm=new URLSearchParams(location.search).get('admin')||'';
  return '?token='+encodeURIComponent(tok)+(adm?('&admin='+encodeURIComponent(adm)):'');
}
function _nflBetToast(msg){
  var t=document.createElement('div');t.textContent=msg;
  t.style.cssText='position:fixed;bottom:80px;left:50%;transform:translateX(-50%);background:#0e7490;color:#fff;padding:10px 20px;border-radius:10px;font-weight:700;font-size:.85rem;z-index:99999;white-space:nowrap;pointer-events:none;box-shadow:0 4px 20px rgba(0,0,0,.5)';
  document.body.appendChild(t);
  setTimeout(function(){t.style.opacity='0';t.style.transition='opacity .4s';setTimeout(function(){t.remove();},400);},2200);
}
var _nflBetN=0;
window.__NFL_BET_SRC__=window.__NFL_BET_SRC__||{};
function _nflBetBtn(p,forceSide){
  if(p.realLine==null||!p.market||p.betQualified===false) return '';
  var side=forceSide||(p.pick==='UNDER'?'UNDER':'OVER');
  var odds=_nflSideOdds(p,side);
  if(odds==null) return '';
  var k='nf'+(++_nflBetN);
  window.__NFL_BET_SRC__[k]={
    name:p.name,pid:(p.pid!=null?String(p.pid):''),team:(p.team||''),opp:(p.opponent||''),
    category:(p.mkt||p.label||''),side:side,market:p.market,stat_label:(p.mkt||p.label||''),
    line:p.realLine,odds:(odds!=null?odds:null),date:(p.slate_date||window.__NFL_DATE__||'')
  };
  return '<button data-betkey="'+k+'" class="admin-only" onclick="event.stopPropagation();_nflBetForm(this.dataset.betkey)" style="background:#0e7490;color:#fff;border:none;border-radius:8px;padding:6px 10px;font-size:.7rem;font-weight:800;cursor:pointer">Track Bet</button>';
}
function _nflBetForm(key){
  var src=(window.__NFL_BET_SRC__||{})[key]; if(!src) return;
  window.__NFL_BET_CUR__=src;
  var ov=document.getElementById('nfl-bet-modal');
  if(!ov){
    ov=document.createElement('div'); ov.id='nfl-bet-modal';
    ov.style.cssText='position:fixed;inset:0;background:rgba(0,0,0,.82);z-index:10000;display:flex;align-items:center;justify-content:center;padding:16px';
    ov.onclick=function(e){if(e.target===ov)ov.style.display='none';};
    document.body.appendChild(ov);
  }
  var pickTxt=src.side+' '+src.line+' '+(src.stat_label||'');
  ov.innerHTML=`<div style="background:#161616;border:1px solid #0e7490;border-radius:16px;max-width:360px;width:100%;box-shadow:0 20px 60px rgba(0,0,0,.6)">
    <div style="display:flex;justify-content:space-between;align-items:flex-start;padding:16px 18px;border-bottom:1px solid #2a2a2a">
      <div>
        <div style="font-weight:800;color:#fff;font-size:1.02rem">${_nflEsc(src.name)}</div>
        <div style="color:#67e8f9;font-size:.82rem;font-weight:800;margin-top:2px">${_nflEsc(pickTxt)}</div>
        <div style="color:#9ca3af;font-size:.72rem;margin-top:2px">${_nflEsc(src.category||'')}${src.opp?' &middot; vs '+_nflEsc(src.opp):''}${src.date?' &middot; '+src.date:''}</div>
      </div>
      <button onclick="document.getElementById('nfl-bet-modal').style.display='none'" style="background:#1f2937;border:none;color:#cbd5e1;width:30px;height:30px;border-radius:8px;cursor:pointer;font-size:1rem">&#215;</button>
    </div>
    <div style="padding:16px 18px;display:grid;gap:12px">
      <label style="font-size:.72rem;color:#9ca3af;font-weight:600">Odds (American)<input id="nfl-bet-odds" type="number" value="${src.odds!=null?src.odds:''}" style="display:block;width:100%;margin-top:5px;background:#0b0b0b;border:1px solid #333;border-radius:8px;padding:9px 11px;color:#fbbf24;font-family:monospace;font-weight:700;font-size:.95rem"></label>
      <label style="font-size:.72rem;color:#9ca3af;font-weight:600">Bet size ($)<input id="nfl-bet-stake" type="number" min="0" step="0.01" placeholder="e.g. 50" style="display:block;width:100%;margin-top:5px;background:#0b0b0b;border:1px solid #333;border-radius:8px;padding:9px 11px;color:#fff;font-weight:700;font-size:.95rem"></label>
      <div id="nfl-bet-payout" style="font-size:.78rem;color:#6b7280;min-height:1em"></div>
      <div id="nfl-bet-msg" style="font-size:.76rem;color:#f87171;min-height:1em"></div>
      <button id="nfl-bet-save" onclick="_nflSaveBet()" style="background:#0e7490;color:#fff;border:none;border-radius:9px;padding:11px;font-weight:800;cursor:pointer;font-size:.92rem">Log Bet</button>
    </div>
  </div>`;
  ov.style.display='flex';
  var so=document.getElementById('nfl-bet-odds'),ss=document.getElementById('nfl-bet-stake');
  function _calc(){
    var o=parseFloat(so.value),s=parseFloat(ss.value);
    var pay=document.getElementById('nfl-bet-payout');
    if(!isFinite(o)||!isFinite(s)||s<=0){pay.textContent='';return;}
    var win=o>0?s*(o/100):s*(100/Math.abs(o));
    pay.innerHTML='To win <strong style="color:#4ade80">$'+win.toFixed(2)+'</strong> &middot; total payout <strong style="color:#cbd5e1">$'+(s+win).toFixed(2)+'</strong>';
  }
  so.oninput=_calc;ss.oninput=_calc;_calc();
  setTimeout(function(){ss.focus();},50);
}
async function _nflSaveBet(){
  var src=window.__NFL_BET_CUR__;if(!src) return;
  var o=parseFloat(document.getElementById('nfl-bet-odds').value);
  var s=parseFloat(document.getElementById('nfl-bet-stake').value);
  var msg=document.getElementById('nfl-bet-msg');
  if(!isFinite(o)){msg.textContent='Enter the odds.';return;}
  if(!isFinite(s)||s<=0){msg.textContent='Enter a bet size greater than 0.';return;}
  var btn=document.getElementById('nfl-bet-save');btn.disabled=true;btn.textContent='Saving\u2026';
  try{
    var body=Object.assign({},src,{odds:Math.round(o),stake:s,placed_at:new Date().toISOString()});
    var res=await fetch('/api/bets'+_nflBetAuthQS(),{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(body)});
    if(!res.ok){throw new Error(await res.text());}
    document.getElementById('nfl-bet-modal').style.display='none';
    _nflBetToast('\u2705 Bet logged');
    var mb=document.getElementById('nfl-mybets-card');
    if(mb&&mb.style.display!=='none') openNflMyBets(false);
  }catch(e){msg.textContent=(e.message||'Save failed');btn.disabled=false;btn.textContent='Log Bet';}
}
async function openNflMyBets(scroll){
  var card=document.getElementById('nfl-mybets-card');if(!card) return;
  card.style.display='block';
  if(scroll!==false) card.scrollIntoView({behavior:'smooth',block:'start'});
  document.getElementById('nfl-mybets-body').innerHTML='<p style="color:#9ca3af;font-size:.85rem">Loading\u2026</p>';
  try{
    var res=await fetch('/api/bets'+_nflBetAuthQS());
    if(!res.ok){
      var t=await res.text();
      if(res.status===403) t='Session expired \u2014 reopen from hub';
      throw new Error(t);
    }
    window.__NFL_MYBETS__=await res.json();
    renderNflMyBets(window.__NFL_MYBETS__);
  }catch(e){
    document.getElementById('nfl-mybets-body').innerHTML='<p style="color:#f87171;padding:16px">'+(e.message||'Error loading bets')+'</p>';
  }
}
function _nflBetOddsDisp(o){return o!=null?((o>0?'+':'')+o):'\u2014';}
function _nflResColor(r){return r==='WIN'?'#4ade80':(r==='LOSS'?'#f87171':(r==='PUSH'?'#facc15':'#9ca3af'));}
function _nflStatBox(lbl,val,clr){
  return '<div style="background:#0e0e0e;border-radius:10px;padding:10px 14px;min-width:92px">'
    +'<div style="font-size:.64rem;color:#6b7280;text-transform:uppercase;letter-spacing:.08em">'+lbl+'</div>'
    +'<div style="font-size:1.12rem;font-weight:800;color:'+(clr||'#e5e7eb')+'">'+val+'</div></div>';
}
function renderNflMyBets(d){
  var s=d.summary||{};var bets=d.bets||[];
  var roiTxt=s.roi!=null?((s.roi>0?'+':'')+s.roi+'%'):'\u2014';
  var roiClr=s.roi==null?'#9ca3af':(s.roi>0?'#4ade80':(s.roi<0?'#f87171':'#facc15'));
  var netClr=(s.profit||0)>0?'#4ade80':((s.profit||0)<0?'#f87171':'#cbd5e1');
  var recTxt=(s.wins||0)+'-'+(s.losses||0)+(s.push?('-'+s.push+'P'):'');
  var head='<div style="display:flex;flex-wrap:wrap;gap:12px;align-items:center;margin-bottom:18px">'
    +_nflStatBox('Record',recTxt,'#e5e7eb')
    +_nflStatBox('Pending',(s.pending||0),'#9ca3af')
    +_nflStatBox('Staked',_nflMoney(s.staked||0),'#cbd5e1')
    +_nflStatBox('Net',_nflMoney(s.profit||0),netClr)
    +_nflStatBox('Returned',_nflMoney(s.returned||0),'#cbd5e1')
    +_nflStatBox('ROI',roiTxt,roiClr)
    +'<div style="margin-left:auto"><button onclick="downloadNflMyBetsCSV()" style="background:#0e7490;color:#fff;border:none;border-radius:8px;padding:8px 12px;font-size:.78rem;font-weight:700;cursor:pointer">&#11015; CSV</button></div>'
    +'</div>';
  var bc=(s.by_category||[]).map(function(c){
    var croi=c.roi!=null?((c.roi>0?'+':'')+c.roi+'%'):'\u2014';
    var cclr=c.roi==null?'#9ca3af':(c.roi>0?'#4ade80':(c.roi<0?'#f87171':'#facc15'));
    return '<tr><td style="font-weight:600">'+_nflEsc(c.category)+'</td>'
      +'<td style="font-family:monospace">'+c.wins+'-'+c.losses+(c.push?('-'+c.push+'P'):'')+'</td>'
      +'<td style="font-family:monospace;color:#9ca3af">'+(c.pending||0)+'</td>'
      +'<td style="font-family:monospace">'+_nflMoney(c.staked)+'</td>'
      +'<td style="font-family:monospace;color:'+((c.profit||0)>=0?'#4ade80':'#f87171')+'">'+_nflMoney(c.profit)+'</td>'
      +'<td style="font-family:monospace;font-weight:700;color:'+cclr+'">'+croi+'</td></tr>';
  }).join('');
  var bcHtml=bc?'<div style="overflow-x:auto;margin-bottom:18px"><table class="nfl-bets-tbl"><thead><tr><th>Category</th><th>W-L</th><th>Pend</th><th>Staked</th><th>Net</th><th>ROI</th></tr></thead><tbody>'+bc+'</tbody></table></div>':'';
  var rows=bets.map(function(b){
    var res=b.result||'pending';
    var delBtn='<button data-delid="'+b.id+'" onclick="_nflDeleteBet(this.dataset.delid)" title="Remove" style="background:none;border:none;color:#6b7280;cursor:pointer;font-size:1rem">&#10006;</button>';
    var pk=b.side+' '+b.line+' '+(b.stat_label||'');
    var actTxt=b.actual!=null?(' <span style="color:#6b7280;font-weight:400;font-size:.72rem">('+b.actual+')</span>'):'';
    return '<tr>'
      +'<td style="white-space:nowrap;color:#9ca3af;font-family:monospace;font-size:.76rem">'+(b.date||'')+'</td>'
      +'<td style="font-weight:600">'+_nflEsc(b.name||'')+'<div style="font-size:.68rem;color:#6b7280">'+_nflEsc(b.category||'')+'</div></td>'
      +'<td style="font-size:.82rem">'+_nflEsc(pk)+'</td>'
      +'<td style="font-family:monospace">'+_nflBetOddsDisp(b.odds)+'</td>'
      +'<td style="font-family:monospace">'+_nflMoney(b.stake)+'</td>'
      +'<td style="font-weight:800;color:'+_nflResColor(res)+'">'+(res==='pending'?'pending':res)+actTxt+'</td>'
      +'<td style="font-family:monospace;font-weight:700;color:'+((b.profit||0)>=0?'#4ade80':'#f87171')+'">'+(b.profit!=null?_nflMoney(b.profit):'\u2014')+'</td>'
      +'<td>'+delBtn+'</td></tr>';
  }).join('');
  var rowsHtml=bets.length
    ?'<div style="overflow-x:auto"><table class="nfl-bets-tbl"><thead><tr><th>Date</th><th>Player</th><th>Pick</th><th>Odds</th><th>Stake</th><th>Result</th><th>Profit</th><th></th></tr></thead><tbody>'+rows+'</tbody></table></div>'
    :'<p style="color:#9ca3af;padding:16px">No bets logged yet. Click <strong style="color:#67e8f9">Track Bet</strong> on any pick card to start.</p>';
  document.getElementById('nfl-mybets-body').innerHTML=head+bcHtml+rowsHtml;
}
async function _nflDeleteBet(id){
  if(!confirm('Remove this bet from your log?')) return;
  try{
    var res=await fetch('/api/bets/'+encodeURIComponent(id)+_nflBetAuthQS(),{method:'DELETE'});
    if(!res.ok) throw new Error(await res.text());
    openNflMyBets(false);
  }catch(e){alert(e.message||'Delete failed');}
}
// ── NFL Track Record ──────────────────────────────────────────────────────────
var _nflTrkData=null,_nflTrkTabMode='cat',_nflTrkReplayDate='',_nflTrkLoadSeq=0;
var _nflOvfData=null,_nflOvfTabMode='cat',_nflOvfLoadSeq=0;
function _nflTrkStake(){
  var el=document.getElementById('nflTrkStake'),n=parseFloat(el&&el.value);
  return isFinite(n)&&n>0?n:20;
}
function _nflTrkProfit(r,stake){
  if(r.observation_only||r.odds==null||!(r.result==='WIN'||r.result==='LOSS')) return null;
  if(r.result==='LOSS') return -stake;
  var o=parseFloat(r.odds);
  if(!isFinite(o)||o===0) return null;
  return o>0?stake*(o/100):stake*(100/Math.abs(o));
}
function _nflOvfStake(){
  var el=document.getElementById('nflOvfStake'),n=parseFloat(el&&el.value);
  return isFinite(n)&&n>0?n:20;
}
function _nflOvfSource(){
  var el=document.getElementById('nflOvfSource');
  return el&&el.value==='historical'?'historical':'official';
}
function _nflOvfPeriod(){
  var el=document.getElementById('nflOvfPeriod');
  return el?el.value:'day';
}
function _nflOvfDayName(){
  var dp=document.getElementById('nflOvfDate'),dn=document.getElementById('nflOvfDayName');
  if(!dp||!dn)return;
  try{var days=['Sunday','Monday','Tuesday','Wednesday','Thursday','Friday','Saturday'];
    dn.textContent=days[new Date(dp.value+'T12:00:00').getDay()];}catch(e){dn.textContent='';}
}
function nflOvfSetTab(tab){
  _nflOvfTabMode=tab==='list'?'list':'cat';
  var bc=document.getElementById('nflOvfBtnCat'),bl=document.getElementById('nflOvfBtnList');
  if(bc)bc.style.background=_nflOvfTabMode==='cat'?'#92400e':'#1f2937';
  if(bl)bl.style.background=_nflOvfTabMode==='list'?'#92400e':'#1f2937';
  renderNflOverflowDay();
}
async function loadNflOverflowRecord(){
  var body=document.getElementById('nflOvfBody'),dp=document.getElementById('nflOvfDate');
  var loadSeq=++_nflOvfLoadSeq;
  var requestedSystem=_nflSystem(),requestGeneration=_nflSystemGeneration,
      requestController=_nflTrackController(new AbortController());
  if(body)body.innerHTML='<p style="color:#9ca3af;padding:24px">Loading Overflow record\u2026</p>';
  try{
    var r=await fetch('/api/track-record?grade=true&date_str='+encodeURIComponent(dp?dp.value:'')+'&system='+encodeURIComponent(requestedSystem),{signal:requestController.signal});
    if(!r.ok)throw new Error(await r.text());
    var data=await r.json();
    if(loadSeq!==_nflOvfLoadSeq||!_nflRequestCurrent(requestGeneration,requestedSystem)
       ||String(data.system||'OLD')!==requestedSystem)return;
    _nflOvfData=data;
    renderNflOverflowDay();
  }catch(e){
    if(loadSeq!==_nflOvfLoadSeq||!_nflRequestCurrent(requestGeneration,requestedSystem))return;
    if(body)body.innerHTML='<p style="color:#f87171;padding:16px">'+_esc(e.message||'Error loading Overflow record')+'</p>';
  }finally{_nflUntrackController(requestController);}
}
function renderNflOverflowDay(){
  if(!_nflOvfData)return;
  var dp=document.getElementById('nflOvfDate'),selDate=dp?dp.value:'';
  var source=_nflOvfSource(),period=_nflOvfPeriod(),stake=_nflOvfStake();
  var dates=source==='historical'
    ?(_nflOvfData.historical_overflow_dates||_nflOvfData.overflow_dates||[])
    :(_nflOvfData.overflow_dates||[]);
  var selected=_nflTrkFilterDates(dates,selDate,period),rows=[];
  selected.forEach(function(d){(d.detail||[]).forEach(function(r){
    if(r.result==='WIN'||r.result==='LOSS')rows.push(Object.assign({record_date:d.date},r));
  });});
  _nflRenderRecordBook(
    rows,stake,_nflTrkPeriodLabel(selDate,period),
    document.getElementById('nflOvfSummary'),document.getElementById('nflOvfBody'),
    true,source,_nflOvfTabMode);
}
function _nflSeasonKey(ds){
  var y=parseInt(String(ds||'').slice(0,4),10),m=parseInt(String(ds||'').slice(5,7),10);
  return isFinite(y)&&isFinite(m)?(m>=9?y:y-1):null;
}
function _nflWeekKey(ds){
  var d=new Date(String(ds||'')+'T12:00:00Z');
  if(isNaN(d.getTime())) return '';
  // NFL reporting week runs Tuesday through Monday so Thursday/Sunday/Monday
  // games from the same football week stay together.
  var day=(d.getUTCDay()+5)%7;
  d.setUTCDate(d.getUTCDate()-day);
  return d.toISOString().slice(0,10);
}
function _nflTrkSource(){
  var el=document.getElementById('nflTrkSource');
  return el&&el.value==='historical'?'historical':'official';
}
function nflTrkSourceChanged(){
  var gpDate=document.getElementById('nflGpDate');
  if(gpDate){gpDate.dataset.ready='';gpDate.value='';}
  if(_nflTrkSource()==='historical'&&_nflTrkData){
    var dates=_nflTrkData.historical_dates||[];
    if(dates.length){
      var latest=dates.reduce(function(best,row){
        var ds=String(row&&row.date||'');
        return ds>best?ds:best;
      },'');
      var dateEl=document.getElementById('nflTrkDate');
      var periodEl=document.getElementById('nflTrkPeriod');
      if(dateEl&&latest) dateEl.value=latest;
      if(periodEl) periodEl.value='season';
      _nflTrkDayName();
    }
  }
  renderNflTrackDay();
  renderNflGpRecord();
}
function _nflTrkPeriod(){
  var el=document.getElementById('nflTrkPeriod');
  return el?el.value:'day';
}
function _nflTrkFilterDates(dates,sel,period){
  if(period==='all') return dates;
  if(period==='season'){
    var sk=_nflSeasonKey(sel);
    return dates.filter(function(d){return _nflSeasonKey(d.date)===sk;});
  }
  if(period==='month'){
    var mk=String(sel||'').slice(0,7);
    return dates.filter(function(d){return String(d.date||'').slice(0,7)===mk;});
  }
  if(period==='week'){
    var wk=_nflWeekKey(sel);
    return dates.filter(function(d){return _nflWeekKey(d.date)===wk;});
  }
  return dates.filter(function(d){return d.date===sel;});
}
function _nflTrkPeriodLabel(sel,period){
  if(period==='all') return 'All Time';
  if(period==='season') return 'NFL Season '+_nflSeasonKey(sel);
  if(period==='month') return String(sel||'').slice(0,7);
  if(period==='week') return 'NFL Week of '+_nflWeekKey(sel);
  return sel||'Selected Day';
}
function openNflTrackRecord(){
  var sec=document.getElementById('nfl-track-section');
  if(sec) sec.scrollIntoView({behavior:'smooth',block:'start'});
}
async function openNflLastSeason(){
  var btn=document.getElementById('lastSeasonBtn');
  var requestedSystem=_nflSystem(),requestGeneration=_nflSystemGeneration,
      requestSeq=++_nflHistSeasonLoadSeq;
  var original=btn?btn.innerHTML:'📚 View Last Season';
  if(btn){btn.disabled=true;btn.innerHTML='<span class="spinner"></span>Loading archive…';}
  try{
    if(!_nflTrkData||!(_nflTrkData.historical_dates||[]).length){
      await loadNflTrackRecord(false);
    }
    if(requestSeq!==_nflHistSeasonLoadSeq||!_nflRequestCurrent(requestGeneration,requestedSystem))return;
    var source=document.getElementById('nflTrkSource');
    if(!source||!_nflTrkData||!(_nflTrkData.historical_dates||[]).length){
      throw new Error('No saved Historical Analysis archive is available yet.');
    }
    source.value='historical';
    // Switching the source selects the latest archived date and the matching
    // NFL season, then redraws both the prop and Game Predictor records.
    nflTrkSourceChanged();
    openNflTrackRecord();
  }catch(e){
    if(requestSeq!==_nflHistSeasonLoadSeq||!_nflRequestCurrent(requestGeneration,requestedSystem))return;
    alert(e.message||'Could not load the saved Historical Analysis archive.');
  }finally{
    if(btn){btn.disabled=false;btn.innerHTML=original;}
  }
}
function openNflGpRecord(){
  renderNflGpRecord();
  var sec=document.getElementById('nfl-gp-record-section');
  if(sec) sec.scrollIntoView({behavior:'smooth',block:'start'});
}
function _nflTrkDayName(){
  var dp=document.getElementById('nflTrkDate'),dn=document.getElementById('nflTrkDayName');
  if(!dp||!dn) return;
  try{var days=['Sunday','Monday','Tuesday','Wednesday','Thursday','Friday','Saturday'];
    dn.textContent=days[new Date(dp.value+'T12:00:00').getDay()];}catch(e){dn.textContent='';}
}
async function loadNflTrackRecord(forceOfficial){
  forceOfficial=forceOfficial!==false;
  var dp=document.getElementById('nflTrkDate');
  // A historical run already contains its freshly graded replay. Pressing
  // Get Results must keep that view instead of replacing it with the separate
  // official ledger, which intentionally has no replay-only dates.
  if(forceOfficial&&_nflTrkReplayDate&&dp&&dp.value===_nflTrkReplayDate){
    renderNflTrackDay();renderNflGpRecord();return;
  }
  var loadSeq=++_nflTrkLoadSeq;
  var requestedSystem=_nflSystem(),requestGeneration=_nflSystemGeneration,
      requestController=_nflTrackController(new AbortController());
  var body=document.getElementById('nflTrkBody');
  if(body) body.innerHTML='<p style="color:#9ca3af;padding:24px">Loading\u2026</p>';
  try{
    var qs=forceOfficial?'?grade=true&date_str='+encodeURIComponent(dp?dp.value:'')+'&system='+encodeURIComponent(requestedSystem):'?system='+encodeURIComponent(requestedSystem);
    var r=await fetch('/api/track-record'+qs,{signal:requestController.signal});
    if(!r.ok) throw new Error(await r.text());
    var officialData=await r.json();
    // The initial official-record request runs in the background. It must not
    // overwrite a replay that finished while that request was in flight.
    if(loadSeq!==_nflTrkLoadSeq || (!forceOfficial&&_nflTrkReplayDate)
       ||!_nflRequestCurrent(requestGeneration,requestedSystem)
       ||String(officialData.system||'OLD')!==requestedSystem) return;
    _nflTrkReplayDate='';
    _nflTrkData=officialData;
    renderNflTrackDay();
    renderNflGpRecord();
  }catch(e){
    if(loadSeq!==_nflTrkLoadSeq||!_nflRequestCurrent(requestGeneration,requestedSystem))return;
    if(body) body.innerHTML='<p style="color:#f87171;padding:16px">'+(e.message||'Error loading track record')+'</p>';
  }finally{_nflUntrackController(requestController);}
}
async function loadNflGpRecord(){
  var body=document.getElementById('nflGpTrkBody'),dateEl=document.getElementById('nflGpDate');
  if(_nflTrkSource()==='historical'){renderNflGpRecord();return;}
  var requestedSystem=_nflSystem(),requestGeneration=_nflSystemGeneration,
      requestSeq=++_nflGpRecordLoadSeq,
      requestController=_nflTrackController(new AbortController());
  if(body) body.innerHTML='<p style="color:#9ca3af;padding:18px 0">Loading Game Predictor results\u2026</p>';
  try{
    var selected=dateEl&&dateEl.value&&dateEl.value!=='all'?dateEl.value:'';
    var r=await fetch('/api/gp-record?grade=true&date_str='+encodeURIComponent(selected)+'&system='+encodeURIComponent(requestedSystem),{signal:requestController.signal});
    if(!r.ok) throw new Error(await r.text());
    var gp=await r.json();
    if(requestSeq!==_nflGpRecordLoadSeq||!_nflRequestCurrent(requestGeneration,requestedSystem)
       ||String(gp.system||'OLD')!==requestedSystem)return;
    _nflTrkData=_nflTrkData||{};
    _nflTrkData.game_predictor=gp;
    renderNflGpRecord();
  }catch(e){
    if(requestSeq!==_nflGpRecordLoadSeq||!_nflRequestCurrent(requestGeneration,requestedSystem))return;
    if(body) body.innerHTML='<p style="color:#f87171;padding:16px">'+_esc(e.message||'Could not load Game Predictor results')+'</p>';
  }finally{_nflUntrackController(requestController);}
}
function nflTrkSetTab(tab){
  _nflTrkTabMode=tab;
  var bc=document.getElementById('nflTrkBtnCat'),bl=document.getElementById('nflTrkBtnList');
  if(bc) bc.style.background=tab==='cat'?'#065f46':'#1f2937';
  if(bl) bl.style.background=tab==='list'?'#065f46':'#1f2937';
  renderNflTrackDay();
}
function _nflGpWeekNumber(ds){
  var season=_nflSeasonKey(ds);
  if(season==null)return null;
  var sep1=new Date(Date.UTC(season,8,1)),firstMonday=1+((8-sep1.getUTCDay())%7);
  var weekOneTuesday=new Date(Date.UTC(season,8,firstMonday+1));
  var wkDate=new Date(_nflWeekKey(ds)+'T12:00:00Z');
  return Math.min(22,Math.max(1,Math.floor((wkDate-weekOneTuesday)/(7*86400000))+1));
}
function _nflGpPopulateControls(daily){
  var seasonEl=document.getElementById('nflGpSeason'),weekEl=document.getElementById('nflGpWeek'),dateEl=document.getElementById('nflGpDate');
  if(!seasonEl||!weekEl||!dateEl)return;
  var boardDate=(document.getElementById('datePicker')||{}).value||'';
  var latest=(daily||[]).reduce(function(v,d){return String(d.date||'')>v?String(d.date):v;},'');
  var target=dateEl.dataset.ready==='1'?'':((daily||[]).some(function(d){return d.date===boardDate;})?boardDate:latest);
  var seasons=[];
  (daily||[]).forEach(function(d){var s=_nflSeasonKey(d.date);if(s!=null&&seasons.indexOf(s)<0)seasons.push(s);});
  seasons.sort(function(a,b){return b-a;});
  var oldSeason=seasonEl.value,oldWeek=weekEl.value,oldDate=dateEl.value;
  seasonEl.innerHTML=seasons.map(function(s){return '<option value="'+s+'">'+s+' Season</option>';}).join('');
  var desiredSeason=target?_nflSeasonKey(target):(oldSeason||seasons[0]);
  if(seasons.indexOf(Number(desiredSeason))<0)desiredSeason=seasons[0];
  if(desiredSeason!=null)seasonEl.value=String(desiredSeason);
  weekEl.innerHTML='<option value="all">All Weeks</option>'+Array.from({length:22},function(_,i){return '<option value="'+(i+1)+'">Week '+(i+1)+'</option>';}).join('');
  var desiredWeek=target?_nflGpWeekNumber(target):(oldWeek||'all');
  if(desiredWeek!=='all'&&(!isFinite(Number(desiredWeek))||Number(desiredWeek)<1||Number(desiredWeek)>22))desiredWeek='all';
  weekEl.value=String(desiredWeek||'all');
  var matching=(daily||[]).filter(function(d){
    return String(_nflSeasonKey(d.date))===seasonEl.value&&(weekEl.value==='all'||String(_nflGpWeekNumber(d.date))===weekEl.value);
  });
  matching.sort(function(a,b){return String(a.date).localeCompare(String(b.date));});
  dateEl.innerHTML='<option value="all">All dates in selection</option>'+matching.map(function(d){
    var games=(d.games||[]).map(function(g){return (g.away_abbr||'?')+' @ '+(g.home_abbr||'?');}).join(', ');
    return '<option value="'+_esc(d.date)+'">'+_esc(d.date)+(games?' · '+_esc(games):'')+'</option>';
  }).join('');
  if(target&&matching.some(function(d){return d.date===target;}))dateEl.value=target;
  else if(oldDate&&matching.some(function(d){return d.date===oldDate;}))dateEl.value=oldDate;
  else dateEl.value='all';
  dateEl.dataset.ready='1';
}
function _nflGpData(){
  var hist=_nflTrkSource()==='historical';
  if(!_nflTrkData)return null;
  if(!hist)return _nflTrkData.game_predictor||null;
  return _nflTrkData.historical===true
    ?(_nflTrkData.game_predictor||null)
    :(_nflTrkData.historical_game_predictor||null);
}
function _nflGpDaily(){
  var gp=_nflGpData();
  return (gp&&gp.daily)||[];
}
function _nflGpControlChanged(which){
  var dateEl=document.getElementById('nflGpDate');
  if(which==='season'){
    var weekEl=document.getElementById('nflGpWeek');if(weekEl)weekEl.value='all';
  }
  if(dateEl){dateEl.value='all';dateEl.dataset.ready='1';}
  _nflGpPopulateControls(_nflGpDaily());
  renderNflGpRecord();
}
function _nflGpStake(){
  var el=document.getElementById('nflGpStake');
  if(el&&el.dataset.ready!=='1'){
    try{var saved=Number(localStorage.getItem('nflGpStake'));if(isFinite(saved)&&saved>0)el.value=String(saved);}catch(e){}
    el.dataset.ready='1';
  }
  var stake=Number(el&&el.value);
  return isFinite(stake)&&stake>0?stake:20;
}
function _nflGpStakeChanged(){
  var el=document.getElementById('nflGpStake'),stake=_nflGpStake();
  if(el&&Number(el.value)!==stake)el.value=stake.toFixed(2);
  try{localStorage.setItem('nflGpStake',String(stake));}catch(e){}
  renderNflGpRecord();
}
function _nflGpOdds(g,key){
  if(key==='winner_result')return g.pick_home?g.home_ml_odds:g.away_ml_odds;
  return g.total_pick==='OVER'?g.total_over_odds:g.total_under_odds;
}
function _nflGpBook(g,key){
  if(key==='winner_result')return g.pick_home?g.home_ml_book:g.away_ml_book;
  return g.total_pick==='OVER'?g.total_over_book:g.total_under_book;
}
function _nflGpProfit(result,odds,stake){
  if(result==='PUSH')return 0;
  if(result!=='WIN'&&result!=='LOSS')return null;
  var n=Number(odds);
  if(!isFinite(n)||n===0)return null;
  if(result==='LOSS')return -stake;
  return n>0?stake*n/100:stake*100/Math.abs(n);
}
function _nflGpImplied(odds){
  var n=Number(odds);
  if(!isFinite(n)||n===0)return null;
  return n>0?100/(n+100)*100:Math.abs(n)/(Math.abs(n)+100)*100;
}
function _nflGpMoney(v){
  if(v==null||!isFinite(Number(v)))return '—';
  return (Number(v)>=0?'+$':'-$')+Math.abs(Number(v)).toFixed(2);
}
function renderNflGpRecord(){
  var sumEl=document.getElementById('nflGpTrkSummary'),bodyEl=document.getElementById('nflGpTrkBody');
  if(!sumEl||!bodyEl) return;
  var hist=_nflTrkSource()==='historical';
  var gp=_nflGpData();
  var daily=(gp&&gp.daily)||[];
  if(!daily.length){
    _nflGpPopulateControls([]);
    sumEl.innerHTML='';
    bodyEl.innerHTML='<p style="color:#6b7280;padding:18px 0;text-align:center">No saved Game Predictor forecasts yet. New pre-game winner and total calls will appear here after games finish.</p>';
    return;
  }
  _nflGpPopulateControls(daily);
  var allGames=[];
  daily.forEach(function(day){(day.games||[]).forEach(function(g){allGames.push(Object.assign({record_date:day.date},g));});});
  function rec(key,games){
    games=games||allGames;
    var w=games.filter(function(g){return g[key]==='WIN';}).length;
    var l=games.filter(function(g){return g[key]==='LOSS';}).length;
    var p=games.filter(function(g){return g[key]==='PUSH';}).length;
    var settled=games.filter(function(g){return g[key]==='WIN'||g[key]==='LOSS'||g[key]==='PUSH';});
    var priced=settled.filter(function(g){return _nflGpOdds(g,key)!=null&&isFinite(Number(_nflGpOdds(g,key)));});
    var stake=_nflGpStake();
    var net=priced.reduce(function(sum,g){return sum+(_nflGpProfit(g[key],_nflGpOdds(g,key),stake)||0);},0);
    var risk=priced.length*stake;
    var avgBe=priced.length?priced.reduce(function(sum,g){return sum+_nflGpImplied(_nflGpOdds(g,key));},0)/priced.length:null;
    return {w:w,l:l,p:p,rate:(w+l)?(w/(w+l)*100):null,priced:priced.length,
      net:net,risk:risk,roi:risk?net/risk*100:null,units:stake?net/stake:null,
      returned:risk+net,breakEven:avgBe};
  }
  var replay=_nflTrkData&&_nflTrkData.historical
    ?'<div style="background:rgba(245,158,11,.1);border:1px solid rgba(245,158,11,.35);border-radius:9px;padding:9px 12px;margin-bottom:10px;color:#fbbf24;font-size:.76rem;font-weight:800">Historical Replay — these results are view-only and excluded from the official Game Predictor record.</div>'
    :'';
  function statCard(title,r,color){
    var plColor=r.net>=0?'#4ade80':'#f87171';
    return '<div style="flex:1;min-width:210px;background:#111827;border:1px solid #293548;border-radius:12px;padding:14px">'
      +'<div style="font-size:.68rem;color:#94a3b8;font-weight:900;letter-spacing:.1em;text-transform:uppercase">'+title+'</div>'
      +'<div style="font-size:1.45rem;color:#fff;font-weight:900;margin-top:4px"><span style="color:#4ade80">'+r.w+'</span>-<span style="color:#f87171">'+r.l+'</span>'
      +(r.p?' <span style="font-size:.72rem;color:#94a3b8">('+r.p+' push)</span>':'')+'</div>'
      +'<div style="font-size:.82rem;color:'+color+';font-weight:800;margin-top:3px">'+(r.rate==null?'Pending':r.rate.toFixed(1)+'% hit rate')+'</div>'
      +'<div style="display:grid;grid-template-columns:repeat(2,minmax(92px,1fr));gap:8px;margin-top:12px;padding-top:10px;border-top:1px solid #293548;font-family:monospace;font-size:.72rem">'
      +'<span style="color:#94a3b8">Risked<br><b style="color:#fff">$'+r.risk.toFixed(2)+'</b></span>'
      +'<span style="color:#94a3b8">Net P/L<br><b style="color:'+plColor+'">'+_nflGpMoney(r.net)+'</b></span>'
      +'<span style="color:#94a3b8">ROI<br><b style="color:'+plColor+'">'+(r.roi==null?'—':(r.roi>=0?'+':'')+r.roi.toFixed(1)+'%')+'</b></span>'
      +'<span style="color:#94a3b8">Units<br><b style="color:'+plColor+'">'+(r.units==null?'—':(r.units>=0?'+':'')+r.units.toFixed(2)+'u')+'</b></span>'
      +'<span style="color:#94a3b8">Return<br><b style="color:#fff">$'+r.returned.toFixed(2)+'</b></span>'
      +'<span style="color:#94a3b8">Avg break-even<br><b style="color:#fff">'+(r.breakEven==null?'—':r.breakEven.toFixed(1)+'%')+'</b></span>'
      +'</div><div style="color:#64748b;font-size:.63rem;margin-top:9px">'+r.priced+' priced settled bet'+(r.priced===1?'':'s')+' · flat $'+_nflGpStake().toFixed(2)+'/pick</div></div>';
  }
  var seasonEl=document.getElementById('nflGpSeason'),weekEl=document.getElementById('nflGpWeek'),dateEl=document.getElementById('nflGpDate');
  var season=seasonEl?seasonEl.value:'',week=weekEl?weekEl.value:'all',sel=dateEl?dateEl.value:'all';
  var scopeGames=allGames.filter(function(g){
    return (!season||String(_nflSeasonKey(g.record_date))===season)
      &&(week==='all'||String(_nflGpWeekNumber(g.record_date))===week)
      &&(sel==='all'||g.record_date===sel);
  });
  var shown=[].concat(scopeGames).sort(function(a,b){return String(b.record_date||'').localeCompare(String(a.record_date||''));}).slice(0,80);
  var wr=rec('winner_result',scopeGames),tr=rec('total_result',scopeGames);
  sumEl.innerHTML=replay+'<div style="display:flex;gap:10px;flex-wrap:wrap;margin-bottom:14px">'
    +statCard('Game Winners',wr,'#a78bfa')+statCard('Point Totals',tr,'#38bdf8')+'</div>'
    +'<div style="color:#64748b;font-size:.68rem;line-height:1.5;margin:-4px 2px 13px">ROI = net profit ÷ amount risked. Units = net profit ÷ selected bet amount. Pushes return the stake. Predictions without captured odds stay in the win/loss record but are excluded from financial results.</div>';
  function badge(result){
    if(!result)return '<span style="color:#64748b;font-weight:800">PENDING</span>';
    var color=result==='WIN'?'#4ade80':result==='LOSS'?'#f87171':'#fbbf24';
    return '<span style="color:'+color+';font-weight:900">'+result+'</span>';
  }
  var label=(sel!=='all'?'Results for '+sel:'Results for '+(season||'selected season')+(week!=='all'?' · Week '+week:' · All Weeks'));
  if(!shown.length){
    bodyEl.innerHTML='<div style="color:#94a3b8;font-size:.72rem;font-weight:900;text-transform:uppercase;letter-spacing:.08em;margin:2px 0 8px">'+label+'</div>'
      +'<p style="color:#6b7280;padding:18px 0;text-align:center">No saved Game Predictor forecast exists for this selection. Run Full Week before kickoff to capture every game in that week.</p>';
    return;
  }
  function gpGroup(title,key,pickKey,actualKey,accent,record){
    var rows=shown.map(function(g){
      var actual=key==='winner_result'
        ?((g.actual_away!=null&&g.actual_home!=null)?_esc(g.away_abbr)+' '+g.actual_away+' — '+_esc(g.home_abbr)+' '+g.actual_home:'—')
        :(g.actual_total!=null?_esc(String(g.actual_total)):'—');
      var pick=key==='winner_result'?(g.pick_abbr||'—'):(g.total_pick?(g.total_pick+' '+g.total_line):'—');
      var book=_nflGpBook(g,key),odds=_nflGpOdds(g,key),stake=_nflGpStake();
      var profit=_nflGpProfit(g[key],odds,stake);
      var oddsLabel=odds==null?'—':(Number(odds)>0?'+':'')+Number(odds);
      var implied=_nflGpImplied(odds);
      return '<tr><td class="trk-date" data-label="Date" style="color:#94a3b8">'+_esc(g.record_date||'')+'</td>'
        +'<td data-label="Matchup" style="color:#fff;font-weight:800">'+_esc(g.away_abbr)+' @ '+_esc(g.home_abbr)
        +(g.weather_applied?'<br><small style="color:#fde68a">'+_esc(g.weather_label||'Weather')+' · '+_esc(g.weather_summary||'weather adjustment saved')+'</small>':'')+'</td>'
        +'<td data-label="Pick" style="color:'+accent+';font-weight:900">'+_esc(pick)+'</td>'
        +'<td data-label="Odds / Book" style="font-family:monospace;color:#fff;font-weight:800">'+_esc(oddsLabel)+'<br><small style="color:#94a3b8">'+_esc(book||'Book unavailable')+'</small></td>'
        +'<td data-label="Implied / Bet" style="font-family:monospace;color:#cbd5e1">'+(implied==null?'—':implied.toFixed(1)+'%')+'<br><small style="color:#94a3b8">$'+stake.toFixed(2)+' risk</small></td>'
        +'<td data-label="Actual" style="color:#cbd5e1">'+actual+'</td>'
        +'<td data-label="Result / P&L">'+badge(g[key])+'<br><small style="font-family:monospace;color:'+(profit!=null&&profit>=0?'#4ade80':'#f87171')+'">'+_nflGpMoney(profit)+'</small></td></tr>';
    }).join('');
    return '<details class="nfl-trk-group" style="--trk-accent:'+accent+'"><summary class="nfl-trk-group-head">'
      +'<div class="nfl-trk-group-title"><span class="nfl-trk-group-kicker">Game Predictor</span><span class="nfl-trk-group-name">'+title+'</span></div>'
      +'<div class="nfl-trk-group-summary"><span>'+record.w+'W · '+record.l+'L'+(record.p?' · '+record.p+'P':'')+'</span>'
      +'<span class="nfl-trk-group-rate">'+(record.rate==null?'—':record.rate.toFixed(1)+'%')+'</span>'
      +'<span style="color:'+(record.net>=0?'#4ade80':'#f87171')+'">'+_nflGpMoney(record.net)+' · '+(record.roi==null?'—':(record.roi>=0?'+':'')+record.roi.toFixed(1)+'% ROI')+'</span>'
      +'<span class="nfl-trk-group-toggle" aria-hidden="true"></span></div></summary>'
      +'<div class="nfl-trk-table-scroll"><table class="nfl-trk-tbl nfl-trk-compact"><thead><tr><th>Date</th><th>Matchup</th><th>Pick</th><th>Odds / Book</th><th>Implied / Bet</th><th>Actual</th><th>Result / P&L</th></tr></thead><tbody>'+rows+'</tbody></table></div></details>';
  }
  bodyEl.innerHTML='<div style="color:#94a3b8;font-size:.72rem;font-weight:900;text-transform:uppercase;letter-spacing:.08em;margin:2px 0 8px">'+label+'</div>'
    +gpGroup('Game Winners','winner_result','pick_abbr','final','#a78bfa',wr)
    +gpGroup('Point Totals','total_result','total_pick','actual_total','#38bdf8',tr);
}
function renderNflTrackDay(){
  if(!_nflTrkData) return;
  var dp=document.getElementById('nflTrkDate');
  var selDate=dp?dp.value:'';
  var source=_nflTrkSource(),period=_nflTrkPeriod(),stake=_nflTrkStake();
  var mainDates=source==='historical'
    ?(_nflTrkData.historical_dates||_nflTrkData.dates||[])
    :(_nflTrkData.dates||[]);
  var selectedMain=_nflTrkFilterDates(mainDates,selDate,period);
  function flatten(days){
    var out=[];
    days.forEach(function(d){(d.detail||[]).forEach(function(r){
      out.push(Object.assign({record_date:d.date},r));
    });});
    return out.filter(function(r){return r.result==='WIN'||r.result==='LOSS';});
  }
  var label=_nflTrkPeriodLabel(selDate,period);
  _nflRenderRecordBook(
    flatten(selectedMain),stake,label,
    document.getElementById('nflTrkSummary'),document.getElementById('nflTrkBody'),
    false,source,_nflTrkTabMode);
}
function _nflRoiFocusSummary(decided,stake){
  var focus=decided.filter(function(r){
    return !r.observation_only&&r.category!=='80-100% Locks'
      &&r.side==='UNDER'&&r.odds!=null&&Number(r.odds)>=-150;
  });
  if(!focus.length) return '';
  var wins=focus.filter(function(r){return r.result==='WIN';}).length;
  var losses=focus.length-wins;
  var net=focus.reduce(function(total,r){return total+(_nflTrkProfit(r,stake)||0);},0);
  var roi=focus.length?net/(focus.length*stake)*100:0;
  var color=net>=0?'#4ade80':'#f87171';
  return '<div style="background:rgba(6,95,70,.18);border:1px solid rgba(52,211,153,.38);border-radius:10px;padding:11px 13px;margin-bottom:10px">'
    +'<div style="display:flex;align-items:center;justify-content:space-between;gap:10px;flex-wrap:wrap">'
    +'<div><div style="color:#6ee7b7;font-size:.76rem;font-weight:900;text-transform:uppercase;letter-spacing:.08em">ROI Focus</div>'
    +'<div style="color:#a7f3d0;font-size:.71rem;margin-top:2px">UNDER picks priced -150 or better · excludes duplicate Locks rows</div></div>'
    +'<div style="display:flex;gap:12px;align-items:center;flex-wrap:wrap;font-family:monospace;font-weight:800">'
    +'<span style="color:#fff">'+wins+'-'+losses+'</span>'
    +'<span style="color:'+color+'">'+(net>=0?'+$':'-$')+Math.abs(net).toFixed(0)+'</span>'
    +'<span style="color:'+color+'">ROI '+(roi>=0?'+':'')+roi.toFixed(1)+'%</span>'
    +'</div></div>'
    +'<div style="color:#6b7280;font-size:.68rem;margin-top:7px">A positive historical filter is not a guarantee of future profit.</div></div>';
}
function _nflRenderRecordBook(decided,stake,label,sumEl,bodyEl,isOverflow,source,tabMode){
  if(!sumEl||!bodyEl) return;
  if(!decided.length){
    sumEl.innerHTML='<p style="color:#9ca3af;padding:12px;text-align:center">No '
      +(source==='historical'?'saved historical':'official graded')+' '
      +(isOverflow?'overflow ':'')+'picks for '+label+'.</p>';
    bodyEl.innerHTML='';return;
  }
  var counted=decided.filter(function(r){return !r.observation_only;});
  var observations=decided.length-counted.length;
  var wins=counted.filter(function(r){return r.result==='WIN';}).length;
  var losses=counted.length-wins;
  var priced=counted.filter(function(r){return r.odds!=null;});
  var netPL=priced.reduce(function(a,r){return a+(_nflTrkProfit(r,stake)||0);},0);
  var totalStaked=priced.length*stake;
  var roi=totalStaked?(netPL/totalStaked*100):null;
  var rate=counted.length?(wins/counted.length*100):null;
  var plColor=netPL>=0?'#4ade80':'#f87171';
  var plSign=netPL>=0?'+$':'-$';
  var replayNotice=source==='historical'
    ?'<div style="background:rgba(245,158,11,.1);border:1px solid rgba(245,158,11,.35);border-radius:9px;padding:9px 12px;margin-bottom:10px;color:#fbbf24;font-size:.76rem;font-weight:800">'
      +'Historical Analysis — saved point-in-time replays; excluded from the official record.</div>'
    :'';
  var roiFocusNotice=isOverflow?'':_nflRoiFocusSummary(decided,stake);
  sumEl.innerHTML=replayNotice+roiFocusNotice+'<div class="nfl-trk-sum">'
    +'<span style="color:#9ca3af;font-size:.78rem;font-weight:800">'+label+'</span>'
    +'<span style="font-size:1.05rem;font-weight:900;color:#fff"><span style="color:#4ade80">'+wins+'</span>/<span style="color:#f87171">'+(wins+losses)+'</span>'
    +(rate!=null?' <span style="color:#9ca3af;font-size:.85rem;font-weight:600">('+rate.toFixed(1)+'%)</span>':'')+'</span>'
    +'<span style="font-family:monospace;font-weight:800;color:'+plColor+'">Net '+plSign+Math.abs(netPL).toFixed(0)+'</span>'
    +(roi!=null?'<span style="font-family:monospace;font-weight:700;color:'+plColor+'">ROI '+(roi>=0?'+':'')+roi.toFixed(1)+'%</span>':'')
    +(observations?'<span style="color:#fbbf24;font-weight:800">'+observations+' TD observation'+(observations===1?'':'s')+'</span>':'')
    +'<span style="color:#6b7280;font-size:.8rem">$'+stake+'/play \u00b7 ROI uses priced plays only</span>'
    +'</div>';
  bodyEl.innerHTML=(tabMode||'cat')==='cat'
    ?_nflTrkCatHtml(decided,stake):_nflTrkListHtml(decided,stake);
}
function _nflTrkCatHtml(decided,stake){
  if(!decided.length) return '<p style="color:#6b7280;padding:20px;text-align:center">No graded picks yet.</p>';
  var cats={};
  decided.forEach(function(r){
    var c=cats[r.category]=cats[r.category]||{w:0,l:0,obs:0,pl:0,staked:0};
    if(r.observation_only){c.obs++;return;}
    if(r.result==='WIN') c.w++; else c.l++;
    if(r.odds!=null){c.pl+=(_nflTrkProfit(r,stake)||0);c.staked+=stake;}
  });
  var entries=Object.entries(cats).sort(function(a,b){
    return ((b[1].pl/b[1].staked)||0)-((a[1].pl/a[1].staked)||0);
  });
  return entries.map(function(e){
    var cat=e[0],c=e[1],total=c.w+c.l;
    var rate=total?(c.w/total*100):0;
    var roi=c.staked?(c.pl/c.staked*100):null;
    var plColor=c.pl>=0?'#4ade80':'#f87171';
    var barColor=rate>=70?'#4ade80':rate>=55?'#facc15':'#f87171';
    var list=decided.filter(function(r){return r.category===cat;}).slice().sort(function(a,b){
      return String(b.record_date||'').localeCompare(String(a.record_date||''))||Number(a.rank||999)-Number(b.rank||999)||String(a.name||'').localeCompare(String(b.name||''));
    });
    var detail=list.map(function(r){
      var result=(r.result||'PENDING').toUpperCase(),profit=_nflTrkProfit(r,stake);
      var odds=r.odds!=null?(Number(r.odds)>0?'+':'')+r.odds:'—';
      var book=r.book||(String(r.side||'').toUpperCase()==='UNDER'?r.under_book:r.over_book)||'Book unavailable';
      return '<tr><td class="trk-date" data-label="Date" style="color:#94a3b8;font-family:monospace">'+_nflEsc(r.record_date||'')+'</td>'
        +'<td class="trk-player" data-label="Player" style="color:#fff;font-weight:900">'+_nflEsc(r.name||'')+'</td>'
        +'<td data-label="Team" style="color:#c4b5fd;font-weight:800">'+_nflEsc(r.team||'')+'</td>'
        +'<td class="trk-play" data-label="Pick" style="color:#e2e8f0;font-weight:800">'+_nflEsc((r.side||'')+(r.line!=null?' '+r.line:''))+'</td>'
        +'<td class="trk-odds" data-label="Odds / Book" style="font-family:monospace">'+odds+'<br><small style="color:#64748b">'+_nflEsc(book)+'</small></td>'
        +'<td class="trk-actual" data-label="Actual">'+(r.actual!=null?_nflEsc(String(r.actual)):'—')+'</td>'
        +'<td class="trk-result" data-label="Result / P&L"><span class="nfl-trk-result '+result.toLowerCase()+'">'+_nflEsc(result)+'</span><br><small style="font-family:monospace;color:'+(r.observation_only?'#fbbf24':profit!=null&&profit>=0?'#4ade80':'#f87171')+'">'+(r.observation_only?'OBSERVATION':profit==null?'—':(profit>=0?'+$':'-$')+Math.abs(profit).toFixed(2))+'</small></td></tr>';
    }).join('');
    return '<details class="nfl-trk-group" style="--trk-accent:'+barColor+'"><summary class="nfl-trk-group-head">'
      +'<div class="nfl-trk-group-title"><span class="nfl-trk-group-kicker">Category</span><span class="nfl-trk-group-name">'+_nflEsc(cat)+'</span></div>'
      +'<div class="nfl-trk-group-summary"><span>'+c.w+'W · '+c.l+'L'+(c.obs?' · '+c.obs+' observations':'')+'</span><span class="nfl-trk-group-rate">'+(total?rate.toFixed(1)+'%':'—')+'</span>'
      +'<span class="nfl-trk-group-pl" style="color:'+plColor+'">'+(c.pl>=0?'+$':'-$')+Math.abs(c.pl).toFixed(0)+'</span>'
      +'<span style="color:'+plColor+'">'+(roi!=null?(roi>=0?'+':'')+roi.toFixed(1)+'% ROI':'—')+'</span><span class="nfl-trk-group-toggle" aria-hidden="true"></span></div></summary>'
      +'<div class="nfl-trk-table-scroll"><table class="nfl-trk-tbl nfl-trk-compact"><thead><tr><th>Date</th><th>Player</th><th>Team</th><th>Pick</th><th>Odds / Book</th><th>Actual</th><th>Result / P&L</th></tr></thead><tbody>'+detail+'</tbody></table></div></details>';
  }).join('');
}
function _nflTrkListHtml(decided,stake){
  if(!decided.length) return '<p style="color:#6b7280;padding:20px;text-align:center">No graded picks yet.</p>';
  var catOrder=['Pass Yds','Pass TDs','Completions','Pass Att','INT Thrown',
    'Rush Yds','RB Total Yds','Rush Att','Rec Yds','Receptions','Anytime TD','Tackles+Ast',
    'Sacks','Def INT','Kick Pts','FG Made','80-100% Locks'];
  var catColors={'Pass Yds':'#38bdf8','Pass TDs':'#818cf8','Completions':'#60a5fa',
    'Pass Att':'#22d3ee','INT Thrown':'#f87171','Rush Yds':'#34d399',
    'RB Total Yds':'#10b981',
    'Rush Att':'#2dd4bf','Rec Yds':'#a78bfa','Receptions':'#c084fc',
    'Anytime TD':'#fbbf24','Tackles+Ast':'#fb923c','Sacks':'#f97316',
    'Def INT':'#f43f5e','Kick Pts':'#facc15','FG Made':'#fde047',
    '80-100% Locks':'#facc15'};
  var groups={},order=[];
  function baseCategory(cat){
    return String(cat||'Other').replace(/\s+\((Over|Under)\)$/i,'');
  }
  decided.forEach(function(r){
    var cat=baseCategory(r.category),side=(r.side||'OVER').toUpperCase();
    var key=cat+'|'+side;
    if(!groups[key]){groups[key]=[];order.push(key);}
    groups[key].push(r);
  });
  function orderKey(key){
    var bits=key.split('|'),idx=catOrder.indexOf(bits[0]);
    return (idx<0?catOrder.length:idx)*2+(bits[1]==='UNDER'?1:0);
  }
  order.sort(function(a,b){return orderKey(a)-orderKey(b);});
  function money(v){return v==null?'—':(v>=0?'+$':'-$')+Math.abs(Number(v)).toFixed(2);}
  function groupBlock(key){
    var bits=key.split('|'),cat=bits[0],side=bits[1],list=groups[key].slice().sort(function(a,b){
      var ar=a.rank==null?999:Number(a.rank),br=b.rank==null?999:Number(b.rank);
      return ar-br||String(b.record_date||'').localeCompare(String(a.record_date||''))
        ||String(a.name||'').localeCompare(String(b.name||''));
    });
    var counted=list.filter(function(r){return !r.observation_only;}),observations=list.length-counted.length;
    var w=counted.filter(function(r){return r.result==='WIN';}).length;
    var l=counted.filter(function(r){return r.result==='LOSS';}).length;
    var pushes=counted.filter(function(r){return r.result==='PUSH';}).length;
    var pending=counted.length-w-l-pushes;
    var priced=counted.filter(function(r){return r.odds!=null;});
    var pl=priced.reduce(function(x,r){return x+(_nflTrkProfit(r,stake)||0);},0);
    var rate=(w+l)?w/(w+l)*100:null;
    var accent=catColors[cat]||'#22d3ee';
    var meta=w+'W · '+l+'L'+(pushes?' · '+pushes+'P':'')+(pending?' · '+pending+' pending':'')+(observations?' · '+observations+' observations':'');
    var rows=list.map(function(r){
      var result=(r.result||'PENDING').toUpperCase();
      var resultClass=result.toLowerCase();
      var profit=_nflTrkProfit(r,stake);
      var odds=r.odds!=null?(Number(r.odds)>0?'+':'')+r.odds:'—';
      var book=r.book||(String(r.side||'').toUpperCase()==='UNDER'?r.under_book:r.over_book)||'Book unavailable';
      var plColor=result==='WIN'?'#4ade80':(result==='LOSS'?'#f87171':'#facc15');
      return '<tr>'
        +'<td style="color:#94a3b8;font-family:monospace;font-size:.82rem">'+_nflEsc(r.record_date||'')+'</td>'
        +'<td style="color:#f8fafc;font-weight:900;font-size:.98rem">'+_nflEsc(r.name||'')+'</td>'
        +'<td style="color:#c4b5fd;font-weight:900">'+_nflEsc(r.team||'')+'</td>'
        +'<td style="color:#e2e8f0;font-weight:800">'+_nflEsc((r.side||'')+(r.line!=null?' '+r.line:''))+'</td>'
        +'<td style="font-family:monospace;color:#cbd5e1;font-weight:800">'+odds+'<br><small style="color:#64748b">'+_nflEsc(book)+'</small></td>'
        +'<td style="color:#cbd5e1;font-weight:800">'+(r.actual!=null?_nflEsc(String(r.actual)):'—')+'</td>'
        +'<td><span class="nfl-trk-result '+resultClass+'">'+_nflEsc(result)+'</span></td>'
        +'<td style="font-family:monospace;font-weight:950;color:'+(r.observation_only?'#fbbf24':plColor)+'">'+(r.observation_only?'OBSERVATION':money(profit))+'</td>'
        +'</tr>';
    }).join('');
    return '<details class="nfl-trk-group" style="--trk-accent:'+accent+'">'
      +'<summary class="nfl-trk-group-head"><div class="nfl-trk-group-title">'
      +'<span class="nfl-trk-group-kicker">Category</span><span class="nfl-trk-group-name">'+_nflEsc(cat)+'</span><span class="nfl-trk-group-side">'+_nflEsc(side)+'</span></div>'
      +'<div class="nfl-trk-group-summary"><span>'+meta+'</span><span class="nfl-trk-group-rate">'+(rate!=null?rate.toFixed(1)+'%':'—')+'</span><span class="nfl-trk-group-pl" style="color:'+(pl>=0?'#4ade80':'#f87171')+'">'+money(pl)+'</span><span class="nfl-trk-group-toggle" aria-hidden="true"></span></div></summary>'
      +'<div class="nfl-trk-table-scroll"><table class="nfl-trk-tbl nfl-trk-compact"><thead><tr>'
      +'<th>Date</th><th>Player</th><th>Team</th><th>Pick</th><th>Odds / Book</th><th>Actual</th><th>Result</th><th>P/L</th>'
      +'</tr></thead><tbody>'+rows+'</tbody></table></div></details>';
  }
  return order.map(groupBlock).join('');
}

function downloadNflMyBetsCSV(){
  var d=window.__NFL_MYBETS__;if(!d){alert('Open My Bets first.');return;}
  var rows=[['Date','Player','Team','Category','Side','Pick','Odds','Stake','Result','Actual','Profit']];
  (d.bets||[]).forEach(function(b){
    rows.push([b.date||'',b.name||'',b.team||'',b.category||'',b.side||'',
      b.side+' '+b.line+' '+(b.stat_label||''),
      b.odds!=null?b.odds:'',b.stake!=null?b.stake:'',
      b.result||'',b.actual!=null?b.actual:'',b.profit!=null?b.profit:'']);
  });
  function _c(v){var sv=String(v==null?'':v);if(/[,"\\n]/.test(sv))sv='"'+sv.replace(/"/g,'""')+'"';return sv;}
  var csv=rows.map(function(r){return r.map(_c).join(',');}).join('\\r\\n');
  var blob=new Blob(['\ufeff'+csv],{type:'text/csv;charset=utf-8;'});
  var url=URL.createObjectURL(blob);
  var a=document.createElement('a');a.href=url;a.download='nfl-my-bets.csv';
  document.body.appendChild(a);a.click();document.body.removeChild(a);URL.revokeObjectURL(url);
}
document.addEventListener('DOMContentLoaded',function(){
  var dp=document.getElementById('nflTrkDate');
  if(dp){dp.value=_nflTodayLocal();
    dp.addEventListener('change',function(){_nflTrkDayName();renderNflTrackDay();renderNflGpRecord();});}
  _nflTrkDayName();
  var ovfDp=document.getElementById('nflOvfDate');
  if(ovfDp)ovfDp.value=_nflTodayLocal();
  _nflOvfDayName();
  loadNflTrackRecord(false);
  var top=document.getElementById('nfl-btn-top'),bot=document.getElementById('nfl-btn-bot');
  function _sc(){var y=window.pageYOffset||document.documentElement.scrollTop;
    var atBot=(y+window.innerHeight)>=document.body.scrollHeight-50;
    if(top) top.style.display=y>400?'block':'none';
    if(bot) bot.style.display=!atBot?'block':'none';}
  window.addEventListener('scroll',_sc,{passive:true});_sc();
});
</script>
<!-- Scroll buttons -->
<button id="nfl-btn-top" onclick="window.scrollTo({top:0,behavior:'smooth'})" title="Back to top" style="position:fixed;bottom:76px;right:22px;z-index:9999;display:none;width:48px;height:48px;border-radius:50%;border:none;cursor:pointer;background:#f59e0b;color:#0a0a0a;font-size:1.4rem;font-weight:900;box-shadow:0 4px 14px rgba(0,0,0,.45);line-height:1">&#8593;</button>
<button id="nfl-btn-bot" onclick="window.scrollTo({top:document.body.scrollHeight,behavior:'smooth'})" title="Scroll to bottom" style="position:fixed;bottom:22px;right:22px;z-index:9999;display:none;width:48px;height:48px;border-radius:50%;border:none;cursor:pointer;background:#0ea5e9;color:#0a0a0a;font-size:1.4rem;font-weight:900;box-shadow:0 4px 14px rgba(0,0,0,.45);line-height:1">&#8595;</button>
</body>
</html>"""
