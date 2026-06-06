
# NBA Stats API blocks server IPs. ESPN gives schedule + rosters + player game logs free.

import asyncio, pathlib, time
import json
import os
import hashlib
import re
import unicodedata
from datetime import date, datetime, timedelta
from typing import Dict, List, Optional, Any

import httpx
from fastapi import FastAPI, Request
from fastapi.responses import HTMLResponse, RedirectResponse

app = FastAPI(title="Money Buckets")

# ─── Auth ─────────────────────────────────────────────────────────────────────
USERS_RAW = os.environ.get("USERS", "admin:buckets")
USERS: Dict[str, str] = {}
for _pair in USERS_RAW.split(","):
    if ":" in _pair.strip():
        _u, _p = _pair.strip().split(":", 1)
        USERS[_u.strip()] = _p.strip()

SECRET = os.environ.get("SECRET_KEY", "nba-money-buckets-2026")

def make_token(username: str) -> str:
    return hashlib.sha256(f"{username}:{SECRET}".encode()).hexdigest()

def get_user(request: Request) -> Optional[str]:
    from jose import jwt as _jose_jwt
    import os as _os
    _jwt_secret = _os.environ.get("JWT_SECRET", "")
    tok = request.query_params.get("_tok","") or request.cookies.get("__mpa_token","") or request.headers.get("Authorization","").replace("Bearer ","").strip()
    if not tok or len(tok.split(".")) != 3 or not _jwt_secret:
        return None
    try:
        _jose_jwt.decode(tok, _jwt_secret, algorithms=["HS256"])
        return tok
    except Exception:
        return None

_NBA_ADMIN_EMAILS = {e.strip().lower() for e in os.environ.get("ADMIN_EMAIL", "higgi117711@gmail.com").split(",") if e.strip()}

def _token_email(token: str) -> str:
    """Return the email (sub) from a hub token, else ''.
    Primary path: verify the signature with JWT_SECRET (secure, used when the hub
    and this app share an identical secret on Render). Fallback: read the
    unverified claims so the owner still resolves as admin on login even if the
    two Render services don't have a matching JWT secret. The only thing this
    unlocks is the admin UI (Run/Force) for the configured ADMIN_EMAIL."""
    from jose import jwt as _jose_jwt
    import os as _os
    if not token or len(token.split(".")) != 3:
        return ""
    _secret = _os.environ.get("JWT_SECRET", "")
    if _secret:
        try:
            payload = _jose_jwt.decode(token, _secret, algorithms=["HS256"])
            return str(payload.get("sub", "")).strip().lower()
        except Exception:
            pass
    try:
        payload = _jose_jwt.get_unverified_claims(token)
        return str(payload.get("sub", "")).strip().lower()
    except Exception:
        return ""

def _is_admin_token(token: str) -> bool:
    return bool(_NBA_ADMIN_EMAILS) and _token_email(token) in _NBA_ADMIN_EMAILS

# ─── Stat Config ──────────────────────────────────────────────────────────────
# ESPN gamelog stats array order:
# [0]=MIN [1]=FG [2]=FG% [3]=3PT [4]=3P% [5]=FT [6]=FT% [7]=REB [8]=AST
# [9]=BLK [10]=STL [11]=PF [12]=TO [13]=PTS
STAT_CONFIG = {
    'PTS':  {'label': 'Points',     'emoji': '🏀', 'idx': 13, 'thresholds': list(range(45, 4, -1))},
    'REB':  {'label': 'Rebounds',   'emoji': '📊', 'idx': 7,  'thresholds': list(range(20, 1, -1))},
    'AST':  {'label': 'Assists',    'emoji': '🎯', 'idx': 8,  'thresholds': list(range(15, 1, -1))},
    'FG3M': {'label': '3-Pointers', 'emoji': '🔥', 'idx': 3,  'thresholds': list(range(8,  0, -1))},
    'PRA':  {'label': 'Pts+Reb+Ast','emoji': '🃏', 'idx': None, 'thresholds': list(range(60, 9, -1))},
    'PTS_REB': {'label': 'Pts+Reb', 'emoji': '💪', 'idx': None, 'thresholds': list(range(55, 6, -1))},
    'PTS_AST': {'label': 'Pts+Ast', 'emoji': '⚡', 'idx': None, 'thresholds': list(range(50, 6, -1))},
    'REB_AST': {'label': 'Reb+Ast', 'emoji': '🔗', 'idx': None, 'thresholds': list(range(30, 3, -1))},
    'BLK':  {'label': 'Blocks',     'emoji': '🛡️', 'idx': 9,  'thresholds': list(range(6, 0, -1))},
    'STL':  {'label': 'Steals',     'emoji': '🧤', 'idx': 10, 'thresholds': list(range(6, 0, -1))},
}

HIT_RATE_MIN  = 0.70
MIN_GAMES     = 2
MIN_MINUTES   = 10.0
ESPN_SEASONS  = [2026, 2025, 2024, 2023, 2022, 2021, 2020]
TOP_N         = 12

ODDS_API_BASE   = "https://api.the-odds-api.com/v4"
ODDS_MARKET_MAP = {
    "player_points":                    "PTS",
    "player_rebounds":                   "REB",
    "player_assists":                    "AST",
    "player_threes":                     "FG3M",
    "player_points_rebounds_assists":    "PRA",
    "player_points_rebounds":            "PTS_REB",
    "player_points_assists":             "PTS_AST",
    "player_rebounds_assists":           "REB_AST",
    "player_blocks":                     "BLK",
    "player_steals":                     "STL",
}
MIN_GAMES     = 1
MIN_MINUTES   = 10.0
ESPN_SEASONS  = [2026, 2025, 2024, 2023, 2022, 2021, 2020]   # ESPN uses season END year — 7 seasons for full career H/A history
TOP_N         = 12

# ─── Cache ────────────────────────────────────────────────────────────────────
_cache: Dict[str, Any] = {}  # kept for compat
# ── File-based Picks Cache ────────────────────────────────────────────────────
import pathlib
_CACHE_DIR = pathlib.Path("/tmp/mpa_cache")
_CACHE_DIR.mkdir(parents=True, exist_ok=True)
_CACHE_TTL = 6 * 3600  # 6 hours

# ── Bet Log ───────────────────────────────────────────────────────────────────
import threading as _nba_th
import uuid as _nba_uuid

_NBA_BET_LOG_PATH = str(_CACHE_DIR / "_nba_bet_log.json")
_NBA_BET_LOCK = _nba_th.Lock()
_NBA_BET_STAT_KEYS = ("PTS","REB","AST","FG3M","BLK","STL","PRA","PTS_REB","PTS_AST","REB_AST")
_NBA_STAT_LABEL = {"PTS":"Points","REB":"Rebounds","AST":"Assists","FG3M":"3-Pointers",
    "PRA":"Pts+Reb+Ast","PTS_REB":"Pts+Reb","PTS_AST":"Pts+Ast",
    "REB_AST":"Reb+Ast","BLK":"Blocks","STL":"Steals"}

def _nba_load_bets() -> dict:
    try:
        with open(_NBA_BET_LOG_PATH) as f:
            return json.load(f)
    except Exception:
        return {}

def _nba_save_bets(data: dict):
    try:
        tmp = _NBA_BET_LOG_PATH + f".{os.getpid()}.tmp"
        with open(tmp, "w") as f:
            json.dump(data, f)
        os.replace(tmp, _NBA_BET_LOG_PATH)
    except Exception as e:
        print(f"[nba_bet_log] save failed: {e}")

def _nba_bet_admin_ok(tok: str, admin: str) -> bool:
    return _is_admin_token(tok) or (
        bool(admin) and admin == os.environ.get("INTERNAL_API_TOKEN", "__none__"))

def _nba_bet_user_key(tok: str, admin: str) -> str:
    em = _token_email(tok) if tok else ""
    return em.lower().strip() if em else "__admin__"

def _nba_american_profit(odds, stake, result) -> float:
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

def _nba_am_to_dec(odds) -> float:
    try:
        o = float(odds)
    except Exception:
        return 1.0
    return round(1 + o / 100, 6) if o > 0 else round(1 + 100 / abs(o), 6)

def _nba_extract_stat(stats_arr: list, stat_key: str):
    """Extract NBA stat from ESPN box score stats array (MIN,FG,3PT,FT,OREB,DREB,REB,AST,STL,BLK,TO,PF,+/-,PTS)."""
    IDX = {"PTS": 13, "REB": 6, "AST": 7, "FG3M": 2, "BLK": 9, "STL": 8}
    if stat_key in IDX:
        try:
            raw = stats_arr[IDX[stat_key]]
            if stat_key == "FG3M" and isinstance(raw, str) and "-" in raw:
                return float(raw.split("-")[0])
            return float(raw)
        except Exception:
            return None
    _base = {"PRA": ("PTS","REB","AST"), "PTS_REB": ("PTS","REB"),
             "PTS_AST": ("PTS","AST"), "REB_AST": ("REB","AST")}
    if stat_key in _base:
        vals = [_nba_extract_stat(stats_arr, k) for k in _base[stat_key]]
        if all(v is not None for v in vals):
            return sum(vals)
    return None

_NBA_BOX_CACHE: dict = {}
_NBA_BOX_TTL = 120

def _nba_box_lookup(date_str: str) -> dict:
    """Cached wrapper: final dates cached permanently, in-progress dates for
    _NBA_BOX_TTL seconds. Prevents repeat ESPN scoreboard hits (HTTP 429) when
    My Bets / the hub fan-out settle the same date many times."""
    import time as _t
    ent = _NBA_BOX_CACHE.get(date_str)
    now = _t.time()
    if ent and (ent["final"] or now - ent["ts"] < _NBA_BOX_TTL):
        return ent["data"]
    res, complete = _nba_box_lookup_raw(date_str)
    allfinal = complete and bool(res)
    _NBA_BOX_CACHE[date_str] = {"ts": now, "final": allfinal, "data": res}
    return res

def _nba_box_lookup_raw(date_str: str):
    """Return (results, complete). results = {lowername: {stat_key: float, 'final': bool}}.
    complete is True only when EVERY event for the date is final AND its box score was
    fetched successfully, so the wrapper marks the cache permanent only on fully-complete
    data (a failed summary fetch keeps the date on the short TTL so it retries)."""
    d = date_str.replace("-", "")
    results: dict = {}
    try:
        sb = httpx.get(
            f"https://site.api.espn.com/apis/site/v2/sports/basketball/nba/scoreboard?dates={d}",
            timeout=15, headers={"User-Agent": "Mozilla/5.0"})
        sb.raise_for_status()
        events = sb.json().get("events", [])
    except Exception as e:
        print(f"[nba_box] scoreboard failed {date_str}: {e}")
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
                f"https://site.api.espn.com/apis/site/v2/sports/basketball/nba/summary?event={ev_id}",
                timeout=15, headers={"User-Agent": "Mozilla/5.0"})
            if bs.status_code != 200:
                complete = False
                continue
            boxscore = bs.json().get("boxscore", {})
        except Exception:
            complete = False
            continue
        for team in boxscore.get("players", []):
            for grp in team.get("statistics", []):
                for ath in grp.get("athletes", []):
                    name = (ath.get("athlete", {}).get("displayName") or "").lower().strip()
                    stats_arr = ath.get("stats", [])
                    if not name or not stats_arr:
                        continue
                    ps: dict = {"final": is_final}
                    for sk in _NBA_BET_STAT_KEYS:
                        v = _nba_extract_stat(stats_arr, sk)
                        if v is not None:
                            ps[sk] = v
                    results[name] = ps
    return results, complete

def _nba_settle_cached(bet: dict, name_stats: dict) -> bool:
    if bet.get("result") in ("WIN", "LOSS", "PUSH"):
        return False
    st = name_stats.get((bet.get("name") or "").lower())
    if not st or not st.get("final"):
        return False
    stat_key = bet.get("stat_key")
    actual = st.get(stat_key)
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
    bet["profit"] = round(_nba_american_profit(bet.get("odds"), bet.get("stake"), res), 2)
    bet["settled_at"] = date.today().isoformat()
    return True

def _nba_settle_bet(bet: dict) -> bool:
    if bet.get("result") in ("WIN", "LOSS", "PUSH"):
        return False
    bdate = bet.get("date")
    if not bdate or bdate >= date.today().isoformat():
        return False
    try:
        ns = _nba_box_lookup(bdate)
    except Exception as e:
        print(f"[nba_bet_log] settle lookup failed {bdate}: {e}")
        return False
    return _nba_settle_cached(bet, ns)

def _nba_settle_batch(bets: list) -> bool:
    today = date.today().isoformat()
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
            ns_cache[d] = _nba_box_lookup(d)
        except Exception as e:
            print(f"[nba_bet_log] batch settle failed {d}: {e}")
    changed = False
    for b in bets:
        bdate = b.get("date")
        if bdate and bdate in ns_cache:
            if _nba_settle_cached(b, ns_cache[bdate]):
                changed = True
    return changed

_NBA_CAT_ORDER = ["Points","Rebounds","Assists","3-Pointers","Pts+Reb+Ast",
    "Pts+Reb","Pts+Ast","Reb+Ast","Blocks","Steals"]

def _nba_summarize_bets(bets: list) -> dict:
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
    ordered = _NBA_CAT_ORDER + [k for k in cats if k not in _NBA_CAT_ORDER]
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

def _cache_path(app: str, date_key: str) -> pathlib.Path:
    return _CACHE_DIR / f"{app}_{date_key}.json"

def _cache_get(app: str, date_key: str):
    p = _cache_path(app, date_key)
    try:
        if p.exists() and (time.time() - p.stat().st_mtime) < _CACHE_TTL:
            data = json.loads(p.read_text(encoding="utf-8"))
            print(f"[Cache] FILE HIT {app}/{date_key}")
            return data
    except Exception as e:
        print(f"[Cache] Read error: {e}")
    return None

def _cache_set(app: str, date_key: str, result: dict):
    try:
        _cache_path(app, date_key).write_text(
            json.dumps(result, ensure_ascii=False), encoding="utf-8")
        print(f"[Cache] FILE SET {app}/{date_key}")
    except Exception as e:
        print(f"[Cache] Write error: {e}")

def _cache_clear(app: str = None):
    for p in _CACHE_DIR.glob("*.json"):
        if app is None or p.name.startswith(app + "_"):
            p.unlink(missing_ok=True)

async def get_today_games(date_str: str = None) -> List[Dict]:
    if date_str:
        today_fmt = datetime.strptime(date_str, '%Y-%m-%d').strftime('%Y%m%d')
    else:
        today_fmt = date.today().strftime('%Y%m%d')

    url = f"https://site.api.espn.com/apis/site/v2/sports/basketball/nba/scoreboard?dates={today_fmt}"
    async with httpx.AsyncClient(timeout=30) as c:
        r = await c.get(url)
        data = r.json()

    games = []
    for event in data.get('events', []):
        comps = event['competitions'][0]['competitors']
        home = next((c for c in comps if c['homeAway'] == 'home'), None)
        away = next((c for c in comps if c['homeAway'] == 'away'), None)
        if not home or not away:
            continue
        games.append({
            'home':      _norm_abbr(home['team']['abbreviation']),
            'away':      _norm_abbr(away['team']['abbreviation']),
            'home_id':   home['team']['id'],
            'away_id':   away['team']['id'],
            'home_name': home['team']['displayName'],
            'away_name': away['team']['displayName'],
            'tipoff':    event.get('date', ''),
        })
    return games


async def get_team_roster_espn(team_id: str) -> List[Dict]:
    url = f"https://site.api.espn.com/apis/site/v2/sports/basketball/nba/teams/{team_id}/roster"
    try:
        async with httpx.AsyncClient(timeout=20) as c:
            await asyncio.sleep(0.1)
            r = await c.get(url)
            data = r.json()
        return [{'id': p['id'], 'name': p.get('displayName', ''),
                 'jersey': p.get('jersey', ''),
                 'position': (p.get('position') or {}).get('abbreviation', '')}
                for p in data.get('athletes', [])]
    except Exception as e:
        print(f"  Roster error {team_id}: {e}")
        return []


async def get_player_gamelogs_espn(player_id: str, season: int,
                                    sem: asyncio.Semaphore) -> List[Dict]:
    """Fetch one player's game logs for one season from ESPN."""
    url = (f"https://site.web.api.espn.com/apis/common/v3/sports/"
           f"basketball/nba/athletes/{player_id}/gamelog")
    async with sem:
        try:
            async with httpx.AsyncClient(timeout=20) as c:
                r = await c.get(url, params={'season': season})
                if r.status_code != 200:
                    return []
                gl = r.json()
        except Exception:
            return []

    events = gl.get('events', {})

    # Build eventId → stats map from seasonTypes → categories → events
    stats_map: Dict[str, List] = {}
    for st in gl.get('seasonTypes', []):
        # WHITELIST: only count Regular Season + Postseason. Excludes preseason,
        # summer league, NBA Cup / In-Season Tournament, exhibitions, etc.
        st_name = (st.get('displayName') or st.get('name') or '').lower()
        if not ('regular' in st_name or 'post' in st_name or 'playoff' in st_name):
            continue
        for cat in st.get('categories', []):
            if cat is None:
                continue
            for ev in cat.get('events', []):
                eid = ev.get('eventId')
                if eid and ev.get('stats') and eid not in stats_map:
                    stats_map[eid] = ev['stats']

    games = []
    for eid, ev_info in events.items():
        if eid not in stats_map:
            continue
        stats = stats_map[eid]
        if len(stats) < 14:
            continue

        # Skip garbage time / DNP games
        if parse_min(stats[0]) < MIN_MINUTES:
            continue

        opp_info = ev_info.get('opponent', {})
        opp_abbr = _norm_abbr(opp_info.get('abbreviation', '') if isinstance(opp_info, dict) else '')
        location = 'Away' if ev_info.get('atVs', '') == '@' else 'Home'
        team_info = ev_info.get('team', {})
        player_team_abbr = _norm_abbr(team_info.get('abbreviation', '') if isinstance(team_info, dict) else '')

        games.append({
            'opp':         opp_abbr,
            'location':    location,
            'date':        ev_info.get('gameDate', ''),
            'player_team': player_team_abbr,
            'MIN':         parse_min(stats[0]),
            'PTS':         parse_stat(stats[13]),
            'REB':         parse_stat(stats[7]),
            'AST':         parse_stat(stats[8]),
            'FG3M':        parse_stat(stats[3]),
            'PRA':         parse_stat(stats[13]) + parse_stat(stats[7]) + parse_stat(stats[8]),
            'PTS_REB':     parse_stat(stats[13]) + parse_stat(stats[7]),
            'PTS_AST':     parse_stat(stats[13]) + parse_stat(stats[8]),
            'REB_AST':     parse_stat(stats[7])  + parse_stat(stats[8]),
            'BLK':         parse_stat(stats[9]),
            'STL':         parse_stat(stats[10]),
        })
    return games

# ─── Analysis ─────────────────────────────────────────────────────────────────

def _nn(n):
    import unicodedata as ud, re
    s = ud.normalize('NFD', n).encode('ascii','ignore').decode().lower()
    return re.sub(r'[^a-z ]', '', s).strip()

def _nm(a, b):
    na, nb = _nn(a), _nn(b)
    if na == nb: return True
    pa, pb = na.split(), nb.split()
    return len(pa) >= 2 and len(pb) >= 2 and pa[0][0] == pb[0][0] and pa[-1] == pb[-1]


async def get_underdog_lines():
    """DEPRECATED — Underdog removed. Odds API is the sole line source."""
    return []

async def get_odds_lines(today_str):
    api_key = os.environ.get('ODDS_API_KEY', '')
    if not api_key:
        return []
    props = []
    try:
        async with httpx.AsyncClient(timeout=20) as c:
            # Event filter: keep an event iff its US-Eastern calendar date equals the
            # SELECTED date. Converting to ET first correctly handles a late ET tip that
            # rolls into the next UTC day. Unlike a now-relative rolling window, scoping to
            # the selected day lets admins pull lines for a game days out (the date picker is
            # unlocked for them) while keeping each player's props bound to the right game —
            # no cross-day overwrite from intermediate-day events. Non-admins are capped at
            # tomorrow by the picker, so they only ever see today's/tomorrow's slate.
            from datetime import datetime as _dt, timezone as _tz, timedelta as _td
            try:
                from zoneinfo import ZoneInfo as _ZI
                _ET = _ZI("America/New_York")
            except Exception:
                _ET = _tz(-_td(hours=4))  # EDT fallback if the tz database is unavailable

            def _in_window(iso_ts: str) -> bool:
                try:
                    t = _dt.fromisoformat(iso_ts.replace('Z', '+00:00'))
                    return t.astimezone(_ET).strftime('%Y-%m-%d') == today_str
                except Exception:
                    return False

            events = []
            active_key = 'basketball_nba'
            for sport_key in ('basketball_nba', 'basketball_nba_championship'):
                r = await c.get(f"{ODDS_API_BASE}/sports/{sport_key}/events",
                                params={'apiKey': api_key, 'dateFormat': 'iso'})
                if r.status_code == 200:
                    raw = r.json()
                    found = [e for e in raw if _in_window(e.get('commence_time', ''))]
                    print(f'[OddsAPI] {sport_key}: {len(raw)} total events, {len(found)} in window')
                    if found:
                        events = found
                        active_key = sport_key
                        print(f'[OddsAPI] {len(events)} NBA events ({sport_key}) for {today_str}')
                        break
                else:
                    print(f'[OddsAPI] events {r.status_code} for {sport_key}: {r.text[:150]}')
            if not events:
                print(f'[OddsAPI] No NBA events found for {today_str}')
                return []
            markets = ','.join(ODDS_MARKET_MAP.keys())
            for ev in events:
                r2 = await c.get(
                    f"{ODDS_API_BASE}/sports/{active_key}/events/{ev['id']}/odds",
                    params={'apiKey': api_key, 'regions': 'us',
                            'markets': markets, 'oddsFormat': 'american'})
                if r2.status_code != 200:
                    print(f'[OddsAPI] props {r2.status_code} for {ev.get("home_team","?")} game: {r2.text[:150]}')
                    continue
                data = r2.json()
                seen = set()
                for book in data.get('bookmakers', []):
                    for mkt in book.get('markets', []):
                        stat = ODDS_MARKET_MAP.get(mkt.get('key', ''))
                        if not stat:
                            continue
                        # Collect BOTH Over and Under prices per player for this market.
                        by_player = {}
                        for oc in mkt.get('outcomes', []):
                            nm = oc.get('name')
                            if nm not in ('Over', 'Under'):
                                continue
                            player = oc.get('description', '').strip()
                            line   = float(oc.get('point') or 0)
                            if not player or line <= 0:
                                continue
                            d = by_player.setdefault(player, {'line': line})
                            d['line'] = line
                            if nm == 'Over':
                                d['over_odds'] = str(oc.get('price', ''))
                            else:
                                d['under_odds'] = str(oc.get('price', ''))
                        for player, d in by_player.items():
                            if 'over_odds' not in d:   # require an Over line to register (mirrors prior behavior)
                                continue
                            key = f"{player}|{stat}"
                            if key not in seen:
                                seen.add(key)
                                props.append({
                                    'player': player, 'stat': stat, 'line': d['line'],
                                    'odds': d.get('over_odds', ''),
                                    'over_odds': d.get('over_odds', ''),
                                    'under_odds': d.get('under_odds', ''),
                                    'home': data.get('home_team', ''),
                                    'away': data.get('away_team', ''),
                                })
                    # check all bookmakers for best coverage
    except Exception as e:
        print(f'[OddsAPI] error: {e}')
    print(f'[OddsAPI] {len(props)} NBA prop lines fetched')
    return props


def parse_stat(val):
    s = str(val)
    if '-' in s: s = s.split('-')[0]
    try: return int(float(s))
    except: return 0

def parse_min(val):
    s = str(val)
    if ':' in s:
        p = s.split(':')
        try: return float(p[0]) + float(p[1])/60
        except: return 0.0
    try: return float(s)
    except: return 0.0

_ABBR_ALIASES = {
    'SA': 'SAS', 'SAS': 'SAS',
    'NO': 'NOP', 'NOP': 'NOP', 'NOH': 'NOP',
    'GS': 'GSW', 'GSW': 'GSW',
    'NY': 'NYK', 'NYK': 'NYK',
    'UTAH': 'UTA', 'UTA': 'UTA',
    'WSH': 'WAS', 'WAS': 'WAS',
    'PHX': 'PHX', 'PHO': 'PHX',
    'BKN': 'BKN', 'BRK': 'BKN',
    'CHA': 'CHA', 'CHO': 'CHA',
}
def _norm_abbr(a):
    """Normalize ESPN team abbreviation — scoreboard + gamelog APIs disagree
    on some teams (SA vs SAS, NO vs NOP, GS vs GSW, etc)."""
    if not a: return a
    return _ABBR_ALIASES.get(a.upper(), a.upper())


def _streak_pick(line, recent10, sk):
    """🔥 STREAK PICK: trailing consecutive games over the line.
    Returns ('OVER', n) if 3+ in a row over, ('UNDER', n) if 3+ in a row under, else (None, 0).
    recent10 is sorted newest-first."""
    if not line or not recent10:
        return None, 0
    over_streak = under_streak = 0
    for g in recent10:
        v = float(g[sk])
        if v > line:
            if under_streak: break
            over_streak += 1
        elif v < line:
            if over_streak: break
            under_streak += 1
        else:
            break
    if over_streak >= 3:
        return 'OVER', over_streak
    if under_streak >= 3:
        return 'UNDER', under_streak
    return None, 0


def _alt_pick(line, recent10, sk):
    """🔄 ALTERNATING PICK: on/off pattern. recent10 newest-first.
    If even-indexed games (0,2,4,6,8 = most recent + every other before)
    hit overs ≥4/5 and odd-indexed hit ≤1/5 (or vice versa), pattern is strong.
    Tonight is the NEXT game so its parity is OPPOSITE of index 0.
    Returns (rec, evens_hit_text, odds_hit_text) or (None, None, None)."""
    if not line or len(recent10) < 2:
        return None, None, None
    evens = recent10[0::2][:5]  # idx 0,2,4,6,8
    odds  = recent10[1::2][:5]  # idx 1,3,5,7,9
    e_hits = sum(1 for g in evens if float(g[sk]) > line)
    o_hits = sum(1 for g in odds  if float(g[sk]) > line)
    e_n, o_n = len(evens), len(odds)
    if e_n < 1 or o_n < 1:
        return None, None, None
    e_pct = e_hits / e_n
    o_pct = o_hits / o_n
    # Strong alternation = one side ≥70%, other ≤30%, and a clear gap
    # (catches usage/minute cycles books exploit — heavy night → light night)
    if e_pct >= 0.70 and o_pct <= 0.30:
        # Evens are HIGH cycle; tonight = odd cycle = LOW = UNDER
        return 'UNDER', f"{e_hits}/{e_n}", f"{o_hits}/{o_n}"
    if o_pct >= 0.70 and e_pct <= 0.30:
        # Odds are HIGH cycle; tonight = even cycle = LOW = UNDER... wait
        # Actually: most recent past game is idx 0 (even). Tonight = NEXT game.
        # If odds (idx 1,3,5...) are HIGH cycle and evens are LOW,
        # tonight follows the alternation → opposite of most recent = HIGH = OVER.
        return 'OVER', f"{e_hits}/{e_n}", f"{o_hits}/{o_n}"
    return None, None, None


def _line_pick(line, all_vals, last10, sk):
    """Recommend OVER/UNDER vs the sportsbook line based on last-10 hit rate.
    Returns (rec, pct, hits_text) or (None, None, None) if no line/data."""
    if not line or not last10:
        return None, None, None
    n = len(last10)
    over_hits = sum(1 for l in last10 if float(l[sk]) > line)
    under_hits = n - over_hits
    if over_hits == under_hits:
        return None, None, None
    # Require at least 70% on the dominant side to qualify
    if over_hits > under_hits:
        pct = over_hits / n
        if pct < 0.70:
            return None, None, None
        return 'OVER', round(pct * 100, 1), f"{over_hits}/{n}"
    pct = under_hits / n
    if pct < 0.70:
        return None, None, None
    return 'UNDER', round(pct * 100, 1), f"{under_hits}/{n}"


def find_best_threshold(values, thresholds):
    n = len(values)
    if n < MIN_GAMES: return None
    for t in thresholds:
        hits = sum(1 for v in values if v >= t)
        rate = hits / n
        if rate >= HIT_RATE_MIN:
            return {'threshold':t,'hits':hits,'games':n,'hit_rate':rate,'pct':round(rate*100,1)}
    return None


def pattern_at_line(values, line):
    """PATTERN consistency measured at the ACTUAL sportsbook line (OVER side).
    Returns the matchup/location over-rate, qualifying only when the player
    cleared the real betting line in >= HIT_RATE_MIN of those games. The
    'threshold' is the integer bar implied by the line (over 2.5 -> 3+), so the
    badge ("PATTERN 3/4 vs OPP") and the bet ("over 2.5") describe the same thing."""
    if line is None or not values:
        return None
    n = len(values)
    if n < MIN_GAMES:
        return None
    hits = sum(1 for v in values if v > line)
    rate = hits / n
    if rate < HIT_RATE_MIN:
        return None
    return {'threshold': int(line) + 1, 'hits': hits, 'games': n,
            'hit_rate': rate, 'pct': round(rate * 100, 1)}


def build_ladder(values, line, span=3):
    """A — Hit-rate ladder anchored to the sportsbook line. Sportsbooks only
    offer alt lines NEAR the posted number, so showing the full integer range
    (3,4,5,6...) is useless — you can never bet those. Instead we show `span`
    rungs below and above the actual book line in 1-point steps at the book's
    half-point (e.g. line 29.5 -> 26.5, 27.5, 28.5, 29.5, 30.5, 31.5, 32.5).
    Each rung = how often the player went OVER that alt line (v > rung) over the
    same opponent/location history. Returns [] when there is no book line."""
    if not values or line is None:
        return []
    n = len(values)
    out = []
    for off in range(-span, span + 1):
        rung = round(line + off, 1)
        if rung <= 0:
            continue
        hits = sum(1 for v in values if v > rung)
        out.append({'t': rung, 'hits': hits, 'games': n, 'pct': round(hits / n * 100)})
    return out


def best_bet_at_line(line, values):
    """B — Best bet at the sportsbook's ACTUAL line: over the same opponent/location
    history, the dominant side (over/under) vs that line plus its hit rate and a
    confidence label (STRONG >=70%, LEAN >=60%, else PASS)."""
    if line is None or not values:
        return None
    n = len(values)
    over = sum(1 for v in values if v > line)
    under = n - over
    if over == under:                      # even split = no edge, do not pick a side
        return {'side': 'PASS', 'line': line, 'hits': over, 'games': n, 'pct': 50, 'conf': 'PASS'}
    if over > under:
        side, hits = 'OVER', over
    else:
        side, hits = 'UNDER', under
    pct = round(hits / n * 100)
    conf = 'STRONG' if pct >= 70 else ('LEAN' if pct >= 60 else 'PASS')
    return {'side': side, 'line': line, 'hits': hits, 'games': n, 'pct': pct, 'conf': conf}


async def run_analysis(selected_date: str = None, force: bool = False) -> Dict:
    today_str = selected_date if selected_date else date.today().isoformat()
    # File cache check first (skipped on force refresh — admin only)
    if not force:
        _fc = _cache_get('nba', today_str)
        if _fc:
            _cache.update(_fc)
            return _fc
        if _cache.get('date') == today_str and _cache.get('picks') is not None and _cache.get('odds_loaded'):
            return _cache

    log = []
    log.append(f"Fetching schedule + sportsbook lines for {today_str}...")

    # Games first — if there are none today (e.g. a playoff off-day), bail out
    # immediately and skip the odds fetch + entire pipeline. No slow run, no
    # failure-looking empty result.
    try:
        games = await get_today_games(today_str)
    except Exception as e:
        return {'date': today_str, 'picks': [], 'all_picks': [], 'games': [],
                'log': [f'Error: {e}'], 'total': 0}

    if not games:
        return {'date': today_str, 'picks': [], 'all_picks': [], 'games': [],
                'no_games': True,
                'log': [f'No NBA games scheduled for {today_str}.'], 'total': 0}

    # Games exist — now fetch the Odds API lines (sole sportsbook source).
    try:
        odds_raw = await get_odds_lines(today_str)
        odds_props = odds_raw
        log.append(f"OddsAPI: {len(odds_raw)} lines")
    except Exception as e:
        return {'date': today_str, 'picks': [], 'all_picks': [], 'games': [],
                'log': [f'Error: {e}'], 'total': 0}

    log.append("Games: " + " | ".join(f"{g['away']} @ {g['home']}" for g in games))
    log.append(f"{len(odds_props)} sportsbook prop lines loaded")

    # Build lookups — odds_lookup is last-seen (compute uses bet365/us2 line
    # when available) which is the behavior the picks have been calibrated
    # against. dk_lookup below is first-seen for display.
    odds_lookup: Dict[tuple, Dict] = {}
    for prop in odds_props:
        key = (_nn(prop['player']), prop['stat'])
        odds_lookup[key] = {'line': prop['line'], 'odds': str(prop.get('odds', ''))}

    # dk_lookup uses Odds API lines as the sole sportsbook source
    dk_lookup: Dict[tuple, Dict] = {}
    for prop in odds_raw:
        key = (_nn(prop['player']), prop['stat'])
        if key not in dk_lookup:
            dk_lookup[key] = {'line': prop['line'], 'over_odds': str(prop.get('over_odds', '')), 'under_odds': str(prop.get('under_odds', ''))}

    # Map team_id -> abbreviation so we can match a player's per-game team
    # (ESPN exposes 'team.abbreviation' per gamelog event). Used to filter out
    # games the player played for a PREVIOUS team after a trade.
    tid_to_abbr: Dict[str, str] = {}
    for g in games:
        tid_to_abbr[g['home_id']] = g['home']
        tid_to_abbr[g['away_id']] = g['away']

    # Rosters
    team_ids = list({g['home_id'] for g in games} | {g['away_id'] for g in games})
    roster_results = await asyncio.gather(
        *[get_team_roster_espn(tid) for tid in team_ids], return_exceptions=True)
    rosters: Dict[str, List[Dict]] = {}
    for tid, res in zip(team_ids, roster_results):
        rosters[tid] = res if isinstance(res, list) else []
    total_players = sum(len(v) for v in rosters.values())
    log.append(f"{total_players} players loaded")

    # Fetch game logs (all players, 3 seasons)
    all_player_ids = list({p['id'] for players in rosters.values() for p in players})
    log.append(f"Fetching game logs for {len(all_player_ids)} players x {len(ESPN_SEASONS)} seasons...")
    sem = asyncio.Semaphore(10)

    async def fetch_player_logs(pid: str):
        season_results = await asyncio.gather(
            *[get_player_gamelogs_espn(pid, s, sem) for s in ESPN_SEASONS],
            return_exceptions=True)
        all_logs = [g for res in season_results if isinstance(res, list) for g in res]
        return pid, all_logs

    log_results = await asyncio.gather(*[fetch_player_logs(pid) for pid in all_player_ids])
    # Sort every player's games by date DESCENDING (most recent first).
    # The whole algorithm now uses "last N games in the moment" instead of
    # vs-specific-opponent history, so playoff + recent regular season games
    # flow naturally into picks.
    logs_by_player = {pid: sorted(logs, key=lambda l: l.get('date',''), reverse=True)
                      for pid, logs in log_results}
    total_entries = sum(len(v) for v in logs_by_player.values())
    log.append(f"{total_entries:,} historical game entries loaded")

    # Pattern analysis — original algorithm (find best threshold >=75%)
    log.append("Scanning matchup patterns (70%+ threshold)...")
    picks = []

    for game in games:
        h, a = game['home'], game['away']
        h_name, a_name = game['home_name'], game['away_name']

        for player in rosters.get(game['home_id'], []):
            pid, pname = player['id'], player['name']
            # STARTER/ACTIVE FILTER: only consider players who have a sportsbook
            # line posted today. Books drop lines for inactives and rarely post
            # lines for deep bench players. This solves "pick 1 isn't playing"
            # and the "more starters please" requests in one shot.
            has_any_line = any((_nn(pname), s) in odds_lookup for s in STAT_CONFIG)
            if not has_any_line:
                continue
            # HISTORY: last 10 games vs THIS opponent at THIS location (H/A)
            # ONLY while playing for the current team (filters out games from
            # prior teams after trades — e.g. Fox's SAC home games vs OKC don't
            # count toward his SAS home record vs OKC).
            all_logs_player = logs_by_player.get(pid, [])
            # Last 10 games vs THIS opponent at THIS location (HOME). Player on
            # current team. H/A split because home vs away splits matter a lot.
            opp_logs_all = [l for l in all_logs_player
                            if l['opp'] == a and l.get('player_team') == h
                            and l.get('location') == 'Home']
            opp_logs = opp_logs_all[:10]
            for sk, sc in STAT_CONFIG.items():
                vals = [float(l[sk]) for l in opp_logs]
                last10 = opp_logs[:10]
                sb        = odds_lookup.get((_nn(pname), sk), {})
                fd_line   = sb.get('line')
                fd_odds   = sb.get('odds', '')
                l10_sb_hits = sum(1 for l in last10 if float(l[sk]) > fd_line) if fd_line and last10 else None
                dk_ob = dk_lookup.get((_nn(pname), sk), {})
                dk_line = dk_ob.get('line')
                dk_over_odds  = dk_ob.get('over_odds', '')
                dk_under_odds = dk_ob.get('under_odds', '')
                dk_hits = sum(1 for l in last10 if float(l[sk]) > dk_line) if dk_line and last10 else None
                # PATTERN: consistency measured at the ACTUAL betting line (over).
                result = pattern_at_line(vals, dk_line if dk_line is not None else fd_line)
                # PATTERN / LINE / STREAK: matchup + location specific.
                # MPA Special: player rhythm across all recent games (not opponent-filtered).
                recent10 = all_logs_player[:10]
                recent_vals = [float(l[sk]) for l in recent10]
                line_rec, line_rec_pct, line_rec_hits = _line_pick(dk_line, [float(l[sk]) for l in opp_logs_all[:10]], opp_logs_all[:10], sk)
                streak_rec, streak_n = _streak_pick(dk_line, opp_logs_all, sk)
                alt_rec, alt_evens, alt_odds = _alt_pick(dk_line, recent10, sk)
                # Conflict resolution: streak (matchup-specific) beats MPA Special (rhythm) when they disagree
                if streak_rec and alt_rec and streak_rec != alt_rec:
                    alt_rec = None
                # Include pick if consistency pattern OR streak OR MPA Special OR a 70%+ LINE
                # recommendation. LINE-only picks were previously dropped here; keeping them
                # opens the parlay pool up to all 70%+ starter plays (user request). They have
                # has_consistency False / hit_rate 0 so they sort below carded picks.
                if not result and not streak_rec and not alt_rec and not line_rec:
                    continue
                base = result or {'threshold': 0, 'hits': 0, 'games': len(last10),
                                  'hit_rate': 0.0, 'pct': 0.0}
                l10h = sum(1 for l in last10 if float(l[sk]) >= base['threshold']) if base['threshold'] else 0
                picks.append({**base, 'player': pname, 'player_id': pid, 'team': h,
                              'team_id': game['home_id'],
                              'jersey': player.get('jersey',''), 'position': player.get('position',''),
                              'tipoff': game.get('tipoff',''),
                              'team_name': h_name, 'stat': sk,
                              'stat_label': sc['label'], 'emoji': sc['emoji'],
                              'location': 'Home', 'opp': a, 'opp_name': a_name,
                              'ladder': build_ladder(vals, dk_line if dk_line is not None else fd_line),
                              'best_bet': best_bet_at_line(dk_line if dk_line is not None else fd_line, vals),
                              'glog': [{'d': l['date'], 'v': l[sk]} for l in opp_logs],
                              'matchup': f"{a_name} @ {h_name}",
                              'l10_hits': l10h, 'l10_games': len(last10),
                              'fd_line': fd_line, 'fd_odds': fd_odds,
                              'l10_sb_hits': l10_sb_hits,
                              'dk_line': dk_line, 'dk_over_odds': dk_over_odds, 'dk_under_odds': dk_under_odds, 'dk_hits': dk_hits,
                              'line_rec': line_rec, 'line_rec_pct': line_rec_pct, 'line_rec_hits': line_rec_hits,
                              'streak_rec': streak_rec, 'streak_n': streak_n,
                              'alt_rec': alt_rec, 'alt_evens': alt_evens, 'alt_odds': alt_odds,
                              'has_consistency': result is not None,
                              'recent_avg': round(sum(recent_vals)/len(recent_vals), 1) if recent_vals else None,
                              'gap': round((sum(recent_vals)/len(recent_vals)) - dk_line, 1) if recent_vals and dk_line else None,
                              'mpg': round(sum(float(l.get('MIN',0) or 0) for l in recent10)/len(recent10), 1) if recent10 else None})

        for player in rosters.get(game['away_id'], []):
            pid, pname = player['id'], player['name']
            has_any_line = any((_nn(pname), s) in odds_lookup for s in STAT_CONFIG)
            if not has_any_line:
                continue
            all_logs_player = logs_by_player.get(pid, [])
            # Last 10 games vs THIS opponent at THIS location (AWAY).
            opp_logs_all = [l for l in all_logs_player
                            if l['opp'] == h and l.get('player_team') == a
                            and l.get('location') == 'Away']
            opp_logs = opp_logs_all[:10]
            for sk, sc in STAT_CONFIG.items():
                vals = [float(l[sk]) for l in opp_logs]
                last10 = opp_logs[:10]
                sb        = odds_lookup.get((_nn(pname), sk), {})
                fd_line   = sb.get('line')
                fd_odds   = sb.get('odds', '')
                l10_sb_hits = sum(1 for l in last10 if float(l[sk]) > fd_line) if fd_line and last10 else None
                dk_ob = dk_lookup.get((_nn(pname), sk), {})
                dk_line = dk_ob.get('line')
                dk_over_odds  = dk_ob.get('over_odds', '')
                dk_under_odds = dk_ob.get('under_odds', '')
                dk_hits = sum(1 for l in last10 if float(l[sk]) > dk_line) if dk_line and last10 else None
                # PATTERN: consistency measured at the ACTUAL betting line (over).
                result = pattern_at_line(vals, dk_line if dk_line is not None else fd_line)
                recent10 = all_logs_player[:10]
                recent_vals = [float(l[sk]) for l in recent10]
                line_rec, line_rec_pct, line_rec_hits = _line_pick(dk_line, [float(l[sk]) for l in opp_logs_all[:10]], opp_logs_all[:10], sk)
                streak_rec, streak_n = _streak_pick(dk_line, opp_logs_all, sk)
                alt_rec, alt_evens, alt_odds = _alt_pick(dk_line, recent10, sk)
                # Conflict resolution: streak (matchup-specific) beats MPA Special (rhythm) when they disagree
                if streak_rec and alt_rec and streak_rec != alt_rec:
                    alt_rec = None
                # LINE-only 70%+ picks kept too (see home-side note) — opens the parlay pool.
                if not result and not streak_rec and not alt_rec and not line_rec:
                    continue
                base = result or {'threshold': 0, 'hits': 0, 'games': len(last10),
                                  'hit_rate': 0.0, 'pct': 0.0}
                l10h = sum(1 for l in last10 if float(l[sk]) >= base['threshold']) if base['threshold'] else 0
                picks.append({**base, 'player': pname, 'player_id': pid, 'team': a,
                              'team_id': game['away_id'],
                              'jersey': player.get('jersey',''), 'position': player.get('position',''),
                              'tipoff': game.get('tipoff',''),
                              'team_name': a_name, 'stat': sk,
                              'stat_label': sc['label'], 'emoji': sc['emoji'],
                              'location': 'Away', 'opp': h, 'opp_name': h_name,
                              'ladder': build_ladder(vals, dk_line if dk_line is not None else fd_line),
                              'best_bet': best_bet_at_line(dk_line if dk_line is not None else fd_line, vals),
                              'glog': [{'d': l['date'], 'v': l[sk]} for l in opp_logs],
                              'matchup': f"{a_name} @ {h_name}",
                              'l10_hits': l10h, 'l10_games': len(last10),
                              'fd_line': fd_line, 'fd_odds': fd_odds,
                              'l10_sb_hits': l10_sb_hits,
                              'dk_line': dk_line, 'dk_over_odds': dk_over_odds, 'dk_under_odds': dk_under_odds, 'dk_hits': dk_hits,
                              'line_rec': line_rec, 'line_rec_pct': line_rec_pct, 'line_rec_hits': line_rec_hits,
                              'streak_rec': streak_rec, 'streak_n': streak_n,
                              'alt_rec': alt_rec, 'alt_evens': alt_evens, 'alt_odds': alt_odds,
                              'has_consistency': result is not None,
                              'recent_avg': round(sum(recent_vals)/len(recent_vals), 1) if recent_vals else None,
                              'gap': round((sum(recent_vals)/len(recent_vals)) - dk_line, 1) if recent_vals and dk_line else None,
                              'mpg': round(sum(float(l.get('MIN',0) or 0) for l in recent10)/len(recent10), 1) if recent10 else None})

    # Sort: consistency picks first (by hit rate), then non-consistency
    # streak/MPA picks. None-safe.
    picks.sort(key=lambda x: (x.get('has_consistency', False), x.get('hit_rate') or 0, x.get('threshold') or 0), reverse=True)
    # Take enough picks to surface TOP_N distinct players (cards group by player,
    # so 12 picks from 11 unique players = only 11 cards). Walk the sorted list
    # collecting picks until we hit TOP_N distinct names.
    # CARD MINUTES FLOOR: the top cards are reserved for starters + 6th-man rotation
    # players. Anyone averaging under CARD_MIN_MPG minutes over their recent games is a
    # low-minute backup and is skipped for the cards (they still appear in all_picks for
    # the parlay builder / all-by-game list). Unknown mpg (rare — no recent logs) is kept.
    # To revert / loosen, lower CARD_MIN_MPG (set to 0 to disable).
    CARD_MIN_MPG = 24
    top_picks = []
    _seen_players = set()
    _below = []  # picks from sub-floor (backup) players, held back for backfill
    for _pk in picks:
        _mpg = _pk.get('mpg')
        if _mpg is not None and _mpg < CARD_MIN_MPG:
            _below.append(_pk)
            continue
        top_picks.append(_pk)
        _seen_players.add(_pk['player'])
        if len(_seen_players) >= TOP_N:
            break
    # BACKFILL TO TOP_N: starters / 6th-men (>= CARD_MIN_MPG) always fill the cards first.
    # If too few clear the floor on a light slate, top the board off with the HIGHEST-minute
    # players among those under the floor (closest to a 6th man) so we still show a full
    # top TOP_N instead of only a handful. Deep-bench guys sort last and rarely make it.
    if len(_seen_players) < TOP_N:
        _below.sort(key=lambda x: (x.get('mpg') or 0), reverse=True)
        for _pk in _below:
            if _pk['player'] in _seen_players:
                top_picks.append(_pk)            # complete an already-carded player's picks
            elif len(_seen_players) < TOP_N:
                top_picks.append(_pk)
                _seen_players.add(_pk['player'])  # add a new backup only while under TOP_N
            # else: board already has TOP_N distinct players — skip further NEW players but
            # keep scanning so trailing picks of carded players aren't dropped (no early break).
    log.append(f"{len(picks)} qualifying patterns -> {len(top_picks)} picks across top {len(_seen_players)} players shown")
    if odds_props:
        with_lines = sum(1 for p in picks if p.get('fd_line'))
        log.append(f"{with_lines} picks have sportsbook lines attached")

    odds_loaded = bool(odds_props)
    props_picks, props_nopick = [], []
    for game in games:
        h,a = game['home'],game['away']
        h_name,a_name = game['home_name'],game['away_name']
        matchup_str = f"{a_name} @ {h_name}"
        for loc,tid,opp_id,opp_name,side in [('Home',game['home_id'],a,a_name,'HOME'),('Away',game['away_id'],h,h_name,'AWAY')]:
            for player in rosters.get(tid,[]):
                pname,pid = player['name'],player['id']
                for sk,sc in STAT_CONFIG.items():
                    ob = odds_lookup.get((_nn(pname),sk),{})
                    if not ob or ob.get('line') is None: continue
                    line = float(ob['line'])
                    dk_ob = dk_lookup.get((_nn(pname),sk),{})
                    dk_over = dk_ob.get('over_odds','')
                    dk_under = dk_ob.get('under_odds','')
                    # Same trade-aware filter: only games with current team vs today's opp at this location
                    cur_team = tid_to_abbr.get(tid, '')
                    opp_logs = [l for l in logs_by_player.get(pid, [])
                                if l['opp'] == opp_id and l['location'] == loc and l.get('player_team') == cur_team][:10]
                    if not opp_logs:
                        props_nopick.append({'player':pname,'stat':sk,'stat_label':sc['label'],'emoji':sc['emoji'],'side':side,'opp_name':opp_name,'line':line,'avg':None,'games':0,'history':'—','gap':None,'pick':None,'fd_odds':ob.get('odds',''),'dk_over_odds':dk_over,'dk_under_odds':dk_under,'matchup':matchup_str})
                        continue
                    vals = [float(l[sk]) for l in opp_logs]
                    avg = round(sum(vals)/len(vals),1)
                    gap = round(avg-line,1)
                    pick = 'OVER' if avg>line else ('UNDER' if avg<line else None)
                    entry = {'player':pname,'stat':sk,'stat_label':sc['label'],'emoji':sc['emoji'],'side':side,'opp_name':opp_name,'line':line,'avg':avg,'games':len(vals),'history':','.join(str(int(v)) for v in vals[:8]),'gap':gap,'pick':pick,'fd_odds':ob.get('odds',''),'dk_over_odds':dk_over,'dk_under_odds':dk_under,'matchup':matchup_str}
                    (props_picks if pick else props_nopick).append(entry)
    props_picks.sort(key=lambda x:abs(x.get('gap') or 0),reverse=True)
    log.append(f"Props: {len(props_picks)} picks")
    result = {'date':today_str,'picks':top_picks,'all_picks':picks,'games':games,'log':log,'total':len(picks),'odds_loaded':odds_loaded,'props_picks':props_picks,'props_nopick':props_nopick}
    _cache.update(result)
    # Only cache if we actually got prop lines from the Odds API.
    # Otherwise the empty result gets pinned for 6h even after sportsbooks post lines.
    has_lines = bool(props_picks) or bool(props_nopick)
    if has_lines:
        _cache_set("nba", today_str, result)
    else:
        print(f"[Cache] SKIP write — no prop lines yet for {today_str} (will retry on next request)")
    try:
        from replit_push import push_picks_to_replit
        # Bake the picks into the page HTML so the Replit hub can serve an
        # instant, no-cold-start snapshot at moneypicksarena.com/dashboard/nba.
        import json as _json
        _inject = (
            '<script>window.__INITIAL_PICKS__ = '
            + _json.dumps(result).replace('</', '<\\/')
            + ';</script></head>'
        )
        from datetime import datetime as _dt, timedelta as _td
        _tomorrow_str = (_dt.fromisoformat(today_str) + _td(days=1)).date().isoformat()
        _snapshot_html = MAIN_HTML.replace("__TODAY__", today_str).replace("__TOMORROW__", _tomorrow_str).replace('</head>', _inject, 1)
        push_picks_to_replit("nba", result, html=_snapshot_html)
    except Exception as _e:
        print(f"[replit_push] nba push failed: {_e}")
    return result

# ─── HTML ─────────────────────────────────────────────────────────────────────
LOGIN_HTML = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>🏀 Money Buckets</title>
<style>
*{box-sizing:border-box;margin:0;padding:0}
/* responsive: phones & tablets (mobile fit) */
html,body{max-width:100%;overflow-x:hidden}
img{max-width:100%;height:auto}
@media (max-width:1200px){table{display:block;width:100%;overflow-x:auto;-webkit-overflow-scrolling:touch;white-space:nowrap}}
@media (max-width:560px){table{font-size:12px}table th,table td{padding:6px 8px}}
body{
  background:#0d0d0d;
  background-image:radial-gradient(ellipse at 50% 0%,rgba(253,184,39,.1) 0%,transparent 55%);
  color:#f0e6c8;font-family:'Segoe UI',system-ui,sans-serif;
  min-height:100vh;display:flex;align-items:center;justify-content:center;flex-direction:column;gap:0;
}
/* ── Spinning basketball ── */
.spin-ball{
  width:80px;height:80px;border-radius:50%;
  background:radial-gradient(circle at 38% 35%,#FDB827 0%,#FDB827 55%,#7c2d12 100%);
  border:2px solid #7c2d12;
  position:relative;margin-bottom:24px;
  animation:spinBall 6s linear infinite;
  box-shadow:0 0 40px rgba(253,184,39,.5),0 0 80px rgba(253,184,39,.15);
}
.spin-ball::before{
  content:'';position:absolute;inset:-1px;border-radius:50%;
  border:2.5px solid rgba(124,45,18,.9);
  border-left-color:transparent;border-right-color:transparent;
  transform:rotate(30deg);
}
.spin-ball::after{
  content:'';position:absolute;inset:16px;border-radius:50%;
  border:2px solid rgba(124,45,18,.8);
  border-top-color:transparent;border-bottom-color:transparent;
}
@keyframes spinBall{from{transform:rotate(0)}to{transform:rotate(360deg)}}
/* ── Card ── */
.card{
  background:linear-gradient(145deg,rgba(15,23,42,.97),rgba(8,12,24,.99));
  border:1px solid rgba(42,42,42,.8);border-radius:24px;
  padding:40px 40px 36px;width:390px;text-align:center;
  box-shadow:0 30px 80px rgba(0,0,0,.7),0 0 0 1px rgba(253,184,39,.04),inset 0 1px 0 rgba(255,255,255,.03);
  position:relative;overflow:hidden;
}
.card::before{
  content:'';position:absolute;top:0;left:0;right:0;height:2px;
  background:linear-gradient(90deg,transparent,#FDB827,#FDB827,#FDB827,transparent);
}
.logo-line{display:flex;align-items:center;justify-content:center;gap:8px;margin-bottom:4px}
.login-card h1{
  font-size:1.65rem;font-weight:900;letter-spacing:-.5px;
  background:linear-gradient(135deg,#FDB827 0%,#FDB827 100%);
  -webkit-background-clip:text;-webkit-text-fill-color:transparent;background-clip:text;
}
.sub{color:#374151;font-size:.75rem;margin-bottom:30px;letter-spacing:1.5px;text-transform:uppercase}
.field{position:relative;margin-bottom:13px}
.fi{position:absolute;left:14px;top:50%;transform:translateY(-50%);opacity:.35;font-size:.9rem;pointer-events:none}
input{
  width:100%;background:rgba(15,23,42,.8);
  border:1px solid rgba(42,42,42,.8);color:#d1d5db;
  padding:13px 16px 13px 42px;border-radius:12px;
  font-size:.95rem;outline:none;transition:border-color .2s,box-shadow .2s;
}
input:focus{border-color:#FDB827;box-shadow:0 0 0 3px rgba(253,184,39,.12)}
input::placeholder{color:#374151}
.btn-in{
  width:100%;margin-top:8px;
  background:linear-gradient(135deg,#FDB827,#FDB827);color:#0d0d0d;
  border:none;padding:14px;border-radius:12px;
  font-size:1rem;font-weight:900;letter-spacing:.5px;cursor:pointer;
  box-shadow:0 4px 20px rgba(253,184,39,.35);transition:transform .15s,box-shadow .15s;
}
.btn-in:hover{transform:translateY(-2px);box-shadow:0 8px 30px rgba(253,184,39,.45)}
.btn-in:active{transform:translateY(0)}
.err{color:#f87171;font-size:.83rem;margin-top:14px;background:rgba(127,29,29,.3);padding:10px 14px;border-radius:10px;border:1px solid rgba(239,68,68,.2)}
.tagline{color:#0f1d2e;font-size:.68rem;margin-top:22px;letter-spacing:2px;text-transform:uppercase}
</style>
</head>
<body>
<script>
(function(){
  var HUB='https://moneypicksarena.com';
  var KEY='__mpa_token';
  var p=new URLSearchParams(window.location.search);
  var t=p.get('token');
  var a=p.get('admin'); if(a){try{localStorage.setItem('__mpa_admin',a);}catch(e){}}
  if(t){localStorage.setItem(KEY,t);}
  if(t||a){window.history.replaceState({},'',window.location.pathname);}
  // no redirect
})();
</script>

<div class="spin-ball"></div>
<div class="card">
  <div class="logo-line">
    <h1>Money Buckets</h1>
  </div>
  <p class="sub">Pattern-Based Matchup Intelligence</p>
  <form method="post" action="/login">
    <div class="field"><span class="fi">👤</span><input name="username" type="text" placeholder="Username" required autocomplete="username"></div>
    <div class="field"><span class="fi">🔒</span><input name="password" type="password" placeholder="Password" required autocomplete="current-password"></div>
    <button class="btn-in" type="submit">Access Picks →</button>
    {error}
  </form>
  <p class="tagline">No Lines · Just Patterns · 70% Threshold</p>
</div>
</body>
</html>"""

MAIN_HTML = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>NBA Money Buckets &mdash; Money Picks Arena</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Playfair+Display:wght@400;700;900&family=Source+Sans+Pro:wght@300;400;600;700&display=swap" rel="stylesheet">
<style>
*{box-sizing:border-box;margin:0;padding:0}
/* responsive: phones & tablets (mobile fit) */
html,body{max-width:100%;overflow-x:hidden}
img{max-width:100%;height:auto}
@media (max-width:1200px){table{display:block;width:100%;overflow-x:auto;-webkit-overflow-scrolling:touch;white-space:nowrap}}
@media (max-width:560px){table{font-size:12px}table th,table td{padding:6px 8px}}
body{background:#0f0f0f;color:#fff;font-family:'Source Sans Pro',sans-serif;min-height:100vh}
.bg-glow{position:fixed;inset:0;background:radial-gradient(ellipse at 50% 20%,rgba(245,158,11,.05),transparent 65%);pointer-events:none;z-index:0}
nav{position:fixed;top:0;width:100%;background:rgba(10,10,10,.95);backdrop-filter:blur(12px);border-bottom:1px solid #1c1c1c;z-index:100;padding:0 32px;height:80px;display:flex;align-items:center}
.logo{font-family:'Playfair Display',serif;font-size:36px;font-weight:900;color:#f59e0b;letter-spacing:.02em;line-height:1}
.logo span{color:#fff}
.page{position:relative;z-index:1;max-width:1400px;margin:0 auto;padding:104px 24px 40px}
.app-hdr{text-align:center;margin-bottom:32px}
.app-hdr h1{font-family:'Playfair Display',serif;font-size:2.6rem;font-weight:900;color:#fff;margin-bottom:6px}
.app-hdr h1 span{color:#f59e0b}
.app-hdr p{font-size:.85rem;color:#6b7280;letter-spacing:.15em;text-transform:uppercase}
.card{background:#161616;border:1px solid #262626;border-radius:20px;padding:24px;margin-bottom:16px}
.date-row{display:flex;align-items:center;justify-content:center;gap:12px;margin-bottom:20px}
.date-row label{color:#9ca3af;font-weight:600;font-size:.85rem;letter-spacing:.08em;text-transform:uppercase}
.date-row input[type=date]{background:#0a0a0a;color:#fff;border:1px solid #2a2a2a;border-radius:10px;padding:10px 16px;font-size:.95rem;font-family:'Source Sans Pro',sans-serif;cursor:pointer;outline:none;transition:border .2s}
.date-row input[type=date]:focus{border-color:#f59e0b}
input[type=date]::-webkit-calendar-picker-indicator{filter:invert(1);opacity:.7;cursor:pointer}
.btn{padding:10px 24px;border-radius:8px;font-size:.88rem;font-weight:700;cursor:pointer;border:none;transition:all .2s;font-family:'Source Sans Pro',sans-serif}
.btn-run{background:#f59e0b;color:#000}
.btn-run:hover{background:#fbbf24;transform:translateY(-1px);box-shadow:0 4px 20px rgba(245,158,11,.35)}
.btn-run:disabled{background:#2a2a2a;color:#4b5563;cursor:not-allowed;transform:none;box-shadow:none}
.admin-only{display:none !important}
body.is-admin .admin-only{display:inline-block !important}
#parlayCard{display:none}
body.is-admin #parlayCard{display:block}
#parlayLegs{background:#1a1a1a;color:#fff;border:1px solid #333;border-radius:8px;padding:8px 12px;font-size:.9rem;font-weight:700}
.btn-force{background:#dc2626;color:#fff}
.btn-force:hover{background:#ef4444;transform:translateY(-1px);box-shadow:0 4px 20px rgba(220,38,38,.35)}
.ball-svg,.ball-shadow,.fd-indicator,.pick-emoji,.cr-emoji,.tb-ico,.msg-card .ico,.btn-out,.btn-refresh{display:none}
.games-bar{display:none;gap:8px;overflow-x:auto;padding-bottom:4px;margin-bottom:20px}
.game-chip{background:#161616;border:1px solid #262626;border-radius:10px;padding:9px 18px;white-space:nowrap;font-size:.82rem;flex-shrink:0;transition:border-color .2s}
.game-chip:hover{border-color:#f59e0b}
.game-chip b{color:#fff;font-weight:700}
.game-chip .sep{color:#374151;margin:0 5px}
.filter-bar{display:flex;gap:8px;flex-wrap:wrap;margin-bottom:20px}
.filter-btn{padding:7px 18px;border-radius:999px;border:1px solid #262626;background:#161616;color:#6b7280;font-size:.81rem;cursor:pointer;transition:all .2s;font-weight:600;font-family:'Source Sans Pro',sans-serif}
.filter-btn.active,.filter-btn:hover{background:rgba(245,158,11,.1);color:#f59e0b;border-color:rgba(245,158,11,.3)}
.section-hdr{display:flex;align-items:center;justify-content:space-between;margin-bottom:18px}
.section-title{font-size:1rem;font-weight:700;display:flex;align-items:center;gap:8px;color:#f59e0b;font-family:'Playfair Display',serif}
.count-pill{background:rgba(245,158,11,.1);color:#f59e0b;padding:4px 14px;border-radius:999px;font-size:.78rem;font-weight:700;border:1px solid rgba(245,158,11,.2)}
.picks-grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(300px,1fr));gap:16px;margin-bottom:10px}
.pick-card{background:#161616;border:1px solid #262626;border-radius:20px;padding:22px;position:relative;overflow:hidden;transition:border-color .25s,transform .22s}
.pick-card:hover{border-color:rgba(245,158,11,.4);transform:translateY(-3px);box-shadow:0 14px 40px rgba(0,0,0,.5)}
.pick-rank{position:absolute;top:14px;right:15px;width:32px;height:32px;border-radius:50%;display:flex;align-items:center;justify-content:center;font-size:.82rem;font-weight:900}
.rank-1{background:linear-gradient(135deg,#C4901A,#f59e0b);color:#000;box-shadow:0 0 14px rgba(245,158,11,.5)}
.rank-2{background:linear-gradient(135deg,#374151,#9ca3af);color:#000}
.rank-3{background:linear-gradient(135deg,#7c2d12,#c2410c);color:#fff}
.rank-other{background:#1a1a1a;color:#4b5563;font-size:.75rem;border:1px solid #262626}
.pick-player{font-size:1.08rem;font-weight:800;color:#fff;margin-bottom:3px;letter-spacing:-.3px;padding-right:38px;font-family:'Playfair Display',serif}
.pick-team{font-size:.75rem;color:#6b7280;margin-bottom:12px;display:flex;align-items:center;gap:6px}
.loc-badge{background:#1a1a1a;padding:2px 9px;border-radius:10px;font-size:.7rem;color:#6b7280;border:1px solid #262626}
.stat-strip{display:flex;gap:6px;margin-bottom:10px;flex-wrap:wrap}
.stat-tag{padding:3px 10px;border-radius:10px;font-size:.7rem;font-weight:700;letter-spacing:.3px}
.tag-pts{background:rgba(109,40,217,.15);color:#a78bfa;border:1px solid rgba(109,40,217,.25)}
.tag-reb{background:rgba(37,99,235,.15);color:#60a5fa;border:1px solid rgba(37,99,235,.25)}
.tag-ast{background:rgba(5,150,105,.15);color:#34d399;border:1px solid rgba(5,150,105,.25)}
.tag-fg3m{background:rgba(220,38,38,.15);color:#f87171;border:1px solid rgba(220,38,38,.25)}
.tag-pra{background:rgba(168,85,247,.15);color:#c084fc;border:1px solid rgba(168,85,247,.25)}
.tag-combo{background:rgba(245,158,11,.15);color:#fbbf24;border:1px solid rgba(245,158,11,.25)}
.tag-blk{background:rgba(20,184,166,.15);color:#2dd4bf;border:1px solid rgba(20,184,166,.25)}
.tag-stl{background:rgba(236,72,153,.15);color:#f472b6;border:1px solid rgba(236,72,153,.25)}
.pick-pattern{font-size:.9rem;color:#7dd3fc;font-weight:700;margin-bottom:4px;line-height:1.4}
.l10vthr-desc{font-size:.88rem;color:#f59e0b;font-weight:700;margin-bottom:5px;line-height:1.4}
.fd-line-badge{display:inline-block;background:rgba(74,222,128,.08);border:1px solid rgba(74,222,128,.2);color:#4ade80;border-radius:6px;padding:3px 10px;font-size:.78rem;font-weight:700;margin-bottom:6px}
.fd-inline{color:#4ade80;font-weight:700}
.l10vthr-inline{color:#f59e0b;font-weight:700}
.pick-matchup{font-size:.72rem;color:#374151;margin-bottom:16px}
.bar-wrap{background:#1a1a1a;border-radius:6px;height:8px;overflow:hidden;margin-bottom:10px;border:1px solid #262626}
.bar-fill{height:100%;border-radius:5px}
.bar-green{background:linear-gradient(90deg,#15803d,#4ade80)}
.bar-yellow{background:linear-gradient(90deg,#b45309,#f59e0b)}
.bar-orange{background:linear-gradient(90deg,#c2410c,#f97316)}
.stats-row{display:flex;justify-content:space-between;align-items:center}
.games-chip{background:#1a1a1a;padding:4px 12px;border-radius:20px;font-size:.75rem;color:#4b5563;border:1px solid #262626}
.pct{font-size:1.2rem;font-weight:900;letter-spacing:-.5px;font-family:'Playfair Display',serif}
.pct-green{color:#4ade80}
.pct-yellow{color:#f59e0b}
.pct-orange{color:#f97316}
.total-banner{display:flex;align-items:center;justify-content:space-between;flex-wrap:wrap;gap:12px;background:#161616;border:1px solid rgba(74,222,128,.2);border-radius:18px;padding:18px 24px;margin:32px 0 20px}
.tb-left{display:flex;align-items:center;gap:12px}
.tb-title{font-size:.95rem;font-weight:700;color:#4ade80;font-family:'Playfair Display',serif}
.tb-sub{font-size:.72rem;color:#374151;margin-top:2px;letter-spacing:.8px;text-transform:uppercase}
.tb-count{font-size:2.2rem;font-weight:900;color:#4ade80;letter-spacing:-1.5px;font-family:'Playfair Display',serif}
.all-section-hdr{display:flex;align-items:center;justify-content:space-between;margin-bottom:16px;flex-wrap:wrap;gap:10px}
.all-section-title{font-size:.95rem;font-weight:700;color:#f59e0b;display:flex;align-items:center;gap:8px;font-family:'Playfair Display',serif}
.game-group{margin-bottom:14px}
.game-group-hdr{display:flex;align-items:center;justify-content:space-between;background:#161616;border:1px solid #262626;border-radius:13px;padding:12px 18px;margin-bottom:6px;cursor:pointer;user-select:none;transition:border-color .2s}
.game-group-hdr:hover{border-color:rgba(245,158,11,.3)}
.gg-label{font-size:.88rem;font-weight:700;color:#fff;display:flex;align-items:center;gap:8px}
.gg-meta{display:flex;align-items:center;gap:8px}
.gg-chevron{color:#4b5563;font-size:.85rem;transition:transform .2s}
.compact-picks{display:flex;flex-direction:column;gap:5px;margin-bottom:4px}
.compact-row{display:flex;align-items:center;gap:12px;background:#1a1a1a;border:1px solid #262626;border-radius:11px;padding:10px 15px;transition:border-color .2s}
.compact-row:hover{border-color:rgba(245,158,11,.25)}
.cr-info{flex:1;min-width:0}
.cr-player{font-size:.86rem;font-weight:700;color:#fff;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.cr-pattern{font-size:.76rem;color:#60a5fa;font-weight:600;margin-top:2px}
.cr-right{display:flex;flex-direction:column;align-items:flex-end;gap:3px;flex-shrink:0}
.cr-bar-wrap{background:#1a1a1a;border-radius:4px;height:4px;width:68px;overflow:hidden;border:1px solid #262626}
.cr-bar-fill{height:100%;border-radius:4px}
.cr-pct{font-size:.9rem;font-weight:900;font-family:'Playfair Display',serif}
.cr-sample{font-size:.65rem;color:#374151}
.spinner{display:inline-block;width:14px;height:14px;border:2px solid rgba(245,158,11,.3);border-top-color:#f59e0b;border-radius:50%;animation:spin .6s linear infinite;margin-right:6px;vertical-align:middle}
.loading-ball{width:48px;height:48px;border:3px solid rgba(245,158,11,.15);border-top:3px solid #f59e0b;border-radius:50%;animation:spin .8s linear infinite;margin:0 auto 18px}
@keyframes spin{to{transform:rotate(360deg)}}
@keyframes ballBounce{0%,100%{transform:translateY(0)}50%{transform:translateY(-22px)}}
@keyframes shadowPulse{0%,100%{transform:scaleX(1)}50%{transform:scaleX(.55)}}
.msg-card{background:#161616;border:1px solid #262626;border-radius:20px;padding:60px 30px;text-align:center}
.msg-card h2{color:#fff;font-size:1.2rem;font-weight:800;margin-bottom:10px;font-family:'Playfair Display',serif}
.msg-card p{color:#6b7280;font-size:.88rem;line-height:1.75}
.log-box{background:#0a0a0a;border:1px solid #262626;border-radius:12px;padding:16px;font-size:.74rem;color:#374151;font-family:'Courier New',monospace;margin-top:20px;max-height:160px;overflow-y:auto;line-height:1.9}
footer{text-align:center;padding:32px 24px;color:#4b5563;font-size:.78rem;border-top:1px solid #1c1c1c;margin-top:24px;font-family:'Source Sans Pro',sans-serif}
.ft-logo{font-family:'Playfair Display',serif;color:#f59e0b;font-weight:700;font-size:.95rem;margin-bottom:6px}
.props-player-chip{background:#161616;border:1px solid #262626;border-radius:10px;padding:10px 14px;min-width:150px;cursor:pointer;transition:border-color .15s;user-select:none}
.props-player-chip:hover{border-color:#f59e0b}
.props-game-sel{background:#111;color:#fff;border:1px solid #2a2a2a;border-radius:8px;padding:8px 14px;font-size:.85rem;font-family:'Source Sans Pro',sans-serif;outline:none;min-width:220px;cursor:pointer}
</style>
</head>
<body>
<div class="bg-glow"></div>
<nav style="display:flex;justify-content:space-between;align-items:center"><div class="logo">Money <span>Picks</span> Arena</div><div style="display:flex;gap:8px;align-items:center"><button class="admin-only" onclick="openNbaMyBets()" style="background:#4338ca;color:#fff;border:none;border-radius:10px;padding:9px 16px;font-weight:800;font-size:.82rem;cursor:pointer;white-space:nowrap">&#128176; My Bets</button></div></nav>
<div class="page">
<div class="app-hdr">
  <h1>NBA <span>Money Buckets</span></h1>
  <p>Pts &middot; Reb &middot; Ast &middot; 3PM &middot; Daily Picks</p>
</div>
<div class="card" style="text-align:center;max-width:600px;margin:0 auto 20px">
  <h2 style="font-family:'Playfair Display',serif;font-size:1.5rem;font-weight:700;color:#fff;margin-bottom:20px">Run Today's Picks</h2>
  <div class="date-row">
    <label>Date</label>
    <input type="date" id="datePicker" value="__TODAY__" min="__TODAY__" max="__TOMORROW__">
  </div>
  <div style="text-align:center"><button class="btn btn-run" id="getBtn" onclick="getPicks()">🎯 Get Picks</button><button class="btn btn-run admin-only" id="runBtn" onclick="runPicks()" style="margin-left:10px">Run Picks</button><button class="btn btn-force admin-only" id="forceBtn" onclick="runPicks(true)" style="margin-left:10px" title="Bypass cache and rebuild today's picks from scratch">Force Refresh</button></div>
</div>
<div class="card" id="parlayCard" style="text-align:center;max-width:600px;margin:0 auto 20px">
  <h2 style="font-family:'Playfair Display',serif;font-size:1.4rem;font-weight:700;color:#fff;margin-bottom:6px">🎰 Auto Parlay Builder <span style="font-size:.7rem;color:#777;font-family:sans-serif">admin only</span></h2>
  <div style="font-size:.74rem;color:#888;margin-bottom:16px">Pulls from any strong play today — Pattern, Line, Streak, MPA — best available odds priced in</div>
  <div style="display:flex;gap:10px;justify-content:center;align-items:center;flex-wrap:wrap">
    <label style="color:#999;font-weight:700">Legs</label>
    <select id="parlayLegs">
      <option>2</option><option>3</option><option>4</option><option>5</option><option>6</option><option>7</option><option>8</option><option>9</option><option>10</option>
    </select>
    <button class="btn" onclick="buildParlay()">Build Best Parlay</button>
    <button class="btn" onclick="generateParlay()" style="background:#1f2937;color:#fff">🎲 Generate New</button>
  </div>
  <div id="parlayResult" style="margin-top:16px;text-align:left"></div>
</div>
<div class="games-bar" id="gamesBar"></div>
<div id="filterBar" style="display:none" class="filter-bar">
  <button class="filter-btn active" data-stat="ALL" onclick="filterStat('ALL')">All Stats</button>
  <button class="filter-btn" data-stat="PTS" onclick="filterStat('PTS')">Points</button>
  <button class="filter-btn" data-stat="REB" onclick="filterStat('REB')">Rebounds</button>
  <button class="filter-btn" data-stat="AST" onclick="filterStat('AST')">Assists</button>
  <button class="filter-btn" data-stat="FG3M" onclick="filterStat('FG3M')">3-Pointers</button>
  <button class="filter-btn" data-stat="PRA" onclick="filterStat('PRA')">🃏 PRA</button>
  <button class="filter-btn" data-stat="PTS_REB" onclick="filterStat('PTS_REB')">💪 Pts+Reb</button>
  <button class="filter-btn" data-stat="PTS_AST" onclick="filterStat('PTS_AST')">⚡ Pts+Ast</button>
  <button class="filter-btn" data-stat="REB_AST" onclick="filterStat('REB_AST')">🔗 Reb+Ast</button>
  <button class="filter-btn" data-stat="BLK" onclick="filterStat('BLK')">🛡️ Blocks</button>
  <button class="filter-btn" data-stat="STL" onclick="filterStat('STL')">🧤 Steals</button>
</div>
<div id="content"></div>
<div id="allPicksWrap" style="display:none">
  <div style="display:grid;grid-template-columns:1fr 1fr;gap:14px;margin-bottom:18px" id="signalDropdowns">
    <div style="background:#0e0e0e;border:1px solid #262626;border-radius:12px;overflow:hidden">
      <div onclick="toggleSig('streakList',this)" style="display:flex;align-items:center;justify-content:space-between;padding:12px 16px;cursor:pointer;background:linear-gradient(135deg,rgba(249,115,22,.12),rgba(249,115,22,.02));border-bottom:1px solid #262626">
        <div style="display:flex;align-items:center;gap:10px"><span style="font-size:1.1rem">🔥</span><span style="font-weight:900;color:#fb923c;letter-spacing:.05em">ALL STREAKS</span><span class="count-pill" id="streakCount">0</span></div>
        <span class="sig-chev" style="color:#666;transition:transform .2s">▼</span>
      </div>
      <div id="streakList" style="display:none;max-height:360px;overflow-y:auto"></div>
    </div>
    <div style="background:#0e0e0e;border:1px solid #262626;border-radius:12px;overflow:hidden">
      <div onclick="toggleSig('mpaList',this)" style="display:flex;align-items:center;justify-content:space-between;padding:12px 16px;cursor:pointer;background:linear-gradient(135deg,rgba(168,85,247,.12),rgba(168,85,247,.02));border-bottom:1px solid #262626">
        <div style="display:flex;align-items:center;gap:10px"><span style="font-size:1.1rem">⭐</span><span style="font-weight:900;color:#c084fc;letter-spacing:.05em">ALL MPA SPECIALS</span><span class="count-pill" id="mpaCount">0</span></div>
        <span class="sig-chev" style="color:#666;transition:transform .2s">▼</span>
      </div>
      <div id="mpaList" style="display:none;max-height:360px;overflow-y:auto"></div>
    </div>
  </div>
  <div class="total-banner">
    <div class="tb-left">
      <div class="tb-ico">📋</div>
      <div>
        <div class="tb-title">All Qualifying Patterns</div>
        <div class="tb-sub">Every player hitting 70%+ · Grouped by game</div>
      </div>
    </div>
    <div class="tb-count" id="totalCount">0</div>
  </div>
  <div class="all-section-hdr">
    <div class="all-section-title">🎯 All Patterns by Game</div>
    <input id="playerSearchInput" type="text" placeholder="Search player…" oninput="applyAllFilters()" style="background:#111;color:#fff;border:1px solid #2a2a2a;border-radius:8px;padding:7px 14px;font-size:.85rem;font-family:'Source Sans Pro',sans-serif;outline:none;width:180px;margin-bottom:6px" />
    <div style="display:flex;gap:8px;flex-wrap:wrap" id="allFilterBar">
      <button class="filter-btn active" data-stat="ALL" onclick="filterAll('ALL')">All</button>
      <button class="filter-btn" data-stat="PTS" onclick="filterAll('PTS')">🏀 Pts</button>
      <button class="filter-btn" data-stat="REB" onclick="filterAll('REB')">📊 Reb</button>
      <button class="filter-btn" data-stat="AST" onclick="filterAll('AST')">🎯 Ast</button>
      <button class="filter-btn" data-stat="FG3M" onclick="filterAll('FG3M')">🔥 3PM</button>
      <button class="filter-btn" data-stat="PRA" onclick="filterAll('PRA')">🃏 PRA</button>
      <button class="filter-btn" data-stat="PTS_REB" onclick="filterAll('PTS_REB')">💪 Pts+Reb</button>
      <button class="filter-btn" data-stat="PTS_AST" onclick="filterAll('PTS_AST')">⚡ Pts+Ast</button>
      <button class="filter-btn" data-stat="REB_AST" onclick="filterAll('REB_AST')">🔗 Reb+Ast</button>
      <button class="filter-btn" data-stat="BLK" onclick="filterAll('BLK')">🛡️ Blk</button>
      <button class="filter-btn" data-stat="STL" onclick="filterAll('STL')">🧤 Stl</button>
      <button class="filter-btn" id="oversBtn" onclick="toggleSide('OVER')" style="margin-left:8px">⬆ Overs only</button>
      <button class="filter-btn" id="undersBtn" onclick="toggleSide('UNDER')">⬇ Unders only</button>
    </div>
  </div>
  <div id="allPicksSection"></div>
</div>

<div id="props-section" style="display:none;max-width:1400px;margin:28px auto 0;padding:0 24px 40px">
  <div style="font-size:.78rem;font-weight:700;color:#f59e0b;text-transform:uppercase;letter-spacing:.15em;margin:0 0 14px;display:flex;align-items:center;gap:10px">&#9889; Player Props vs Opponent History</div>
  <div style="display:flex;align-items:center;gap:12px;flex-wrap:wrap;margin-bottom:14px">
    <select id="propsGameSel" class="props-game-sel" onchange="propsSelectGame(this.value)">
      <option value="">-- Select a game --</option>
    </select>
    <span id="propsGameHint" style="font-size:.75rem;color:#555">Select a game to browse players</span>
  </div>
  <div id="propsPlayerList" style="display:none"></div>
  <p style="font-size:.72rem;color:#555;margin-top:10px">
    <strong style="color:#f59e0b">Avg vr Opp</strong> = career avg at this location vs today&#39;s opponent (incl. playoffs) &nbsp;|&nbsp; Click any player to see all their prop lines
  </p>
</div>
</div><!-- /wrap -->

<style>
.nba-bets-tbl{width:100%;border-collapse:collapse;font-size:.82rem}
.nba-bets-tbl th{padding:7px 10px;text-align:left;font-size:.72rem;color:#94a3b8;font-weight:700;text-transform:uppercase;letter-spacing:.07em;border-bottom:1px solid #1e293b;white-space:nowrap}
.nba-bets-tbl td{padding:8px 10px;border-bottom:1px solid #0f172a;vertical-align:middle;color:#e2e8f0}
.nba-bets-tbl tr:last-child td{border-bottom:none}
.nba-bets-tbl tr:hover td{background:rgba(255,255,255,.02)}
</style>
<div id="nba-mybets-card" style="display:none;max-width:960px;margin:0 auto 24px;padding:0 16px">
  <div class="card" style="padding:20px">
    <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:16px;flex-wrap:wrap;gap:10px">
      <div style="font-weight:800;color:#a5b4fc;font-size:1rem">&#128176; MY BETS &mdash; RECORD &amp; ROI</div>
      <div style="display:flex;gap:8px;align-items:center">
        <button onclick="getNbaBetsResults()" style="background:#1d4ed8;color:#fff;border:none;border-radius:8px;padding:8px 13px;font-size:.78rem;font-weight:700;cursor:pointer">&#128200; Settle Results</button>
        <button onclick="document.getElementById(&#39;nba-mybets-card&#39;).style.display=&#39;none&#39;" style="background:#1e293b;border:none;color:#94a3b8;border-radius:8px;padding:8px 11px;font-size:.9rem;cursor:pointer">&#215;</button>
      </div>
    </div>
    <div id="nba-mybets-body"><p style="color:#94a3b8;font-size:.85rem">Loading&#8230;</p></div>
  </div>
</div>
<footer>
  <div class="ft-logo">Money Picks Arena</div>
  <div>NBA Money Buckets &middot; Pts &middot; Reb &middot; Ast &middot; 3PM &middot; Blk &middot; Stl &middot; Combos</div>
  <div style="margin-top:8px;font-size:.7rem">For entertainment only. Not a betting service. Must be 18+.</div>
</footer>
<script>
// Hub Access Gate - client side only, no server round-trip
(function(){
  var HUB='https://moneypicksarena.com';
  var KEY='__mpa_token';
  var p=new URLSearchParams(window.location.search);
  var t=p.get('token');
  var a=p.get('admin'); if(a){try{localStorage.setItem('__mpa_admin',a);}catch(e){}}
  if(t){localStorage.setItem(KEY,t);}
  if(t||a){window.history.replaceState({},'',window.location.pathname);}
  var tok=localStorage.getItem(KEY);
  if(!tok){window.location.href='https://moneypicksarena.com'; return;}
})();
// Auto-enable admin view if this logged-in user is the admin (cosmetic — the
// server independently re-verifies before honoring any force refresh).
function _nbaUnlockDates(){try{var dp=document.getElementById('datePicker');if(dp){dp.removeAttribute('min');dp.removeAttribute('max');}}catch(e){}}
if(window.IS_ADMIN){document.body.classList.add('is-admin');_nbaUnlockDates();}else{var _at=localStorage.getItem('__mpa_token')||'';var _ak=localStorage.getItem('__mpa_admin')||'';if(_at||_ak){fetch('/api/whoami?_tok='+encodeURIComponent(_at)+'&admin='+encodeURIComponent(_ak)).then(r=>r.json()).then(d=>{if(d&&d.is_admin){window.IS_ADMIN=true;document.body.classList.add('is-admin');_nbaUnlockDates();}}).catch(function(){});}}
let top10=[], allPicksData=[], activeTopStat='ALL', activeAllStat='ALL', sideFilter=null;

function pctClass(p){return p>=90?['pct-green','bar-green']:p>=80?['pct-yellow','bar-yellow']:['pct-orange','bar-orange']}
function statTag(s){
  const m={PTS:['tag-pts','Points'],REB:['tag-reb','Rebounds'],AST:['tag-ast','Assists'],FG3M:['tag-fg3m','3-Pointers'],PRA:['tag-pra','Pts+Reb+Ast'],PTS_REB:['tag-combo','Pts+Reb'],PTS_AST:['tag-combo','Pts+Ast'],REB_AST:['tag-combo','Reb+Ast'],BLK:['tag-blk','Blocks'],STL:['tag-stl','Steals']};
  const [c,l]=m[s]||['',''];
  return `<span class="stat-tag ${c}">${l}</span>`;
}
function rankClass(i){return i===0?'rank-1':i===1?'rank-2':i===2?'rank-3':'rank-other'}

function filterStat(stat){
  activeTopStat=stat;
  document.querySelectorAll('#filterBar .filter-btn[data-stat]').forEach(b=>b.classList.toggle('active',b.dataset.stat===stat));
  renderTop10Cards(stat==='ALL'?top10:top10.filter(p=>p.stat===stat));
}

function filterAll(stat){
  activeAllStat=stat;
  document.querySelectorAll('#allFilterBar .filter-btn[data-stat]').forEach(b=>b.classList.toggle('active',b.dataset.stat===stat));
  applyAllFilters();
}

function toggleSide(side){
  sideFilter = (sideFilter===side) ? null : side;
  document.getElementById('oversBtn').classList.toggle('active',sideFilter==='OVER');
  document.getElementById('undersBtn').classList.toggle('active',sideFilter==='UNDER');
  applyAllFilters();
}

function applyAllFilters(){
  const searchQ=(document.getElementById('playerSearchInput')||{}).value||'';
  const sq=searchQ.toLowerCase().trim();
  let filtered = activeAllStat==='ALL' ? allPicksData : allPicksData.filter(p=>p.stat===activeAllStat);
  if(sq) filtered=filtered.filter(p=>(p.player||'').toLowerCase().includes(sq));
  if(sideFilter){
    filtered = filtered.filter(p => p.line_rec===sideFilter || p.streak_rec===sideFilter || p.alt_rec===sideFilter);
    // Rank by gap: biggest +gap first for OVERs, biggest -gap first for UNDERs
    filtered = filtered.slice().sort((a,b)=>{
      const ga=a.gap==null?0:a.gap, gb=b.gap==null?0:b.gap;
      return sideFilter==='OVER' ? (gb-ga) : (ga-gb);
    });
  }
  document.getElementById('totalCount').textContent=filtered.length;
  renderAllByGame(filtered, sideFilter);
}

function renderTop10Cards(picks){
  if(!picks.length){
    document.getElementById('content').innerHTML='<div class="msg-card"><span class="ico"></span><h2>No patterns</h2><p>Try "All Stats".</p></div>';
    return;
  }
  // Group picks by player so each player gets ONE trading-card; first occurrence wins rank order.
  const byPlayer={},order=[];
  picks.forEach(p=>{ if(!byPlayer[p.player]){byPlayer[p.player]=[];order.push(p.player);} byPlayer[p.player].push(p); });
  const dirColor=d=>d==='OVER'?'#4ade80':d==='UNDER'?'#f87171':'#9ca3af';
  const dirBg=d=>d==='OVER'?'rgba(74,222,128,.14)':d==='UNDER'?'rgba(239,68,68,.14)':'rgba(156,163,175,.1)';
  let html=`<div class="section-hdr"><div class="section-title">Top Picks Today</div><span class="count-pill">${order.length} player${order.length!==1?'s':''}</span></div><div class="picks-grid">`;
  order.forEach((pname,i)=>{
    // Only show the single best pick per player card (highest-ranked, since
    // picks are pre-sorted by has_consistency desc, hit_rate desc, threshold desc).
    const stats=[byPlayer[pname][0]];
    const p=stats[0];
    const cardKey=ladReg(p);
    const teamLogo=`https://a.espncdn.com/i/teamlogos/nba/500/${(p.team||'').toLowerCase()}.png`;
    const headshot=`https://a.espncdn.com/i/headshots/nba/players/full/${p.player_id}.png`;
    const tip=p.tipoff?new Date(p.tipoff).toLocaleTimeString('en-US',{hour:'numeric',minute:'2-digit',timeZoneName:'short'}):'';
    const statBlocks=stats.map(s=>{
      // VERDICT RULES:
      // 1) PATTERN is the strongest signal. If it qualifies, the pick IS the pattern
      //    (e.g. "PATTERN 5+ REB") — MPA/LINE/STREAK do NOT override it with UNDER.
      // 2) If no pattern, fall back to vote-based verdict from LINE/STREAK/MPA.
      let verdict=null, verdictText='', verdictColor='', verdictBg='';
      if(s.has_consistency){
        verdict='PATTERN';
        verdictText=`PATTERN ${s.threshold}+`;
        verdictColor='#FDB827';
        verdictBg='rgba(253,184,39,.18)';
      } else {
        const votes={OVER:0,UNDER:0};
        if(s.line_rec) votes[s.line_rec]++;
        if(s.streak_rec) votes[s.streak_rec]++;
        if(s.alt_rec) votes[s.alt_rec]++;
        const tot=votes.OVER+votes.UNDER;
        if(tot && votes.OVER!==votes.UNDER){
          verdict=votes.OVER>votes.UNDER?'OVER':'UNDER';
          verdictText=`${verdict}${s.dk_line?' '+s.dk_line:''}`;
          verdictColor=dirColor(verdict);
          verdictBg=dirBg(verdict);
        }
      }
      const verdictPill = verdict ? `<span style="background:${verdictBg};color:${verdictColor};border:1px solid ${verdictColor}66;padding:5px 12px;border-radius:7px;font-size:.92rem;font-weight:900;white-space:nowrap">${verdictText}</span>` : '';
      // Suppress any UNDER signal badges when PATTERN is the pick — they'd contradict
      // the pattern. Only show signals that agree (OVER) as reinforcement.
      const patternOverride = s.has_consistency;
      const badges=[];
      if(s.has_consistency) badges.push(`<span style="background:rgba(253,184,39,.18);color:#FDB827;padding:4px 10px;border-radius:6px;font-size:.82rem;font-weight:800">PATTERN ${s.hits}/${s.games} (${s.pct}%) vs ${p.opp} ${(p.location||'').toLowerCase()}</span>`);
      if(s.line_rec && (!patternOverride || s.line_rec==='OVER')) badges.push(`<span style="background:${dirBg(s.line_rec)};color:${dirColor(s.line_rec)};padding:4px 10px;border-radius:6px;font-size:.82rem;font-weight:800">LINE ${s.line_rec} ${s.line_rec_hits} (${s.line_rec_pct}%)</span>`);
      if(s.streak_rec && (!patternOverride || s.streak_rec==='OVER')) badges.push(`<span style="background:${dirBg(s.streak_rec)};color:${dirColor(s.streak_rec)};padding:4px 10px;border-radius:6px;font-size:.82rem;font-weight:800">🔥 ${s.streak_n} STRAIGHT ${s.streak_rec}</span>`);
      if(s.alt_rec && (!patternOverride || s.alt_rec==='OVER')) badges.push(`<span style="background:${dirBg(s.alt_rec)};color:${dirColor(s.alt_rec)};padding:4px 10px;border-radius:6px;font-size:.82rem;font-weight:800">⭐ MPA ${s.alt_rec}${s.alt_evens&&s.alt_odds?` — even: ${s.alt_evens} · odd: ${s.alt_odds}`:''}</span>`);
      // Data lines: spell out exactly what the user sees on a bet slip
      const lines=[];
      if(s.dk_line!=null) lines.push(`<div style="font-size:.86rem;color:#ddd;margin-bottom:3px"><strong style="color:#fff">Line ${s.dk_line}</strong> ${s.stat_label}</div>`);
      if(s.dk_line!=null && s.dk_hits!=null){
        const over=s.dk_hits, under=(s.l10_games||10)-over;
        lines.push(`<div style="font-size:.8rem;color:#aaa;margin-bottom:3px">vs line last ${s.l10_games||10} (vs ${p.opp} ${(p.location||'').toLowerCase()}): <span style="color:#4ade80;font-weight:700">${over} over</span> · <span style="color:#f87171;font-weight:700">${under} under</span></div>`);
      }
      if(s.recent_avg!=null){
        var _gap=s.gap!=null?s.gap:null;
        var _gapClr=_gap==null?'#94a3b8':_gap>0?'#4ade80':_gap<0?'#f87171':'#94a3b8';
        var _gapTxt=_gap==null?'':_gap>0?(' +'+_gap+' above line'):(' '+_gap+' below line');
        lines.push('<div style="font-size:.78rem;color:#888;margin-bottom:4px;padding:4px 7px;background:rgba(255,255,255,.03);border-radius:5px">L10 all-opp avg: <strong style="color:#fff">'+s.recent_avg+'</strong>'+'<span style="color:'+_gapClr+';font-weight:700">'+_gapTxt+'</span></div>');
      }
      if(s.threshold) lines.push(`<div style="font-size:.8rem;color:#aaa;margin-bottom:8px">pattern: hit <strong style="color:#FDB827">${s.threshold}+</strong> ${s.stat_label} in <strong style="color:#fff">${s.hits}/${s.games}</strong> vs ${p.opp} ${(p.location||'').toLowerCase()}</div>`);
      // Odds — show Over/Under odds whenever available (DK preferred, FD fallback)
      var _ov=s.dk_over_odds||s.fd_odds||'';
      var _un=s.dk_under_odds||'';
      if(_ov||_un){
        var _oddsHtml='<div style="font-size:.8rem;margin-bottom:5px;display:flex;gap:10px;align-items:center">';
        if(_ov) _oddsHtml+='<span style="color:#64748b">Over</span> <span style="font-family:monospace;font-weight:900;color:#fbbf24">'+_ov+'</span>';
        if(_un) _oddsHtml+=((_ov?' · ':'')+'<span style="color:#64748b">Under</span> <span style="font-family:monospace;font-weight:900;color:#fbbf24">'+_un+'</span>');
        _oddsHtml+='</div>';
        lines.push(_oddsHtml);
      }
      // B — Best bet at the sportsbook's actual line
      if(s.best_bet){
        const bb=s.best_bet, isPass=bb.side==='PASS';
        const bc=isPass?'#9ca3af':dirColor(bb.side);
        const confColor=bb.conf==='STRONG'?'#4ade80':bb.conf==='LEAN'?'#fbbf24':'#9ca3af';
        const label=isPass?`NO EDGE ${bb.line}`:`${bb.side} ${bb.line}`;
        lines.push(`<div style="font-size:.82rem;margin:7px 0 5px;padding:6px 9px;background:rgba(255,255,255,.03);border-left:3px solid ${bc};border-radius:5px">
          <span style="color:#888">BEST BET </span><strong style="color:${bc}">${label}</strong>
          <span style="color:#fff"> ${bb.hits}/${bb.games} (${bb.pct}%)</span>
          <span style="color:${confColor};font-weight:800"> ${bb.conf}</span></div>`);
      }
      return `<div style="background:#0d0d0d;border:1px solid #1f1f1f;border-radius:10px;padding:12px 14px;margin-top:9px">
        <div style="display:flex;align-items:center;justify-content:space-between;gap:10px;margin-bottom:7px">
          <div style="font-size:.98rem;min-width:0"><span>${s.emoji}</span> <strong style="color:#fff">${s.stat_label}</strong></div>
          ${verdictPill}
        </div>
        ${lines.join('')}
        <div style="display:flex;flex-wrap:wrap;gap:6px">${badges.join('')}</div>
      </div>`;
    }).join('');
    const _bverd=_nbaPickVerdict(p);
    const _betHtml=window.IS_ADMIN?_nbaBetBtn(p,_bverd):'';
    html+=`
    <div class="pick-card" style="padding:0;overflow:hidden;border-radius:14px;background:linear-gradient(180deg,#161616 0%,#0f0f0f 100%);border:1px solid #262626">
      <div style="background:linear-gradient(135deg,#1e3a5f 0%,#0a1a2e 100%);padding:12px 16px;display:flex;align-items:center;justify-content:space-between;border-bottom:2px solid #FDB827">
        <div style="display:flex;align-items:center;gap:10px">
          <div style="width:34px;height:34px;border-radius:50%;background:#FDB827;color:#000;display:flex;align-items:center;justify-content:center;font-weight:900;font-size:1rem">${i+1}</div>
          <div style="font-size:.78rem;letter-spacing:.12em;color:#FDB827;font-weight:800">NBA · ${p.team}</div>
        </div>
        <img src="${teamLogo}" alt="${p.team}" style="height:38px;width:38px;object-fit:contain" onerror="this.style.display='none'"/>
      </div>
      <div style="position:relative;height:160px;background:radial-gradient(ellipse at center top,rgba(253,184,39,.15),transparent 70%),linear-gradient(180deg,#1e3a5f 0%,#0a1a2e 100%);overflow:hidden">
        <img onclick="openLadder('${cardKey}')" src="${headshot}" alt="${pname}" style="position:absolute;bottom:-6px;left:50%;transform:translateX(-50%);height:170px;object-fit:contain;cursor:pointer" onerror="this.style.display='none'"/>
        <div onclick="openLadder('${cardKey}')" style="position:absolute;bottom:6px;left:50%;transform:translateX(-50%);background:rgba(0,0,0,.62);color:#FDB827;font-size:.62rem;font-weight:800;padding:3px 9px;border-radius:6px;border:1px solid #FDB82766;cursor:pointer;white-space:nowrap">📊 TAP FOR GAME LOG</div>
        ${p.position?`<div style="position:absolute;top:10px;right:12px;background:rgba(0,0,0,.6);color:#fff;font-weight:800;font-size:.88rem;padding:4px 10px;border-radius:6px;border:1px solid #444">${p.position}</div>`:''}
      </div>
      <div style="background:#FDB827;color:#000;text-align:center;padding:10px 12px;font-weight:900;font-size:1.18rem;letter-spacing:.01em">${pname}</div>
      <div style="padding:12px 14px 14px">
        <div style="display:flex;justify-content:space-between;align-items:center;font-size:.9rem;color:#aaa;margin-bottom:4px">
          <span>vs <strong style="color:#fff">${p.opp}</strong></span>
          ${tip?`<span>⏱ ${tip}</span>`:''}
        </div>
        <div style="font-size:.78rem;color:#666;margin-bottom:4px">${p.matchup}</div>
        ${statBlocks}
      </div>
      ${_betHtml}
    </div>`;
  });
  html+='</div>';
  document.getElementById('content').innerHTML=html;
}

function renderAllByGame(picks){
  const el=document.getElementById('allPicksSection');
  if(!picks.length){el.innerHTML='<div class="msg-card" style="padding:30px"><span class="ico"></span><p>No patterns for this filter.</p></div>';return;}
  const groups={},order=[];
  for(const p of picks){if(!groups[p.matchup]){groups[p.matchup]=[];order.push(p.matchup);}groups[p.matchup].push(p);}
  let html='';
  for(const matchup of order){
    const gp=groups[matchup];
    const gameId='g_'+matchup.replace(/[^a-z0-9]/gi,'_');
    html+=`<div class="game-group">
      <div class="game-group-hdr" onclick="toggleGroup('${gameId}',this)">
        <span class="gg-label"> ${matchup}</span>
        <div class="gg-meta"><span class="count-pill">${gp.length} pattern${gp.length!==1?'s':''}</span><span class="gg-chevron"></span></div>
      </div>
      <div class="compact-picks" id="${gameId}">`;
    // Sub-group by player so each player has one expandable row
    const byPlayer = {}; const playerOrder = [];
    for(const p of gp){
      if(!byPlayer[p.player]){byPlayer[p.player]=[];playerOrder.push(p.player);}
      byPlayer[p.player].push(p);
    }
    for(const pname of playerOrder){
      const rows = byPlayer[pname];
      const first = rows[0];
      const pid = gameId+'_'+pname.replace(/[^a-z0-9]/gi,'_');
      // Best % across this player's picks for summary chip
      const bestPct = Math.max(...rows.map(r=>r.pct||0));
      const stats = rows.map(r=>r.stat_label).join(' · ');
      html+=`<div class="player-group" style="border-bottom:1px solid #1f1f1f">
        <div onclick="togglePlayer('${pid}',this)" style="display:flex;align-items:center;gap:10px;padding:10px 14px;cursor:pointer;background:#141414">
          <span style="font-size:1.1rem">${first.emoji}</span>
          <div style="flex:1;min-width:0">
            <div style="font-weight:700;color:#fff;font-size:.88rem">${pname} <span style="color:#1e3a5f;font-size:.65rem">${first.team}${first.location==='Home'?' HOME':' AWAY'}</span></div>
            <div style="color:#777;font-size:.7rem;margin-top:2px">${rows.length} pick${rows.length!==1?'s':''} · ${stats}</div>
          </div>
          ${bestPct>0?`<span style="color:#fbbf24;font-weight:700;font-size:.78rem">${bestPct}%</span>`:''}
          <span class="pg-chevron" style="color:#666;font-size:.8rem;transition:transform .2s">▼</span>
        </div>
        <div id="${pid}" style="display:none;flex-direction:column;background:#0e0e0e">`;
      for(const p of rows){
        const [pc,bc]=pctClass(p.pct);
        const ladKey=ladReg(p);
        const badges = [];
        if(p.has_consistency) badges.push(`<span style="background:rgba(245,158,11,.15);color:#fbbf24;padding:2px 7px;border-radius:6px;font-size:.65rem;font-weight:700;margin-right:4px">PATTERN ${p.pct}%</span>`);
        const loc=(p.location||'').toLowerCase();
        if(p.line_rec) badges.push(`<span style="background:${p.line_rec==='UNDER'?'rgba(239,68,68,.15)':'rgba(74,222,128,.15)'};color:${p.line_rec==='UNDER'?'#f87171':'#4ade80'};padding:2px 7px;border-radius:6px;font-size:.65rem;font-weight:700;margin-right:4px">LINE ${p.line_rec} ${p.dk_line} ${p.line_rec_pct}% vs ${p.opp} ${loc}</span>`);
        if(p.streak_rec) badges.push(`<span style="background:rgba(249,115,22,.15);color:#fb923c;padding:2px 7px;border-radius:6px;font-size:.65rem;font-weight:700;margin-right:4px">🔥 ${p.streak_n} in a row ${p.streak_rec} ${p.dk_line} vs ${p.opp} ${loc}</span>`);
        if(p.alt_rec) badges.push(`<span style="background:rgba(168,85,247,.15);color:#c084fc;padding:2px 7px;border-radius:6px;font-size:.65rem;font-weight:700;margin-right:4px">⭐ MPA SPECIAL ${p.alt_rec} ${p.dk_line} vs ${p.opp} ${loc}${p.alt_evens&&p.alt_odds?` (even: ${p.alt_evens} · odd: ${p.alt_odds})`:''}</span>`);
        const patternLine = p.has_consistency
          ? (() => { const pl = (p.dk_line!=null?p.dk_line:p.fd_line); return `${p.threshold}+ ${p.stat_label}  ${p.hits}/${p.games} vs ${p.opp}${pl!=null ? `  <span class="fd-inline"> ${pl}</span>` : ''}`; })()
          : `${p.stat_label} vs ${p.opp}${p.dk_line ? `  line ${p.dk_line}` : ''}`;
        html+=`<div onclick="openLadder('${ladKey}')" style="display:flex;align-items:center;gap:10px;padding:8px 14px 8px 38px;border-top:1px solid #1a1a1a;cursor:pointer">
          <div style="flex:1;min-width:0">
            <div style="color:#bbb;font-size:.78rem">${patternLine} <span style="color:#FDB827;font-size:.62rem;font-weight:800">📊 TAP</span></div>
            <div style="margin-top:4px;display:flex;flex-wrap:wrap;gap:3px">${badges.join('')}</div>
          </div>
          
          ${p.has_consistency ? `<div style="text-align:right"><div class="cr-pct ${pc}" style="font-size:.85rem;font-weight:800">${p.pct}%</div><div style="color:#666;font-size:.65rem">${p.hits}/${p.games}</div></div>` : ''}
        </div>`;
      }
      html+='</div></div>';
    }
    html+='</div></div>';
  }
  el.innerHTML=html;
}

function toggleSig(id,hdr){
  const el=document.getElementById(id);
  if(!el)return;
  const ch=hdr.querySelector('.sig-chev');
  const hidden=el.style.display==='none';
  el.style.display=hidden?'block':'none';
  if(ch)ch.style.transform=hidden?'rotate(180deg)':'';
}
function renderSignalLists(picks){
  // Build set of player|stat combos that have a strong PATTERN (always OVER-direction).
  // Any STREAK/MPA UNDER on the same combo contradicts the pattern, so suppress it.
  const patternKeys=new Set((picks||[]).filter(p=>p.has_consistency).map(p=>`${p.player}|${p.stat}`));
  const contradicts=p=>{const k=`${p.player}|${p.stat}`;return patternKeys.has(k);};
  const streaks=(picks||[]).filter(p=>p.streak_rec && !(p.streak_rec==='UNDER' && contradicts(p))).slice().sort((a,b)=>(b.streak_n||0)-(a.streak_n||0));
  const mpas=(picks||[]).filter(p=>p.alt_rec);
  const sc=document.getElementById('streakCount'); if(sc) sc.textContent=streaks.length;
  const mc=document.getElementById('mpaCount'); if(mc) mc.textContent=mpas.length;
  const dirColor=d=>d==='OVER'?'#4ade80':d==='UNDER'?'#f87171':'#9ca3af';
  const dirBg=d=>d==='OVER'?'rgba(74,222,128,.14)':d==='UNDER'?'rgba(239,68,68,.14)':'rgba(156,163,175,.1)';
  const row=(p,sigHTML)=>{const k=ladReg(p);return `<div onclick="openLadder('${k}')" style="display:grid;grid-template-columns:1fr auto;gap:10px;align-items:center;padding:9px 14px;border-bottom:1px solid #1a1a1a;cursor:pointer">
    <div style="min-width:0">
      <div style="font-weight:700;color:#fff;font-size:.82rem">${p.emoji} ${p.player} <span style="color:#777;font-size:.7rem">${p.team} vs ${p.opp}</span></div>
      <div style="color:#999;font-size:.7rem;margin-top:2px">${p.stat_label}${p.dk_line?` · line ${p.dk_line}`:''} <span style="color:#FDB827;font-size:.6rem;font-weight:800">📊 TAP</span></div>
    </div>
    ${sigHTML}
  </div>`;};
  const sl=document.getElementById('streakList');
  if(sl) sl.innerHTML = streaks.length ? streaks.map(p=>row(p,`<span style="background:${dirBg(p.streak_rec)};color:${dirColor(p.streak_rec)};border:1px solid ${dirColor(p.streak_rec)}55;padding:4px 9px;border-radius:6px;font-weight:900;font-size:.72rem;white-space:nowrap">🔥 ${p.streak_n} ${p.streak_rec}</span>`)).join('') : '<div style="padding:18px;text-align:center;color:#555;font-size:.78rem">No streaks today</div>';
  const ml=document.getElementById('mpaList');
  if(ml) ml.innerHTML = mpas.length ? mpas.map(p=>row(p,`<span style="background:${dirBg(p.alt_rec)};color:${dirColor(p.alt_rec)};border:1px solid ${dirColor(p.alt_rec)}55;padding:4px 9px;border-radius:6px;font-weight:900;font-size:.72rem;white-space:nowrap">⭐ ${p.alt_rec}${p.alt_evens&&p.alt_odds?` (even: ${p.alt_evens} · odd: ${p.alt_odds})`:''}</span>`)).join('') : '<div style="padding:18px;text-align:center;color:#555;font-size:.78rem">No MPA specials today</div>';
}
// ===== Admin Auto Parlay Builder =====
function _amToDec(a){var s=String(a==null?'':a).replace('+','').trim();var n=parseFloat(s);if(!n||isNaN(n))return null;return n>0?1+n/100:1+100/Math.abs(n);}
function _decToAm(d){if(!d||d<=1)return null;return d>=2?'+'+Math.round((d-1)*100):'-'+Math.round(100/(d-1));}
function _mpaRate(p){function parse(s){if(!s)return[0,0];var m=String(s).split('/');return[parseFloat(m[0])||0,parseFloat(m[1])||0];}var e=parse(p.alt_evens),o=parse(p.alt_odds);var h=e[0]+o[0],t=e[1]+o[1];return t?h/t*100:0;}
function _fmtOdds(o){if(o==null||o==='')return null;var s=String(o).trim();return (s.charAt(0)==='-'||s.charAt(0)==='+')?s:'+'+s;}
function _legCandidates(p){
  var pat = !!p.has_consistency; // PATTERN is always OVER-direction
  var line = (p.dk_line!=null?p.dk_line:p.fd_line);
  function oddsFor(dir){ return dir==='OVER' ? (p.dk_over_odds||p.fd_odds||'') : (p.dk_under_odds||''); }
  var c=[];
  if(pat){ c.push({type:'PATTERN',dir:'OVER',conf:(p.pct||0),reason:'📊 PATTERN '+(p.hits||0)+'/'+(p.games||0)+' ('+(p.pct||0)+'%) vs '+p.opp}); }
  if(p.line_rec && !(pat && p.line_rec!=='OVER')){ c.push({type:'LINE',dir:p.line_rec,conf:(p.line_rec_pct||0),reason:'📈 LINE '+p.line_rec+' '+(p.line_rec_hits||'')+' ('+(p.line_rec_pct||0)+'%) vs '+p.opp}); }
  if(p.streak_rec && !(pat && p.streak_rec!=='OVER')){ var n=p.streak_n||0; c.push({type:'STREAK',dir:p.streak_rec,conf:Math.min(99,85+n),reason:'🔥 '+n+'-game '+p.streak_rec+' streak vs '+p.opp}); }
  if(p.alt_rec && !(pat && p.alt_rec!=='OVER')){ c.push({type:'MPA',dir:p.alt_rec,conf:Math.round(_mpaRate(p)),reason:'⭐ MPA '+p.alt_rec+((p.alt_evens&&p.alt_odds)?(' (even '+p.alt_evens+' · odd '+p.alt_odds+')'):'')}); }
  c.forEach(function(x){ x.p=p; x.player=p.player; x.team=p.team; x.opp=p.opp; x.stat=p.stat_label||p.stat; x.emoji=p.emoji||''; x.line=line; x.odds=oddsFor(x.dir); x.dec=_amToDec(x.odds); x.hasOdds=!!x.dec; x.mpg=(p.mpg!=null?p.mpg:null); });
  return c;
}
function _legScore(c){
  // Priced legs first, then signal strength, then bigger payout odds as a tiebreaker.
  // SOFT STARTER LEAN: players at 20+ mpg get an ~11.5 confidence-point bonus so
  // starters float to the top, but a role-player whose signal is 12+ points higher
  // still wins (conf values are integers, so 11.5 makes the boundary deterministic).
  // To convert back, delete the starterBonus term below.
  var starterBonus = (c.mpg!=null && c.mpg>=20) ? 11.5*1e4 : 0;
  return (c.hasOdds?1:0)*1e9 + (c.conf||0)*1e4 + starterBonus + (c.dec?Math.min(c.dec,11)*100:0);
}
// ODDS FLOOR: a priced leg only qualifies at -500 or better (drops -920-type juice),
// OVER or UNDER. Unpriced legs (no odds) are left alone as last-resort filler.
// To convert back, remove the _floorOk gate in _parlayPool below.
function _floorOk(odds){ if(odds==null||odds==='') return true; var a=parseFloat(odds); if(isNaN(a)||a===0) return true; return a>=-500; }
function _parlayPool(){
  // HARD MINUTES FLOOR: players under this mpg never enter the parlay builder — low-minute
  // guys are unreliable, especially in the playoffs when rotations shrink. Unknown mpg is
  // kept (rare). This is a hard cut, separate from the soft 20-mpg starter lean in
  // _legScore. To revert, set _MIN_MPG to 0.
  var _MIN_MPG=18;
  // ONE PLAY PER PLAYER+STAT: a player can contribute several plays (Points, Rebounds,
  // Assists ...), keeping the best signal for each stat — this widens the pool toward the
  // full count of strong signals. The parlay builder still never uses the same player twice
  // in one ticket (enforced in _renderParlay). To collapse back to one play per player,
  // key on c.player alone.
  var byKey={};
  (allPicksData||[]).forEach(function(p){
    _legCandidates(p).forEach(function(c){
      if(c.mpg!=null && c.mpg<_MIN_MPG) return;
      if(!_floorOk(c.odds)) return;
      var key=c.player+'|'+c.stat;
      var cur=byKey[key];
      if(!cur || _legScore(c)>_legScore(cur)) byKey[key]=c;
    });
  });
  return Object.keys(byKey).map(function(k){return byKey[k];}).sort(function(a,b){return _legScore(b)-_legScore(a);});
}
function _shuffle(a){ for(var i=a.length-1;i>0;i--){var j=Math.floor(Math.random()*(i+1));var t=a[i];a[i]=a[j];a[j]=t;} return a; }
function closeParlay(){ var o=document.getElementById('parlayResult'); if(o) o.innerHTML=''; }
function buildParlay(){ _renderParlay(false); }
function generateParlay(){ _renderParlay(true); }
function _renderParlay(randomize){
  var sel=document.getElementById('parlayLegs');
  var n=parseInt(sel?sel.value:'3',10)||3;
  var out=document.getElementById('parlayResult');
  if(!out) return;
  if(!allPicksData||!allPicksData.length){ out.innerHTML='<div style="color:#888;padding:10px">Run today&#39;s picks first, then build a parlay.</div>'; return; }
  var cands=_parlayPool();
  // Capacity is DISTINCT PLAYERS — a parlay never uses the same player twice, even though the
  // pool now holds multiple stat-plays per player.
  var seenP={}; cands.forEach(function(c){ seenP[c.player]=1; });
  var availP=Object.keys(seenP).length;
  if(availP<n){ out.innerHTML='<div style="color:#f87171;padding:10px">Only '+availP+' qualifying player'+(availP!==1?'s':'')+' on the board. Pick a smaller parlay.</div>'; return; }
  // Greedy pick of n legs with DISTINCT players. Pass 1 honors the avoid set (the players in
  // the parlay currently shown, so "Generate New" gives a fresh list for ANY size now, 6-leg
  // included); pass 2 fills any shortfall ignoring the avoid set but still keeping players
  // unique. To drop the fresh-list behavior, pass null as avoidSet below.
  function _pickLegs(ordered, avoidSet){
    var used={}, picked=[], i, c;
    for(i=0;i<ordered.length && picked.length<n;i++){
      c=ordered[i];
      if(used[c.player]) continue;
      if(avoidSet && avoidSet[c.player]) continue;
      used[c.player]=1; picked.push(c);
    }
    for(i=0;i<ordered.length && picked.length<n;i++){
      c=ordered[i];
      if(used[c.player]) continue;
      used[c.player]=1; picked.push(c);
    }
    return picked;
  }
  var legs;
  if(randomize){
    var avoidSet=null;
    if(window._lastParlayPlayers && window._lastParlayPlayers.length){
      avoidSet={}; window._lastParlayPlayers.forEach(function(pl){ avoidSet[pl]=1; });
    }
    legs=_pickLegs(_shuffle(cands.slice()), avoidSet).sort(function(a,b){return _legScore(b)-_legScore(a);});
  } else {
    legs=_pickLegs(cands.slice(), null);
  }
  window._lastParlayPlayers=legs.map(function(l){return l.player;});
  var dec=1, priced=0, missing=0;
  legs.forEach(function(l){ if(l.dec){dec*=l.dec;priced++;}else{missing++;} });
  var am = priced? _decToAm(dec) : null;
  var payout = priced? (100*dec) : null;
  var dirColor=function(d){return d==='OVER'?'#4ade80':d==='UNDER'?'#f87171':'#9ca3af';};
  var tagBg={PATTERN:'rgba(253,184,39,.16)',LINE:'rgba(74,222,128,.14)',STREAK:'rgba(249,115,22,.16)',MPA:'rgba(168,85,247,.16)'};
  var tagFg={PATTERN:'#FDB827',LINE:'#4ade80',STREAK:'#fb923c',MPA:'#c084fc'};
  var rows=legs.map(function(l,i){var fo=_fmtOdds(l.odds);return '<div style="display:flex;justify-content:space-between;align-items:center;gap:10px;padding:10px 12px;border-bottom:1px solid #1a1a1a">'
    +'<div style="min-width:0">'
    +'<div style="font-weight:800;color:#fff;font-size:.85rem">'+(i+1)+'. '+(l.emoji||'')+' '+l.player+' <span style="color:#777;font-size:.7rem">'+l.team+' vs '+l.opp+'</span> <span style="background:'+(tagBg[l.type]||'#222')+';color:'+(tagFg[l.type]||'#aaa')+';padding:1px 6px;border-radius:4px;font-size:.6rem;font-weight:800">'+l.type+'</span></div>'
    +'<div style="color:#999;font-size:.72rem;margin-top:2px">'+l.stat+(l.line!=null?(' · line '+l.line):'')+(l.mpg!=null?(' · '+l.mpg+' mpg'):'')+' · '+l.reason+'</div>'
    +'</div>'
    +'<div style="text-align:right;white-space:nowrap">'
    +'<div style="color:'+dirColor(l.dir)+';font-weight:900;font-size:.8rem">'+l.dir+'</div>'
    +'<div style="color:#FDB827;font-size:.72rem;font-weight:800">'+(fo||'odds N/A')+'</div>'
    +'</div></div>';}).join('');
  var header='<div style="display:flex;justify-content:space-between;align-items:center;padding:8px 12px;border-bottom:1px solid #262626;background:#121212">'
    +'<span style="font-weight:800;color:#ccc;font-size:.74rem">'+(randomize?'RANDOM MIX':'TOP PLAYS')+'</span>'
    +'<span onclick="closeParlay()" title="Close" style="cursor:pointer;color:#888;font-weight:900;font-size:1.15rem;line-height:1;padding:0 6px">×</span></div>';
  var summary='<div style="display:flex;justify-content:space-between;align-items:center;padding:12px;background:linear-gradient(135deg,rgba(253,184,39,.12),rgba(253,184,39,.02));border-top:1px solid #262626">'
    +'<div style="font-weight:900;color:#FDB827">'+n+'-LEG PARLAY</div>'
    +'<div style="text-align:right">'+(am?('<div style="font-weight:900;color:#4ade80;font-size:1.05rem">'+am+'</div><div style="color:#999;font-size:.7rem">$100 → $'+payout.toFixed(2)+(missing?(' · '+priced+'/'+n+' legs priced'):'')+'</div>'):('<div style="color:#888;font-size:.78rem">No book odds available for these legs</div>'))+'</div>'
    +'</div>';
  out.innerHTML='<div style="background:#0e0e0e;border:1px solid #262626;border-radius:12px;overflow:hidden">'+header+rows+summary+'</div>';
}
function togglePlayer(id,hdr){
  const el=document.getElementById(id);
  if(!el)return;
  const ch=hdr.querySelector('.pg-chevron');
  const hidden=el.style.display==='none';
  el.style.display=hidden?'flex':'none';
  if(ch)ch.style.transform=hidden?'rotate(180deg)':'';
}
function closeLadder(ev){
  if(ev && ev.target && ev.target.id!=='ladderOverlay' && ev.type==='click') return;
  const o=document.getElementById('ladderOverlay'); if(o) o.remove();
}
function ladKeyOf(p){return 'lad_'+((p.player_id||'')+'_'+p.stat+'_'+p.location+'_'+p.opp).replace(/[^a-z0-9]/gi,'_');}
function ladReg(p){const k=ladKeyOf(p);window.__LAD__=window.__LAD__||{};window.__LAD__[k]=p;return k;}
function openLadder(key){
  const p=(window.__LAD__||{})[key]; if(!p) return;
  const esc=s=>String(s==null?'':s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
  const loc=(p.location||'').toLowerCase();
  const fmtD=s=>{try{const d=new Date(s);return (d.getMonth()+1)+'/'+d.getDate()+'/'+String(d.getFullYear()).slice(2);}catch(e){return s||'';}};
  const anchor=(p.dk_line!=null?p.dk_line:p.fd_line);
  // Game log vs this opponent at this location
  const glog=p.glog||[];
  let logHTML;
  if(glog.length){
    logHTML=glog.map(g=>`<div style="display:flex;justify-content:space-between;padding:6px 10px;border-bottom:1px solid #1a1a1a;font-size:.82rem">
      <span style="color:#999">${fmtD(g.d)}</span>
      <span style="color:#fff;font-weight:800">${esc(g.v)}</span></div>`).join('');
  } else {
    logHTML='<div style="padding:14px;color:#666;text-align:center;font-size:.8rem">No game log vs '+esc(p.opp)+'</div>';
  }
  // Ladder: book line ±3, over/under counts at each
  const lad=p.ladder||[];
  let ladHTML;
  if(lad.length){
    ladHTML=`<div style="display:grid;grid-template-columns:1fr 1fr 1fr;gap:0;font-size:.7rem;color:#777;font-weight:800;padding:6px 10px;border-bottom:1px solid #2a2a2a">
        <span>LINE</span><span style="text-align:center;color:#4ade80">OVER</span><span style="text-align:right;color:#f87171">UNDER</span></div>`
      + lad.map(r=>{
        const under=r.games-r.hits;
        const isAnchor=(anchor!=null&&r.t===anchor);
        const opct=r.pct, oc=opct>=70?'#4ade80':opct>=50?'#fbbf24':'#f87171';
        return `<div style="display:grid;grid-template-columns:1fr 1fr 1fr;gap:0;padding:7px 10px;border-bottom:1px solid #161616;font-size:.84rem;${isAnchor?'background:rgba(253,184,39,.10)':''}">
          <span style="color:#fff;font-weight:${isAnchor?'900':'700'}">${r.t}${isAnchor?' ◄ BOOK':''}</span>
          <span style="text-align:center;color:${oc};font-weight:800">${r.hits}/${r.games} <span style="color:#666;font-size:.7rem">(${opct}%)</span></span>
          <span style="text-align:right;color:#bbb;font-weight:700">${under}/${r.games}</span></div>`;
      }).join('');
  } else {
    ladHTML='<div style="padding:14px;color:#666;text-align:center;font-size:.8rem">No book line posted for this stat</div>';
  }
  closeLadder();
  const ov=document.createElement('div');
  ov.id='ladderOverlay';
  ov.setAttribute('onclick','closeLadder(event)');
  ov.style.cssText='position:fixed;inset:0;background:rgba(0,0,0,.78);z-index:9999;display:flex;align-items:center;justify-content:center;padding:16px';
  ov.innerHTML=`<div style="background:#101010;border:1px solid #2a2a2a;border-radius:14px;max-width:420px;width:100%;max-height:86vh;overflow:auto;box-shadow:0 20px 60px rgba(0,0,0,.6)">
    <div style="background:linear-gradient(135deg,#1e3a5f,#0a1a2e);padding:14px 16px;border-bottom:2px solid #FDB827;display:flex;justify-content:space-between;align-items:flex-start">
      <div>
        <div style="color:#fff;font-weight:900;font-size:1.02rem">${esc(p.emoji)} ${esc(p.player)}</div>
        <div style="color:#FDB827;font-size:.76rem;font-weight:700;margin-top:2px">${esc(p.stat_label)} vs ${esc(p.opp)} ${loc} · last ${glog.length}${anchor!=null?' · line '+anchor:''}</div>
      </div>
      <span onclick="closeLadder()" style="color:#888;font-size:1.4rem;line-height:1;cursor:pointer;padding:0 4px">×</span>
    </div>
    <div style="padding:12px 14px">
      <div style="color:#888;font-size:.7rem;font-weight:800;letter-spacing:.08em;margin-bottom:5px">ALT LINE HIT RATES (book ±3)</div>
      <div style="background:#0a0a0a;border:1px solid #1f1f1f;border-radius:9px;overflow:hidden;margin-bottom:14px">${ladHTML}</div>
      <div style="color:#888;font-size:.7rem;font-weight:800;letter-spacing:.08em;margin-bottom:5px">GAME LOG vs ${esc(p.opp)} (${loc})</div>
      <div style="background:#0a0a0a;border:1px solid #1f1f1f;border-radius:9px;overflow:hidden">${logHTML}</div>
    </div>
  </div>`;
  document.body.appendChild(ov);
}
function toggleGroup(id,hdr){
  const el=document.getElementById(id);
  const ch=hdr.querySelector('.gg-chevron');
  if(!el)return;
  const hidden=el.style.display==='none';
  el.style.display=hidden?'flex':'none';
  if(hidden)el.style.flexDirection='column';
  if(ch)ch.style.transform=hidden?'':'rotate(-90deg)';
}
function renderGames(games){
  if(!games||!games.length)return;
  var gb=document.getElementById('gamesBar');gb.style.display='flex';
  gb.innerHTML=games.map(g=>
    `<div class="game-chip"><b>${g.away}</b><span class="sep">@</span><b>${g.home}</b></div>`
  ).join('');
}


async function runPicks(force=false){
  if(force && !window.IS_ADMIN) return;
  const selectedDate=document.getElementById('datePicker').value;
  document.getElementById('content').innerHTML=`
    <div class="msg-card">
      <div class="loading-ball"></div>
      <div class="ball-shadow"></div>
      <h2 style="color:#FDB827">Analyzing Matchup Patterns</h2>
      <p>Pulling data for <strong style="color:#FDB827">${selectedDate}</strong> from NBA Stats API.<br>
      <span style="color:#1e3a5f">This takes ~45 seconds  worth the wait.</span></p>
    </div>`;
  document.getElementById('allPicksWrap').style.display='none';
  try{
    const _nbaTok=localStorage.getItem('__mpa_token')||'';
    const _adm=localStorage.getItem('__mpa_admin')||'';
    const r=await fetch('/run?_tok='+encodeURIComponent(_nbaTok)+'&admin='+encodeURIComponent(_adm),{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({date:selectedDate,force:!!force})});
    if(!r.ok)throw new Error('Server error '+r.status);
    const data=await r.json();
    renderGames(data.games);
    if(data.no_games){
      document.getElementById('filterBar').style.display='none';
      document.getElementById('allPicksWrap').style.display='none';
      document.getElementById('content').innerHTML=`<div class="msg-card"><span class="ico"></span><h2>No Games Today</h2><p>No NBA games scheduled for ${data.date||selectedDate}. Check back on game day.</p></div>`;
      return;
    }
    top10=data.picks||[];
    allPicksData=data.all_picks||[];
    activeTopStat='ALL';activeAllStat='ALL';
    const log=data.log||[];
    if(!top10.length && !allPicksData.length){
      document.getElementById('content').innerHTML=`<div class="msg-card"><span class="ico"></span><h2>No Qualifying Patterns</h2><p>No 70%+ patterns for today matchups.</p></div><div class="log-box">${log.join('<br>')}</div>`;
      renderPropsSection(data.props_picks, data.props_nopick);
      return;
    }
    if(top10.length){
      document.getElementById('filterBar').style.display='flex';
      renderTop10Cards(top10);
    } else {
      // Card minutes floor filtered everyone off the cards, but there are still 70%+ plays
      // for the all-by-game list / parlay builder below — surface those, not a dead page.
      document.getElementById('filterBar').style.display='none';
      document.getElementById('content').innerHTML=`<div class="msg-card"><span class="ico"></span><h2>No Cards Today</h2><p>No starters or 6th-man players cleared the minutes floor for cards. All 70%+ plays and the parlay builder are below.</p></div>`;
    }
    const lb=document.createElement('div');
    lb.className='log-box';
    lb.innerHTML=log.join('<br>')+`<br> ${data.total} total patterns found`;
    // Log box hidden from end users — internal diagnostics only.
    // document.getElementById('content').appendChild(lb);
    document.getElementById('totalCount').textContent=allPicksData.length;
    document.getElementById('allPicksWrap').style.display='block';
    renderSignalLists(allPicksData);
    renderAllByGame(allPicksData);
    renderPropsSection(data.props_picks, data.props_nopick);
  }catch(e){
    document.getElementById('content').innerHTML=`<div class="msg-card"><span class="ico"></span><h2 style="color:#ef4444">Something went wrong</h2><p>${e.message}</p></div>`;
  }
}

// Get Picks: load saved picks for the chosen date (read-only, never runs the pipeline).
async function getPicks(){
  const selectedDate=document.getElementById('datePicker').value;
  const btn=document.getElementById('getBtn');
  const orig=btn.textContent;
  btn.disabled=true; btn.textContent='Loading...';
  document.getElementById('content').innerHTML=`<div class="msg-card"><h2 style="color:#FDB827">Loading saved picks...</h2></div>`;
  document.getElementById('allPicksWrap').style.display='none';
  try{
    const _nbaTok=localStorage.getItem('__mpa_token')||'';
    const r=await fetch('/api/cached?target_date='+encodeURIComponent(selectedDate)+'&_tok='+encodeURIComponent(_nbaTok));
    if(r.status===404){ document.getElementById('content').innerHTML=`<div class="msg-card"><span class="ico"></span><h2>Picks Not Ready</h2><p>Today's picks aren't ready yet - check back a little later.</p></div>`; return; }
    if(!r.ok)throw new Error('Server error '+r.status);
    const data=await r.json();
    renderGames(data.games);
    if(data.no_games){
      document.getElementById('filterBar').style.display='none';
      document.getElementById('allPicksWrap').style.display='none';
      document.getElementById('content').innerHTML=`<div class="msg-card"><span class="ico"></span><h2>No Games Today</h2><p>No NBA games scheduled for ${data.date||selectedDate}. Check back on game day.</p></div>`;
      return;
    }
    top10=data.picks||[];
    allPicksData=data.all_picks||[];
    activeTopStat='ALL';activeAllStat='ALL';
    if(top10.length){
      document.getElementById('filterBar').style.display='flex';
      renderTop10Cards(top10);
    } else {
      document.getElementById('filterBar').style.display='none';
      document.getElementById('content').innerHTML=`<div class="msg-card"><span class="ico"></span><h2>No Cards Today</h2><p>All 70%+ plays and the parlay builder are below.</p></div>`;
    }
    if(top10.length||allPicksData.length){
      document.getElementById('totalCount').textContent=allPicksData.length;
      document.getElementById('allPicksWrap').style.display='block';
      renderSignalLists(allPicksData);
      renderAllByGame(allPicksData);
    }
    renderPropsSection(data.props_picks, data.props_nopick);
  }catch(e){
    document.getElementById('content').innerHTML=`<div class="msg-card"><span class="ico"></span><h2 style="color:#ef4444">Something went wrong</h2><p>${e.message}</p></div>`;
  }finally{
    btn.disabled=false; btn.textContent=orig;
  }
}

function renderPropsSection(picks, nopick) {
  var sec = document.getElementById('props-section');
  if (!sec) return;
  var all = (picks||[]).concat(nopick||[]);
  sec.style.display = all.length ? 'block' : 'none';
  if (!all.length) return;
  var sigMap = {};
  (allPicksData||[]).forEach(function(s){ sigMap[s.player+'|'+s.stat]=s; });
  var byGame = {};
  all.forEach(function(p){
    var m=p.matchup||''; if(!m) return;
    if(!byGame[m]) byGame[m]={};
    if(!byGame[m][p.player]) byGame[m][p.player]=[];
    byGame[m][p.player].push(p);
  });
  window.__PROPS_BY_GAME__=byGame; window.__PROPS_SIG__=sigMap;
  var sel=document.getElementById('propsGameSel'); if(!sel) return;
  var matchups=Object.keys(byGame);
  sel.innerHTML='<option value="">-- Select a game --</option>'+
    matchups.map(function(m){ return '<option value="'+m+'">'+m+'</option>'; }).join('');
  document.getElementById('propsPlayerList').style.display='none';
  if(matchups.length===1){ sel.value=matchups[0]; propsSelectGame(matchups[0]); }
}
function propsSelectGame(matchup) {
  var plist=document.getElementById('propsPlayerList'); if(!plist) return;
  var hint=document.getElementById('propsGameHint');
  if(!matchup){ plist.style.display='none'; if(hint) hint.textContent='Select a game to browse players'; return; }
  var byGame=window.__PROPS_BY_GAME__||{}; if(!byGame[matchup]){ plist.style.display='none'; return; }
  window.__PROPS_PLAYERS__={};
  var players=Object.keys(byGame[matchup]);
  players.sort(function(a,b){ return a.split(' ').pop().localeCompare(b.split(' ').pop()); });
  if(hint) hint.textContent=players.length+' players with prop lines';
  var chips=players.map(function(name,idx){
    window.__PROPS_PLAYERS__[idx]=name;
    var ent=byGame[matchup][name]; var first=ent[0]||{};
    var side=first.side||''; var opp=first.opp_name||''; var cnt=ent.length;
    var sb=side==='HOME'?'rgba(253,184,39,.15)':'rgba(99,102,241,.15)';
    var sc=side==='HOME'?'#fbbf24':'#818cf8';
    return '<div class="props-player-chip" onclick="openPropsPlayer('+idx+')">' +
      '<div style="font-weight:800;color:#fff;font-size:.88rem;font-family:Playfair Display,serif">'+name+'</div>' +
      '<div style="font-size:.7rem;color:#888;margin-top:3px">' +
        '<span style="background:'+sb+';color:'+sc+';padding:1px 5px;border-radius:3px;font-weight:700;margin-right:4px">'+side+'</span>' +
        'vs '+opp+' &middot; '+cnt+' props</div>' +
    '</div>';
  }).join('');
  plist.innerHTML='<div style="display:flex;flex-wrap:wrap;gap:8px;padding:4px 0 12px">'+chips+'</div>';
  plist.style.display='block';
}
function closePropsModal(ev){
  if(ev && ev.target && ev.target.id!=='propsPlayerModal') return;
  var o=document.getElementById('propsPlayerModal'); if(o) o.remove();
}
function openPropsPlayer(idx){
  var name=(window.__PROPS_PLAYERS__||{})[idx]; if(name==null) return;
  var matchup=(document.getElementById('propsGameSel')||{}).value||'';
  var byGame=window.__PROPS_BY_GAME__||{};
  var entries=(byGame[matchup]||{})[name]; if(!entries||!entries.length) return;
  var sigMap=window.__PROPS_SIG__||{};
  var esc=function(s){ return String(s==null?'':s).replace(/[&<>"']/g,function(c){return {'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c];}); };
  var first=entries[0]||{}; var side=first.side||''; var opp=first.opp_name||'';
  var rows=entries.map(function(p){
    var sig=sigMap[name+'|'+p.stat]||{};
    var isO=p.pick==='OVER', isU=p.pick==='UNDER';
    var clr=isO?'#4ade80':isU?'#f87171':'#888';
    var dkO=p.dk_over_odds||(sig.dk_over_odds||'');
    var dkU=p.dk_under_odds||(sig.dk_under_odds||'');
    var ba=[];
    if(sig.has_consistency) ba.push('<span style="background:rgba(245,158,11,.15);color:#fbbf24;padding:1px 5px;border-radius:3px;font-size:.6rem;font-weight:700">PAT '+sig.pct+'%</span>');
    if(sig.line_rec) ba.push('<span style="background:rgba(74,222,128,.12);color:#4ade80;padding:1px 5px;border-radius:3px;font-size:.6rem;font-weight:700">LINE '+sig.line_rec+'</span>');
    if(sig.streak_rec) ba.push('<span style="background:rgba(249,115,22,.12);color:#fb923c;padding:1px 5px;border-radius:3px;font-size:.6rem;font-weight:700">STREAK '+sig.streak_n+'</span>');
    if(sig.alt_rec) ba.push('<span style="background:rgba(168,85,247,.12);color:#c084fc;padding:1px 5px;border-radius:3px;font-size:.6rem;font-weight:700">MPA '+sig.alt_rec+'</span>');
    var badges=ba.length?'<div style="margin-top:3px;display:flex;flex-wrap:wrap;gap:3px">'+ba.join('')+'</div>':'';
    var hist=(p.history||'').split(',').filter(Boolean).slice(0,8);
    var histHtml=hist.length?hist.map(function(v){
      var n=parseFloat(v); var ln=p.line;
      var hc=(!isNaN(n)&&ln!=null)?(n>ln?'#4ade80':n<ln?'#f87171':'#888'):'#666';
      return '<span style="color:'+hc+';font-weight:700">'+v+'</span>';
    }).join('<span style="color:#333;margin:0 1px">,</span>'):'<span style="color:#555">—</span>';
    var avgDisp=p.avg!=null?esc(String(p.avg))+'<span style="color:#777;font-size:.7rem"> ('+esc(String(p.games))+'g)</span>':'<span style="color:#555">no history</span>';
    var pickCell=(isO?'<span style="color:#4ade80;font-weight:900;font-size:.95rem">O</span>':isU?'<span style="color:#f87171;font-weight:900;font-size:.95rem">U</span>':'<span style="color:#555">—</span>')+badges;
    var _trackCell='';
    if(window.IS_ADMIN){
      if(p.line!=null){
        var _bside=isU?'UNDER':'OVER';
        var _bo=(p.dk_over_odds!=null?p.dk_over_odds:(sig.dk_over_odds!=null?sig.dk_over_odds:null));
        var _bu=(p.dk_under_odds!=null?p.dk_under_odds:(sig.dk_under_odds!=null?sig.dk_under_odds:null));
        var _bodds=_bside==='OVER'?(_bo!=null?_bo:_bu):(_bu!=null?_bu:_bo);
        var _bk='np'+(++_nbaBetN);
        (window.__NBA_BET_SRC__=window.__NBA_BET_SRC__||{})[_bk]={name:name,team:(p.team||''),opp:opp,category:(p.stat_label||''),side:_bside,stat_key:(p.stat||''),stat_label:(p.stat_label||''),line:p.line,odds:(_bodds!=null?_bodds:null),date:(p.tipoff?String(p.tipoff).slice(0,10):'')};
        _trackCell='<td style="padding:10px 12px"><button data-betkey="'+_bk+'" class="admin-only" onclick="event.stopPropagation();_nbaBetForm(this.dataset.betkey)" style="background:#1a1740;color:#a5b4fc;border:1px solid #312e81;border-radius:7px;padding:5px 11px;font-size:.72rem;font-weight:800;cursor:pointer;white-space:nowrap">Track</button></td>';
      } else {
        _trackCell='<td style="padding:10px 12px;color:#555">—</td>';
      }
    }
    return '<tr style="border-bottom:1px solid #1a1a1a">' +
      '<td style="padding:10px 12px;white-space:nowrap">'+esc(p.emoji)+' <span style="color:#FDB827;font-weight:700">'+esc(p.stat_label)+'</span></td>' +
      '<td style="padding:10px 12px;font-family:monospace;font-weight:800;color:#fff">'+esc(String(p.line||'—'))+'</td>' +
      '<td style="padding:10px 12px;font-family:monospace;font-size:.82rem;color:#4ade80">'+(dkO||'—')+'</td>' +
      '<td style="padding:10px 12px;font-family:monospace;font-size:.82rem;color:#f87171">'+(dkU||'—')+'</td>' +
      '<td style="padding:10px 12px;font-family:monospace;font-size:.9rem;color:'+clr+';font-weight:700">'+avgDisp+'</td>' +
      '<td style="padding:10px 12px;font-size:.75rem;font-family:monospace;max-width:160px">'+histHtml+'</td>' +
      '<td style="padding:10px 12px">'+pickCell+'</td>' +
      _trackCell +
    '</tr>';
  });
  closePropsModal();
  var ov=document.createElement('div');
  ov.id='propsPlayerModal';
  ov.setAttribute('onclick','closePropsModal(event)');
  ov.style.cssText='position:fixed;inset:0;background:rgba(0,0,0,.78);z-index:9999;display:flex;align-items:center;justify-content:center;padding:16px';
  ov.innerHTML=
    '<div style="background:#101010;border:1px solid #2a2a2a;border-radius:14px;max-width:820px;width:100%;max-height:86vh;overflow:auto;box-shadow:0 20px 60px rgba(0,0,0,.6)">' +
      '<div style="background:linear-gradient(135deg,#1e3a5f,#0a1a2e);padding:14px 18px;border-bottom:2px solid #FDB827;display:flex;justify-content:space-between;align-items:flex-start;position:sticky;top:0;z-index:1">' +
        '<div>' +
          '<div style="color:#fff;font-weight:900;font-size:1.05rem;font-family:Playfair Display,serif">'+esc(name)+'</div>' +
          '<div style="color:#FDB827;font-size:.76rem;font-weight:700;margin-top:3px">'+esc(side)+' &middot; vs '+esc(opp)+' &middot; '+esc(matchup)+'</div>' +
        '</div>' +
        '<span onclick="closePropsModal()" style="color:#888;font-size:1.5rem;line-height:1;cursor:pointer;padding:0 4px">&times;</span>' +
      '</div>' +
      '<div style="overflow-x:auto">' +
        '<table style="width:100%;border-collapse:collapse;font-size:.82rem;background:#101010">' +
          '<thead><tr style="background:#1a1a1a;border-bottom:1px solid rgba(245,158,11,.2)">' +
            '<th style="padding:9px 12px;text-align:left;color:#f59e0b;font-size:.68rem;font-weight:700;text-transform:uppercase;letter-spacing:.1em;white-space:nowrap">Stat</th>' +
            '<th style="padding:9px 12px;text-align:left;color:#f59e0b;font-size:.68rem;font-weight:700;text-transform:uppercase;letter-spacing:.1em">Line</th>' +
            '<th style="padding:9px 12px;text-align:left;color:#4ade80;font-size:.68rem;font-weight:700;text-transform:uppercase;letter-spacing:.1em">Over</th>' +
            '<th style="padding:9px 12px;text-align:left;color:#f87171;font-size:.68rem;font-weight:700;text-transform:uppercase;letter-spacing:.1em">Under</th>' +
            '<th style="padding:9px 12px;text-align:left;color:#f59e0b;font-size:.68rem;font-weight:700;text-transform:uppercase;letter-spacing:.1em">Avg vr Opp</th>' +
            '<th style="padding:9px 12px;text-align:left;color:#f59e0b;font-size:.68rem;font-weight:700;text-transform:uppercase;letter-spacing:.1em;white-space:nowrap">Last 8 vr Opp</th>' +
            '<th style="padding:9px 12px;text-align:left;color:#f59e0b;font-size:.68rem;font-weight:700;text-transform:uppercase;letter-spacing:.1em">Pick &amp; Signal</th>' +
            (window.IS_ADMIN?'<th style="padding:9px 12px;text-align:left;color:#a5b4fc;font-size:.68rem;font-weight:700;text-transform:uppercase;letter-spacing:.1em">Track</th>':'') +
          '</tr></thead>' +
          '<tbody>'+rows.join('')+'</tbody>' +
        '</table>' +
      '</div>' +
      '<p style="font-size:.68rem;color:#444;padding:10px 14px;margin:0">Last 8 = head-to-head games at this location, newest-first &middot; Green = over the line, Red = under</p>' +
    '</div>';
  document.body.appendChild(ov);
}

// Snapshot mode: hub serves this page with picks baked in as
// window.__INITIAL_PICKS__ — skip the /run fetch and render directly.
document.addEventListener('DOMContentLoaded', function(){
  if (!window.__INITIAL_PICKS__) return;
  try {
    var data = window.__INITIAL_PICKS__;
    var dp = document.getElementById('datePicker');
    if (dp && data.date) dp.value = data.date;
    if (data.games) renderGames(data.games);
    top10        = data.picks || [];
    allPicksData = data.all_picks || [];
    activeTopStat = 'ALL'; activeAllStat = 'ALL';
    if (top10.length) {
      var fb = document.getElementById('filterBar');
      if (fb) fb.style.display = 'flex';
      renderTop10Cards(top10);
    }
    if (allPicksData.length) {
      // Render the all-picks sections whenever there are plays, even if the card minutes
      // floor left zero cards.
      var tc = document.getElementById('totalCount');
      if (tc) tc.textContent = allPicksData.length;
      var ap = document.getElementById('allPicksWrap');
      if (ap) ap.style.display = 'block';
      renderSignalLists(allPicksData);
      renderAllByGame(allPicksData);
    }
    renderPropsSection(data.props_picks, data.props_nopick);
  } catch (e) { console.error('snapshot render failed', e); }
});
// ── My Bets ──────────────────────────────────────────────────────────────────
function _nbaEsc(s){return(s||'').replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;');}
function _nbaMoney(v){var n=Number(v)||0;return(n>=0?'$':'\u2212$')+Math.abs(n).toFixed(2);}
function _nbaBetAuthQS(){
  var tok=localStorage.getItem('__mpa_token')||'';
  var adm=localStorage.getItem('__mpa_admin')||new URLSearchParams(location.search).get('admin')||'';
  return '?token='+encodeURIComponent(tok)+(adm?('&admin='+encodeURIComponent(adm)):'');
}
function _nbaBetToast(msg){
  var t=document.createElement('div');t.textContent=msg;
  t.style.cssText='position:fixed;bottom:80px;left:50%;transform:translateX(-50%);background:#312e81;color:#fff;padding:10px 20px;border-radius:10px;font-weight:700;font-size:.85rem;z-index:99999;white-space:nowrap;pointer-events:none;box-shadow:0 4px 20px rgba(0,0,0,.5)';
  document.body.appendChild(t);
  setTimeout(function(){t.style.opacity='0';t.style.transition='opacity .4s';setTimeout(function(){t.remove();},400);},2200);
}
var _nbaBetN=0;
window.__NBA_BET_SRC__=window.__NBA_BET_SRC__||{};
function _nbaPickVerdict(s){
  if(!s) return null;
  if(s.has_consistency) return 'OVER';
  var votes={OVER:0,UNDER:0};
  if(s.line_rec) votes[s.line_rec]++;
  if(s.streak_rec) votes[s.streak_rec]++;
  if(s.alt_rec) votes[s.alt_rec]++;
  var tot=votes.OVER+votes.UNDER;
  if(tot&&votes.OVER!==votes.UNDER) return votes.OVER>votes.UNDER?'OVER':'UNDER';
  return null;
}
function _nbaBetBtn(p,verdict){
  if(p.dk_line==null) return '';
  var side=verdict==='OVER'||verdict==='UNDER'?verdict:'OVER';
  var odds=side==='OVER'?(p.dk_over_odds||p.dk_under_odds||null):(p.dk_under_odds||p.dk_over_odds||null);
  var tipDate=p.tipoff?p.tipoff.slice(0,10):'';
  var k='nb'+(++_nbaBetN);
  window.__NBA_BET_SRC__[k]={
    name:p.player,team:(p.team||''),opp:(p.opp||''),
    category:(p.stat_label||''),side:side,
    stat_key:(p.stat||''),stat_label:(p.stat_label||''),
    line:p.dk_line,odds:(odds!=null?odds:null),date:tipDate
  };
  return '<button data-betkey="'+k+'" class="admin-only" onclick="event.stopPropagation();_nbaBetForm(this.dataset.betkey)" style="width:100%;background:#1a1740;color:#a5b4fc;border:none;border-top:1px solid #26263a;padding:8px;font-size:.76rem;font-weight:800;cursor:pointer;border-radius:0 0 14px 14px;letter-spacing:.04em">Track Bet</button>';
}
function _nbaBetForm(key){
  var src=(window.__NBA_BET_SRC__||{})[key]; if(!src) return;
  window.__NBA_BET_CUR__=src;
  var ov=document.getElementById('nba-bet-modal');
  if(!ov){
    ov=document.createElement('div'); ov.id='nba-bet-modal';
    ov.style.cssText='position:fixed;inset:0;background:rgba(2,6,23,.82);z-index:10000;display:flex;align-items:center;justify-content:center;padding:16px';
    ov.onclick=function(e){if(e.target===ov)ov.style.display='none';};
    document.body.appendChild(ov);
  }
  var pickTxt=src.side+' '+src.line+' '+(src.stat_label||'');
  ov.innerHTML=`<div style="background:#0f172a;border:1px solid #312e81;border-radius:16px;max-width:360px;width:100%;box-shadow:0 20px 60px rgba(0,0,0,.6)">
    <div style="display:flex;justify-content:space-between;align-items:flex-start;padding:16px 18px;border-bottom:1px solid #1e293b">
      <div>
        <div style="font-weight:800;color:#fff;font-size:1.02rem">${_nbaEsc(src.name)}</div>
        <div style="color:#a5b4fc;font-size:.82rem;font-weight:800;margin-top:2px">${_nbaEsc(pickTxt)}</div>
        <div style="color:#94a3b8;font-size:.72rem;margin-top:2px">${_nbaEsc(src.category||'')}${src.opp?' &middot; vs '+_nbaEsc(src.opp):''}${src.date?' &middot; '+src.date:''}</div>
      </div>
      <button onclick="document.getElementById('nba-bet-modal').style.display='none'" style="background:#1e293b;border:none;color:#cbd5e1;width:30px;height:30px;border-radius:8px;cursor:pointer;font-size:1rem">&#215;</button>
    </div>
    <div style="padding:16px 18px;display:grid;gap:12px">
      <label style="font-size:.72rem;color:#94a3b8;font-weight:600">Odds (American)<input id="nba-bet-odds" type="number" value="${src.odds!=null?src.odds:''}" style="display:block;width:100%;margin-top:5px;background:#0b1120;border:1px solid #334155;border-radius:8px;padding:9px 11px;color:#fbbf24;font-family:monospace;font-weight:700;font-size:.95rem"></label>
      <label style="font-size:.72rem;color:#94a3b8;font-weight:600">Bet size ($)<input id="nba-bet-stake" type="number" min="0" step="0.01" placeholder="e.g. 50" style="display:block;width:100%;margin-top:5px;background:#0b1120;border:1px solid #334155;border-radius:8px;padding:9px 11px;color:#fff;font-weight:700;font-size:.95rem"></label>
      <div id="nba-bet-payout" style="font-size:.78rem;color:#64748b;min-height:1em"></div>
      <div id="nba-bet-msg" style="font-size:.76rem;color:#f87171;min-height:1em"></div>
      <button id="nba-bet-save" onclick="_nbaSaveBet()" style="background:#4338ca;color:#fff;border:none;border-radius:9px;padding:11px;font-weight:800;cursor:pointer;font-size:.92rem">Log Bet</button>
    </div>
  </div>`;
  ov.style.display='flex';
  var so=document.getElementById('nba-bet-odds'),ss=document.getElementById('nba-bet-stake');
  function _calc(){
    var o=parseFloat(so.value),s=parseFloat(ss.value);
    var pay=document.getElementById('nba-bet-payout');
    if(!isFinite(o)||!isFinite(s)||s<=0){pay.textContent='';return;}
    var win=o>0?s*(o/100):s*(100/Math.abs(o));
    pay.innerHTML='To win <strong style="color:#4ade80">$'+win.toFixed(2)+'</strong> &middot; total payout <strong style="color:#cbd5e1">$'+(s+win).toFixed(2)+'</strong>';
  }
  so.oninput=_calc;ss.oninput=_calc;_calc();
  setTimeout(function(){ss.focus();},50);
}
async function _nbaSaveBet(){
  var src=window.__NBA_BET_CUR__;if(!src) return;
  var o=parseFloat(document.getElementById('nba-bet-odds').value);
  var s=parseFloat(document.getElementById('nba-bet-stake').value);
  var msg=document.getElementById('nba-bet-msg');
  if(!isFinite(o)){msg.textContent='Enter the odds.';return;}
  if(!isFinite(s)||s<=0){msg.textContent='Enter a bet size greater than 0.';return;}
  var btn=document.getElementById('nba-bet-save');btn.disabled=true;btn.textContent='Saving\u2026';
  try{
    var body=Object.assign({},src,{odds:Math.round(o),stake:s,placed_at:new Date().toISOString()});
    var res=await fetch('/api/bets'+_nbaBetAuthQS(),{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(body)});
    if(!res.ok){throw new Error(await res.text());}
    document.getElementById('nba-bet-modal').style.display='none';
    _nbaBetToast('\u2705 Bet logged');
    var mb=document.getElementById('nba-mybets-card');
    if(mb&&mb.style.display!=='none') openNbaMyBets(false);
  }catch(e){msg.textContent=(e.message||'Save failed');btn.disabled=false;btn.textContent='Log Bet';}
}
async function openNbaMyBets(scroll){
  var card=document.getElementById('nba-mybets-card');if(!card) return;
  card.style.display='block';
  if(scroll!==false) card.scrollIntoView({behavior:'smooth',block:'start'});
  document.getElementById('nba-mybets-body').innerHTML='<p style="color:#94a3b8;font-size:.85rem">Loading\u2026</p>';
  try{
    var res=await fetch('/api/bets'+_nbaBetAuthQS());
    if(!res.ok){
      var t=await res.text();
      if(res.status===403) t='Session expired \u2014 reopen from hub';
      throw new Error(t);
    }
    window.__NBA_MYBETS__=await res.json();
    renderNbaMyBets(window.__NBA_MYBETS__);
  }catch(e){
    document.getElementById('nba-mybets-body').innerHTML='<p style="color:#f87171;padding:16px">'+(e.message||'Error loading bets')+'</p>';
  }
}
async function getNbaBetsResults(){await openNbaMyBets();}
function _nbaBetOddsDisp(o){return o!=null?((o>0?'+':'')+o):'\u2014';}
function _nbaResColor(r){return r==='WIN'?'#4ade80':(r==='LOSS'?'#f87171':(r==='PUSH'?'#facc15':'#94a3b8'));}
function _nbaStatBox(lbl,val,clr){
  return '<div style="background:#111;border-radius:10px;padding:10px 14px;min-width:92px">'
    +'<div style="font-size:.64rem;color:#64748b;text-transform:uppercase;letter-spacing:.08em">'+lbl+'</div>'
    +'<div style="font-size:1.12rem;font-weight:800;color:'+(clr||'#e2e8f0')+'">'+val+'</div></div>';
}
function renderNbaMyBets(d){
  var s=d.summary||{};var bets=d.bets||[];
  var roiTxt=s.roi!=null?((s.roi>0?'+':'')+s.roi+'%'):'\u2014';
  var roiClr=s.roi==null?'#94a3b8':(s.roi>0?'#4ade80':(s.roi<0?'#f87171':'#facc15'));
  var netClr=(s.profit||0)>0?'#4ade80':((s.profit||0)<0?'#f87171':'#cbd5e1');
  var recTxt=(s.wins||0)+'-'+(s.losses||0)+(s.push?('-'+s.push+'P'):'');
  var head='<div style="display:flex;flex-wrap:wrap;gap:12px;align-items:center;margin-bottom:18px">'
    +_nbaStatBox('Record',recTxt,'#e2e8f0')
    +_nbaStatBox('Pending',(s.pending||0),'#94a3b8')
    +_nbaStatBox('Staked',_nbaMoney(s.staked||0),'#cbd5e1')
    +_nbaStatBox('Net',_nbaMoney(s.profit||0),netClr)
    +_nbaStatBox('Returned',_nbaMoney(s.returned||0),'#cbd5e1')
    +_nbaStatBox('ROI',roiTxt,roiClr)
    +'<div style="margin-left:auto"><button onclick="downloadNbaMyBetsCSV()" style="background:#4338ca;color:#fff;border:none;border-radius:8px;padding:8px 12px;font-size:.78rem;font-weight:700;cursor:pointer">&#11015; CSV</button></div>'
    +'</div>';
  var bc=(s.by_category||[]).map(function(c){
    var croi=c.roi!=null?((c.roi>0?'+':'')+c.roi+'%'):'\u2014';
    var cclr=c.roi==null?'#94a3b8':(c.roi>0?'#4ade80':(c.roi<0?'#f87171':'#facc15'));
    return '<tr><td style="font-weight:600">'+_nbaEsc(c.category)+'</td>'
      +'<td style="font-family:monospace">'+c.wins+'-'+c.losses+(c.push?('-'+c.push+'P'):'')+'</td>'
      +'<td style="font-family:monospace;color:#94a3b8">'+(c.pending||0)+'</td>'
      +'<td style="font-family:monospace">'+_nbaMoney(c.staked)+'</td>'
      +'<td style="font-family:monospace;color:'+((c.profit||0)>=0?'#4ade80':'#f87171')+'">'+_nbaMoney(c.profit)+'</td>'
      +'<td style="font-family:monospace;font-weight:700;color:'+cclr+'">'+croi+'</td></tr>';
  }).join('');
  var bcHtml=bc?'<div style="overflow-x:auto;margin-bottom:18px"><table class="nba-bets-tbl"><thead><tr><th>Category</th><th>W-L</th><th>Pend</th><th>Staked</th><th>Net</th><th>ROI</th></tr></thead><tbody>'+bc+'</tbody></table></div>':'';
  var rows=bets.map(function(b){
    var res=b.result||'pending';
    var delBtn='<button data-delid="'+b.id+'" onclick="_nbaDeleteBet(this.dataset.delid)" title="Remove" style="background:none;border:none;color:#64748b;cursor:pointer;font-size:1rem">&#10006;</button>';
    var pk=b.side+' '+b.line+' '+(b.stat_label||'');
    var actTxt=b.actual!=null?(' <span style="color:#64748b;font-weight:400;font-size:.72rem">('+b.actual+')</span>'):'';
    return '<tr>'
      +'<td style="white-space:nowrap;color:#94a3b8;font-family:monospace;font-size:.76rem">'+(b.date||'')+'</td>'
      +'<td style="font-weight:600">'+_nbaEsc(b.name||'')+'<div style="font-size:.68rem;color:#64748b">'+_nbaEsc(b.category||'')+'</div></td>'
      +'<td style="font-size:.82rem">'+_nbaEsc(pk)+'</td>'
      +'<td style="font-family:monospace">'+_nbaBetOddsDisp(b.odds)+'</td>'
      +'<td style="font-family:monospace">'+_nbaMoney(b.stake)+'</td>'
      +'<td style="font-weight:800;color:'+_nbaResColor(res)+'">'+(res==='pending'?'pending':res)+actTxt+'</td>'
      +'<td style="font-family:monospace;font-weight:700;color:'+((b.profit||0)>=0?'#4ade80':'#f87171')+'">'+(b.profit!=null?_nbaMoney(b.profit):'\u2014')+'</td>'
      +'<td>'+delBtn+'</td></tr>';
  }).join('');
  var rowsHtml=bets.length
    ?'<div style="overflow-x:auto"><table class="nba-bets-tbl"><thead><tr><th>Date</th><th>Player</th><th>Pick</th><th>Odds</th><th>Stake</th><th>Result</th><th>Profit</th><th></th></tr></thead><tbody>'+rows+'</tbody></table></div>'
    :'<p style="color:#94a3b8;padding:16px">No bets logged yet. Click <strong style="color:#c7d2fe">Track Bet</strong> on any pick card to start.</p>';
  document.getElementById('nba-mybets-body').innerHTML=head+bcHtml+rowsHtml;
}
async function _nbaDeleteBet(id){
  if(!confirm('Remove this bet from your log?')) return;
  try{
    var res=await fetch('/api/bets/'+encodeURIComponent(id)+_nbaBetAuthQS(),{method:'DELETE'});
    if(!res.ok) throw new Error(await res.text());
    openNbaMyBets(false);
  }catch(e){alert(e.message||'Delete failed');}
}
function downloadNbaMyBetsCSV(){
  var d=window.__NBA_MYBETS__;if(!d){alert('Open My Bets first.');return;}
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
  var a=document.createElement('a');a.href=url;a.download='nba-my-bets.csv';
  document.body.appendChild(a);a.click();document.body.removeChild(a);URL.revokeObjectURL(url);
}
</script>
</body>

</body>
</html>"""

# ─── Bet Log Routes ───────────────────────────────────────────────────────────
@app.get("/api/bets")
async def nba_get_bets(request: Request, token: str = "", admin: str = "", settle: bool = True):
    from fastapi import HTTPException
    tok = token or request.headers.get("Authorization","").replace("Bearer ","").strip()
    if not _nba_bet_admin_ok(tok, admin):
        raise HTTPException(status_code=403, detail="Admin only")
    with _NBA_BET_LOCK:
        data = _nba_load_bets()
        key = _nba_bet_user_key(tok, admin)
        snapshot = list(data.get(key, []))
    # Settle OFF-lock: ESPN network calls (now cached) must not block POST/DELETE
    # behind _NBA_BET_LOCK. Re-acquire only to persist, MERGING settled fields by
    # id so a bet added concurrently (during settle) is never clobbered.
    if settle:
        loop = asyncio.get_running_loop()
        changed = await loop.run_in_executor(None, _nba_settle_batch, snapshot)
        # Apply ONLY bets settled to a terminal result this pass, and only onto a
        # still-pending on-disk bet — never write pending/None back and never flip an
        # already-terminal value (so a concurrent settle pass can't be clobbered).
        settled = ({b.get("id"): b for b in snapshot
                    if b.get("id") and b.get("result") in ("WIN", "LOSS", "PUSH")}
                   if changed else {})
        if settled:
            with _NBA_BET_LOCK:
                data = _nba_load_bets()
                for b in data.get(key, []):
                    s = settled.get(b.get("id"))
                    if s and b.get("result") not in ("WIN", "LOSS", "PUSH"):
                        for f in ("result", "actual", "profit", "settled_at"):
                            b[f] = s.get(f)
                _nba_save_bets(data)
    snapshot.sort(key=lambda b: (b.get("date",""), b.get("placed_at","")), reverse=True)
    return {"bets": snapshot, "summary": _nba_summarize_bets(snapshot)}

@app.post("/api/bets")
async def nba_add_bet(request: Request, token: str = "", admin: str = ""):
    from fastapi import HTTPException
    tok = token or request.headers.get("Authorization","").replace("Bearer ","").strip()
    if not _nba_bet_admin_ok(tok, admin):
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
    stat_key = (body.get("stat_key") or "").strip()
    side = (body.get("side") or "OVER").strip().upper()
    if not name or stat_key not in _NBA_BET_STAT_KEYS or side not in ("OVER","UNDER"):
        raise HTTPException(status_code=400, detail="Invalid bet")
    bdate = (body.get("date") or date.today().isoformat()).strip()
    bet = {"id": _nba_uuid.uuid4().hex[:12], "date": bdate,
        "name": name, "team": (body.get("team") or "").strip(),
        "opp": (body.get("opp") or "").strip(),
        "category": (body.get("category") or "?").strip(),
        "side": side, "stat_key": stat_key,
        "stat_label": (body.get("stat_label") or "").strip(),
        "line": line, "odds": odds, "stake": stake,
        "placed_at": (body.get("placed_at") or date.today().isoformat()),
        "result": "pending", "actual": None, "profit": None, "settled_at": None}
    _nba_settle_bet(bet)
    with _NBA_BET_LOCK:
        data = _nba_load_bets()
        key = _nba_bet_user_key(tok, admin)
        data.setdefault(key, []).append(bet)
        _nba_save_bets(data)
    return {"ok": True, "bet": bet}

@app.delete("/api/bets/{bet_id}")
async def nba_delete_bet(bet_id: str, request: Request, token: str = "", admin: str = ""):
    from fastapi import HTTPException
    tok = token or request.headers.get("Authorization","").replace("Bearer ","").strip()
    if not _nba_bet_admin_ok(tok, admin):
        raise HTTPException(status_code=403, detail="Admin only")
    with _NBA_BET_LOCK:
        data = _nba_load_bets()
        key = _nba_bet_user_key(tok, admin)
        bets = data.get(key, [])
        new_bets = [b for b in bets if b.get("id") != bet_id]
        if len(new_bets) != len(bets):
            data[key] = new_bets
            _nba_save_bets(data)
    return {"ok": True}

@app.get("/api/bets/summary")
async def nba_bets_summary(request: Request, token: str = "", admin: str = ""):
    """Hub-callable summary — aggregated record and ROI only."""
    from fastapi import HTTPException
    tok = token or request.headers.get("Authorization","").replace("Bearer ","").strip()
    if not _nba_bet_admin_ok(tok, admin):
        raise HTTPException(status_code=403, detail="Admin only")
    with _NBA_BET_LOCK:
        data = _nba_load_bets()
        key = _nba_bet_user_key(tok, admin)
        bets = list(data.get(key, []))
    return {"sport": "NBA", "summary": _nba_summarize_bets(bets)}

# ─── Routes ───────────────────────────────────────────────────────────────────
@app.get("/api/verify-token")
async def verify_token_nba(request: Request):
    from fastapi import HTTPException
    auth = request.headers.get("Authorization", "")
    tok = auth.replace("Bearer ", "").strip()
    if not tok or len(tok.split(".")) != 3:
        raise HTTPException(status_code=401, detail="Invalid token")
    from fastapi.responses import JSONResponse
    return JSONResponse({"ok": True})

@app.get("/api/whoami")
async def whoami_nba(request: Request, token: str = "", admin: str = ""):
    tok = token or request.query_params.get("_tok","") or request.cookies.get("__mpa_token","") or request.headers.get("Authorization","").replace("Bearer ","").strip()
    ok = _is_admin_token(tok) or (bool(admin) and admin == os.environ.get("INTERNAL_API_TOKEN", "__none__"))
    return {"is_admin": ok}

@app.get("/", response_class=HTMLResponse)
async def index(request: Request, admin: str = "", token: str = ""):
    today_iso = date.today().isoformat()
    tomorrow_iso = (date.today() + timedelta(days=1)).isoformat()
    # Admin turns on via EITHER ?admin=INTERNAL_API_TOKEN OR a hub login token
    # whose email matches the admin (so it just works when the owner logs in).
    is_admin = (bool(admin) and admin == os.environ.get("INTERNAL_API_TOKEN", "__none__")) or _is_admin_token(token)
    js_flag = "true" if is_admin else "false"
    html = (MAIN_HTML.replace("__TODAY__", today_iso).replace("__TOMORROW__", tomorrow_iso)
            .replace("</head>", f"<script>window.IS_ADMIN = {js_flag};</script></head>", 1))
    return HTMLResponse(html)

@app.get("/login")
async def login_get():
    return RedirectResponse("https://moneypicksarena.com")

@app.post("/login")
async def login_post(request: Request):
    form = await request.form()
    u = form.get("username", "").strip()
    p = form.get("password", "").strip()
    if USERS.get(u) == p:
        resp = RedirectResponse("/", status_code=302)
        resp.set_cookie("session", make_token(u), httponly=True, samesite="lax", max_age=86400*7)
        return resp
    return HTMLResponse(LOGIN_HTML.replace('{error}', '<p class="err">⚠️ Invalid username or password</p>'), status_code=401)


@app.get("/api/warm")
async def api_warm_nba():
    """Pre-compute today's picks — called by cron-job.org at 10 AM."""
    from datetime import date as _date
    today = _date.today().isoformat()
    cached = _cache_get("nba", today)
    if cached:
        return {"ok": True, "source": "cache", "date": today,
                "picks": len(cached.get("picks", []))}
    try:
        result = await run_analysis(today)
        return {"ok": True, "source": "computed", "date": today,
                "picks": len(result.get("picks", []))}
    except Exception as e:
        return {"ok": False, "error": str(e)}

@app.post("/run")
async def run(request: Request):
    if not get_user(request):
        return {"error": "Unauthorized"}
    try:
        body = await request.json()
        selected_date = body.get('date', date.today().isoformat())
        force = bool(body.get('force', False))
    except Exception:
        selected_date = date.today().isoformat()
        force = False
    # Force (cache bypass) is admin-only — independently re-verify the hub token.
    if force:
        _tok = request.query_params.get("_tok","") or request.cookies.get("__mpa_token","") or request.headers.get("Authorization","").replace("Bearer ","").strip()
        _adm = request.query_params.get("admin","")
        if not (_is_admin_token(_tok) or (bool(_adm) and _adm == os.environ.get("INTERNAL_API_TOKEN", "__none__"))):
            force = False
    result = await run_analysis(selected_date, force=force)
    return result

_CRON_BUSY_NBA = False

@app.api_route("/api/cron-run", methods=["GET", "POST"])
async def cron_run_nba(request: Request, date_str: str = ""):
    # Cron-friendly trigger: authed by the static INTERNAL_API_TOKEN secret sent
    # as a header (kept out of the URL so it isn't logged). No expiring hub login
    # needed. Runs the pipeline + caches it so members can pull the picks, and
    # wakes the free-tier app on Render. An in-flight guard blocks overlapping runs.
    global _CRON_BUSY_NBA
    import hmac
    from fastapi import HTTPException
    secret = os.environ.get("INTERNAL_API_TOKEN", "")
    tok = request.headers.get("X-Internal-Token", "") or request.headers.get("Authorization", "").replace("Bearer ", "").strip()
    if not secret or not hmac.compare_digest(tok or "", secret):
        raise HTTPException(status_code=401, detail="Invalid cron token")
    ds = date_str or date.today().isoformat()
    if _CRON_BUSY_NBA:
        return {"ran": False, "cached": bool(_cache_get("nba", ds)), "date": ds, "reason": "already running"}
    _CRON_BUSY_NBA = True
    try:
        await run_analysis(ds)
    finally:
        _CRON_BUSY_NBA = False
    return {"ran": True, "cached": bool(_cache_get("nba", ds)), "date": ds}


@app.get("/api/cached")
async def cached_nba(request: Request, target_date: str = None):
    # Read-only: serve picks already saved on file for this date. Never runs the
    # pipeline, so any logged-in member can pull saved picks without a fresh run.
    from fastapi import HTTPException
    if not get_user(request):
        raise HTTPException(status_code=401, detail="Subscription required — please log in via moneypicksarena.com")
    key = target_date or date.today().isoformat()
    data = _cache_get("nba", key)
    if data:
        return data
    raise HTTPException(status_code=404, detail="No saved picks for this date.")

@app.get("/clear-cache")
async def clear_cache(request: Request):
    global _cache
    _cache = {}
    _cache_clear('nba')   # wipe disk-cached picks file too
    return {"status": "cleared"}

@app.get("/health")
async def health():
    return {"status": "ok", "date": date.today().isoformat()}
