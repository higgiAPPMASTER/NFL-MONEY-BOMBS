"""
NFL Money Bombs — main.py
Sportsbook lines: The Odds API
Historical stats:  nfl_data_py (nfl-verse GitHub data — no rate limits)
Schedule:          ESPN scoreboard API
"""

import os, re, asyncio, uuid, time, json, pathlib
from typing import Dict, List, Optional
from datetime import datetime, timedelta, timezone

import httpx
from fastapi import FastAPI, Request, HTTPException
from fastapi.responses import HTMLResponse, JSONResponse
from jose import jwt as jose_jwt

# ── Config ─────────────────────────────────────────────────────────────────────
ODDS_API_KEY  = os.environ.get("ODDS_API_KEY", "")
ODDS_BASE     = "https://api.the-odds-api.com/v4"
JWT_SECRET    = os.environ.get("JWT_SECRET", "")
# Current NFL season + previous one, computed automatically (season year rolls
# over in September — so in Jan 2026 the "current" season is 2025).
_now_utc      = datetime.now(timezone.utc)
_cur_season   = _now_utc.year if _now_utc.month >= 9 else _now_utc.year - 1
NFL_SEASONS   = [_cur_season, _cur_season - 1]

PROP_MARKETS = [
    # passing
    "player_pass_yds", "player_pass_tds", "player_pass_completions",
    "player_pass_attempts", "player_pass_interceptions",
    # rushing
    "player_rush_yds", "player_rush_attempts", "player_anytime_td",
    # receiving
    "player_reception_yds", "player_receptions",
    # defense
    "player_tackles_assists", "player_sacks", "player_defensive_interceptions",
    # kicking
    "player_kicking_points", "player_field_goals",
]
PROP_LABELS = {
    "player_pass_yds":"Pass Yds", "player_pass_tds":"Pass TDs",
    "player_pass_completions":"Completions", "player_pass_attempts":"Pass Att",
    "player_pass_interceptions":"INT Thrown",
    "player_rush_yds":"Rush Yds", "player_rush_attempts":"Rush Att",
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
_BOOK_LABEL = {"bet99":"Bet99","thescore":"theScore","bet365":"Bet365","draftkings":"DK",
               "fanduel":"FanDuel","betmgm":"BetMGM","caesars":"Caesars",
               "williamhill_us":"Caesars","betrivers":"BetRivers","ballybet":"Bally Bet",
               "espnbet":"ESPN BET","fliff":"Fliff","mybookieag":"MyBookie",
               "betonlineag":"BetOnline","bovada":"Bovada"}

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

# ── File cache ─────────────────────────────────────────────────────────────────
_CACHE_DIR = pathlib.Path("/tmp/mpa_cache")
_CACHE_DIR.mkdir(parents=True, exist_ok=True)
_CACHE_TTL = 6 * 3600

def _is_past_date(date_key) -> bool:
    """Past dates are FINAL — historical odds/results never change, so their
    caches never expire. (Historical Odds API calls cost 10x live ones, so
    re-buying the same finished lines burns credits for nothing.)"""
    try:
        return str(date_key) < datetime.now(timezone.utc).strftime("%Y-%m-%d")
    except Exception:
        return False

def _cache_get(date_key):
    p = _CACHE_DIR / f"nfl_{date_key}.json"
    try:
        if p.exists() and (_is_past_date(date_key)
                           or (time.time() - p.stat().st_mtime) < _CACHE_TTL):
            return json.loads(p.read_text(encoding="utf-8"))
    except: pass
    return None

def _cache_set(date_key, result):
    try:
        (_CACHE_DIR / f"nfl_{date_key}.json").write_text(
            json.dumps(result, ensure_ascii=False), encoding="utf-8")
    except: pass

# Odds-layer cache: stores the raw Odds API prop lines per date so re-runs
# (forced re-rank, runs after the result cache expires) reuse the odds already
# pulled instead of hitting the Odds API again. Shorter TTL than the result
# cache so lines still refresh over the day. Cleared by /api/clear-cache (which
# globs nfl_*.json), so a true fresh run still re-pulls.
_ODDS_TTL = 6 * 3600  # match the 6h result cache — both expire together

def _odds_cache_get(date_key):
    """Returns (props_list, game_lines_by_id) or (None, None) on miss.
    Handles the old list-only format for backward compat."""
    p = _CACHE_DIR / f"nfl_odds_{date_key}.json"
    try:
        if p.exists() and (_is_past_date(date_key)
                           or (time.time() - p.stat().st_mtime) < _ODDS_TTL):
            print(f"[OddsCache] HIT nfl/{date_key}")
            raw = json.loads(p.read_text(encoding="utf-8"))
            if isinstance(raw, dict) and "props" in raw:
                return raw["props"], raw.get("game_lines", {})
            return raw, {}   # old list-only format
    except Exception as e:
        print(f"[OddsCache] read error: {e}")
    return None, None

def _odds_cache_set(date_key, props, game_lines):
    try:
        (_CACHE_DIR / f"nfl_odds_{date_key}.json").write_text(
            json.dumps({"props": props, "game_lines": game_lines}, ensure_ascii=False),
            encoding="utf-8")
        print(f"[OddsCache] SET nfl/{date_key} ({len(props)} props, {len(game_lines)} games)")
    except Exception as e:
        print(f"[OddsCache] write error: {e}")

# ── nfl_data_py stats loader ───────────────────────────────────────────────────
_nfl_df = None
_nfl_df_lock = asyncio.Lock()
_NFL_PKL      = _CACHE_DIR / "nfl_df_cache_v3.pkl"  # v3: ESPN team codes + scorer-only anytime_td

# nfl-verse team codes that differ from ESPN's (ESPN is what the schedule,
# H/A lookup and card display all use). Normalized ONCE at data load so every
# comparison in the app speaks the same language. Without this, LAR/WSH
# players look "traded" (wrong team + wrong home/away on cards, starters
# evicted by mislabeled players) and their vs-opponent history comes up empty.
_NFLVERSE_TO_ESPN = {"LA": "LAR", "WAS": "WSH"}
_NFL_PKL_TTL  = 20 * 3600  # 20h — refresh once a day

# ── ESPN H/A Lookup — (season, week, team_abbr) → 'HOME' or 'AWAY' ───────────
_HA_LOOKUP: dict = {}
_HA_LOADED = False
_HA_LOCK   = asyncio.Lock()

_HA_CACHE_FILE = _CACHE_DIR / "nfl_ha_lookup.json"

async def _build_ha_lookup():
    """Build home/away lookup from ESPN historical schedules (18 weeks x 5 seasons).
    Result is persisted to disk so subsequent requests within the same dyno instance
    skip the 90-request ESPN fetch entirely."""
    global _HA_LOOKUP, _HA_LOADED
    async with _HA_LOCK:
        if _HA_LOADED:
            return
        # Try disk cache first — survives spin-down within the same deploy
        try:
            if _HA_CACHE_FILE.exists():
                raw = json.loads(_HA_CACHE_FILE.read_text(encoding="utf-8"))
                _HA_LOOKUP = {tuple(int(x) if x.isdigit() else x for x in k.split("|")): v
                              for k, v in raw.items()}
                _HA_LOADED = True
                print(f"[H/A] Loaded from disk cache: {len(_HA_LOOKUP)} entries")
                return
        except Exception as e:
            print(f"[H/A] Disk cache load failed: {e}")

        print("[H/A] Building home/away lookup from ESPN schedules (90 requests)…")
        sem = asyncio.Semaphore(15)
        async def fetch_week(season, week):
            async with sem:
                try:
                    async with httpx.AsyncClient(timeout=8) as c:
                        r = await c.get(
                            "https://site.api.espn.com/apis/site/v2/sports/football/nfl/scoreboard",
                            params={"seasontype":2,"week":week,"season":season})
                        for ev in r.json().get("events",[]):
                            comp = ev.get("competitions",[{}])[0]
                            for t in comp.get("competitors",[]):
                                abbr = t["team"].get("abbreviation","")
                                ha   = "HOME" if t["homeAway"]=="home" else "AWAY"
                                if abbr:
                                    _HA_LOOKUP[(season, week, abbr)] = ha
                except Exception:
                    pass
        pairs = [(s, w) for s in NFL_SEASONS for w in range(1, 19)]
        await asyncio.gather(*[fetch_week(s, w) for s, w in pairs])
        _HA_LOADED = True
        print(f"[H/A] Built lookup: {len(_HA_LOOKUP)} entries")
        # Persist to disk so the next request skips this step
        try:
            serializable = {f"{s}|{w}|{a}": v for (s, w, a), v in _HA_LOOKUP.items()}
            _HA_CACHE_FILE.write_text(json.dumps(serializable), encoding="utf-8")
            print(f"[H/A] Saved to disk cache")
        except Exception as e:
            print(f"[H/A] Disk cache save failed: {e}")

# Direct nfl-verse CSV URLs (no package needed)
_NFL_CSV_URL  = "https://github.com/nflverse/nflverse-data/releases/download/player_stats/player_stats_{year}.csv"
_NFL_DEF_URL  = "https://github.com/nflverse/nflverse-data/releases/download/player_stats/player_stats_def_{year}.csv"
_NFL_KICK_URL = "https://github.com/nflverse/nflverse-data/releases/download/player_stats/player_stats_kicking_{year}.csv"
# nfl-verse retired the per-type player_stats files after 2024. Seasons 2025+
# live in ONE combined weekly file (offense + defense + kicking per player-week).
_NFL_NEW_URL       = "https://github.com/nflverse/nflverse-data/releases/download/stats_player/stats_player_week_{year}.csv"
_NFL_NEW_FMT_START = 2025
_KEEP_COLS   = ["player_display_name","player_id","headshot_url","recent_team","opponent_team",
                "season","week","season_type","rushing_yards","receiving_yards","passing_yards",
                "receptions","targets","passing_tds","rushing_tds","receiving_tds",
                "completions","attempts","interceptions","carries"]

def _dl_csv(url):
    """Download one nfl-verse CSV (regular season only) as a DataFrame.
    Uses httpx with a hard 60-second total timeout so a stalled download
    fails fast instead of hanging forever."""
    import pandas as pd, io
    last_err = None
    for attempt in range(3):   # retry — a single flaky download must not silently
        try:                   # drop a whole season of stats from every pick
            r = httpx.get(url, headers={"User-Agent": "Mozilla/5.0"}, timeout=60, follow_redirects=True)
            r.raise_for_status()
            break
        except Exception as e:
            last_err = e
            print(f"[NFL Data] download attempt {attempt+1}/3 failed for {url}: {e}")
            time.sleep(2 * (attempt + 1))
    else:
        raise last_err
    d = pd.read_csv(io.BytesIO(r.content), low_memory=False)
    if "season_type" in d.columns:
        d = d[d["season_type"] == "REG"]
    return d

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
            _nfl_df = pickle.loads(_NFL_PKL.read_bytes())
            print(f"[NFL Data] Loaded from disk cache: {len(_nfl_df):,} rows")
            return _nfl_df
    except Exception as e:
        print(f"[NFL Data] Disk cache load failed: {e}")
    print(f"[NFL Data] Downloading stats for seasons {NFL_SEASONS} in parallel from nfl-verse…")
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
        all_tasks = off_urls + def_urls + kick_urls + new_urls

        results: dict = {}
        with ThreadPoolExecutor(max_workers=len(all_tasks)) as ex:
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
            d["tackles_assists"] = col("def_tackles_solo") + col("def_tackle_assists")
            d["def_ints"]        = col("def_interceptions")
            d["kicking_points"]  = col("fg_made") * 3 + col("pat_made")
            extra = ["anytime_td","tackles_assists","def_sacks","def_ints",
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
        print(f"[NFL Data] Total: {len(_nfl_df):,} rows "
              f"(off {len(off):,}"
              + (f", def {len(deff):,}" if deff is not None else "")
              + (f", kick {len(kick):,}" if kick is not None else "") + ")")
        # Persist to disk so spin-down restarts skip the download entirely.
        # ONLY cache a COMPLETE dataset — pickling a partial one (a season's
        # download failed) would serve season-less picks for hours.
        try:
            got_seasons = {int(s) for s in _nfl_df["season"].dropna().unique()}
            if all(y in got_seasons for y in NFL_SEASONS):
                import pickle
                _NFL_PKL.write_bytes(pickle.dumps(_nfl_df))
                print(f"[NFL Data] Saved to disk cache ({_NFL_PKL})")
            else:
                print(f"[NFL Data] NOT caching — missing seasons "
                      f"{sorted(set(NFL_SEASONS) - got_seasons)}; next run retries")
        except Exception as pe:
            print(f"[NFL Data] Disk cache save failed: {pe}")
    except Exception as e:
        print(f"[NFL Data] Error: {e}")
        import traceback; traceback.print_exc()
        _nfl_df = None
    return _nfl_df

async def get_nfl_stats():
    # Fire H/A lookup in background — analysis falls back gracefully when not ready
    if not _HA_LOADED:
        asyncio.create_task(_build_ha_lookup())
    async with _nfl_df_lock:
        if _nfl_df is not None:
            return _nfl_df
        loop = asyncio.get_event_loop()
        try:
            # Hard wall-clock deadline: even a pathological slow-drip download
            # can't hold the job in "running" forever — after 150s we give up
            # and the pipeline returns a clean error the user can retry.
            return await asyncio.wait_for(
                loop.run_in_executor(None, _load_nfl_stats_sync), timeout=150)
        except asyncio.TimeoutError:
            print("[NFL Data] Stats load exceeded 150s deadline — giving up this run")
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
    try:
        async with httpx.AsyncClient(timeout=10) as c:
            r = await c.get(
                "https://site.api.espn.com/apis/site/v2/sports/football/nfl/scoreboard",
                params={"dates": dc})
            if not r.is_success: return []
            games = []
            for ev in r.json().get("events", []):
                comp  = ev.get("competitions", [{}])[0]
                teams = {t["homeAway"]: t["team"] for t in comp.get("competitors", [])}
                home  = teams.get("home", {})
                away  = teams.get("away", {})
                games.append({
                    "id":        "",
                    "home_team": home.get("displayName", ""),
                    "away_team": away.get("displayName", ""),
                    "home_abbr": home.get("abbreviation", ""),
                    "away_abbr": away.get("abbreviation", ""),
                    "game":      f"{away.get('displayName','')} @ {home.get('displayName','')}",
                    # ISO kickoff time — picks carry this so finished games drop off board
                    "start":     ev.get("date", "") or comp.get("date", ""),
                })
            print(f"[ESPN] {len(games)} NFL games for {date_str}")
            return games
    except Exception as e:
        print(f"[ESPN] {e}"); return []

# ── Odds API ───────────────────────────────────────────────────────────────────
async def get_odds_events(date_str: str, espn_games: List[Dict]) -> List[Dict]:
    if not ODDS_API_KEY: return []
    today    = datetime.now(timezone.utc).strftime("%Y-%m-%d")
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
                _match_events(odds_evs)
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

async def get_prop_lines(event_id: str, date_str: str) -> List[Dict]:
    """Fetch player prop lines for one NFL game. Returns a list of prop dicts.
    Kept as a props-only call (PROP_MARKETS only) so it stays within Odds API
    plan market limits. Game-level lines (h2h/totals) are fetched separately."""
    if not event_id or not ODDS_API_KEY: return []
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    is_past = date_str < today
    try:
        async with httpx.AsyncClient(timeout=20) as c:
            if is_past:
                base = f"{ODDS_BASE}/historical/sports/americanfootball_nfl/events/{event_id}/odds"
                params = {"apiKey": ODDS_API_KEY, "regions": "us",
                         "markets": ",".join(PROP_MARKETS), "oddsFormat": "american",
                         "date": f"{date_str}T12:00:00Z"}
            else:
                base = f"{ODDS_BASE}/sports/americanfootball_nfl/events/{event_id}/odds"
                params = {"apiKey": ODDS_API_KEY, "regions": "us",
                         "markets": ",".join(PROP_MARKETS), "oddsFormat": "american"}
            r = await c.get(base, params=params)
            if not r.is_success:
                print(f"[OddsAPI props] {event_id} HTTP {r.status_code}")
                return []
            raw  = r.json()
            data = raw.get("data", raw) if isinstance(raw, dict) and "data" in raw else raw
            if not isinstance(data, dict): return []
            lines = {}
            for bm in data.get("bookmakers", []):
                bkey = bm.get("key", "")
                for mkt in bm.get("markets", []):
                    mk = mkt.get("key", "")
                    if mk not in PROP_MARKETS: continue
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
                        key = f"{_norm(name)}_{mk}"
                        if key not in lines:
                            lines[key] = {"name": name, "market": mk,
                                "label": PROP_LABELS.get(mk, mk),
                                "stat_col": PROP_TO_COL.get(mk, ""),
                                "line": float(point), "over_odds": None, "under_odds": None,
                                "over_book": None, "under_book": None}
                        if abs(float(point) - lines[key]["line"]) > 1e-9:
                            continue
                        if side == "Over":
                            _take_odds(lines[key], "over_odds", "over_book", price, bkey)
                        elif side == "Under":
                            _take_odds(lines[key], "under_odds", "under_book", price, bkey)
            out = list(lines.values())
            for l in out:
                l["over_book"]  = _book_label(l["over_book"])  if l.get("over_book")  else ""
                l["under_book"] = _book_label(l["under_book"]) if l.get("under_book") else ""
            return out
    except Exception as e:
        print(f"[OddsAPI props] {e}"); return []

async def get_nfl_game_lines(event_id: str, date_str: str) -> dict:
    """Fetch moneyline (h2h) + totals for one NFL game — separate call so it
    never competes with the player-prop market quota."""
    if not event_id or not ODDS_API_KEY: return {}
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    is_past = date_str < today
    try:
        async with httpx.AsyncClient(timeout=15) as c:
            if is_past:
                base   = f"{ODDS_BASE}/historical/sports/americanfootball_nfl/events/{event_id}/odds"
                params = {"apiKey": ODDS_API_KEY, "regions": "us",
                          "markets": "h2h,totals", "oddsFormat": "american",
                          "date": f"{date_str}T12:00:00Z"}
            else:
                base   = f"{ODDS_BASE}/sports/americanfootball_nfl/events/{event_id}/odds"
                params = {"apiKey": ODDS_API_KEY, "regions": "us",
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
            return res
    except Exception as e:
        print(f"[GP GameLines] {e}"); return {}

# ── Analysis using nfl_data_py ─────────────────────────────────────────────────
def _ha_side(row, is_home):
    if not _HA_LOADED:
        return True
    key = (int(row["season"]), int(row["week"]), str(row["recent_team"]))
    val = _HA_LOOKUP.get(key)
    if val is None:
        return True
    return val == ("HOME" if is_home else "AWAY")

def _book_tag_nfl(pick, score, gap, under_rate):
    """SUGGESTED when the OVER side has a strong recent hit rate + edge over the
    line; FADE when the UNDER side is strong + the line sits above the average."""
    if pick == "OVER" and score is not None and score >= 65 and (gap or 0) > 0:
        return "SUGGESTED"
    if pick == "UNDER" and score is not None and score >= 65 and (gap or 0) < 0:
        return "FADE"   # score is side-aware — for UNDER picks it already measures under-hits
    return ""


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
    "rushing_yards": "rush D", "carries": "rush D",
    "receiving_yards": "pass D", "receptions": "pass D",
    "anytime_td": "TD D",
}
_DEFF_CACHE: dict = {"df_ref": None, "maps": {}}

def _def_factor_map(df, stat_col: str, n_games: int = 8) -> dict:
    """{team_abbr: (factor, rank)} — factor clamped 0.90-1.10, rank 1 = stingiest
    (allows the LEAST of this stat per game over its last n_games)."""
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
                    f = max(0.90, min(1.10, allowed / lg))
                    out[tm] = (round(f, 3), i + 1)
    except Exception as e:
        print(f"[DefFactor] {stat_col} failed: {e}")
    _DEFF_CACHE["maps"][stat_col] = out
    return out

def _analyze_prop(pl: Dict, df, home_abbr: str, away_abbr: str) -> Optional[Dict]:
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
    mask = df["player_display_name"].str.lower() == name.lower()
    pdf  = df[mask]
    if pdf.empty:
        last = name.split()[-1].lower()
        pdf  = df[df["player_display_name"].str.lower().str.endswith(last)]
    if pdf.empty:
        return None

    # Use MOST RECENT team (not historical mode) so traded players show correct team
    pdf_sorted = pdf.sort_values(["season", "week"], ascending=False) if not pdf.empty else pdf
    recent_team = pdf_sorted["recent_team"].iloc[0] if not pdf_sorted.empty else ""

    # Determine home/away using current game teams first, fall back to historical
    if home_abbr and recent_team == home_abbr:
        opp_abbr = away_abbr; is_home = True;  home_road = "H"; side = "HOME"; game_team = home_abbr
    elif away_abbr and recent_team == away_abbr:
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

    # Career vs opponent (H/A filtered, fallback to all-vs-opp)
    vs_opp_all = pdf[pdf["opponent_team"] == opp_abbr] if opp_abbr else pdf
    if is_home is not None and _HA_LOADED and not vs_opp_all.empty:
        vs_ha = vs_opp_all[vs_opp_all.apply(lambda r: _ha_side(r, is_home), axis=1)]
        vs_opp = vs_ha if not vs_ha.empty else vs_opp_all
    else:
        vs_opp = vs_opp_all

    vs_vals = vs_opp[stat_col].dropna().tolist() if not vs_opp.empty else []
    avg_a   = round(sum(vs_vals)/len(vs_vals), 1) if vs_vals else None
    hits_a  = sum(1 for v in vs_vals if v > line)
    tot_a   = len(vs_vals)
    rate_a  = round(hits_a/tot_a*100, 1) if tot_a >= 1 else None

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

    ref_avg = avg_b if avg_b is not None else avg_a

    # Opponent-defense adjustment: project vs THIS defense, not a neutral one.
    def_factor = 1.0; def_rank = None; def_lbl = _OPP_ADJ_COLS.get(stat_col, "")
    if opp_abbr and stat_col in _OPP_ADJ_COLS:
        _fr = _def_factor_map(df, stat_col).get(opp_abbr)
        if _fr:
            def_factor, def_rank = _fr
    adj_avg = round(ref_avg * def_factor, 1) if ref_avg is not None else None
    def_adj = round((def_factor - 1) * 100)

    gap     = round(adj_avg - line, 1) if adj_avg is not None else None
    # EVERY player with any history gets a pick — a 0.0 average is a real
    # signal (obvious UNDER), not "no data". Ties lean UNDER (book gets the push).
    pick    = None
    if adj_avg is not None:
        pick = "OVER" if adj_avg > line else "UNDER"

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
    score = round(sum(rates)/len(rates), 1) if rates else 0
    tag     = _book_tag_nfl(pick, score, gap, under_rate)

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
        for _, r in vs_opp_all.sort_values(["season", "week"], ascending=False).iterrows():
            try:
                v = r[stat_col]
                if v is None or (isinstance(v, float) and v != v):
                    continue
                vs_opp_log.append({"d": f"{int(r['season'])} W{int(r['week'])}", "v": round(float(v), 1)})
            except Exception:
                continue

    return {
        # identity
        "name": name, "pid": pid, "team": game_team, "opponent": opp_abbr or "--",
        "homeRoad": home_road, "side": side, "head": head, "game": pl.get("game",""),
        "game_start": pl.get("game_start",""),
        # market
        "mkt": label, "label": label, "market": market,
        "line": line, "dispLine": line, "realLine": line,
        "realOdds": pl.get("over_odds"), "realUnderOdds": pl.get("under_odds"),
        "over_odds": pl.get("over_odds"), "under_odds": pl.get("under_odds"),
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
        # opponent-defense adjustment
        "defAdj": def_adj, "defRank": def_rank, "defLbl": def_lbl,
        "projAvg": adj_avg,
        # score / pick
        "score": score, "dispScore": score, "gap": gap, "pick": pick, "tag": tag,
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

# ── NFL Game Predictor helpers ─────────────────────────────────────────────────

def _nfl_team_pts_projection(team_abbr: str, df, n_games: int = 5) -> float:
    """Project a team's offensive point output from their L5 total yards (nfl-verse).
    ~350 total yards per game ≈ league avg 23 pts; clamped 10-45."""
    try:
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

def _nfl_team_def_strength(opp_abbr: str, df, n_games: int = 5) -> float:
    """Defensive strength multiplier (1.0 = league avg, <1 = strong, >1 = weak).
    Measures how many offensive yards opponents piled up against this team."""
    try:
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

def _nfl_starter_name(team_abbr: str, df, col: str = "passing_yards") -> str:
    """Name of the CURRENT starter for this team: latest season only, and only
    players whose most recent game was with this team (excludes traded players
    like Geno Smith whose old-team rows would otherwise win on career volume)."""
    try:
        if col not in df.columns:
            return "TBD"
        latest = int(df["season"].max())
        cur = df[df["season"] == latest]
        team_df = cur[cur["recent_team"] == team_abbr]
        if not team_df.empty:
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
                                      gl_cache: dict = None) -> tuple:
    """Build Game Predictor payload for every game on today's slate.
    Fetches h2h + totals for all games concurrently via get_nfl_game_lines.
    Uses cached game lines when available (past-date lines are final) and
    returns (predictions, newly_fetched_lines_by_event_id) so the caller can
    persist them — every skipped historical call saves 10x-priced credits."""
    HOME_ADJ = 1.05
    predictions = []
    gl_cache = dict(gl_cache or {})
    fetched: dict = {}
    async def _one_gl(g):
        eid = g.get("id", "")
        if eid and eid in gl_cache:
            return gl_cache[eid]
        gl = await get_nfl_game_lines(eid, date_str)
        if eid and gl:
            fetched[eid] = gl
        return gl
    all_gl = await asyncio.gather(*[_one_gl(g) for g in espn_games])
    for g, gl in zip(espn_games, all_gl):
        ha = g.get("home_abbr", ""); aa = g.get("away_abbr", "")
        if not ha or not aa:
            continue
        # Offensive projections (L5 team yards → pts)
        home_off = _nfl_team_pts_projection(ha, df)
        away_off = _nfl_team_pts_projection(aa, df)
        # Defensive strength of each team's OPPONENT
        home_def_str = _nfl_team_def_strength(ha, df)   # how tough home D is (for away offense)
        away_def_str = _nfl_team_def_strength(aa, df)   # how tough away D is (for home offense)
        # Projected score: own offense × opp's defensive resistance × home adj
        proj_home = round(home_off * home_def_str * HOME_ADJ, 1)
        proj_away = round(away_off * away_def_str, 1)
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
        away_sp = _nfl_starter_name(aa, df, "passing_yards")
        home_sp = _nfl_starter_name(ha, df, "passing_yards")
        # Driver phrases
        drivers = []
        if pick_home:
            drivers.append(f"{ha} projects {proj_home} pts vs {aa} projects {proj_away} pts")
        else:
            drivers.append(f"{aa} projects {proj_away} pts vs {ha} projects {proj_home} pts")
        if home_def_str < 0.95:
            drivers.append(f"{ha} defense has allowed fewer yards than average")
        elif away_def_str < 0.95:
            drivers.append(f"{aa} defense has allowed fewer yards than average")
        if value_flag and mkt_edge:
            drivers.append(f"model {pick_abbr} {model_pct}% vs market {mkt_pct}% — +{mkt_edge}% value edge")
        elif mkt_edge is not None:
            drivers.append(f"model {pick_abbr} {model_pct}% vs market {mkt_pct}%")
        predictions.append({
            "away_abbr": aa, "home_abbr": ha,
            "away_sp": away_sp, "home_sp": home_sp,
            "proj_away": proj_away, "proj_home": proj_home, "proj_total": proj_total,
            "win_away": win_away, "win_home": win_home,
            "pick_home": pick_home, "pick_abbr": pick_abbr, "conf": conf,
            "away_ml_odds": away_ml, "home_ml_odds": home_ml,
            "total_line": total_line, "total_pick": total_pick, "total_edge": total_edge,
            "total_over_odds": total_over_odds, "total_under_odds": total_under_odds,
            "mkt_home_pct": mkt_home_pct, "mkt_away_pct": mkt_away_pct,
            "mkt_edge": mkt_edge, "value_flag": value_flag,
            "drivers": drivers, "game_start": g.get("start", ""),
        })
    return predictions, fetched

# ── Pipeline ───────────────────────────────────────────────────────────────────
async def run_pipeline(date_str: str, progress=None) -> Dict:
    def _p(msg):
        print(f"[Pipeline] {msg}")
        if progress:
            try: progress(msg)
            except Exception: pass

    cached = _cache_get(date_str)
    if cached:
        return cached

    # 1. Get game schedule from ESPN
    _p("Fetching NFL schedule from ESPN…")
    espn_games = await get_espn_games(date_str)
    if not espn_games:
        return {"picks":[],"all":[],"error":f"No NFL games found for {date_str} — NFL season runs Sept–Feb. (Note: check the exact date — e.g. Championship Sunday was Jan 26, not Jan 25.)"}

    # 2+3. Odds layer — ONE call per game fetches props + h2h + totals together.
    #      All games are fetched concurrently (asyncio.gather) then cached for 6h.
    #      On a cache hit the result cache (6h) fires first so no API calls happen.
    all_lines, game_lines_by_id = _odds_cache_get(date_str)
    if all_lines is None:
        # 2. Match Odds API event IDs
        _p(f"Matching {len(espn_games)} games with sportsbook events…")
        espn_games = await get_odds_events(date_str, espn_games)

        # 3. Fetch prop lines per game
        all_lines = []
        for gi, ev in enumerate(espn_games):
            ev_id = ev.get("id", "")
            _p(f"Fetching prop lines — game {gi+1}/{len(espn_games)}: {ev.get('game','')}…")
            lines = await get_prop_lines(ev_id, date_str) if ev_id else []
            home_abbr = ev.get("home_abbr", "") or _name_to_abbr(ev.get("home_team",""))
            away_abbr = ev.get("away_abbr", "") or _name_to_abbr(ev.get("away_team",""))
            for l in lines:
                l["home_team"] = ev.get("home_team","")
                l["away_team"] = ev.get("away_team","")
                l["home_abbr"] = home_abbr
                l["away_abbr"] = away_abbr
                l["game"]      = ev.get("game","")
                l["game_start"]= ev.get("start","")
            all_lines.extend(lines)
        if all_lines:
            _odds_cache_set(date_str, all_lines, {})

    if not all_lines:
        today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
        if date_str < today:
            msg = f"No prop data found for {date_str} — the Odds API may not have archived lines for these games."
        else:
            msg = "No prop lines available yet — check back closer to game time"
        return {"picks":[],"all":[],"games":len(espn_games),"error":msg}

    # 4. Load NFL stats (nfl_data_py — downloads once, cached in memory)
    _p(f"Loading player stats ({len(all_lines)} props to analyze) — first run after deploy downloads ~20s…")
    df = await get_nfl_stats()
    if df is None:
        return {"picks":[],"all":[],"error":"Could not load NFL stats data — try again in a moment"}

    # 5. Analyze props synchronously (pandas is fast, no I/O)
    _p(f"Analyzing {len(all_lines)} player prop histories…")
    all_results = []
    for pl in all_lines:
        result = _analyze_prop(pl, df, pl.get("home_abbr",""), pl.get("away_abbr",""))
        if result:
            all_results.append(result)

    # 6. Starter filter — for EVERY market keep only the player per team with the
    # highest career volume in that stat column (the starter / primary option).
    # If only one player per team appears for a market they are kept regardless.
    # This removes backups, 3rd-string RBs, etc. across all categories.
    def _starter_score(r):
        try:
            nm  = r["name"].lower()
            col = PROP_TO_COL.get(r.get("market",""), "")
            if not col or col not in df.columns:
                return 0
            mask = df["player_display_name"].str.lower() == nm
            return float(df[mask][col].fillna(0).sum())
        except Exception:
            return 0

    _scored = [(r, _starter_score(r)) for r in all_results]
    _team_mkt_best: dict = {}
    for r, score in _scored:
        key = (r.get("team",""), r.get("mkt",""))
        if key not in _team_mkt_best or score > _team_mkt_best[key][1]:
            _team_mkt_best[key] = (r, score)
    all_results = [v[0] for v in _team_mkt_best.values()]

    picks   = sorted([r for r in all_results if r.get("pick")],
                     key=lambda x: abs(x.get("gap") or 0), reverse=True)
    games_out = [{"home_team":g.get("home_team",""), "away_team":g.get("away_team",""),
                  "home_abbr":g.get("home_abbr",""), "away_abbr":g.get("away_abbr",""),
                  "game":g.get("game","")} for g in espn_games]
    # 7. Game Predictor — fetches h2h + totals concurrently (separate calls from props
    #    so player-prop market quota is never shared with game-level markets)
    _p("Building game predictions…")
    game_predictions, new_gl = await _build_nfl_game_predictions(
        espn_games, df, date_str, game_lines_by_id)
    if new_gl:
        # Persist freshly-bought game lines so re-runs never re-buy them
        merged_gl = {**(game_lines_by_id or {}), **new_gl}
        _odds_cache_set(date_str, all_lines, merged_gl)
    _p("Finishing up…")
    # Data health: if a whole season failed to download, SAY so on screen —
    # picks silently built from old seasons look like nonsense stats.
    data_warning = ""
    try:
        loaded_seasons = sorted({int(s) for s in df["season"].dropna().unique()})
        missing = [y for y in NFL_SEASONS if y not in loaded_seasons]
        if missing:
            data_warning = ("⚠️ " + ", ".join(map(str, missing)) +
                            " season stats failed to download — picks below use only " +
                            ", ".join(map(str, loaded_seasons)) +
                            " data. Tap Force Refresh to retry.")
    except Exception:
        pass

    result  = {"picks":picks, "all":all_results, "date":date_str,
               "games":games_out, "qualified":len(picks),
               "data_warning": data_warning,
               "game_predictions": game_predictions}
    _cache_set(date_str, result)
    _nfl_save_picks_snapshot(date_str, result)
    try:
        from replit_push import push_picks_to_replit
        push_picks_to_replit("nfl", result)
    except Exception as _e:
        print(f"[replit_push] nfl push failed: {_e}")
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
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    cached = _cache_get(today)
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

_CRON_BUSY_NFL = False

@app.api_route("/api/cron-run", methods=["GET", "POST"])
async def cron_run_nfl(request: Request, date_str: str = ""):
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
    ds = date_str or datetime.now(timezone.utc).strftime("%Y-%m-%d")
    if _CRON_BUSY_NFL:
        return {"ran": False, "cached": bool(_cache_get(ds)), "date": ds, "reason": "already running"}
    _CRON_BUSY_NFL = True
    try:
        await run_pipeline(ds)
    finally:
        _CRON_BUSY_NFL = False
    return {"ran": True, "cached": bool(_cache_get(ds)), "date": ds}


@app.post("/api/run")
async def api_run(request: Request):
    body     = await request.json() if request.headers.get("content-type","").startswith("application/json") else {}
    tok = body.get("token","") or request.headers.get("Authorization","").replace("Bearer ","").strip()
    if not _verify_hub_token(tok):
        raise HTTPException(status_code=401, detail="Subscription required — please log in via moneypicksarena.com")
    date_str = body.get("date", datetime.now(timezone.utc).strftime("%Y-%m-%d"))
    job_id   = str(uuid.uuid4())[:8]
    JOBS[job_id] = {"status":"running","result":None,"error":None,"progress":"Starting…"}
    async def _run():
        try:
            # Job-level watchdog: no matter what hangs inside, the job always
            # resolves to done/error within 5 minutes so the UI never spins forever.
            result = await asyncio.wait_for(
                run_pipeline(date_str,
                    progress=lambda m: JOBS.get(job_id, {}).update({"progress": m})),
                timeout=300)
            JOBS[job_id].update({"status":"done","result":result})
        except asyncio.TimeoutError:
            JOBS[job_id].update({"status":"error",
                "error":"Run timed out after 5 minutes — the data sources may be slow right now. Please try again."})
        except Exception as e:
            JOBS[job_id].update({"status":"error","error":str(e)})
    asyncio.create_task(_run())
    return {"job_id": job_id}

@app.get("/api/run/{job_id}")
async def api_poll(job_id: str):
    job = JOBS.get(job_id)
    if not job: raise HTTPException(404, "Job not found")
    return job

@app.get("/api/cached")
async def api_cached(request: Request, target_date: str = "", token: str = ""):
    # Read-only: serve picks already saved on file. Never runs the pipeline, so any
    # logged-in member can pull the latest saved picks without triggering a fresh run.
    tok = token or request.headers.get("Authorization", "").replace("Bearer ", "").strip()
    if not _verify_hub_token(tok):
        raise HTTPException(status_code=401, detail="Subscription required — please log in via moneypicksarena.com")
    date_str = target_date or datetime.now(timezone.utc).strftime("%Y-%m-%d")
    cached = _cache_get(date_str)
    if cached:
        return cached
    raise HTTPException(status_code=404, detail="No saved picks for this date.")

@app.get("/api/whoami")
async def whoami(request: Request, token: str = ""):
    tok = token or request.headers.get("Authorization", "").replace("Bearer ", "").strip()
    return {"is_admin": _is_admin_token(tok)}

# ─────────────────────────────────────────────────────────────────────────────
#  My Bets (bet tracking) — admin-only, mirrors NBA/NHL/MLB
# ─────────────────────────────────────────────────────────────────────────────
import threading as _bt_th, uuid as _bt_uuid
from datetime import date as _bt_date

_NFL_BET_LOG_PATH = str(_CACHE_DIR / "_nfl_bet_log.json")
_NFL_BET_LOCK = _bt_th.Lock()
_NFL_BET_STAT_KEYS = tuple(PROP_MARKETS)
_NFL_STAT_LABEL = dict(PROP_LABELS)
_NFL_CAT_ORDER = [PROP_LABELS[m] for m in PROP_MARKETS]


def _nfl_load_bets() -> dict:
    try:
        with open(_NFL_BET_LOG_PATH) as f:
            return json.load(f)
    except Exception:
        return {}


def _nfl_save_bets(data: dict):
    try:
        tmp = _NFL_BET_LOG_PATH + f".{os.getpid()}.tmp"
        with open(tmp, "w") as f:
            json.dump(data, f)
        os.replace(tmp, _NFL_BET_LOG_PATH)
    except Exception as e:
        print(f"[nfl_bet_log] save failed: {e}")


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
        sb = httpx.get(
            f"https://site.api.espn.com/apis/site/v2/sports/football/nfl/scoreboard?dates={d}",
            timeout=15, headers={"User-Agent": "Mozilla/5.0"})
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
                timeout=15, headers={"User-Agent": "Mozilla/5.0"})
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
                results[name] = ps
    return results, complete


def _nfl_settle_cached(bet: dict, name_stats: dict) -> bool:
    if bet.get("result") in ("WIN", "LOSS", "PUSH"):
        return False
    st = name_stats.get((bet.get("name") or "").lower().strip())
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
    bet["settled_at"] = _bt_date.today().isoformat()
    return True


def _nfl_settle_bet(bet: dict) -> bool:
    if bet.get("result") in ("WIN", "LOSS", "PUSH"):
        return False
    bdate = bet.get("date")
    if not bdate or bdate >= _bt_date.today().isoformat():
        return False
    try:
        ns = _nfl_box_lookup(bdate)
    except Exception as e:
        print(f"[nfl_bet_log] settle lookup failed {bdate}: {e}")
        return False
    return _nfl_settle_cached(bet, ns)


def _nfl_settle_batch(bets: list) -> bool:
    today = _bt_date.today().isoformat()
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

# ── Pick snapshot ─────────────────────────────────────────────────────────────
_NFL_TRK_APP   = "nfl"
_NFL_PICKS_CAT = "__picks__"
_NFL_TRK_STAKE = 20.0
_NFL_TRK_TOP   = 10   # picks per market+direction that count in main record

def _nfl_save_picks_snapshot(date_str: str, result: dict):
    """Persist today's qualified picks to Supabase so they survive redeploys
    and can be graded once game box scores are final."""
    picks = result.get("picks") or []
    if not picks:
        return
    row = {
        "app": _NFL_TRK_APP, "date": date_str,
        "category": _NFL_PICKS_CAT, "side": "ALL",
        "wins": 0, "losses": 0, "locked": False,
        "detail": picks,
    }
    ok = _nfl_sb_upsert("mpa_track_ledger", [row], on_conflict="app,date,category,side")
    print(f"[nfl_track] snapshot {'saved' if ok else 'FAILED'}: {len(picks)} picks -> {date_str}")

def _nfl_load_picks_snapshot(date_str: str) -> list:
    rows = _nfl_sb_get("mpa_track_ledger", {
        "app": f"eq.{_NFL_TRK_APP}", "category": f"eq.{_NFL_PICKS_CAT}",
        "side": "eq.ALL", "date": f"eq.{date_str}",
        "select": "detail", "limit": "1",
    })
    if rows:
        d = rows[0].get("detail") or []
        return d if isinstance(d, list) else []
    return []

def _nfl_list_snap_dates() -> list:
    rows = _nfl_sb_get("mpa_track_ledger", {
        "app": f"eq.{_NFL_TRK_APP}", "category": f"eq.{_NFL_PICKS_CAT}",
        "side": "eq.ALL", "select": "date", "limit": "365",
    })
    return sorted({r["date"] for r in rows if r.get("date")})

# ── Grading ───────────────────────────────────────────────────────────────────
def _nfl_grade_date(date_str: str, snap: list) -> dict:
    """Grade every pick in snap against ESPN box scores.
    Groups by market+direction, ranks by score desc.
    Top _NFL_TRK_TOP per group -> main record; extras -> NFL Overflow."""
    from collections import defaultdict
    box = _nfl_box_lookup(date_str)
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

    main_rows, ovf_rows = [], []
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
            }
            if rank <= _NFL_TRK_TOP:
                main_rows.append(row)
            else:
                ovf_rows.append({**row, "category": "NFL Overflow"})

    return {"any_game": any_game, "all_final": all_final,
            "main": main_rows, "overflow": ovf_rows}

def _nfl_aggregate_graded(graded: dict) -> dict:
    agg: dict = {}
    for row in graded.get("main", []) + graded.get("overflow", []):
        if row.get("result") not in ("WIN", "LOSS"):
            continue
        if row.get("odds") is None:
            continue
        cat  = row["category"]
        side = row.get("side", "OVER")
        rec  = agg.setdefault(cat, {}).setdefault(side, [0, 0])
        if row["result"] == "WIN":
            rec[0] += 1
        else:
            rec[1] += 1
    return agg

def _nfl_detail_graded(graded: dict) -> list:
    out = []
    for row in graded.get("main", []) + graded.get("overflow", []):
        if row.get("result") not in ("WIN", "LOSS"):
            continue
        if row.get("odds") is None:
            continue
        out.append({k: row.get(k) for k in (
            "name", "team", "category", "side", "market",
            "line", "odds", "rank", "result", "actual", "profit",
        )})
    return out

# ── Track ledger update ───────────────────────────────────────────────────────
_NFL_TRK_LOCK = _bt_th.Lock()

def _nfl_update_track_ledger():
    """Grade all saved pick snapshots for past dates not yet locked.
    Safe to call repeatedly — locked dates are skipped."""
    from datetime import date as _d
    today = _d.today().isoformat()
    with _NFL_TRK_LOCK:
        locked_rows = _nfl_sb_get("mpa_track_ledger", {
            "app": f"eq.{_NFL_TRK_APP}", "category": "eq.__ledger__",
            "locked": "eq.true", "select": "date", "limit": "500",
        })
        locked = {r["date"] for r in (locked_rows or [])}
        upserts = []
        for d in _nfl_list_snap_dates():
            if d >= today or d in locked:
                continue
            snap = _nfl_load_picks_snapshot(d)
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
            det = _nfl_detail_graded(graded)
            upserts += [
                {"app": _NFL_TRK_APP, "date": d, "category": "__ledger__", "side": "ALL",
                 "wins": 0, "losses": 0, "locked": True, "detail": agg},
                {"app": _NFL_TRK_APP, "date": d, "category": "__detail__", "side": "ALL",
                 "wins": 0, "losses": 0, "locked": True, "detail": det},
            ]
        if upserts:
            for i in range(0, len(upserts), 10):
                _nfl_sb_upsert("mpa_track_ledger", upserts[i:i+10], "app,date,category,side")
            print(f"[nfl_track] locked {len(upserts)//2} dates into ledger")

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
    with _NFL_BET_LOCK:
        data = _nfl_load_bets()
        key = _nfl_bet_user_key(tok, admin)
        snapshot = list(data.get(key, []))
    # Settle OFF-lock (see NBA): ESPN calls (now cached) must not hold _NFL_BET_LOCK.
    # Merge settled fields by id so a concurrently-added bet is never clobbered.
    if settle and _nfl_settle_batch(snapshot):
        # Apply ONLY bets settled to a terminal result this pass, and only onto a
        # still-pending on-disk bet — never write pending/None back and never flip an
        # already-terminal value (so a concurrent settle pass can't be clobbered).
        settled = {b.get("id"): b for b in snapshot
                   if b.get("id") and b.get("result") in ("WIN", "LOSS", "PUSH")}
        if settled:
            with _NFL_BET_LOCK:
                data = _nfl_load_bets()
                for b in data.get(key, []):
                    s = settled.get(b.get("id"))
                    if s and b.get("result") not in ("WIN", "LOSS", "PUSH"):
                        for f in ("result", "actual", "profit", "settled_at"):
                            b[f] = s.get(f)
                _nfl_save_bets(data)
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
    bdate = (body.get("date") or _bt_date.today().isoformat()).strip()
    bet = {"id": _bt_uuid.uuid4().hex[:12], "date": bdate,
           "name": name, "pid": str(body.get("pid") or ""),
           "team": (body.get("team") or "").strip(),
           "opp": (body.get("opp") or "").strip(),
           "category": (body.get("category") or _NFL_STAT_LABEL.get(market, "?")).strip(),
           "side": side, "market": market,
           "stat_label": (body.get("stat_label") or _NFL_STAT_LABEL.get(market, "")).strip(),
           "line": line, "odds": odds, "stake": stake,
           "placed_at": (body.get("placed_at") or _bt_date.today().isoformat()),
           "result": "pending", "actual": None, "profit": None, "settled_at": None}
    try:
        _nfl_settle_bet(bet)
    except Exception:
        pass
    with _NFL_BET_LOCK:
        data = _nfl_load_bets()
        key = _nfl_bet_user_key(tok, admin)
        data.setdefault(key, []).append(bet)
        _nfl_save_bets(data)
    return {"ok": True, "bet": bet}


@app.delete("/api/bets/{bet_id}")
async def nfl_delete_bet(bet_id: str, request: Request, token: str = "", admin: str = ""):
    tok = token or request.headers.get("Authorization", "").replace("Bearer ", "").strip()
    if not _nfl_bet_admin_ok(tok, admin):
        raise HTTPException(status_code=403, detail="Admin only")
    with _NFL_BET_LOCK:
        data = _nfl_load_bets()
        key = _nfl_bet_user_key(tok, admin)
        bets = data.get(key, [])
        new_bets = [b for b in bets if b.get("id") != bet_id]
        if len(new_bets) != len(bets):
            data[key] = new_bets
            _nfl_save_bets(data)
    return {"ok": True}


@app.get("/api/bets/summary")
async def nfl_bets_summary(request: Request, token: str = "", admin: str = "", settle: bool = True):
    tok = token or request.headers.get("Authorization", "").replace("Bearer ", "").strip()
    if not _nfl_bet_admin_ok(tok, admin):
        raise HTTPException(status_code=403, detail="Admin only")
    with _NFL_BET_LOCK:
        data = _nfl_load_bets()
        key = _nfl_bet_user_key(tok, admin)
        bets = data.get(key, [])
        if settle and _nfl_settle_batch(bets):
            data[key] = bets
            _nfl_save_bets(data)
        snapshot = list(bets)
    return {"sport": "NFL", "summary": _nfl_summarize_bets(snapshot)}


@app.get("/api/track-record")
async def nfl_track_record():
    """NFL Track Record — all graded picks by date with W/L, ROI at $20/play."""
    _bt_th.Thread(target=_nfl_trk_bg, daemon=True).start()
    led_rows = _nfl_sb_get("mpa_track_ledger", {
        "app": f"eq.{_NFL_TRK_APP}", "category": "eq.__detail__",
        "locked": "eq.true", "select": "date,detail", "limit": "365",
    })
    detail_by_date = {r["date"]: (r.get("detail") or []) for r in (led_rows or [])}
    dates = sorted(detail_by_date.keys(), reverse=True)
    result = []
    for d in dates:
        det = detail_by_date[d]
        decided = [r for r in det if r.get("result") in ("WIN","LOSS") and r.get("odds") is not None]
        wins   = sum(1 for r in decided if r["result"] == "WIN")
        losses = len(decided) - wins
        net_pl = round(sum(r.get("profit") or 0 for r in decided), 2)
        staked = len(decided) * _NFL_TRK_STAKE
        roi    = round(net_pl / staked * 100, 1) if staked else None
        cats: dict = {}
        for r in decided:
            cat = r.get("category","?")
            e = cats.setdefault(cat, {"wins":0,"losses":0,"pl":0.0,"staked":0.0})
            if r["result"] == "WIN": e["wins"] += 1
            else: e["losses"] += 1
            e["pl"] = round(e["pl"] + (r.get("profit") or 0), 2)
            e["staked"] += _NFL_TRK_STAKE
        by_cat = []
        for cat, e in cats.items():
            total = e["wins"] + e["losses"]
            by_cat.append({
                "category": cat, "wins": e["wins"], "losses": e["losses"],
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
    return JSONResponse({"dates": result, "stake": _NFL_TRK_STAKE})


@app.get("/", response_class=HTMLResponse)
async def index(admin: str = "", token: str = ""):
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    is_admin = (bool(admin) and admin == os.environ.get("INTERNAL_API_TOKEN", "__none__")) or _is_admin_token(token)
    js_flag = "true" if is_admin else "false"
    html = HTML.replace("__TODAY__", today).replace("</head>", f"<script>window.IS_ADMIN = {js_flag};</script></head>", 1)
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
.sec{display:flex;align-items:center;gap:10px;font-size:.78rem;font-weight:700;color:#f59e0b;text-transform:uppercase;letter-spacing:.15em;margin:28px 0 12px}
.sec::after{content:'';flex:1;height:1px;background:rgba(245,158,11,.15)}
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
.pick-card.acc-rush{border-top:3px solid #34d399}
.pick-card.acc-rec{border-top:3px solid #60a5fa}
.pick-card.acc-pass{border-top:3px solid #f59e0b}
.pick-card.acc-recpt{border-top:3px solid #a78bfa}
.pick-card.acc-td{border-top:3px solid #f87171}
.pick-card.acc-ptd{border-top:3px solid #38bdf8}
.pick-card.acc-def{border-top:3px solid #fb7185}
.pick-card.acc-kick{border-top:3px solid #2dd4bf}
.nfl-toolbar{display:flex;justify-content:flex-end;margin:0 0 14px}
#nflSearch{background:#111;color:#fff;border:1px solid #2a2a2a;border-radius:8px;padding:8px 14px;font-size:.9rem;outline:none;width:240px;max-width:60vw;font-family:'Source Sans Pro',sans-serif}
.sec-hdr{cursor:pointer;display:flex;align-items:center;justify-content:space-between;user-select:none}
.sec-caret{font-size:.85rem;color:#9ca3af;margin-left:10px}
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
</style>
</head>
<body>
<nav style="display:flex;justify-content:space-between;align-items:center"><div class="logo">Money <span>Picks</span> Arena</div><div style="display:flex;gap:8px;align-items:center"><button onclick="openNflTrackRecord()" style="background:#065f46;color:#fff;border:none;border-radius:10px;padding:9px 16px;font-weight:800;font-size:.82rem;cursor:pointer;white-space:nowrap">&#128202; Track Record</button><button class="admin-only" onclick="openNflMyBets()" style="background:#0e7490;color:#fff;border:none;border-radius:10px;padding:9px 16px;font-weight:800;font-size:.82rem;cursor:pointer;white-space:nowrap">&#128176; My Bets</button></div></nav>
<style>
.nfl-bets-tbl{width:100%;border-collapse:collapse;font-size:.82rem}
.nfl-bets-tbl th{padding:7px 10px;text-align:left;font-size:.72rem;color:#9ca3af;font-weight:700;text-transform:uppercase;letter-spacing:.07em;border-bottom:1px solid #2a2a2a;white-space:nowrap}
.nfl-bets-tbl td{padding:8px 10px;border-bottom:1px solid #161616;vertical-align:middle;color:#e5e7eb}
.nfl-bets-tbl tr:last-child td{border-bottom:none}
.nfl-bets-tbl tr:hover td{background:rgba(255,255,255,.02)}
/* NFL Track Record */
.nfl-trk-sum{background:#1a1a1a;border-radius:12px;padding:14px 18px;display:flex;flex-wrap:wrap;gap:18px;align-items:center;margin-bottom:14px}
.nfl-trk-tbl{width:100%;border-collapse:collapse;font-size:.82rem;background:#161616}
.nfl-trk-tbl thead tr{border-bottom:1px solid rgba(52,211,153,.2)}
.nfl-trk-tbl th{padding:10px 12px;text-align:left;color:#34d399;font-size:.7rem;font-weight:700;text-transform:uppercase;letter-spacing:.1em;background:#1a1a1a;white-space:nowrap}
.nfl-trk-tbl td{padding:9px 12px;border-bottom:1px solid #1c1c1c;white-space:nowrap}
.nfl-trk-tbl tr:last-child td{border-bottom:none}
.nfl-trk-tbl tr:hover td{background:rgba(255,255,255,.02)}
.nfl-trk-bar-wrap{width:80px;background:#1f2937;border-radius:4px;height:8px;overflow:hidden;display:inline-block;vertical-align:middle}
.nfl-trk-bar{height:100%;border-radius:4px}
</style>
<div id="nfl-track-card" style="display:none;max-width:960px;margin:18px auto 0;padding:0 16px">
  <div class="card" style="padding:20px 22px">
    <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:14px">
      <h2 style="font-family:'Playfair Display',serif;font-size:1.4rem;font-weight:700;color:#fff">&#128202; NFL Track Record</h2>
      <button onclick="document.getElementById('nfl-track-card').style.display='none'" style="background:#1f2937;border:none;color:#9ca3af;border-radius:8px;padding:8px 11px;font-size:.9rem;cursor:pointer">&#215;</button>
    </div>
    <div style="display:flex;align-items:center;gap:10px;flex-wrap:wrap;margin-bottom:14px">
      <label style="color:#9ca3af;font-size:.78rem;font-weight:700;text-transform:uppercase;letter-spacing:.1em">Date</label>
      <input type="date" id="nflTrkDate" class="date-input" style="width:auto" onchange="_nflTrkDayName();renderNflTrackDay()">
      <span id="nflTrkDayName" style="color:#34d399;font-weight:700;font-size:.9rem"></span>
      <button onclick="loadNflTrackRecord()" style="background:#065f46;color:#fff;border:none;border-radius:8px;padding:8px 14px;font-weight:700;cursor:pointer;font-size:.82rem">&#8635; Get Results</button>
      <button id="nflTrkBtnCat" onclick="nflTrkSetTab('cat')" style="background:#065f46;color:#fff;border:none;border-radius:8px;padding:8px 14px;font-weight:700;cursor:pointer;font-size:.82rem">By Category</button>
      <button id="nflTrkBtnList" onclick="nflTrkSetTab('list')" style="background:#1f2937;color:#fff;border:none;border-radius:8px;padding:8px 14px;font-weight:700;cursor:pointer;font-size:.82rem">Full List</button>
    </div>
    <div id="nflTrkSummary"></div>
    <div id="nflTrkBody"></div>
  </div>
</div>
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
    <p>NFL Daily Picks</p>
  </div>
  <div class="card run-card">
    <h2>Run Today&#39;s Picks</h2>
    <div class="date-row">
      <label>Date</label>
      <input type="date" id="datePicker" class="date-input" value="__TODAY__" >
    </div>
    <button class="btn" id="getBtn" onclick="getPicks()">🎯 Get Picks</button>
    <button class="btn admin-only" id="runBtn" onclick="runPicks()" style="margin-left:10px">Run Picks</button>
    <div class="status-msg" id="statusMsg"></div>
  </div>
  <div class="card" id="parlayCard" style="text-align:center;max-width:600px;margin:0 auto 16px">
    <h2 style="font-family:'Playfair Display',serif;font-size:1.3rem;font-weight:700;color:#fff;margin-bottom:6px">🎰 Auto Parlay Builder <span style="font-size:.7rem;color:#777;font-family:sans-serif">admin only</span></h2>
    <p style="font-size:.74rem;color:#888;margin-bottom:14px">Best available legs from today&#39;s board — priced odds combined</p>
    <div style="display:flex;gap:10px;justify-content:center;align-items:center;flex-wrap:wrap">
      <label style="color:#9ca3af;font-size:.85rem;font-weight:600">Legs
        <select id="parlayLegs" style="background:#1a1a1a;color:#fff;border:1px solid #333;border-radius:8px;padding:8px 12px;font-size:.9rem;font-weight:700;margin-left:6px">
          <option>2</option><option selected>3</option><option>4</option><option>5</option><option>6</option><option>7</option><option>8</option><option>9</option><option>10</option>
        </select>
      </label>
      <button class="btn" onclick="buildParlay()">Build Best Parlay</button>
      <button class="btn" onclick="generateParlay()" style="background:#1f2937;color:#fff">🎲 Generate New</button>
    </div>
    <div id="parlayResult" style="margin-top:16px;text-align:left"></div>
  </div>
  <div id="nfl-gp-card" style="display:none;max-width:960px;margin:18px auto 0;padding:0 16px">
    <div style="font-size:1rem;font-weight:900;color:#a78bfa;margin-bottom:6px">&#128302; Game Predictor &#8212; Today&#39;s Winners</div>
    <div style="font-size:.72rem;color:#64748b;margin-bottom:14px">Model picks each game&#39;s winner from L5 team offensive yards, opponent defensive strength, and home-field advantage. Tap a game for the full breakdown.</div>
    <div id="nfl-gp-body"></div>
  </div>
  <div id="results"></div>
</main>
<footer>
  <div class="ft-logo">Money Picks Arena</div>
  <div>NFL Money Bombs &middot; Player Props &middot; Daily Picks</div>
  <div style="margin-top:8px;font-size:.7rem">For entertainment only. Not a betting service. Must be 18+. Please gamble responsibly.</div>
</footer>
<script>


var _nflKey='__mpa_token';
var _nflParams=new URLSearchParams(window.location.search);
var _nflUrlTok=_nflParams.get('token');
if(_nflUrlTok){localStorage.setItem(_nflKey,_nflUrlTok);window.history.replaceState({},'',window.location.pathname);}
var _nflTok=localStorage.getItem(_nflKey)||'';
if(!_nflTok){window.location.href='https://moneypicksarena.com';}
function _applyAdmin(){if(window.IS_ADMIN){document.body&&document.body.classList.add('is-admin');}else{if(_nflTok){fetch('/api/whoami?token='+encodeURIComponent(_nflTok)).then(function(r){return r.json();}).then(function(d){if(d&&d.is_admin){window.IS_ADMIN=true;document.body&&document.body.classList.add('is-admin');}}).catch(function(){});}}}
if(document.readyState==='loading'){document.addEventListener('DOMContentLoaded',_applyAdmin);}else{_applyAdmin();}

// ===== Admin Auto Parlay Builder (NFL) =====
function _amToDec(a){var s=String(a==null?'':a).replace('+','').trim();var n=parseFloat(s);if(!n||isNaN(n))return null;return n>0?1+n/100:1+100/Math.abs(n);}
function _decToAm(d){if(!d||d<=1)return null;return d>=2?'+'+Math.round((d-1)*100):'-'+Math.round(100/(d-1));}
function _fmtOdds(o){if(o==null||o==='')return null;var s=String(o).trim();if(!s||s==='0')return null;return (s.charAt(0)==='-'||s.charAt(0)==='+')?s:'+'+s;}
function _floorOk(odds){if(odds==null||odds==='')return true;var a=parseFloat(odds);if(isNaN(a)||a===0)return true;return a>=-500;}
function _legScore(c){return (c.hasOdds?1:0)*1e9+(c.rate||0)*1e4+(c.dec?Math.min(c.dec,11)*100:0);}
function _nflLeg(p){
  var dir=(p.pick==='O'||p.pick==='OVER')?'OVER':(p.pick==='U'||p.pick==='UNDER')?'UNDER':p.pick;
  var line=(p.realLine!=null?p.realLine:(p.dispLine!=null?p.dispLine:0));
  var rate=(p.vsLineRate||p.rateB||p.rateA||p.dispScore||0);
  var odds=(dir==='OVER')?p.realOdds:(dir==='UNDER')?p.realUnderOdds:null;var dec=_amToDec(odds);
  return {player:p.name,team:p.team||'',opp:p.opponent||'',market:p.mkt||p.label||'',dir:dir,line:line,rate:Math.round(rate||0),odds:odds,dec:dec,hasOdds:!!dec};
}
function _parlayPool(){
  var plays=window.__NFL_PLAYS__||[];var byP={};
  plays.forEach(function(p){
    if(!p||!p.name||!p.pick)return;
    if(p.score==null||p.score<55)return;
    var c=_nflLeg(p);
    if(!c.dir)return;
    if(!_floorOk(c.odds))return;
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
  if(!cands.length){out.innerHTML='<div style="color:#888;padding:10px">Run today&#39;s picks first, then build a parlay.</div>';return;}
  if(cands.length<n){out.innerHTML='<div style="color:#f87171;padding:10px">Only '+cands.length+' qualifying play'+(cands.length!==1?'s':'')+' on the board. Pick a smaller parlay.</div>';return;}
  function _pick(ordered,avoid){var used={},picked=[],i,c;for(i=0;i<ordered.length&&picked.length<n;i++){c=ordered[i];if(used[c.player])continue;if(avoid&&avoid[c.player])continue;used[c.player]=1;picked.push(c);}for(i=0;i<ordered.length&&picked.length<n;i++){c=ordered[i];if(used[c.player])continue;used[c.player]=1;picked.push(c);}return picked;}
  var legs;
  if(randomize){var avoid=null;if(window._lastParlay&&window._lastParlay.length){avoid={};window._lastParlay.forEach(function(pl){avoid[pl]=1;});}legs=_pick(_shuffle(cands.slice()),avoid).sort(function(a,b){return _legScore(b)-_legScore(a);});}
  else{legs=_pick(cands.slice(),null);}
  window._lastParlay=legs.map(function(l){return l.player;});
  var dec=1,priced=0,missing=0;
  legs.forEach(function(l){if(l.dec){dec*=l.dec;priced++;}else{missing++;}});
  var am=priced?_decToAm(dec):null;var payout=priced?(100*dec):null;
  var dirColor=function(d){return d==='OVER'?'#4ade80':d==='UNDER'?'#f87171':'#9ca3af';};
  var rows=legs.map(function(l,i){var fo=_fmtOdds(l.odds);return '<div style="display:flex;justify-content:space-between;align-items:center;gap:10px;padding:10px 12px;border-bottom:1px solid #1a1a1a">'
    +'<div style="min-width:0">'
    +'<div style="font-weight:800;color:#fff;font-size:.85rem">'+(i+1)+'. '+l.player+' <span style="color:#777;font-size:.7rem">'+l.team+(l.opp?(' vs '+l.opp):'')+'</span></div>'
    +'<div style="color:#999;font-size:.72rem;margin-top:2px">'+l.market+(l.line!=null?(' · line '+l.line):'')+(l.rate?(' · '+l.rate+'% hit'):'')+'</div>'
    +'</div>'
    +'<div style="text-align:right;white-space:nowrap">'
    +'<div style="color:'+dirColor(l.dir)+';font-weight:900;font-size:.8rem">'+l.dir+'</div>'
    +'<div style="color:#f59e0b;font-size:.72rem;font-weight:800">'+(fo||'odds N/A')+'</div>'
    +'</div></div>';}).join('');
  var header='<div style="display:flex;justify-content:space-between;align-items:center;padding:8px 12px;border-bottom:1px solid #262626;background:#121212">'
    +'<span style="font-weight:800;color:#ccc;font-size:.74rem">'+(randomize?'RANDOM MIX':'TOP PLAYS')+'</span>'
    +'<span onclick="closeParlay()" title="Close" style="cursor:pointer;color:#888;font-weight:900;font-size:1.15rem;line-height:1;padding:0 6px">×</span></div>';
  var summary='<div style="display:flex;justify-content:space-between;align-items:center;padding:12px;background:linear-gradient(135deg,rgba(245,158,11,.12),rgba(245,158,11,.02));border-top:1px solid #262626">'
    +'<div style="font-weight:900;color:#f59e0b">'+n+'-LEG PARLAY</div>'
    +'<div style="text-align:right">'+(am?('<div style="font-weight:900;color:#4ade80;font-size:1.05rem">'+am+'</div><div style="color:#999;font-size:.7rem">$100 → $'+payout.toFixed(2)+(missing?(' · '+priced+'/'+n+' legs priced'):'')+'</div>'):('<div style="color:#888;font-size:.78rem">No book odds available for these legs</div>'))+'</div>'
    +'</div>';
  out.innerHTML='<div style="background:#0e0e0e;border:1px solid #262626;border-radius:12px;overflow:hidden">'+header+rows+summary+'</div>';
}

var jobId=null, pollTimer=null;

async function runPicks(){
  var date=document.getElementById('datePicker').value;
  if(!date){alert('Please select a date');return;}
  var btn=document.getElementById('runBtn');
  var status=document.getElementById('statusMsg');
  btn.disabled=true;
  btn.innerHTML='<span class="spinner"></span>Running...';
  status.innerHTML='<span class="spinner"></span>Fetching prop lines and loading NFL stats...';
  document.getElementById('results').innerHTML='';
  try{
    const r=await fetch('/api/run',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({date:date,token:_nflTok})});
    const d=await r.json();
    jobId=d.job_id;
    pollTimer=setInterval(pollJob,2500);
  }catch(e){
    status.textContent='Error: '+e.message;
    btn.disabled=false;btn.textContent='Run Picks';
  }
}

var _pollFails=0;
async function pollJob(){
  if(!jobId)return;
  try{
    const r=await fetch('/api/run/'+jobId);
    if(!r.ok){
      // 404 = job gone (server restarted mid-run); stop and tell user
      if(r.status===404){
        clearInterval(pollTimer);
        document.getElementById('statusMsg').textContent='Server restarted mid-run — please try again.';
        document.getElementById('runBtn').disabled=false;
        document.getElementById('runBtn').textContent='Run Picks';
      }
      return;
    }
    const d=await r.json();
    _pollFails=0;
    if(d.status==='done'){
      clearInterval(pollTimer);
      renderResults(d.result);
      document.getElementById('runBtn').disabled=false;
      document.getElementById('runBtn').textContent='Run Picks';
      document.getElementById('statusMsg').textContent='';
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
    // Network error — retry up to 5 times before giving up
    _pollFails++;
    if(_pollFails>=5){
      clearInterval(pollTimer);
      document.getElementById('statusMsg').textContent='Connection lost — please refresh and try again.';
      document.getElementById('runBtn').disabled=false;
      document.getElementById('runBtn').textContent='Run Picks';
    }
  }
}

// Get Picks: load saved picks for the chosen date (read-only, never runs the pipeline).
async function getPicks(){
  var date=document.getElementById('datePicker').value;
  if(!date){alert('Please select a date');return;}
  var btn=document.getElementById('getBtn');
  var status=document.getElementById('statusMsg');
  var orig=btn.textContent;
  btn.disabled=true;
  btn.innerHTML='<span class="spinner"></span>Loading...';
  status.innerHTML='<span class="spinner"></span>Loading saved picks...';
  document.getElementById('results').innerHTML='';
  try{
    var r=await fetch('/api/cached?target_date='+encodeURIComponent(date)+'&token='+encodeURIComponent(_nflTok));
    if(r.status===404){ status.textContent=''; alert("Today's picks aren't ready yet -- check back a little later."); return; }
    if(!r.ok) throw new Error('Server error '+r.status);
    var d=await r.json();
    renderResults(d);
    status.textContent='';
  }catch(e){
    status.textContent='Error: '+e.message;
  }finally{
    btn.disabled=false; btn.textContent=orig;
  }
}

// ===== NBA-style cards (NFL) =====
window.__NFLLAD__ = window.__NFLLAD__ || {};
var _MORDER=['Pass Yds','Pass TDs','Completions','Pass Att','INT Thrown','Rush Yds','Rush Att','Rec Yds','Receptions','Anytime TD','Tackles+Ast','Sacks','Def INT','Kick Pts','FG Made'];
var _MLBL={'Pass Yds':'Pass','Pass TDs':'Pass TD','Completions':'Comp','Pass Att':'Att','INT Thrown':'INT','Rush Yds':'Rush','Rush Att':'Carries','Rec Yds':'Rec','Receptions':'Recept','Anytime TD':'TD','Tackles+Ast':'Tkl','Sacks':'Sacks','Def INT':'D INT','Kick Pts':'K Pts','FG Made':'FG'};

function _nflGameDone(p){
  var s=p&&p.game_start; if(!s) return false;
  var t=new Date(s).getTime(); if(!t||isNaN(t)) return false;
  // Only auto-hide finished games on TODAY'S live slate. When browsing a
  // past date every game is long over — show ALL picks (historical review).
  var d=new Date(t), now=new Date();
  if(d.toDateString()!==now.toDateString()) return false;
  return Date.now() > (t + 4*3600*1000);
}
function rateClass(r){ return r >= 70 ? 'green' : r >= 55 ? 'gold' : 'red-txt'; }
function _initials(name){
  var parts=String(name||'').trim().split(/\s+/);
  if(!parts.length||!parts[0]) return '?';
  if(parts.length===1) return parts[0].slice(0,2).toUpperCase();
  return (parts[0][0]+parts[parts.length-1][0]).toUpperCase();
}
function _accFor(mkt){
  if(mkt==='Rush Yds'||mkt==='Rush Att') return 'acc-rush';
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
  var pct=(rate==null)?'--':rate+'%';
  return '<span class="'+(rate==null?'gray':rateClass(rate))+'">'+hits+'/'+tot+' ('+pct+')</span>';
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
function fmtVsLine(p){
  if(p.realLine==null||!p.vsLineTotal) return '<span class="gray">—</span>';
  return '<span class="'+rateClass(p.vsLineRate)+'">'+p.vsLineHits+'/'+p.vsLineTotal+' ('+p.vsLineRate+'%)</span>';
}
function nflCard(p,i){
  var key=_ladKey(p); window.__NFLLAD__[key]=p;
  var ha=p.homeRoad==='H';
  var hasHA=(p.homeRoad==='H'||p.homeRoad==='R');
  var head=p.head||'';
  var logo='https://a.espncdn.com/i/teamlogos/nfl/500/'+_logoAbbr(p.team)+'.png';
  var lineHtml=(p.realLine!=null)
    ? `<span class="ln">${p.dispLine}</span> <span class="od">${p.realOdds||''}</span>`
    : `<span class="est">~${p.dispLine}</span>`;
  var lastStat=(p.realLine!=null&&p.vsLineTotal)
    ? `<div class="pc-stat"><div class="k">vs Book L10</div><div class="v ${rateClass(p.vsLineRate)}">${p.vsLineHits}/${p.vsLineTotal} (${p.vsLineRate}%)</div></div>`
    : `<div class="pc-stat"><div class="k">Under L10</div><div class="v ${rateClass(p.underRate)}">${p.underHits}/${p.underTotal} (${p.underRate}%)</div></div>`;
  var haBadge=hasHA?`<span class="${ha?'home':'away'}">${ha?'HOME':'AWAY'}</span>`:'';
  var defChip='';
  if(p.defRank&&p.defAdj){
    var dcol=p.defAdj>0?'#4ade80':'#f87171';
    defChip='<div style="font-size:.62rem;font-weight:800;color:'+dcol+';margin-top:2px">vs #'+p.defRank+' '+(p.defLbl||'D')+' · '+(p.defAdj>0?'+':'')+p.defAdj+'% proj</div>';
  }
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
         <div class="pc-meta">${p.team} vs ${p.opponent} ${haBadge}</div>
         <div class="pc-mkt">${p.mkt||''} · ${p.pick||''}</div>
         ${defChip}
       </div>
     </div>
     <div class="pc-tagrow">${fmtTag(p.tag)}</div>
     <div class="pc-line-row"><span>${lineHtml}</span><span class="od">Line</span></div>
     <div class="pc-stats">
       <div class="pc-stat"><div class="k">Career vs ${p.opponent}</div><div class="v">${_rateHtml(p.rateA,p.hitsA,p.totA)}</div></div>
       <div class="pc-stat"><div class="k">L10 ${hasHA?(ha?'Home':'Away'):'H/A'}</div><div class="v">${_rateHtml(p.rateB,p.hitsB,p.totB)}</div></div>
       <div class="pc-stat"><div class="k">Avg</div><div class="v gold">${p.avg}</div></div>
       ${lastStat}
     </div>
     <div class="pc-foot"><span class="pc-score">${p.dispScore}</span>
       <span style="display:flex;gap:6px">${_nflBetBtn(p)}<button class="pc-tap" onclick="openNflLadder('${key}')">📊 Game Log</button></span></div>
   </div>`;
}
function nflCardGrid(picks){
  if(!picks||!picks.length) return '<div class="no-picks">No qualifying picks for this market.</div>';
  return '<div class="picks-grid">'+picks.map(function(p,i){return nflCard(p,i+1);}).join('')+'</div>';
}
function _spRow(p){
  var key=_ladKey(p); window.__NFLLAD__[key]=p;
  var best=Math.max(p.rateA||0,p.rateB||0);
  return `<div class="sp-row" onclick="openNflLadder('${key}')"><div><div class="nm">${p.name}</div><div class="mt">${p.team} vs ${p.opponent} · ${p.dispLine} ${p.pick||''}</div></div><div class="${rateClass(best)}" style="font-weight:800">${best}%</div></div>`;
}
function _edge(p){ var g=(p.gap==null?0:p.gap); return (p.pick==='UNDER')?(-g):g; }
function _collapseSec(id,title,inner,open){
  var disp=open?'block':'none'; var car=open?'▾':'▸';
  return '<div class="sec sec-hdr" onclick="_secToggle(&#39;'+id+'&#39;)"><span>'+title+'</span>'+
         '<span class="sec-caret" id="car_'+id+'">'+car+'</span></div>'+
         '<div id="sec_'+id+'" style="display:'+disp+'">'+inner+'</div>';
}
function _secToggle(id){
  var el=document.getElementById('sec_'+id); var c=document.getElementById('car_'+id);
  if(!el) return; var hidden=el.style.display==='none';
  el.style.display=hidden?'block':'none'; if(c) c.textContent=hidden?'▾':'▸';
}
function _playRow(p){
  var key=_ladKey(p); window.__NFLLAD__[key]=p;
  var best=Math.max(p.rateA||0,p.rateB||0);
  var sub=p.team+' vs '+p.opponent+' · '+(p.mkt||p.label)+' · '+p.dispLine+' '+(p.pick||'');
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
  _openModal(mu, ((st.d||{}).date||'')+' · tap any play for its game log', body);
}
function _marketModal(m){
  var st=window._nflState||{};
  var plays=(st.all||[]).filter(function(p){return (p.mkt||p.label)===m;}).sort(function(a,b){return _edge(b)-_edge(a);});
  var body=plays.length?plays.map(_playRow).join(''):'<div class="mt" style="color:#6b7280;padding:10px">No plays.</div>';
  _openModal(_mIcon(m)+' '+m, plays.length+' plays · tap any play for its game log', body);
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
    return `<div class="uprow" onclick="openNflLadder('${key}')"><div><div class="nm">${p.name}</div><div class="mt">${p.team} vs ${p.opponent} · ${p.mkt} · under ${p.underLine}</div></div><div class="${rateClass(p.underRate)}" style="font-weight:800">${p.underHits}/${p.underTotal} (${p.underRate}%)</div></div>`;
  }).join('');
  return '<div class="uplays">'+rows+'</div>';
}
function openNflLadder(key){
  var p=window.__NFLLAD__[key]; if(!p) return;
  var line=p.dispLine;
  var chips=(p.glog||[]).map(function(g){
    var hit=g.v>line; var cls=hit?'hit':'miss';
    var od=g.o?(' · '+g.o):'';
    return `<div class="glchip ${cls}"><div class="d">${g.d}${od}</div><div class="v">${g.v}</div></div>`;
  }).join('');
  if(!chips) chips='<span class="gray">No game log available.</span>';
  var vslRow=(p.realLine!=null&&p.vsLineTotal)
    ? `<div class="lad-stat"><span class="k">Hits vs Book Line (${p.realLine}) L10</span><span class="v ${rateClass(p.vsLineRate)}">${p.vsLineHits}/${p.vsLineTotal} (${p.vsLineRate}%)</span></div>`
    : '';
  var hasHA=(p.homeRoad==='H'||p.homeRoad==='R');
  var vol=(p.vsOppLog||[]);
  var voHtml='';
  if(vol.length){
    voHtml='<div style="font-size:.7rem;color:#6b7280;text-transform:uppercase;letter-spacing:.08em;font-weight:700;margin:12px 0 4px">Every game vs '+p.opponent+' ('+vol.length+')</div>';
    voHtml+=vol.map(function(g){var hit=g.v>line;return '<div class="vsopp-row"><span style="color:#9ca3af">'+g.d+'</span><span style="font-weight:700;color:'+(hit?'#4ade80':'#f87171')+'">'+g.v+'</span></div>';}).join('');
  }
  var html=`
    <div class="lad-modal" onclick="event.stopPropagation()">
      <button class="lad-close" onclick="closeNflLadder()">✕</button>
      <h3>${p.name}</h3>
      <div class="lad-sub">${p.mkt} · ${p.team} vs ${p.opponent} · Line ${p.dispLine} · ${p.pick||''}</div>
      <div style="font-size:.7rem;color:#6b7280;text-transform:uppercase;letter-spacing:.08em;font-weight:700;margin-bottom:4px">Recent Games (green = over line)</div>
      <div class="lad-glog">${chips}</div>
      ${voHtml}
      <div class="lad-stat"><span class="k">Career vs ${p.opponent}</span><span class="v">${_rateHtml(p.rateA,p.hitsA,p.totA)}</span></div>
      <div class="lad-stat"><span class="k">L10 ${hasHA?(p.homeRoad==='H'?'Home':'Away'):'H/A'}</span><span class="v">${_rateHtml(p.rateB,p.hitsB,p.totB)}</span></div>
      ${vslRow}
      <div class="lad-stat"><span class="k">Under Line L10</span><span class="v ${rateClass(p.underRate)}">${p.underHits}/${p.underTotal} (${p.underRate}%)</span></div>
      <div class="lad-stat"><span class="k">Average</span><span class="v gold">${p.avg}</span></div>
      ${(p.defRank!=null&&p.defAdj!=null)?`<div class="lad-stat"><span class="k">Opp Def Adj (#${p.defRank} ${p.defLbl||'D'})</span><span class="v" style="color:${p.defAdj>0?'#4ade80':(p.defAdj<0?'#f87171':'#9ca3af')}">${p.defAdj>0?'+':''}${p.defAdj}% → ${p.projAvg!=null?p.projAvg:p.avg}</span></div>`:''}
      <div class="lad-stat"><span class="k">Score</span><span class="v" style="color:#f59e0b">${p.dispScore}</span></div>
    </div>`;
  var ov=document.createElement('div');
  ov.className='lad-ov'; ov.id='nflLadOv'; ov.onclick=closeNflLadder;
  ov.innerHTML=html;
  document.body.appendChild(ov);
}
function closeNflLadder(){var o=document.getElementById('nflLadOv');if(o)o.remove();}

function buildNormTable(picks, startNum){
  var thead = '<thead><tr><th>#</th><th>PLAYER</th><th>TEAM</th><th>OPP</th><th>H/A</th>' +
    '<th>BOOK</th><th>AVG vs OPP</th><th>AVG L10 H/A</th><th>HITS BOOK L10</th>' +
    '<th>GAP vs BOOK</th><th>Career vs OPP</th><th>L10 H/A</th><th>SCORE</th><th>PICK</th><th>TAG</th></tr></thead>';
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
      '<td>' + (p.realLine!=null ? '<span class="real-line">' + p.dispLine + '</span> <span class="odds-txt">' + (p.realOdds||'') + '</span>' : '<span class="est">~' + p.dispLine + '</span>') + '</td>' +
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
  var _gd=window.__NFL_DATE__||'';
  var _ha=g.home_abbr||'',_aa=g.away_abbr||'';
  window.__NFL_GP_BET__=window.__NFL_GP_BET__||{};
  var n=0;
  function _od(v){return v!=null?(v>0?'+'+v:''+v):'&#8212;';}
  function _regML(abbr,side,odds,sfx){
    var k='nfgpml'+idx+sfx; window.__NFL_GP_BET__[k]={
      name:_aa+' @ '+_ha+' \u2014 '+abbr+' to Win',team:abbr,opp:(side==='HOME'?_aa:_ha),
      category:'Game Predictor',side:side,stat_key:'gp_winner',stat_label:'to Win',
      line:null,odds:odds,home_abbr:_ha,away_abbr:_aa,date:_gd}; return k;
  }
  function _regTot(dir,odds,sfx){
    var k='nfgptl'+idx+sfx; window.__NFL_GP_BET__[k]={
      name:_aa+' @ '+_ha+' '+dir+' '+g.total_line,team:_aa+'@'+_ha,opp:'',
      category:'Game Predictor',side:dir,stat_key:'gp_total',stat_label:'Point Total',
      line:g.total_line,odds:odds,home_abbr:_ha,away_abbr:_aa,date:_gd}; return k;
  }
  function _row(label,od,k,isPick){
    if(od==null||!k) return '';
    var star=isPick?'&#9733; ':''; var lc=isPick?'#e9d5ff':'#94a3b8';
    return '<div style="display:flex;align-items:center;gap:6px;padding:5px 12px;border-top:1px solid #111c2e">'
      +'<div style="flex:1;font-size:.7rem;font-weight:800;color:'+lc+'">'+star+label+'</div>'
      +'<div style="font-family:monospace;font-size:.7rem;font-weight:700;color:#fbbf24;min-width:36px;text-align:right">'+_od(od)+'</div>'
      +'<button onclick="event.stopPropagation();_nflGpBetForm(&#39;'+k+'&#39;)" style="background:#1a1740;color:#a5b4fc;border:none;border-radius:5px 0 0 5px;padding:4px 9px;font-size:.65rem;font-weight:800;cursor:pointer;white-space:nowrap">Track</button>'
      +'</div>';
  }
  var rows='';
  if(g.away_ml_odds!=null) rows+=_row(_aa+' ML',g.away_ml_odds,_regML(_aa,'AWAY',g.away_ml_odds,'a'),!g.pick_home);
  if(g.home_ml_odds!=null) rows+=_row(_ha+' ML',g.home_ml_odds,_regML(_ha,'HOME',g.home_ml_odds,'h'),g.pick_home);
  if(g.total_line!=null){
    if(g.total_over_odds!=null) rows+=_row('OVER '+g.total_line,g.total_over_odds,_regTot('OVER',g.total_over_odds,'o'),g.total_pick==='OVER');
    if(g.total_under_odds!=null) rows+=_row('UNDER '+g.total_line,g.total_under_odds,_regTot('UNDER',g.total_under_odds,'u'),g.total_pick==='UNDER');
  }
  if(!rows) return '';
  return '<div style="margin-top:8px;margin-left:-15px;margin-right:-15px;margin-bottom:-13px;border-top:1px solid #1e293b;border-radius:0 0 14px 14px;overflow:hidden;background:#070d1a">'
    +'<div style="padding:4px 12px 3px;font-size:.58rem;font-weight:800;color:#7c3aed;letter-spacing:.07em;background:rgba(124,58,237,.1)">&#128203; TRACK &#9733; = model pick</div>'
    +rows+'</div>';
}
function _nflGpCard(g,i){
  var cc=_nflGpConfClr(g.conf);
  function teamRow(abbr,sp,proj,win,isPick){
    var barClr=isPick?'#a78bfa':'#334155';
    return '<div style="display:flex;align-items:center;gap:8px;padding:5px 0">'
      +'<div style="width:44px;font-weight:900;color:'+(isPick?'#e9d5ff':'#cbd5e1')+';font-size:.9rem">'+_esc(abbr)+'</div>'
      +'<div style="flex:1;min-width:0"><div style="height:8px;background:#0f172a;border-radius:5px;overflow:hidden"><div style="height:100%;width:'+win+'%;background:'+barClr+'"></div></div>'
      +'<div style="font-size:.6rem;color:#64748b;margin-top:2px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis">'+_esc(sp||'TBD')+'</div></div>'
      +'<div style="width:32px;text-align:right;font-weight:800;color:#e2e8f0;font-size:.82rem">'+_nflGpFix(proj)+'</div>'
      +'<div style="width:42px;text-align:right;font-weight:900;color:'+(isPick?'#4ade80':'#94a3b8')+';font-size:.82rem">'+win+'%</div>'
      +'</div>';
  }
  var drivers=(g.drivers||[]).map(function(d){return _esc(d);}).join(' &#183; ');
  var vb=g.value_flag?('<span style="background:#166534;color:#fff;font-weight:900;font-size:.62rem;border-radius:6px;padding:2px 7px;letter-spacing:.04em">VALUE +'+g.mkt_edge+'%</span>'):'';
  var bdr=g.value_flag?'#166534':'#1e293b';
  // Total row
  var totRow='';
  if(g.total_line==null){
    totRow='<div style="margin-top:8px;padding-top:7px;border-top:1px solid #111c2e;font-size:.66rem;color:#64748b">POINT TOTAL <span style="color:#cbd5e1;font-weight:800">'+_nflGpFix(g.proj_total)+'</span> proj &#183; no line posted</div>';
  } else {
    var ov=g.total_pick==='OVER'; var ec=(g.total_edge>0?'+':'')+_nflGpFix(g.total_edge);
    totRow='<div style="margin-top:8px;padding-top:7px;border-top:1px solid #111c2e;display:flex;align-items:center;justify-content:space-between">'
      +'<span style="font-size:.66rem;color:#64748b;font-weight:700">POINT TOTAL <span style="color:#cbd5e1">'+_nflGpFix(g.proj_total)+'</span> vs line '+_nflGpFix(g.total_line)+'</span>'
      +'<span style="background:'+(ov?'#166534':'#7f1d1d')+';color:#fff;font-weight:900;font-size:.62rem;border-radius:6px;padding:2px 8px">'+g.total_pick+' '+ec+'</span>'
      +'</div>';
  }
  // Market edge row
  var mktRow='';
  if(g.mkt_edge!=null){
    var mp=(g.pick_home?g.mkt_home_pct:g.mkt_away_pct), md=(g.pick_home?g.win_home:g.win_away);
    var col=(g.mkt_edge>0?'#166534':(g.mkt_edge<0?'#7f1d1d':'#334155')), sign=(g.mkt_edge>0?'+':'');
    mktRow='<div style="margin-top:6px;padding-top:6px;border-top:1px solid #111c2e;display:flex;align-items:center;justify-content:space-between">'
      +'<span style="font-size:.66rem;color:#64748b;font-weight:700">MARKET '+_esc(g.pick_abbr)+' <span style="color:#cbd5e1">'+mp+'%</span> vs model '+md+'%</span>'
      +'<span style="background:'+col+';color:#fff;font-weight:900;font-size:.62rem;border-radius:6px;padding:2px 8px">EDGE '+sign+g.mkt_edge+'%</span>'
      +'</div>';
  }
  return '<div onclick="_openNflGamePred('+i+')" style="background:#0a1120;border:1px solid '+bdr+';border-radius:14px;padding:13px 15px;cursor:pointer" onmouseover="this.style.borderColor=&#39;#3b2c63&#39;" onmouseout="this.style.borderColor=&#39;'+bdr+'&#39;">'
    +'<div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:7px">'
    +'<div style="font-weight:800;color:#94a3b8;font-size:.72rem;letter-spacing:.04em">'+_esc(g.away_abbr)+' @ '+_esc(g.home_abbr)+'</div>'
    +'<div style="display:flex;gap:6px;align-items:center">'+vb
    +'<span style="background:'+cc+';color:#fff;font-weight:900;font-size:.62rem;border-radius:6px;padding:2px 7px;letter-spacing:.04em">'+_esc(g.conf)+'</span>'
    +'<span style="background:rgba(167,139,250,.15);color:#c4b5fd;font-weight:900;font-size:.68rem;border-radius:6px;padding:2px 8px">PICK '+_esc(g.pick_abbr)+'</span>'
    +'</div></div>'
    +teamRow(g.away_abbr,g.away_sp,g.proj_away,g.win_away,!g.pick_home)
    +teamRow(g.home_abbr,g.home_sp,g.proj_home,g.win_home,g.pick_home)
    +totRow+mktRow
    +'<div style="margin-top:6px;font-size:.66rem;color:#94a3b8;line-height:1.5"><span style="color:#7c3aed;font-weight:800">Why:</span> '+drivers+'</div>'
    +_nflGpBetPanel(g,i)
    +'</div>';
}
function _openNflGamePred(i){
  var gp=(window.__NFL_GP__||[])[i]; if(!gp) return;
  var ov=document.getElementById('nfl-gp-modal');
  if(!ov){ov=document.createElement('div');ov.id='nfl-gp-modal';
    ov.style.cssText='position:fixed;inset:0;background:rgba(0,0,0,.85);z-index:10000;display:flex;align-items:center;justify-content:center;padding:16px;overflow:auto';
    ov.onclick=function(e){if(e.target===ov)ov.style.display='none';};
    document.body.appendChild(ov);}
  ov.style.display='flex';
  function gpBig(abbr,proj,win,isPick){
    return '<div style="flex:1;text-align:center;padding:12px 16px;background:#0f172a;border-radius:10px;border:1px solid '+(isPick?'#7c3aed':'#1e293b')+'">'
      +'<div style="font-size:1.3rem;font-weight:900;color:'+(isPick?'#e9d5ff':'#94a3b8')+'">'+_esc(abbr)+'</div>'
      +'<div style="font-size:2rem;font-weight:900;color:'+(isPick?'#4ade80':'#e2e8f0');+';margin:4px 0">'+_nflGpFix(proj)+'</div>'
      +'<div style="font-size:.8rem;color:#94a3b8">proj pts</div>'
      +'<div style="font-size:1.1rem;font-weight:800;color:'+(isPick?'#4ade80':'#94a3b8')+';margin-top:4px">'+win+'%</div>'
      +'</div>';
  }
  var totStr=(gp.total_line!=null?('proj <b>'+_nflGpFix(gp.proj_total)+'</b> · book line <b>'+_nflGpFix(gp.total_line)+'</b>'):'proj <b>'+_nflGpFix(gp.proj_total)+'</b> · no line posted');
  var driversHtml=(gp.drivers||[]).map(function(d){return '<li style="margin-bottom:4px">'+_esc(d)+'</li>';}).join('');
  ov.innerHTML='<div style="background:#0d1117;border:1px solid #7c3aed;border-radius:18px;max-width:500px;width:100%;padding:22px;box-shadow:0 20px 60px rgba(0,0,0,.7)">'
    +'<div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:14px">'
    +'<div style="font-size:1rem;font-weight:900;color:#c4b5fd">'+_esc(gp.away_abbr)+' @ '+_esc(gp.home_abbr)+'</div>'
    +'<button onclick="document.getElementById(&#39;nfl-gp-modal&#39;).style.display=&#39;none&#39;" style="background:none;border:none;color:#64748b;font-size:1.2rem;cursor:pointer">&#10005;</button></div>'
    +'<div style="font-size:.68rem;color:#64748b;margin-bottom:12px">Model picks the winner from L5 team offensive yards + opponent defensive strength + home-field advantage</div>'
    +'<div style="display:flex;gap:10px;margin-bottom:14px">'+gpBig(gp.away_abbr,gp.proj_away,gp.win_away,!gp.pick_home)+gpBig(gp.home_abbr,gp.proj_home,gp.win_home,gp.pick_home)+'</div>'
    +'<div style="margin-bottom:10px;color:#94a3b8;font-size:.76rem">'+totStr+'</div>'
    +(gp.mkt_edge!=null?('<div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:12px;background:#0a1120;border-radius:8px;padding:8px 12px">'
      +'<div><div style="font-size:.7rem;font-weight:800;color:#c4b5fd">Model pick: '+_esc(gp.pick_abbr)+'</div>'
      +'<div style="color:#e2e8f0;font-size:.8rem;margin-top:2px">model <b>'+(gp.pick_home?gp.win_home:gp.win_away)+'%</b> · market <b>'+(gp.pick_home?gp.mkt_home_pct:gp.mkt_away_pct)+'%</b></div></div>'
      +'<span style="background:'+(gp.mkt_edge>0?'#166534':(gp.mkt_edge<0?'#7f1d1d':'#334155'))+';color:#fff;font-weight:900;font-size:.74rem;border-radius:8px;padding:4px 11px">'+(gp.value_flag?'VALUE ':'EDGE ')+(gp.mkt_edge>0?'+':'')+gp.mkt_edge+'%</span>'
      +'</div>'):'')
    +'<div style="background:#0a1120;border-radius:8px;padding:10px 14px;font-size:.72rem;color:#94a3b8"><span style="color:#7c3aed;font-weight:800">Key factors:</span><ul style="margin:6px 0 0;padding-left:18px;line-height:1.7">'+driversHtml+'</ul></div>'
    +'<div style="color:#64748b;font-size:.62rem;margin-top:10px;text-align:center">Display only · not tracked · based on L5 team offensive production</div>'
    +'</div>';
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
  var payload=Object.assign({},src,{odds:odds,stake:stake,date_placed:window.__NFL_DATE__||''});
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
  var html='<div style="display:grid;grid-template-columns:repeat(auto-fill,minmax(300px,1fr));gap:12px">';
  for(var i=0;i<gp.length;i++) html+=_nflGpCard(gp[i],i);
  html+='</div>';
  document.getElementById('nfl-gp-body').innerHTML=html;
}
function renderResults(d){
  var res=document.getElementById('results');
  if(!d){ res.innerHTML=''; return; }
  if(d.error){
    res.innerHTML='<div class="err-box">'+d.error+'<div style="font-size:13px;color:#9ca3af;margin-top:6px;font-weight:400">NFL season runs September through February</div></div>';
    return;
  }
  window._nflState={d:d, all:(d.all||[])};
  window.__NFL_PLAYS__=d.all||[];
  window.__NFL_DATE__=d.date||'';
  var warn=d.data_warning?('<div class="err-box" style="margin-bottom:10px">'+d.data_warning+'</div>'):'';
  res.innerHTML=warn+'<div class="nfl-toolbar"><input id="nflSearch" type="text" placeholder="Search player…" oninput="_nflPaint(this.value)"/></div><div id="nflBody"></div>';
  _renderNflGamePredictor(d);
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

  // Chips (market chips are tappable -> all plays for that market)
  h+='<div class="chips">';
  h+='<div class="chip"><div class="val">'+((d.games||[]).length)+'</div><div class="lbl">Games</div></div>';
  _MORDER.forEach(function(m){ if(byM[m]&&byM[m].length){ h+='<div class="chip" style="cursor:pointer" onclick="_marketModal(&#39;'+m+'&#39;)"><div class="val">'+byM[m].length+'</div><div class="lbl">'+(_MLBL[m]||m)+'</div></div>'; }});
  h+='</div>';

  // ── 💯 100% Lock Board — every tracked sample hit at 100% ─────────────────
  var lockPicks=(d.all||[]).filter(function(p){
    return !_nflGameDone(p) && Number(p.score||p.dispScore)>=100 && p.pick;
  });
  if(q) lockPicks=lockPicks.filter(function(p){return (p.name||'').toLowerCase().indexOf(q)>=0;});
  lockPicks.sort(function(a,b){
    var ai=_MORDER.indexOf(a.mkt||a.label),bi=_MORDER.indexOf(b.mkt||b.label);
    return ai-bi||(a.name||'').localeCompare(b.name||'');
  });
  if(lockPicks.length){
    h+='<div style="background:linear-gradient(135deg,rgba(245,158,11,.1),rgba(74,222,128,.05));border:1px solid rgba(245,158,11,.4);border-radius:14px;margin-bottom:14px;overflow:hidden">'
      +'<div style="display:flex;align-items:center;gap:10px;padding:12px 16px;cursor:pointer;user-select:none" onclick="_secToggle(&#39;lock100&#39;)">'
      +'<span style="font-size:1.4rem;flex-shrink:0">&#128175;</span>'
      +'<div style="flex:1;min-width:0">'
      +'<div style="font-weight:900;font-size:1rem;color:#f59e0b;letter-spacing:.03em">100% Lock Board</div>'
      +'<div style="font-size:.72rem;color:#9ca3af;margin-top:2px">Every tracked sample hit — career vs opp <span style="color:#4ade80;font-weight:700">&amp;</span> L10 H/A both at 100%</div>'
      +'</div>'
      +'<div style="background:rgba(245,158,11,.2);border:1px solid rgba(245,158,11,.5);border-radius:20px;padding:3px 12px;font-size:.73rem;font-weight:900;color:#f59e0b;flex-shrink:0">'+lockPicks.length+' lock'+(lockPicks.length!==1?'s':'')+'</div>'
      +'<span id="car_lock100" style="color:#f59e0b;font-size:1rem;flex-shrink:0">&#9660;</span>'
      +'</div>'
      +'<div id="sec_lock100">'+nflCardGrid(lockPicks)+'</div>'
      +'</div>';
  }

  // Games (tappable -> all plays for that game)
  if((d.games||[]).length){
    h+='<div class="sec">- Games -- '+(d.date||'')+'</div><div class="games">';
    d.games.forEach(function(g,gi){
      var mu=(g.away_abbr||g.away_team||'?')+' @ '+(g.home_abbr||g.home_team||'?');
      h+='<div class="gcard" onclick="_gameModal('+gi+')"><div class="mu">'+mu+'</div><div class="gc-hint">tap for plays</div></div>';
    });
    h+='</div>';
  }

  // Card grids per market — separate OVER and UNDER boards, each top 10 + overflow.
  // Finished games (kickoff + 4h elapsed) drop off the board.
  var hasCards=false;
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

  // Under track (collapsible)
  var ub=_underBox(allF);
  if(ub){ h+=_collapseSec('under_track','⬇ UNDER Track', ub, expand); }

  // Special — Best Plays: same clickable cards as the top boards (open by default)
  var present=_MORDER.filter(function(m){return byM[m]&&byM[m].length;});
  if(present.length){
    h+='<div class="sec">⭐ Special — Best Plays</div>';
    present.forEach(function(m,i){
      var sp=(byM[m]||[]).filter(function(p){return !_nflGameDone(p);}).slice(0,6);
      if(!sp.length) return;
      h+=_collapseSec('sp_'+i, _mIcon(m)+' '+m, nflCardGrid(sp), true);
    });
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
  if(p.realLine==null||!p.market) return '';
  var side=forceSide||(p.pick==='UNDER'?'UNDER':'OVER');
  var odds=side==='OVER'?(p.realOdds!=null?p.realOdds:p.realUnderOdds):(p.realUnderOdds!=null?p.realUnderOdds:p.realOdds);
  var k='nf'+(++_nflBetN);
  window.__NFL_BET_SRC__[k]={
    name:p.name,pid:(p.pid!=null?String(p.pid):''),team:(p.team||''),opp:(p.opponent||''),
    category:(p.mkt||p.label||''),side:side,market:p.market,stat_label:(p.mkt||p.label||''),
    line:p.realLine,odds:(odds!=null?odds:null),date:(window.__NFL_DATE__||'')
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
var _nflTrkData=null,_nflTrkTabMode='cat';
function openNflTrackRecord(){
  var card=document.getElementById('nfl-track-card');
  if(!card) return;
  var mb=document.getElementById('nfl-mybets-card');
  if(mb) mb.style.display='none';
  if(card.style.display!=='none'){card.style.display='none';return;}
  card.style.display='block';
  card.scrollIntoView({behavior:'smooth',block:'start'});
  var dp=document.getElementById('nflTrkDate');
  if(dp&&!dp.value){var pd=document.getElementById('datePicker');if(pd) dp.value=pd.value;}
  _nflTrkDayName();
  if(!_nflTrkData) loadNflTrackRecord(); else renderNflTrackDay();
}
function _nflTrkDayName(){
  var dp=document.getElementById('nflTrkDate'),dn=document.getElementById('nflTrkDayName');
  if(!dp||!dn) return;
  try{var days=['Sunday','Monday','Tuesday','Wednesday','Thursday','Friday','Saturday'];
    dn.textContent=days[new Date(dp.value+'T12:00:00').getDay()];}catch(e){dn.textContent='';}
}
async function loadNflTrackRecord(){
  var body=document.getElementById('nflTrkBody');
  if(body) body.innerHTML='<p style="color:#9ca3af;padding:24px">Loading\u2026</p>';
  try{
    var r=await fetch('/api/track-record');
    if(!r.ok) throw new Error(await r.text());
    _nflTrkData=await r.json();
    renderNflTrackDay();
  }catch(e){
    if(body) body.innerHTML='<p style="color:#f87171;padding:16px">'+(e.message||'Error loading track record')+'</p>';
  }
}
function nflTrkSetTab(tab){
  _nflTrkTabMode=tab;
  var bc=document.getElementById('nflTrkBtnCat'),bl=document.getElementById('nflTrkBtnList');
  if(bc) bc.style.background=tab==='cat'?'#065f46':'#1f2937';
  if(bl) bl.style.background=tab==='list'?'#065f46':'#1f2937';
  renderNflTrackDay();
}
function renderNflTrackDay(){
  if(!_nflTrkData) return;
  var dp=document.getElementById('nflTrkDate');
  var selDate=dp?dp.value:'';
  var dates=_nflTrkData.dates||[];
  var dayData=selDate?dates.find(function(d){return d.date===selDate;}):null;
  var sumEl=document.getElementById('nflTrkSummary'),bodyEl=document.getElementById('nflTrkBody');
  if(!sumEl||!bodyEl) return;
  // Flatten rows from selected date (or all dates if none selected)
  var rows=[];
  if(dayData) rows=dayData.detail||[];
  else dates.forEach(function(d){(d.detail||[]).forEach(function(r){rows.push(r);});});
  var decided=rows.filter(function(r){return(r.result==='WIN'||r.result==='LOSS')&&r.odds!=null;});
  if(!decided.length&&selDate){
    sumEl.innerHTML='<p style="color:#9ca3af;padding:12px;text-align:center">No graded picks for '+selDate+'. Games may not be final yet.</p>';
    bodyEl.innerHTML='';return;
  }
  var stake=_nflTrkData.stake||20;
  var wins=decided.filter(function(r){return r.result==='WIN';}).length;
  var losses=decided.length-wins;
  var netPL=decided.reduce(function(a,r){return a+(r.profit||0);},0);
  var totalStaked=decided.length*stake;
  var roi=totalStaked?(netPL/totalStaked*100):null;
  var rate=decided.length?(wins/decided.length*100):null;
  var plColor=netPL>=0?'#4ade80':'#f87171';
  var plSign=netPL>=0?'+$':'-$';
  sumEl.innerHTML='<div class="nfl-trk-sum">'
    +'<span style="font-size:1.05rem;font-weight:900;color:#fff"><span style="color:#4ade80">'+wins+'</span>/<span style="color:#f87171">'+(wins+losses)+'</span>'
    +(rate!=null?' <span style="color:#9ca3af;font-size:.85rem;font-weight:600">('+rate.toFixed(1)+'%)</span>':'')+'</span>'
    +'<span style="font-family:monospace;font-weight:800;color:'+plColor+'">Net '+plSign+Math.abs(netPL).toFixed(0)+'</span>'
    +(roi!=null?'<span style="font-family:monospace;font-weight:700;color:'+plColor+'">ROI '+(roi>=0?'+':'')+roi.toFixed(1)+'%</span>':'')
    +'<span style="color:#6b7280;font-size:.8rem">$'+stake+'/play \u00b7 $20 flat</span>'
    +'</div>';
  bodyEl.innerHTML=_nflTrkTabMode==='cat'?_nflTrkCatHtml(decided):_nflTrkListHtml(decided);
}
function _nflTrkCatHtml(decided){
  if(!decided.length) return '<p style="color:#6b7280;padding:20px;text-align:center">No graded picks yet.</p>';
  var cats={};
  decided.forEach(function(r){
    var c=cats[r.category]=cats[r.category]||{w:0,l:0,pl:0,staked:0};
    if(r.result==='WIN') c.w++; else c.l++;
    c.pl+=(r.profit||0); c.staked+=20;
  });
  var entries=Object.entries(cats).sort(function(a,b){
    return ((b[1].pl/b[1].staked)||0)-((a[1].pl/a[1].staked)||0);
  });
  var rows=entries.map(function(e){
    var cat=e[0],c=e[1],total=c.w+c.l;
    var rate=total?(c.w/total*100):0;
    var roi=c.staked?(c.pl/c.staked*100):null;
    var plColor=c.pl>=0?'#4ade80':'#f87171';
    var barColor=rate>=70?'#4ade80':rate>=55?'#facc15':'#f87171';
    var barW=Math.min(100,Math.round(rate));
    return '<tr>'
      +'<td style="color:#fff;font-weight:700">'+cat+'</td>'
      +'<td style="font-family:monospace;color:#fff">'+c.w+'-'+c.l+'</td>'
      +'<td><div style="display:flex;align-items:center;gap:8px">'
      +'<div class="nfl-trk-bar-wrap"><div class="nfl-trk-bar" style="width:'+barW+'%;background:'+barColor+'"></div></div>'
      +'<span style="color:'+barColor+';font-weight:700;font-size:.82rem">'+rate.toFixed(0)+'%</span></div></td>'
      +'<td style="font-family:monospace;font-weight:800;color:'+plColor+'">'+(c.pl>=0?'+$':'-$')+Math.abs(c.pl).toFixed(0)+'</td>'
      +'<td style="font-family:monospace;font-weight:700;color:'+plColor+'">'+(roi!=null?(roi>=0?'+':'')+roi.toFixed(1)+'%':'—')+'</td>'
      +'</tr>';
  }).join('');
  return '<div class="tbl-wrap"><table class="nfl-trk-tbl">'
    +'<thead><tr><th>Category</th><th>Record</th><th>Hit Rate</th><th>Net P/L</th><th>ROI</th></tr></thead>'
    +'<tbody>'+rows+'</tbody></table></div>';
}
function _nflTrkListHtml(decided){
  if(!decided.length) return '<p style="color:#6b7280;padding:20px;text-align:center">No graded picks yet.</p>';
  var sorted=[].concat(decided).sort(function(a,b){return(b.profit||0)-(a.profit||0);});
  var rows=sorted.map(function(r){
    var plColor=r.result==='WIN'?'#4ade80':'#f87171';
    var pl=r.profit!=null?((r.profit>=0?'+$':'-$')+Math.abs(r.profit).toFixed(0)):'—';
    var odds=r.odds!=null?(r.odds>0?'+':'')+r.odds:'—';
    return '<tr>'
      +'<td style="color:#9ca3af;font-size:.78rem">'+r.category+'</td>'
      +'<td style="color:#fff;font-weight:700">'+r.name+'</td>'
      +'<td style="color:#6b7280">'+r.team+'</td>'
      +'<td style="color:#d1d5db">'+(r.side||'')+(r.line!=null?' '+r.line:'')+'</td>'
      +'<td style="font-family:monospace;color:#9ca3af">'+odds+'</td>'
      +'<td style="color:#6b7280">'+((r.actual!=null)?r.actual:'—')+'</td>'
      +'<td style="font-weight:800;color:'+plColor+'">'+r.result+'</td>'
      +'<td style="font-family:monospace;font-weight:700;color:'+plColor+'">'+pl+'</td>'
      +'</tr>';
  }).join('');
  return '<div class="tbl-wrap"><table class="nfl-trk-tbl">'
    +'<thead><tr><th>Category</th><th>Player</th><th>Team</th><th>Pick</th><th>Odds</th><th>Actual</th><th>Result</th><th>P/L</th></tr></thead>'
    +'<tbody>'+rows+'</tbody></table></div>';
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
</script>
</body>
</html>"""
