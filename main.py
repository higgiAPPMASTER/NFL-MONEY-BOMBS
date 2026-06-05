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
NFL_SEASONS   = [2024, 2023, 2022, 2021, 2020]

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
    "kansas city chiefs":"KC","los angeles chargers":"LAC","los angeles rams":"LA",
    "las vegas raiders":"LV","miami dolphins":"MIA","minnesota vikings":"MIN",
    "new england patriots":"NE","new orleans saints":"NO","new york giants":"NYG",
    "new york jets":"NYJ","philadelphia eagles":"PHI","pittsburgh steelers":"PIT",
    "seattle seahawks":"SEA","san francisco 49ers":"SF","tampa bay buccaneers":"TB",
    "tennessee titans":"TEN","washington commanders":"WSH","washington football team":"WSH",
    "raiders":"LV","rams":"LA","chargers":"LAC","49ers":"SF",
}

def _name_to_abbr(full_name: str) -> str:
    return _TEAM_NAME_TO_ABBR.get(full_name.lower().strip(), "")

def _norm(s): return re.sub(r"[^a-z0-9]", "", s.lower())
def _match(t1, t2):
    n1, n2 = _norm(t1), _norm(t2)
    return n1 == n2 or n1 in n2 or n2 in n1

app  = FastAPI(title="NFL Money Bombs", docs_url=None, redoc_url=None)
JOBS: Dict[str, Dict] = {}

# ── File cache ─────────────────────────────────────────────────────────────────
_CACHE_DIR = pathlib.Path("/tmp/mpa_cache")
_CACHE_DIR.mkdir(parents=True, exist_ok=True)
_CACHE_TTL = 6 * 3600

def _cache_get(date_key):
    p = _CACHE_DIR / f"nfl_{date_key}.json"
    try:
        if p.exists() and (time.time() - p.stat().st_mtime) < _CACHE_TTL:
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
_ODDS_TTL = 3 * 3600  # 3 hours

def _odds_cache_get(date_key):
    p = _CACHE_DIR / f"nfl_odds_{date_key}.json"
    try:
        if p.exists() and (time.time() - p.stat().st_mtime) < _ODDS_TTL:
            print(f"[OddsCache] HIT nfl/{date_key}")
            return json.loads(p.read_text(encoding="utf-8"))
    except Exception as e:
        print(f"[OddsCache] read error: {e}")
    return None

def _odds_cache_set(date_key, data):
    try:
        (_CACHE_DIR / f"nfl_odds_{date_key}.json").write_text(
            json.dumps(data, ensure_ascii=False), encoding="utf-8")
        print(f"[OddsCache] SET nfl/{date_key}")
    except Exception as e:
        print(f"[OddsCache] write error: {e}")

# ── nfl_data_py stats loader ───────────────────────────────────────────────────
_nfl_df = None
_nfl_df_lock = asyncio.Lock()

# ── ESPN H/A Lookup — (season, week, team_abbr) → 'HOME' or 'AWAY' ───────────
_HA_LOOKUP: dict = {}
_HA_LOADED = False
_HA_LOCK   = asyncio.Lock()

async def _build_ha_lookup():
    """Build home/away lookup from ESPN historical schedules (18 weeks x 5 seasons)."""
    global _HA_LOOKUP, _HA_LOADED
    async with _HA_LOCK:
        if _HA_LOADED:
            return
        print("[H/A] Building home/away lookup from ESPN schedules...")
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

# Direct nfl-verse CSV URLs (no package needed)
_NFL_CSV_URL  = "https://github.com/nflverse/nflverse-data/releases/download/player_stats/player_stats_{year}.csv"
_NFL_DEF_URL  = "https://github.com/nflverse/nflverse-data/releases/download/player_stats/player_stats_def_{year}.csv"
_NFL_KICK_URL = "https://github.com/nflverse/nflverse-data/releases/download/player_stats/player_stats_kicking_{year}.csv"
_KEEP_COLS   = ["player_display_name","player_id","headshot_url","recent_team","opponent_team",
                "season","week","season_type","rushing_yards","receiving_yards","passing_yards",
                "receptions","targets","passing_tds","rushing_tds","receiving_tds",
                "completions","attempts","interceptions","carries"]

def _dl_csv(url):
    """Download one nfl-verse CSV (regular season only) as a DataFrame."""
    import pandas as pd, io, urllib.request
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
    with urllib.request.urlopen(req, timeout=45) as r:
        d = pd.read_csv(io.BytesIO(r.read()), low_memory=False)
    if "season_type" in d.columns:
        d = d[d["season_type"] == "REG"]
    return d

def _load_nfl_stats_sync():
    """Download offense + defense + kicking CSVs from nfl-verse GitHub and merge
    into one frame on the shared schema (player, season, week, recent_team,
    opponent_team). The def/kicking files lack opponent_team, so it is derived
    from the offense schedule. No package needed beyond pandas."""
    global _nfl_df
    if _nfl_df is not None:
        return _nfl_df
    print("[NFL Data] Downloading from nfl-verse GitHub...")
    try:
        import pandas as pd
        # ---- offense (skill-position) ----
        frames = []
        for year in NFL_SEASONS:
            try:
                df_yr = _dl_csv(_NFL_CSV_URL.format(year=year))
                keep  = [c for c in _KEEP_COLS if c in df_yr.columns]
                frames.append(df_yr[keep])
                print(f"[NFL Data] off {year}: {len(df_yr)} rows")
            except Exception as e:
                print(f"[NFL Data] off {year} failed: {e}")
        if not frames:
            return None
        off = pd.concat(frames, ignore_index=True)
        # Compute anytime TD (offense only)
        td_cols = [c for c in ["rushing_tds","receiving_tds","passing_tds"] if c in off.columns]
        if td_cols:
            off["anytime_td"] = off[td_cols].sum(axis=1)

        # (season, week, team) -> opponent_team map, from offense rows (carry both)
        opp_map = {}
        try:
            sched = off[["season","week","recent_team","opponent_team"]].dropna()
            sched = sched.drop_duplicates(subset=["season","week","recent_team"])
            for t in sched.itertuples(index=False):
                opp_map[(int(t.season), int(t.week), str(t.recent_team))] = str(t.opponent_team)
        except Exception as e:
            print(f"[NFL Data] opp map failed: {e}")

        def _load_extra(tag, url_tpl, rename, computed):
            """Download a def/kicking CSV family, normalize to the offense schema
            (recent_team + derived opponent_team) and return the merged frame."""
            parts = []
            ident = ["player_display_name","player_id","headshot_url","season","week","season_type"]
            for year in NFL_SEASONS:
                try:
                    d = _dl_csv(url_tpl.format(year=year))
                    if "team" in d.columns:
                        d = d.rename(columns={"team":"recent_team"})
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
                    print(f"[NFL Data] {tag} {year}: {len(d)} rows")
                except Exception as e:
                    print(f"[NFL Data] {tag} {year} failed: {e}")
            return pd.concat(parts, ignore_index=True) if parts else None

        # ---- defense ----
        deff = _load_extra("def", _NFL_DEF_URL,
            rename={"def_tackles":"tackles_assists", "def_sacks":"def_sacks",
                    "def_interceptions":"def_ints"},
            computed={})
        # ---- kicking (kicking_points = 3*FG + PAT) ----
        kick = _load_extra("kick", _NFL_KICK_URL,
            rename={"fg_made":"fg_made"},
            computed={"kicking_points": lambda d: d.get("fg_made", 0).fillna(0)*3
                                                 + d.get("pat_made", 0).fillna(0)})

        all_frames = [off] + [f for f in (deff, kick) if f is not None]
        df = pd.concat(all_frames, ignore_index=True)
        _nfl_df = df
        print(f"[NFL Data] Total: {len(_nfl_df):,} rows (off {len(off):,}"
              + (f", def {len(deff):,}" if deff is not None else "")
              + (f", kick {len(kick):,}" if kick is not None else "") + ")")
        # H/A will be added after ESPN lookup is built
    except Exception as e:
        print(f"[NFL Data] Error: {e}")
        _nfl_df = None
    return _nfl_df

async def get_nfl_stats():
    # Ensure H/A lookup is built (runs concurrently with stat download)
    await _build_ha_lookup()
    async with _nfl_df_lock:
        if _nfl_df is not None:
            return _nfl_df
        loop = asyncio.get_event_loop()
        return await loop.run_in_executor(None, _load_nfl_stats_sync)

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
    try:
        async with httpx.AsyncClient(timeout=15) as c:
            if date_str >= today:
                r = await c.get(f"{ODDS_BASE}/sports/americanfootball_nfl/events",
                    params={"apiKey": ODDS_API_KEY, "dateFormat": "iso",
                            "commenceTimeFrom": f"{date_str}T00:00:00Z",
                            "commenceTimeTo":   f"{tomorrow}T06:00:00Z"})
                odds_evs = r.json() if r.is_success and isinstance(r.json(), list) else []
            else:
                r = await c.get(f"{ODDS_BASE}/historical/sports/americanfootball_nfl/events",
                    params={"apiKey": ODDS_API_KEY, "date": f"{date_str}T12:00:00Z", "dateFormat": "iso"})
                data = r.json()
                odds_evs = data.get("data", data) if isinstance(data, dict) else []
                odds_evs = odds_evs if isinstance(odds_evs, list) else []
            # Match to ESPN games
            for g in espn_games:
                for ev in odds_evs:
                    if (_match(g["home_team"], ev.get("home_team", "")) and
                            _match(g["away_team"], ev.get("away_team", ""))):
                        g["id"] = ev.get("id", "")
                        break
            return espn_games
    except Exception as e:
        print(f"[OddsAPI events] {e}"); return espn_games

async def get_prop_lines(event_id: str, date_str: str) -> List[Dict]:
    if not event_id or not ODDS_API_KEY: return []
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    is_past = date_str < today
    try:
        async with httpx.AsyncClient(timeout=15) as c:
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
            if not r.is_success: return []
            raw  = r.json()
            data = raw.get("data", raw) if isinstance(raw, dict) and "data" in raw else raw
            if not isinstance(data, dict): return []
            lines = {}
            for bm in data.get("bookmakers", []):
                for mkt in bm.get("markets", []):
                    mk = mkt.get("key", "")
                    if mk not in PROP_MARKETS: continue
                    for oc in mkt.get("outcomes", []):
                        name  = oc.get("description") or oc.get("name", "")
                        side  = oc.get("name", "")
                        point = oc.get("point")
                        price = oc.get("price")
                        if not name or point is None: continue
                        key = f"{_norm(name)}_{mk}"
                        if key not in lines:
                            lines[key] = {"name": name, "market": mk,
                                "label": PROP_LABELS.get(mk, mk),
                                "stat_col": PROP_TO_COL.get(mk, ""),
                                "line": float(point), "over_odds": None, "under_odds": None}
                        if side == "Over":  lines[key]["over_odds"] = price
                        elif side == "Under": lines[key]["under_odds"] = price
                break  # first bookmaker only
            return list(lines.values())
    except Exception as e:
        print(f"[OddsAPI props] {e}"); return []

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
    if pick == "UNDER" and under_rate is not None and under_rate >= 65 and (gap or 0) < 0:
        return "FADE"
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

    recent_team = pdf["recent_team"].mode().iloc[0] if not pdf.empty else ""
    if recent_team == home_abbr:
        opp_abbr = away_abbr; is_home = True;  home_road = "H"; side = "HOME"
    elif recent_team == away_abbr:
        opp_abbr = home_abbr; is_home = False; home_road = "R"; side = "AWAY"
    else:
        opp_abbr = home_abbr; is_home = None;  home_road = "";  side = "--"

    if recent_team and recent_team == opp_abbr:
        return None

    pdf_sorted = pdf.sort_values(["season", "week"], ascending=False) if not pdf.empty else pdf

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
    rate_a  = round(hits_a/tot_a*100, 1) if tot_a >= 2 else None

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
    rate_b   = round(hits_b/tot_b*100, 1) if tot_b >= 3 else None
    under_hits = sum(1 for v in l10_vals if v < line)
    under_rate = round(under_hits/tot_b*100, 1) if tot_b >= 3 else None

    # Hits vs the book line over last 10 games (any location)
    last10_any = pdf_sorted.head(10)
    la_vals    = last10_any[stat_col].dropna().tolist() if not last10_any.empty else []
    vsl_hits   = sum(1 for v in la_vals if v > line)
    vsl_tot    = len(la_vals)
    vsl_rate   = round(vsl_hits/vsl_tot*100, 1) if vsl_tot >= 1 else None

    rates = [r for r in [rate_a, rate_b] if r is not None]
    score = round(sum(rates)/len(rates), 1) if rates else 0

    ref_avg = avg_b if avg_b is not None else avg_a
    gap     = round(ref_avg - line, 1) if ref_avg is not None else None
    pick    = "OVER" if (ref_avg and ref_avg > line) else ("UNDER" if (ref_avg and ref_avg < line) else None)
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
        "name": name, "pid": pid, "team": recent_team, "opponent": opp_abbr or "--",
        "homeRoad": home_road, "side": side, "head": head, "game": pl.get("game",""),
        # market
        "mkt": label, "label": label, "market": market,
        "line": line, "dispLine": line, "realLine": line,
        "realOdds": pl.get("over_odds"), "realUnderOdds": pl.get("under_odds"),
        "over_odds": pl.get("over_odds"), "under_odds": pl.get("under_odds"),
        # averages
        "avg": avg_b if avg_b is not None else (avg_a if avg_a is not None else 0),
        "avgA": avg_a if avg_a is not None else 0,
        # career vs opp
        "rateA": rate_a or 0, "hitsA": hits_a, "totA": tot_a,
        # L10 H/A
        "rateB": rate_b or 0, "hitsB": hits_b, "totB": tot_b,
        # hits vs book line L10
        "vsLineHits": vsl_hits, "vsLineTotal": vsl_tot, "vsLineRate": vsl_rate or 0,
        # under track
        "underHits": under_hits, "underTotal": tot_b, "underRate": under_rate or 0, "underLine": line,
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

# ── Pipeline ───────────────────────────────────────────────────────────────────
async def run_pipeline(date_str: str) -> Dict:
    cached = _cache_get(date_str)
    if cached:
        return cached

    # 1. Get game schedule from ESPN
    espn_games = await get_espn_games(date_str)
    if not espn_games:
        return {"picks":[],"all":[],"error":f"No NFL games found for {date_str} — NFL season runs Sept–Feb"}

    # 2+3. Odds layer (event match + prop lines) — cached per date so re-runs
    #      within _ODDS_TTL reuse pulled odds instead of re-hitting the Odds API.
    #      The cached lines already carry team/abbr/game, so on a hit we skip the
    #      event-match call too. ESPN game count (espn_games) is unaffected.
    all_lines = _odds_cache_get(date_str)
    if all_lines is None:
        # 2. Match Odds API event IDs
        espn_games = await get_odds_events(date_str, espn_games)

        # 3. Get prop lines for each game
        all_lines = []
        for ev in espn_games:
            ev_id = ev.get("id", "")
            lines = await get_prop_lines(ev_id, date_str) if ev_id else []
            home_abbr = ev.get("home_abbr", "") or _name_to_abbr(ev.get("home_team",""))
            away_abbr = ev.get("away_abbr", "") or _name_to_abbr(ev.get("away_team",""))
            for l in lines:
                l["home_team"] = ev.get("home_team","")
                l["away_team"] = ev.get("away_team","")
                l["home_abbr"] = home_abbr
                l["away_abbr"] = away_abbr
                l["game"]      = ev.get("game","")
            all_lines.extend(lines)
        if all_lines:
            _odds_cache_set(date_str, all_lines)

    if not all_lines:
        return {"picks":[],"all":[],"games":len(espn_games),
                "error":"No prop lines available yet — check back closer to game time"}

    # 4. Load NFL stats (nfl_data_py — downloads once, cached in memory)
    print(f"[Pipeline] Loading NFL stats for {len(all_lines)} props...")
    df = await get_nfl_stats()
    if df is None:
        return {"picks":[],"all":[],"error":"Could not load NFL stats data — try again in a moment"}

    # 5. Analyze props synchronously (pandas is fast, no I/O)
    all_results = []
    for pl in all_lines:
        result = _analyze_prop(pl, df, pl.get("home_abbr",""), pl.get("away_abbr",""))
        if result:
            all_results.append(result)

    picks   = sorted([r for r in all_results if r.get("pick")],
                     key=lambda x: abs(x.get("gap") or 0), reverse=True)
    games_out = [{"home_team":g.get("home_team",""), "away_team":g.get("away_team",""),
                  "home_abbr":g.get("home_abbr",""), "away_abbr":g.get("away_abbr",""),
                  "game":g.get("game","")} for g in espn_games]
    result  = {"picks":picks, "all":all_results, "date":date_str,
               "games":games_out, "qualified":len(picks)}
    _cache_set(date_str, result)
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
    JOBS[job_id] = {"status":"running","result":None,"error":None}
    async def _run():
        try:
            result = await run_pipeline(date_str)
            JOBS[job_id].update({"status":"done","result":result})
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
<nav style="display:flex;justify-content:space-between;align-items:center"><div class="logo">Money <span>Picks</span> Arena</div><div style="display:flex;gap:8px;align-items:center"><button class="admin-only" onclick="openNflMyBets()" style="background:#0e7490;color:#fff;border:none;border-radius:10px;padding:9px 16px;font-weight:800;font-size:.82rem;cursor:pointer;white-space:nowrap">&#128176; My Bets</button></div></nav>
<style>
.nfl-bets-tbl{width:100%;border-collapse:collapse;font-size:.82rem}
.nfl-bets-tbl th{padding:7px 10px;text-align:left;font-size:.72rem;color:#9ca3af;font-weight:700;text-transform:uppercase;letter-spacing:.07em;border-bottom:1px solid #2a2a2a;white-space:nowrap}
.nfl-bets-tbl td{padding:8px 10px;border-bottom:1px solid #161616;vertical-align:middle;color:#e5e7eb}
.nfl-bets-tbl tr:last-child td{border-bottom:none}
.nfl-bets-tbl tr:hover td{background:rgba(255,255,255,.02)}
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

async function pollJob(){
  if(!jobId)return;
  try{
    const r=await fetch('/api/run/'+jobId);
    const d=await r.json();
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
      document.getElementById('statusMsg').innerHTML='<span class="spinner"></span>Analyzing player histories...';
    }
  }catch(e){}
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
  return '<span class="'+rateClass(rate)+'">'+hits+'/'+tot+' ('+rate+'%)</span>';
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
  var u=(picks||[]).filter(function(p){return p.underTotal>=2 && p.underRate>=60;})
      .sort(function(a,b){return b.underRate-a.underRate;}).slice(0,10);
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
  res.innerHTML='<div class="nfl-toolbar"><input id="nflSearch" type="text" placeholder="Search player…" oninput="_nflPaint(this.value)"/></div><div id="nflBody"></div>';
  _nflPaint('');
}

// Paints chips/games/special/cards into #nflBody. Re-runs on every search
// keystroke with a name filter; the search box itself lives outside #nflBody so
// it keeps focus. Sections are collapsible (default closed) to cut scrolling;
// a non-empty search auto-expands them so matches are visible.
function _nflPaint(q){
  var st=window._nflState||{}; var d=st.d; if(!d) return;
  q=(q||'').toLowerCase().trim();
  var expand=!!q;
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

  // Games (tappable -> all plays for that game)
  if((d.games||[]).length){
    h+='<div class="sec">- Games -- '+(d.date||'')+'</div><div class="games">';
    d.games.forEach(function(g,gi){
      var mu=(g.away_abbr||g.away_team||'?')+' @ '+(g.home_abbr||g.home_team||'?');
      h+='<div class="gcard" onclick="_gameModal('+gi+')"><div class="mu">'+mu+'</div><div class="gc-hint">tap for plays</div></div>';
    });
    h+='</div>';
  }

  // Card grids per market (collapsible pop-downs, Top 12 each)
  var hasCards=false;
  _MORDER.forEach(function(m,i){
    var g=(byM[m]||[]).slice(0,12);
    if(!g.length) return;
    hasCards=true;
    h+=_collapseSec('mkt_'+i, _mIcon(m)+' Top '+g.length+' '+m, nflCardGrid(g), expand);
  });
  if(!hasCards){
    h+='<div class="no-picks">No qualifying picks'+(q?' for "'+q+'"':' for '+(d.date||'today'))+'.</div>';
  }

  // Under track (collapsible)
  var ub=_underBox(allF);
  if(ub){ h+=_collapseSec('under_track','⬇ UNDER Track', ub, expand); }

  // Special - best plays (collapsible per category, 5 each)
  var present=_MORDER.filter(function(m){return byM[m]&&byM[m].length;});
  if(present.length){
    h+='<div class="sec">⭐ Special — Best Plays</div>';
    present.forEach(function(m,i){
      var rows=(byM[m]||[]).slice(0,5).map(_spRow).join('')||'<div class="mt" style="color:#6b7280;padding:6px">None</div>';
      h+=_collapseSec('sp_'+i, _mIcon(m)+' '+m, rows, expand);
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
