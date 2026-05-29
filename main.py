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
    "player_rush_yds", "player_reception_yds", "player_pass_yds",
    "player_anytime_td", "player_receptions", "player_pass_tds",
]
PROP_LABELS = {
    "player_rush_yds":"Rush Yds", "player_reception_yds":"Rec Yds",
    "player_pass_yds":"Pass Yds", "player_anytime_td":"Anytime TD",
    "player_receptions":"Receptions", "player_pass_tds":"Pass TDs",
}
# nfl-verse column names
PROP_TO_COL = {
    "player_rush_yds":       "rushing_yards",
    "player_reception_yds":  "receiving_yards",
    "player_pass_yds":       "passing_yards",
    "player_anytime_td":     "anytime_td",   # computed
    "player_receptions":     "receptions",
    "player_pass_tds":       "passing_tds",
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
_NFL_CSV_URL = "https://github.com/nflverse/nflverse-data/releases/download/player_stats/player_stats_{year}.csv"
_KEEP_COLS   = ["player_display_name","recent_team","opponent_team",
                "season","week","season_type","rushing_yards","receiving_yards","passing_yards",
                "receptions","targets","passing_tds","rushing_tds","receiving_tds"]

def _load_nfl_stats_sync():
    """Download CSV files from nfl-verse GitHub — no package needed, just pandas."""
    global _nfl_df
    if _nfl_df is not None:
        return _nfl_df
    print("[NFL Data] Downloading from nfl-verse GitHub...")
    try:
        import pandas as pd, io, urllib.request
        frames = []
        for year in NFL_SEASONS:
            url = _NFL_CSV_URL.format(year=year)
            try:
                req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
                with urllib.request.urlopen(req, timeout=45) as r:
                    df_yr = pd.read_csv(io.BytesIO(r.read()), low_memory=False)
                    # Regular season only
                    if "season_type" in df_yr.columns:
                        df_yr = df_yr[df_yr["season_type"]=="REG"]
                    keep = [c for c in _KEEP_COLS if c in df_yr.columns]
                    frames.append(df_yr[keep])
                    print(f"[NFL Data] {year}: {len(df_yr)} rows")
            except Exception as e:
                print(f"[NFL Data] {year} failed: {e}")
        if not frames:
            return None
        import pandas as pd
        df = pd.concat(frames, ignore_index=True)
        # Compute anytime TD
        td_cols = [c for c in ["rushing_tds","receiving_tds","passing_tds"] if c in df.columns]
        if td_cols:
            df["anytime_td"] = df[td_cols].sum(axis=1)
        _nfl_df = df
        print(f"[NFL Data] Total: {len(_nfl_df):,} rows")
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

def _analyze_prop(pl: Dict, df, home_abbr: str, away_abbr: str) -> Optional[Dict]:
    """NHL-style: career vs opp + last 10 H/A + hit rates vs line."""
    name     = pl["name"]
    line     = pl["line"]
    label    = pl["label"]
    stat_col = pl.get("stat_col", "")

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
        opp_abbr = away_abbr; is_home = True;  side = "HOME"
    elif recent_team == away_abbr:
        opp_abbr = home_abbr; is_home = False; side = "AWAY"
    else:
        opp_abbr = home_abbr; is_home = None;  side = "--"

    if recent_team and recent_team == opp_abbr:
        return None

    # Career vs opponent (H/A filtered)
    vs_opp_all = pdf[pdf["opponent_team"] == opp_abbr] if opp_abbr else pdf
    if is_home is not None and _HA_LOADED and not vs_opp_all.empty:
        vs_ha = vs_opp_all[vs_opp_all.apply(lambda r: _ha_side(r, is_home), axis=1)]
        vs_opp = vs_ha if not vs_ha.empty else vs_opp_all
    else:
        vs_opp = vs_opp_all

    vs_vals  = vs_opp[stat_col].dropna().tolist() if not vs_opp.empty else []
    vs_avg   = round(sum(vs_vals)/len(vs_vals), 1) if vs_vals else None
    vs_hits  = sum(1 for v in vs_vals if v > line)
    vs_rate  = round(vs_hits/len(vs_vals)*100, 1) if len(vs_vals) >= 2 else None

    # Last 10 H/A games (any opponent)
    if is_home is not None and _HA_LOADED:
        l10_pool = pdf[pdf.apply(lambda r: _ha_side(r, is_home), axis=1)]
    else:
        l10_pool = pdf
    l10 = l10_pool.sort_values(["season","week"], ascending=False).head(10) if not l10_pool.empty else l10_pool
    l10_vals = l10[stat_col].dropna().tolist() if not l10.empty else []
    l10_avg  = round(sum(l10_vals)/len(l10_vals), 1) if l10_vals else None
    l10_hits = sum(1 for v in l10_vals if v > line)
    l10_rate = round(l10_hits/len(l10_vals)*100, 1) if len(l10_vals) >= 3 else None

    rates = [r for r in [vs_rate, l10_rate] if r is not None]
    score = round(sum(rates)/len(rates), 1) if rates else 0

    ref_avg = l10_avg if l10_avg is not None else vs_avg
    gap     = round(ref_avg - line, 1) if ref_avg is not None else None
    pick    = "OVER" if (ref_avg and ref_avg > line) else ("UNDER" if (ref_avg and ref_avg < line) else None)

    return {
        "name": name, "label": label, "line": line,
        "side": side, "opp": opp_abbr or "--", "game": pl.get("game",""),
        "team": recent_team,
        "vs_opp_avg": vs_avg, "vs_opp_games": len(vs_vals),
        "vs_opp_hits": vs_hits, "vs_opp_rate": vs_rate,
        "l10_avg": l10_avg, "l10_games": len(l10_vals),
        "l10_hits": l10_hits, "l10_rate": l10_rate,
        "score": score, "pick": pick, "gap": gap,
        "over_odds": pl.get("over_odds"), "under_odds": pl.get("under_odds"),
        "avg": vs_avg or l10_avg, "games": len(vs_vals),
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
    result  = {"picks":picks,"all":all_results,"date":date_str,"games":len(espn_games)}
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

@app.get("/", response_class=HTMLResponse)
async def index():
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    return HTMLResponse(HTML.replace("__TODAY__", today))

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
body{background:#0f0f0f;color:#fff;font-family:'Source Sans Pro',sans-serif;min-height:100vh}
nav{position:fixed;top:0;width:100%;background:rgba(10,10,10,.95);backdrop-filter:blur(12px);border-bottom:1px solid #1c1c1c;z-index:100;padding:0 32px;height:80px;display:flex;align-items:center}
.logo{font-family:'Playfair Display',serif;font-size:36px;font-weight:900;color:#f59e0b;letter-spacing:.02em;line-height:1}
.logo span{color:#fff}
main{max-width:900px;margin:0 auto;padding:100px 20px 60px}
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
.section-hdr{display:flex;align-items:center;gap:10px;font-size:.78rem;font-weight:700;color:#f59e0b;text-transform:uppercase;letter-spacing:.15em;margin-bottom:14px}
.section-hdr::after{content:'';flex:1;height:1px;background:rgba(245,158,11,.15)}
.tbl-wrap{overflow-x:auto;border-radius:14px;border:1px solid #262626}
table{width:100%;border-collapse:collapse;font-size:.82rem;background:#161616}
thead tr{border-bottom:1px solid rgba(245,158,11,.2)}
th{padding:11px 12px;text-align:left;color:#f59e0b;font-size:.7rem;font-weight:700;text-transform:uppercase;letter-spacing:.1em;background:#1a1a1a;white-space:nowrap}
td{padding:9px 12px;border-bottom:1px solid #1c1c1c;white-space:nowrap}
tr:nth-child(even) td{background:#141414}
tr:last-child td{border-bottom:none}
.err-card{background:#161616;border:1px solid #262626;border-radius:14px;padding:40px;text-align:center;color:#6b7280}
footer{text-align:center;padding:32px 24px;color:#4b5563;font-size:.78rem;border-top:1px solid #1c1c1c;margin-top:24px;font-family:'Source Sans Pro',sans-serif}
.ft-logo{font-family:'Playfair Display',serif;color:#f59e0b;font-weight:700;font-size:.95rem;margin-bottom:6px}
</style>
</head>
<body>
<nav><div class="logo">Money <span>Picks</span> Arena</div></nav>
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
    <button class="btn" id="runBtn" onclick="runPicks()">Run Picks</button>
    <div class="status-msg" id="statusMsg"></div>
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

var jobId=null, pollTimer=null;

function fmtOdds(o){return o==null?'':(o>0?'+':'')+o;}

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

function rateClass(r){
  if(r==null) return '#4b5563';
  return r>=75?'#4ade80':r>=55?'#f59e0b':'#f87171';
}

function fmtHits(hits, total, rate){
  if(total<2) return '<span style="color:#4b5563">N/A</span>';
  var clr=rateClass(rate);
  return '<span style="color:'+clr+';font-weight:700">'+hits+'/'+total+' ('+rate+'%)</span>';
}

function buildTopRow(p, i){
  var clr=rateClass(p.score);
  var sBg=p.side==='HOME'?'rgba(245,158,11,.12)':'rgba(99,102,241,.12)';
  var sClr=p.side==='HOME'?'#f59e0b':'#818cf8';
  var rBg=i%2===0?'#161616':'#141414';
  var pt=p.pick==='OVER'?'O':p.pick==='UNDER'?'U':(p.pick||'--');
  var pClr=p.pick==='OVER'||p.pick==='O'?'#4ade80':p.pick==='UNDER'||p.pick==='U'?'#f87171':'#4b5563';
  var l10Avg=p.l10_avg!=null?'<span style="color:#f59e0b;font-weight:700">'+p.l10_avg+'</span>':'<span style="color:#4b5563">--</span>';
  var vOppAvg=p.vs_opp_avg!=null?'<span style="font-weight:700">'+p.vs_opp_avg+'</span>':'<span style="color:#4b5563">N/A</span>';
  return '<tr style="background:'+rBg+'">'
    +'<td style="color:#4b5563;font-size:.85rem">'+(i+1)+'</td>'
    +'<td style="font-weight:700;color:#fff;white-space:nowrap">'+p.name+'</td>'
    +'<td style="color:#9ca3af;font-size:.78rem">'+(p.team||'--')+'</td>'
    +'<td style="color:#9ca3af;font-size:.78rem">'+(p.opp||'--')+'</td>'
    +'<td><span style="background:'+sBg+';color:'+sClr+';padding:2px 8px;border-radius:4px;font-size:.72rem;font-weight:700">'+(p.side||'--')+'</span></td>'
    +'<td style="font-family:monospace;font-weight:700">'+p.line+'</td>'
    +'<td style="font-family:monospace">'+vOppAvg+'</td>'
    +'<td style="font-family:monospace">'+l10Avg+'</td>'
    +'<td>'+fmtHits(p.vs_opp_hits,p.vs_opp_games,p.vs_opp_rate)+'</td>'
    +'<td>'+fmtHits(p.l10_hits,p.l10_games,p.l10_rate)+'</td>'
    +'<td style="font-weight:900;color:'+clr+';font-size:1.05rem">'+p.score+'</td>'
    +'<td><span style="color:'+pClr+';font-weight:900">'+pt+'</span></td>'
    +'</tr>';
}

function buildRow(p, i){
  var isO=p.pick==='OVER'||p.pick==='O';
  var isU=p.pick==='UNDER'||p.pick==='U';
  var clr=isO?'#4ade80':isU?'#f87171':'#4b5563';
  var pt=p.pick==='OVER'?'O':p.pick==='UNDER'?'U':(p.pick||'--');
  var gap=p.gap!=null?(p.gap>0?'+':'')+p.gap:'--';
  var sBg=p.side==='HOME'?'rgba(245,158,11,.12)':'rgba(99,102,241,.12)';
  var sClr=p.side==='HOME'?'#f59e0b':'#818cf8';
  var rBg=i%2===0?'#161616':'#141414';
  return '<tr style="background:'+rBg+'">'
    +'<td style="color:#4b5563">'+(i+1)+'</td>'
    +'<td style="font-weight:700;color:#fff">'+p.name+'</td>'
    +'<td style="color:#9ca3af;font-size:.78rem">'+(p.team||'--')+'</td>'
    +'<td style="color:#f59e0b;font-size:.78rem">'+p.label+'</td>'
    +'<td><span style="background:'+sBg+';color:'+sClr+';padding:2px 8px;border-radius:4px;font-size:.72rem;font-weight:700">'+(p.side||'--')+'</span></td>'
    +'<td style="color:#9ca3af;font-size:.78rem">'+(p.opp||'--')+'</td>'
    +'<td style="font-family:monospace;font-weight:700">'+p.line+'</td>'
    +'<td style="font-family:monospace;color:#f59e0b;font-weight:700">'+(p.vs_opp_avg!=null?p.vs_opp_avg:'--')+'</td>'
    +'<td style="font-family:monospace;font-weight:700;color:#f59e0b">'+(p.l10_avg!=null?p.l10_avg:'--')+'</td>'
    +'<td style="font-family:monospace;color:'+clr+';font-weight:700">'+(p.gap!=null?(p.gap>0?'+':'')+p.gap:'--')+'</td>'
    +'<td><span style="color:'+clr+';font-weight:900">'+pt+'</span></td>'
    +'</tr>';
}

function buildTopTable(rows){
  var h='<div class="card" style="padding:0;overflow:hidden;margin-bottom:16px">';
  h+='<div style="padding:14px 20px;border-bottom:1px solid #262626;display:flex;align-items:center;justify-content:space-between">';
  h+='<span style="color:#f59e0b;font-size:.72rem;font-weight:900;letter-spacing:.18em;text-transform:uppercase">Top 10 Money Bombs</span>';
  h+='<span style="background:rgba(245,158,11,.1);color:#f59e0b;padding:3px 12px;border-radius:999px;font-size:.75rem;font-weight:700">'+rows.length+' picks</span>';
  h+='</div><div class="tbl-wrap"><table><thead><tr>';
  var cols=['#','Player','Team','Opp','H/A','Line','Avg vs Opp','L10 H/A Avg','VS OPP HIT%','L10 H/A HIT%','Score','Pick'];
  cols.forEach(function(c){h+='<th>'+c+'</th>';});
  h+='</tr></thead><tbody>';
  if(!rows.length){
    h+='<tr><td colspan="12" style="text-align:center;padding:28px;color:#4b5563">No qualifying picks (need 3+ H/A games, 55%+ hit rate)</td></tr>';
  }else{
    rows.forEach(function(p,i){h+=buildTopRow(p,i);});
  }
  h+='</tbody></table></div>';
  h+='<p style="padding:6px 16px 10px;font-size:.72rem;color:#4b5563">';
  h+='<strong style="color:#f59e0b">VS OPP HIT%</strong> = career games vs opponent beating the line &nbsp;|&nbsp;';
  h+='<strong style="color:#f59e0b">L10 H/A HIT%</strong> = last 10 H/A games (any opp) beating the line &nbsp;|&nbsp;';
  h+='<strong style="color:#f59e0b">Score</strong> = avg of both hit rates';
  h+='</p></div>';
  return h;
}

function buildGameTable(rows){
  var cols=['#','Player','Team','Stat','H/A','Opp','Line','Avg vs Opp','L10 Avg','Gap','Pick'];
  var h='<table style="width:100%;border-collapse:collapse;background:#161616"><thead><tr style="border-bottom:1px solid rgba(245,158,11,.2)">';
  cols.forEach(function(c){h+='<th style="padding:10px 12px;text-align:left;color:#f59e0b;font-size:.7rem;font-weight:700;text-transform:uppercase;letter-spacing:.1em;background:#1a1a1a;white-space:nowrap">'+c+'</th>';});
  h+='</tr></thead><tbody>';
  rows.forEach(function(p,i){h+=buildRow(p,i);});
  h+='</tbody></table>';
  return h;
}

function toggleGame(n){
  var el=document.getElementById('game_'+n);
  var btn=document.getElementById('game_btn_'+n);
  if(!el) return;
  var hidden=el.style.display==='none';
  el.style.display=hidden?'block':'none';
  if(btn) btn.textContent=hidden?'Collapse':'Expand';
}

function renderResults(data){
  var el=document.getElementById('results');
  if(!data){el.innerHTML='';return;}
  if(data.error){
    el.innerHTML='<div class="err-card"><h3 style="font-family:Playfair Display,serif;margin-bottom:8px">'+data.error+'</h3><p style="font-size:13px">NFL season runs September through February</p></div>';
    return;
  }
  var all=data.all||[];
  if(!all.length){el.innerHTML='<div class="err-card">No prop lines found.</div>';return;}

  // Top 10: l10 >= 3 games, l10_rate >= 55%, sorted by score
  var qualified=all.filter(function(p){
    return p.l10_games>=3 && p.l10_rate!=null && p.l10_rate>=55 && p.pick;
  });
  qualified.sort(function(a,b){return b.score-a.score;});
  var top10=qualified.slice(0,10);

  var html=buildTopTable(top10);

  // All plays by game
  html+='<div style="display:flex;align-items:center;gap:10px;font-size:.78rem;font-weight:700;color:#f59e0b;text-transform:uppercase;letter-spacing:.15em;margin:24px 0 12px">';
  html+='All Plays by Game<span style="flex:1;height:1px;background:rgba(245,158,11,.15);display:inline-block;margin-left:8px"></span></div>';

  var games={},order=[];
  all.forEach(function(p){
    var g=p.game||'Unknown';
    if(!games[g]){games[g]=[];order.push(g);}
    games[g].push(p);
  });

  order.forEach(function(game,gi){
    var gPlays=games[game];
    var gPicks=gPlays.filter(function(p){return p.pick;}).length;
    html+='<div style="margin-bottom:10px">';
    html+='<div onclick="toggleGame('+gi+')" style="background:#161616;border:1px solid #262626;border-radius:12px;padding:12px 18px;cursor:pointer;display:flex;align-items:center;justify-content:space-between">';
    html+='<span style="font-weight:700;color:#fff;font-size:.92rem">'+game+'</span>';
    html+='<div style="display:flex;align-items:center;gap:10px">';
    html+='<span style="background:rgba(245,158,11,.1);color:#f59e0b;padding:3px 12px;border-radius:999px;font-size:.75rem;font-weight:700">'+gPlays.length+' props | '+gPicks+' picks</span>';
    html+='<button id="game_btn_'+gi+'" onclick="event.stopPropagation();toggleGame('+gi+')" style="background:none;border:1px solid #374151;color:#9ca3af;border-radius:6px;padding:3px 12px;font-size:.72rem;cursor:pointer">Expand</button>';
    html+='</div></div>';
    html+='<div id="game_'+gi+'" style="display:none;margin-top:6px;border-radius:12px;overflow:hidden;border:1px solid #262626">';
    html+=buildGameTable(gPlays);
    html+='</div></div>';
  });

  el.innerHTML=html;
}
</script>
</body>
</html>"""
