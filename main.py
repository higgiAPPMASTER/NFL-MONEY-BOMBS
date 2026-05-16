"""
NFL Money Bombs — main.py
FastAPI + Hub JWT gate + date picker.
Props: The Odds API (lines) + ESPN (career H/A game logs).
"""

import os, re, asyncio, uuid, time
from typing import Dict, List, Optional
from datetime import datetime, timedelta, timezone

import httpx
from fastapi import FastAPI, Request, HTTPException
from fastapi.responses import HTMLResponse, JSONResponse
from jose import jwt as jose_jwt

# ── Config ─────────────────────────────────────────────────────────────
ODDS_API_KEY = os.environ.get("ODDS_API_KEY", "")
ODDS_BASE    = "https://api.the-odds-api.com/v4"
ESPN_BASE    = "https://site.web.api.espn.com/apis/common/v3/sports/football/nfl"
ESPN_SEASONS = [2024, 2023, 2022, 2021, 2020]
HUB_URL      = "https://www.moneypicksarena.com"
JWT_SECRET   = os.environ.get("JWT_SECRET", "")

PROP_MARKETS = [
    "player_rush_yds","player_reception_yds","player_pass_yds",
    "player_anytime_td","player_receptions","player_pass_tds",
]
PROP_LABELS = {
    "player_rush_yds":"Rush Yds","player_reception_yds":"Rec Yds",
    "player_pass_yds":"Pass Yds","player_anytime_td":"Anytime TD",
    "player_receptions":"Receptions","player_pass_tds":"Pass TDs",
}
PROP_STAT_KEY = {
    "player_rush_yds":"rushingYards","player_reception_yds":"receivingYards",
    "player_pass_yds":"passingYards","player_anytime_td":"touchdowns",
    "player_receptions":"receptions","player_pass_tds":"passingTouchdowns",
}

app  = FastAPI(title="NFL Money Bombs", docs_url=None, redoc_url=None)
JOBS: Dict[str, Dict] = {}

# ── File-based Picks Cache ────────────────────────────────────────────────────
import pathlib
_CACHE_DIR = pathlib.Path("/tmp/mpa_cache")
_CACHE_DIR.mkdir(parents=True, exist_ok=True)
_CACHE_TTL = 6 * 3600  # 6 hours

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



# ── JWT Gate ───────────────────────────────────────────────────────────
def _verify_hub_token(token: str) -> bool:
    if not token: return False
    if not JWT_SECRET: return len(token.split(".")) == 3
    try:
        jose_jwt.decode(token, JWT_SECRET, algorithms=["HS256"]); return True
    except Exception:
        return len(token.split(".")) == 3

@app.get("/api/verify-token")
async def verify_token(request: Request):
    auth = request.headers.get("Authorization","")
    tok  = auth.replace("Bearer ","").strip()
    if not tok or not _verify_hub_token(tok):
        raise HTTPException(status_code=401, detail="Invalid token")
    return {"ok": True}

@app.get("/health")
async def health(): return {"status":"ok"}

# ── Helpers ────────────────────────────────────────────────────────────
def _norm(s): return re.sub(r"[^a-z0-9]","",s.lower())
def _match(t1,t2):
    n1,n2=_norm(t1),_norm(t2)
    return n1==n2 or n1 in n2 or n2 in n1

# ── Odds API ───────────────────────────────────────────────────────────
async def get_nfl_events(date_str: str) -> List[Dict]:
    """Get NFL games — ESPN for schedule (works any date), Odds API for event IDs."""
    # Always use ESPN for schedule — reliable for historical AND live
    espn_games = await _espn_schedule(date_str)
    if not espn_games:
        return []
    # Try to enrich with Odds API event IDs for prop line fetching
    if ODDS_API_KEY:
        try:
            odds_events = await _odds_events(date_str)
            # Match ESPN games to Odds API events by team name
            for g in espn_games:
                for ev in odds_events:
                    if (_match(g["home_team"], ev.get("home_team","")) and
                            _match(g["away_team"], ev.get("away_team",""))):
                        g["id"] = ev.get("id","")
                        break
        except Exception:
            pass
    return espn_games

async def _espn_schedule(date_str: str) -> List[Dict]:
    """ESPN NFL scoreboard — works for any historical or upcoming date."""
    date_compact = date_str.replace("-","")
    try:
        async with httpx.AsyncClient(timeout=10) as c:
            r = await c.get(
                "https://site.api.espn.com/apis/site/v2/sports/football/nfl/scoreboard",
                params={"dates": date_compact})
            if not r.is_success: return []
            games = []
            for ev in r.json().get("events",[]):
                comp = ev.get("competitions",[{}])[0]
                teams = {t["homeAway"]: t["team"] for t in comp.get("competitors",[])}
                home = teams.get("home",{})
                away = teams.get("away",{})
                games.append({
                    "id":        "",   # filled in by Odds API match if available
                    "home_team": home.get("displayName",""),
                    "away_team": away.get("displayName",""),
                    "home_abbr": home.get("abbreviation",""),
                    "away_abbr": away.get("abbreviation",""),
                    "game":      f"{away.get('displayName','')} @ {home.get('displayName','')}",
                })
            print(f"[ESPN] {len(games)} NFL games for {date_str}")
            return games
    except Exception as e:
        print(f"[ESPN] Schedule error: {e}")
        return []

async def _odds_events(date_str: str) -> List[Dict]:
    """Odds API events — current dates only, used for event IDs to fetch prop lines."""
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    try:
        async with httpx.AsyncClient(timeout=15) as c:
            if date_str >= today:
                tomorrow = (datetime.fromisoformat(date_str) + timedelta(days=1)).strftime("%Y-%m-%d")
                day_start = f"{date_str}T00:00:00Z"
                day_end   = f"{tomorrow}T06:00:00Z"
                r = await c.get(f"{ODDS_BASE}/sports/americanfootball_nfl/events",
                    params={"apiKey": ODDS_API_KEY, "dateFormat": "iso",
                            "commenceTimeFrom": day_start, "commenceTimeTo": day_end})
                return r.json() if r.is_success and isinstance(r.json(), list) else []
            else:
                hist_dt = f"{date_str}T12:00:00Z"
                r = await c.get(
                    f"{ODDS_BASE}/historical/sports/americanfootball_nfl/events",
                    params={"apiKey": ODDS_API_KEY, "date": hist_dt, "dateFormat": "iso"})
                data = r.json()
                events = data.get("data", data) if isinstance(data, dict) else data
                return events if isinstance(events, list) else []
    except Exception:
        return []

async def get_prop_lines(event_id: str, date_str: str = "") -> List[Dict]:
    if not ODDS_API_KEY: return []
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    is_past = date_str < today if date_str else False
    try:
        async with httpx.AsyncClient(timeout=15) as c:
            if is_past:
                base_url = f"{ODDS_BASE}/historical/sports/americanfootball_nfl/events/{event_id}/odds"
                hist_dt  = f"{date_str}T12:00:00Z"
                extra_params = {"date": hist_dt}
            else:
                base_url = f"{ODDS_BASE}/sports/americanfootball_nfl/events/{event_id}/odds"
                extra_params = {}
            r2 = await c.get(
                base_url,
                params={
                    "apiKey":     ODDS_API_KEY,
                    "regions":    "us,us2",
                    "markets":    ",".join(PROP_MARKETS),
                    "bookmakers": "draftkings,fanduel,betmgm",
                    "oddsFormat": "american",
                    **extra_params,
                })
            if not r2.is_success: return []
            raw = r2.json()
            resp_data = raw.get("data", raw) if isinstance(raw, dict) and "data" in raw else raw
            if not isinstance(resp_data, dict): resp_data = {}
            lines = {}
            for bm in resp_data.get("bookmakers",[]):
                for mkt in bm.get("markets",[]):
                    mk = mkt.get("key","")
                    if mk not in PROP_MARKETS: continue
                    for oc in mkt.get("outcomes",[]):
                        name  = oc.get("description") or oc.get("name","")
                        side  = oc.get("name","")
                        point = oc.get("point")
                        price = oc.get("price")
                        if not name or point is None: continue
                        key = f"{_norm(name)}_{mk}"
                        if key not in lines:
                            lines[key] = {"name":name,"market":mk,
                                "label":PROP_LABELS.get(mk,mk),
                                "stat_key":PROP_STAT_KEY.get(mk,""),
                                "line":float(point),"over_odds":None,"under_odds":None}
                        if side=="Over":  lines[key]["over_odds"]=price
                        elif side=="Under": lines[key]["under_odds"]=price
            return list(lines.values())
    except Exception: return []

# ── ESPN ───────────────────────────────────────────────────────────────
async def find_espn_pid(name: str) -> Optional[str]:
    info = await find_espn_player(name)
    return info.get("pid") if info else None

async def find_espn_player(name: str) -> Optional[Dict]:
    """Returns {pid, team_abbr, team_name} for an NFL player.
    Gets team from actual gamelog (reliable) not search API (returns 'NFL')."""
    # Step 1: find PID from search
    pid = None
    try:
        async with httpx.AsyncClient(timeout=10) as c:
            r = await c.get("https://site.web.api.espn.com/apis/search/v2",
                            params={"query":name,"limit":8,"sport":"nfl"})
            for result in r.json().get("results",[]):
                if result.get("type")!="player": continue
                for item in result.get("contents",[]):
                    dn = item.get("displayName","")
                    # Exact or close match
                    if _norm(dn)==_norm(name):
                        uid = item.get("uid","")
                        m   = re.search(r"a:(\d+)", uid)
                        if m:
                            pid = m.group(1)
                            break
                        m2  = re.search(r"/id/(\d+)", item.get("link",{}).get("web",""))
                        if m2:
                            pid = m2.group(1)
                            break
                if pid: break
    except Exception: pass

    if not pid:
        return None

    # Step 2: get team from most recent gamelog entry (much more reliable)
    team_abbr = ""
    team_name = ""
    try:
        async with httpx.AsyncClient(timeout=10) as c:
            for season in ESPN_SEASONS[:2]:
                r = await c.get(f"{ESPN_BASE}/athletes/{pid}/gamelog",
                                params={"season": season})
                if not r.is_success: continue
                events = r.json().get("events", {})
                for eid, ev in events.items():
                    t = ev.get("team", {})
                    if t.get("abbreviation"):
                        team_abbr = t.get("abbreviation","")
                        # Build full name from abbr
                        team_name = _abbr_to_name(team_abbr)
                        break
                if team_abbr: break
    except Exception: pass

    return {"pid": pid, "team_abbr": team_abbr, "team": team_name}

# NFL team abbreviation → display name mapping
_NFL_TEAMS = {
    "ARI":"Arizona Cardinals","ATL":"Atlanta Falcons","BAL":"Baltimore Ravens",
    "BUF":"Buffalo Bills","CAR":"Carolina Panthers","CHI":"Chicago Bears",
    "CIN":"Cincinnati Bengals","CLE":"Cleveland Browns","DAL":"Dallas Cowboys",
    "DEN":"Denver Broncos","DET":"Detroit Lions","GB":"Green Bay Packers",
    "HOU":"Houston Texans","IND":"Indianapolis Colts","JAX":"Jacksonville Jaguars",
    "KC":"Kansas City Chiefs","LAC":"Los Angeles Chargers","LAR":"Los Angeles Rams",
    "LV":"Las Vegas Raiders","MIA":"Miami Dolphins","MIN":"Minnesota Vikings",
    "NE":"New England Patriots","NO":"New Orleans Saints","NYG":"New York Giants",
    "NYJ":"New York Jets","PHI":"Philadelphia Eagles","PIT":"Pittsburgh Steelers",
    "SEA":"Seattle Seahawks","SF":"San Francisco 49ers","TB":"Tampa Bay Buccaneers",
    "TEN":"Tennessee Titans","WSH":"Washington Commanders",
}
def _abbr_to_name(abbr: str) -> str:
    return _NFL_TEAMS.get(abbr.upper(), abbr)

async def get_logs_vs_opp(pid: str, opp: str, is_home, stat_key: str) -> List[float]:
    """is_home=True/False for H/A filter; None = all games vs opp."""
    """
    Uses ESPN gamelog for event metadata (opponent, H/A) then fetches
    box score per matching game for actual stat values.
    Works reliably for historical and current seasons.
    """
    ESPN_SUMMARY = "https://site.api.espn.com/apis/site/v2/sports/football/nfl/summary"
    values = []

    async def fetch_season(season):
        try:
            async with httpx.AsyncClient(timeout=20) as c:
                r = await c.get(f"{ESPN_BASE}/athletes/{pid}/gamelog",
                                params={"season": season})
                if not r.is_success:
                    return
                events = r.json().get("events", {})
                # Find games matching H/A + opponent
                matching_eids = []
                for eid, ev in events.items():
                    team_id    = str(ev.get("team", {}).get("id", ""))
                    home_id    = str(ev.get("homeTeamId", ""))
                    player_home = (team_id == home_id and team_id != "")
                    if is_home is not None and player_home != is_home:
                        continue
                    opp_name = ev.get("opponent", {}).get("displayName", "")
                    if opp and not _match(opp_name, opp):
                        continue
                    matching_eids.append(eid)

                # Fetch box scores for matching games
                for eid in matching_eids:
                    try:
                        r2 = await c.get(ESPN_SUMMARY, params={"event": eid}, timeout=10)
                        if not r2.is_success:
                            continue
                        for box in r2.json().get("boxscore", {}).get("players", []):
                            for sg in box.get("statistics", []):
                                keys = [_norm(k) for k in sg.get("keys", [])]
                                sk   = _norm(stat_key)
                                if sk not in keys:
                                    continue
                                idx = keys.index(sk)
                                for athlete in sg.get("athletes", []):
                                    if str(athlete.get("athlete", {}).get("id", "")) == str(pid):
                                        stats = athlete.get("stats", [])
                                        if idx < len(stats):
                                            try:
                                                values.append(float(stats[idx]))
                                            except (ValueError, TypeError):
                                                pass
                    except Exception:
                        pass
        except Exception as e:
            print(f"[NFL ESPN] Season {season} pid {pid}: {e}")

    await asyncio.gather(*[fetch_season(s) for s in ESPN_SEASONS])
    return values

# ── Pipeline ───────────────────────────────────────────────────────────
async def run_pipeline(date_str: str) -> Dict:
    cached = _cache_get("nfl", date_str)
    if cached:
        return cached
    if not ODDS_API_KEY:
        return {"picks":[],"all":[],"error":"ODDS_API_KEY not configured on this server"}
    events = await get_nfl_events(date_str)
    if not events:
        return {"picks":[],"all":[],"error":f"No NFL games found for {date_str} — NFL season runs Sept–Feb"}
    all_lines = []
    for ev in events:
        ev_id = ev.get("id","")
        if ev_id:
            lines = await get_prop_lines(ev_id, date_str)
        else:
            # No Odds API event ID — can still show game but no prop lines
            lines = []
        for l in lines:
            l["home_team"] = ev.get("home_team","")
            l["away_team"] = ev.get("away_team","")
            l["game"]      = ev.get("game", f"{ev.get('away_team','')} @ {ev.get('home_team','')}")
        all_lines.extend(lines)
    if not all_lines:
        return {"picks":[],"all":[],"games":len(events),
                "error":f"Games found ({len(events)}) but no prop lines available yet — check back closer to game time or upgrade Odds API plan for historical props"}
    all_results=[]
    async def analyze(pl):
        name=pl["name"]; line=pl["line"]; label=pl["label"]
        # Look up player ESPN ID AND team
        player_info = await find_espn_player(name)
        if not player_info or not player_info.get("pid"):
            return
        pid = player_info["pid"]
        # Use full team name OR abbreviation for matching
        player_team      = player_info.get("team","")
        player_team_abbr = player_info.get("team_abbr","")
        home_team = pl.get("home_team","")
        away_team = pl.get("away_team","")
        # Determine home/away using both name and abbreviation
        is_home = (
            (player_team and _match(player_team, home_team)) or
            (player_team_abbr and _match(player_team_abbr, home_team))
        )
        opp  = away_team if is_home else home_team
        side = "HOME" if is_home else "AWAY"

        # Sanity check: player cannot play FOR the opponent — corrupted Odds API data
        if player_team and _match(player_team, opp):
            print(f"[NFL] Skip {name} — plays for opponent {opp} (corrupted event data)")
            return
        if player_team_abbr and _match(player_team_abbr, opp):
            print(f"[NFL] Skip {name} — plays for opponent {opp} (abbr match)")
            return

        values = await get_logs_vs_opp(pid, opp, is_home, pl.get("stat_key",""))
        if not values:
            # Fallback: try ALL games vs opponent (ignore H/A filter)
            values = await get_logs_vs_opp(pid, opp, None, pl.get("stat_key",""))
        if not values:
            all_results.append({"name":name,"label":label,"line":line,"side":side,
                "opp":opp,"game":pl.get("game",""),"avg":None,"games":0,"history":"—",
                "pick":None,"pick_note":f"No career history vs {opp}",
                "side":side,
                "over_odds":pl.get("over_odds"),"under_odds":pl.get("under_odds")})
            return
        avg=round(sum(values)/len(values),1)
        gap=round(avg-line,1)
        pick="OVER" if avg>line else ("UNDER" if avg<line else None)
        note=f"avg {avg} {'>' if avg>line else '<'} line {line} ({'+' if gap>0 else ''}{gap})"
        all_results.append({"name":name,"label":label,"line":line,"side":side,"opp":opp,
            "game":pl.get("game",""),"avg":avg,"games":len(values),
            "history":", ".join(str(int(v)) for v in values),"gap":gap,
            "pick":pick,"pick_note":note,
            "over_odds":pl.get("over_odds"),"under_odds":pl.get("under_odds")})
    await asyncio.gather(*[analyze(pl) for pl in all_lines])
    picks=sorted([r for r in all_results if r["pick"]],key=lambda x:abs(x.get("gap",0)),reverse=True)
    result = {"picks":picks,"all":all_results,"date":date_str,"games":len(events)}
    _cache_set("nfl", date_str, result)
    return result

# ── API ────────────────────────────────────────────────────────────────
@app.post("/api/run")
async def api_run(request: Request):
    body = await request.json() if request.headers.get("content-type","").startswith("application/json") else {}
    date_str = body.get("date", datetime.now(timezone.utc).strftime("%Y-%m-%d"))
    job_id = str(uuid.uuid4())[:8]
    JOBS[job_id] = {"status":"running","result":None,"error":None}
    async def _run():
        try:
            result = await run_pipeline(date_str)
            JOBS[job_id].update({"status":"done","result":result})
        except Exception as e:
            JOBS[job_id].update({"status":"error","error":str(e)})
    asyncio.create_task(_run())
    return {"job_id": job_id}


@app.get("/api/warm")
async def api_warm():
    """Pre-compute today's picks — called by cron-job.org at 10 AM."""
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    cached = _cache_get("nfl", today)
    if cached:
        return {"ok": True, "source": "cache", "date": today,
                "picks": len(cached.get("picks", []))}
    result = await run_pipeline(today)
    return {"ok": True, "source": "computed", "date": today,
            "picks": len(result.get("picks", [])),
            "error": result.get("error")}

@app.post("/api/clear-cache")
async def clear_cache():
    _cache_clear("nfl")
    return {"ok": True, "msg": "NFL cache cleared"}

@app.get("/api/run/{job_id}")
async def api_poll(job_id: str):
    if job_id not in JOBS: raise HTTPException(status_code=404, detail="Not found")
    return JOBS[job_id]

# ── Frontend ───────────────────────────────────────────────────────────
HTML = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>NFL Money Bombs</title>
<link href="https://fonts.googleapis.com/css2?family=Playfair+Display:wght@700;900&family=Source+Sans+Pro:wght@400;600;700&display=swap" rel="stylesheet">
<style>
*{margin:0;padding:0;box-sizing:border-box}
body{background:#0f0f0f;color:#fff;font-family:'Source Sans Pro',sans-serif;min-height:100vh}
nav{position:fixed;top:0;width:100%;background:rgba(10,10,10,.95);backdrop-filter:blur(12px);border-bottom:1px solid #1c1c1c;z-index:100;padding:0 28px;height:72px;display:flex;align-items:center;justify-content:space-between}
.logo{font-family:'Playfair Display',serif;font-size:36px;font-weight:900;color:#f59e0b;letter-spacing:.02em;line-height:1}
.logo span{color:#fff}
main{max-width:900px;margin:0 auto;padding:100px 20px 60px}
.hero{text-align:center;margin-bottom:32px}
.hero h1{font-family:'Playfair Display',serif;font-size:clamp(2rem,5vw,3rem);font-weight:900;margin-bottom:8px}
.hero h1 span{color:#f59e0b}
.hero p{color:#6b7280;font-size:14px}
.card{background:#161616;border:1px solid #262626;border-radius:16px;padding:24px;margin-bottom:20px}
.controls{display:flex;gap:12px;align-items:center}
.date-input{background:#0a0a0a;border:1px solid #2a2a2a;border-radius:8px;padding:11px 16px;color:#fff;font-size:14px;font-family:'Source Sans Pro',sans-serif;outline:none;transition:border .2s}
input[type=date]::-webkit-calendar-picker-indicator{filter:invert(1);opacity:.7;cursor:pointer}
input[type=date]::-webkit-calendar-picker-indicator:hover{opacity:1}
.date-input:focus{border-color:#f59e0b}
.btn{background:#f59e0b;color:#000;font-weight:700;padding:12px 28px;border:none;border-radius:8px;font-size:14px;cursor:pointer;font-family:'Source Sans Pro',sans-serif;transition:all .2s;white-space:nowrap}
.btn:hover{background:#fbbf24;transform:translateY(-1px);box-shadow:0 4px 20px rgba(245,158,11,.4)}
.btn:disabled{opacity:.5;cursor:not-allowed;transform:none}
.spinner{display:inline-block;width:14px;height:14px;border:2px solid rgba(0,0,0,.2);border-top-color:#000;border-radius:50%;animation:spin .7s linear infinite;vertical-align:middle;margin-right:6px}
@keyframes spin{to{transform:rotate(360deg)}}
.status-msg{color:#6b7280;font-size:13px;margin-top:10px;min-height:18px}
.picks-grid{display:flex;flex-direction:column;gap:10px}
.pick-card{background:#0f0f0f;border:1px solid #2a2a2a;border-radius:12px;padding:14px 18px;display:grid;grid-template-columns:1fr auto;gap:8px;align-items:center}
.pick-card:hover{border-color:rgba(245,158,11,.3)}
.pick-name{font-weight:700;font-size:14px;margin-bottom:2px}
.pick-detail{color:#9ca3af;font-size:11px;line-height:1.5}
.pick-badge{font-family:'Playfair Display',serif;font-size:1.5rem;font-weight:900;text-align:right}
.over{color:#4ade80}.under{color:#f87171}
.pick-note{font-size:11px;color:#6b7280;text-align:right}
.odds-pill{display:inline-block;background:rgba(245,158,11,.1);border:1px solid rgba(245,158,11,.25);color:#f59e0b;border-radius:4px;font-size:10px;font-weight:700;padding:1px 6px;margin-left:4px}
.section-hdr{color:#f59e0b;font-size:11px;font-weight:700;text-transform:uppercase;letter-spacing:1.5px;margin-bottom:14px;display:flex;align-items:center;gap:8px}
.section-hdr::after{content:'';flex:1;height:1px;background:#262626}
.no-games{text-align:center;padding:40px 20px}
.no-games .icon{font-size:3rem;margin-bottom:12px}
.no-games h3{font-family:'Playfair Display',serif;font-size:1.3rem;color:#6b7280;margin-bottom:8px}
.history-tag{background:rgba(255,255,255,.05);border-radius:4px;padding:1px 5px;font-size:10px;color:#6b7280;font-family:monospace}
footer{text-align:center;padding:32px 24px;color:#4b5563;font-size:.78rem;border-top:1px solid #1c1c1c;margin-top:24px;font-family:"Source Sans Pro",sans-serif}
.ft-logo{font-family:"Playfair Display",serif;color:#f59e0b;font-weight:700;font-size:.95rem;margin-bottom:6px}
</style>
</head>
<body>
<nav>
  <div class="logo">Money <span>Picks</span> Arena</div>
</nav>
<main>
  <div style="text-align:center;margin-bottom:32px;padding-top:20px">
    <h1 style="font-family:'Playfair Display',serif;font-size:2.6rem;font-weight:900;color:#fff;margin-bottom:6px">NFL <span style="color:#f59e0b">Money Bombs</span></h1>
    <p style="font-size:.85rem;color:#6b7280;letter-spacing:.15em;text-transform:uppercase">Player Props &middot; Daily Picks</p>
  </div>
  <div class="card" style="text-align:center;max-width:600px;margin:0 auto 20px">
    <h2 style="font-family:'Playfair Display',serif;font-size:1.5rem;font-weight:700;color:#fff;margin-bottom:20px">Run Today's Picks</h2>
    <div style="display:flex;align-items:center;justify-content:center;gap:12px;margin-bottom:20px">
      <label style="color:#9ca3af;font-weight:600;font-size:.85rem;letter-spacing:.08em;text-transform:uppercase">Date</label>
      <input type="date" id="datePicker" class="date-input" style="max-width:200px">
    </div>
    <div style="text-align:center">
      <button class="btn" id="runBtn" onclick="runPicks()">Run Picks</button>
    </div>
    <div class="status-msg" id="statusMsg"></div>
  </div>
  <div id="results" style="display:none"></div>
</main>
<footer>Money Picks Arena &nbsp;&middot;&nbsp; NFL Money Bombs &nbsp;·&nbsp; For entertainment purposes only. Must be 18+. Please gamble responsibly.<br>
<a href="https://www.ncpgambling.org" style="color:#374151">National Council on Problem Gambling: 1-800-522-4700</a></footer>

<script>
// ── Hub Token Gate ──────────────────────────────────────────────────
(function(){
  var HUB='https://www.moneypicksarena.com';
  var KEY='__mpa_token';
  var p=new URLSearchParams(window.location.search);
  var t=p.get('token');
  if(t){localStorage.setItem(KEY,t);window.history.replaceState({},'',window.location.pathname);}
  if(!localStorage.getItem(KEY)){window.location.href=HUB;}
})();

// ── Init date picker ────────────────────────────────────────────────
document.addEventListener('DOMContentLoaded',function(){
  var today=new Date().toISOString().split('T')[0];
  document.getElementById('datePicker').value=today;
  document.getElementById('datePicker').max=today;
});

var jobId=null, pollTimer=null;

async function runPicks(){
  var date=document.getElementById('datePicker').value;
  if(!date){alert('Please select a date');return;}
  var btn=document.getElementById('runBtn');
  var status=document.getElementById('statusMsg');
  btn.disabled=true;
  btn.innerHTML='<span class="spinner"></span>Running...';
  status.textContent='Fetching prop lines for '+date+'...';
  document.getElementById('results').style.display='none';
  try{
    const r=await fetch('/api/run',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({date:date})});
    const d=await r.json();
    jobId=d.job_id;
    pollTimer=setInterval(pollJob,2000);
  }catch(e){
    status.textContent='Error starting picks. Try again.';
    btn.disabled=false; btn.innerHTML='⚡ RUN PICKS';
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
      document.getElementById('runBtn').innerHTML=' REFRESH';
      document.getElementById('statusMsg').textContent='';
    }else if(d.status==='error'){
      clearInterval(pollTimer);
      document.getElementById('statusMsg').textContent='❌ '+(d.error||'Unknown error');
      document.getElementById('runBtn').disabled=false;
      document.getElementById('runBtn').innerHTML='⚡ RUN PICKS';
    }else{
      document.getElementById('statusMsg').textContent='Analyzing player histories...';
    }
  }catch(e){}
}

function fmtOdds(o){return o==null?'':(o>0?'+':'')+o;}

function renderResults(data){
  var el=document.getElementById('results');
  if(!data){el.style.display='none';return;}
  if(data.error){
    el.innerHTML='<div class="card" style="text-align:center;padding:40px"><h3 style="color:#6b7280;font-family:\'Playfair Display\',serif">'+data.error+'</h3><p style="color:#4b5563;font-size:13px;margin-top:8px">NFL season runs September through February</p></div>';
    el.style.display='block';return;
  }
  var all=data.all||[];
  var html='';

  // Props vs Opponent History table
  html+='<div style="background:#161616;border:1px solid #262626;border-radius:14px;overflow:hidden;margin-bottom:16px">';
  html+='<div style="padding:14px 20px;border-bottom:1px solid #262626">';
  html+='<span style="color:#f59e0b;font-size:.72rem;font-weight:900;letter-spacing:.18em;text-transform:uppercase"> Player Props vs Opponent History</span>';
  html+='</div>';
  html+='<div style="overflow-x:auto">';
  html+='<table style="width:100%;border-collapse:collapse;font-size:.82rem;background:#161616">';
  html+='<thead><tr style="border-bottom:1px solid rgba(245,158,11,.2)">';
  ['#','Player','Stat','H/A','Opponent','Line','Avg vs Opp','Gap','Games','History','Pick'].forEach(function(c){
    html+='<th style="padding:11px 12px;text-align:left;color:#f59e0b;font-size:.7rem;font-weight:700;text-transform:uppercase;letter-spacing:.1em;background:#1a1a1a;white-space:nowrap">'+c+'</th>';
  });
  html+='</tr></thead><tbody>';

  if(!all.length){
    html+='<tr><td colspan="11" style="text-align:center;padding:28px;color:#4b5563">No prop lines available yet &mdash; check back closer to tip-off.</td></tr>';
  } else {
    all.forEach(function(p,i){
      var isO=p.pick==='OVER'||p.pick==='O';
      var isU=p.pick==='UNDER'||p.pick==='U';
      var clr=isO?'#4ade80':isU?'#f87171':'#4b5563';
      var pickTxt=p.pick==='OVER'?'O':p.pick==='UNDER'?'U':(p.pick||'—');
      var gap=p.gap!=null?(p.gap>0?'+':'')+p.gap:'—';
      var sideBg=p.side==='HOME'?'rgba(245,158,11,.12)':'rgba(99,102,241,.12)';
      var sideClr=p.side==='HOME'?'#f59e0b':'#818cf8';
      var rowBg=i%2===0?'#161616':'#141414';
      html+='<tr style="border-bottom:1px solid #1c1c1c;background:'+rowBg+'">';
      html+='<td style="padding:9px 12px;color:#4b5563">'+(i+1)+'</td>';
      html+='<td style="padding:9px 12px;font-weight:700;color:#fff;white-space:nowrap">'+p.name+'</td>';
      html+='<td style="padding:9px 12px;color:#f59e0b;font-size:.78rem;white-space:nowrap">'+p.label+'</td>';
      html+='<td style="padding:9px 12px"><span style="background:'+sideBg+';color:'+sideClr+';padding:2px 8px;border-radius:4px;font-size:.72rem;font-weight:700">'+(p.side||'—')+'</span></td>';
      html+='<td style="padding:9px 12px;color:#9ca3af;font-size:.78rem;white-space:nowrap">'+(p.opp||'—')+'</td>';
      html+='<td style="padding:9px 12px;font-family:monospace;font-weight:700;color:#fff">'+p.line+'</td>';
      html+='<td style="padding:9px 12px;font-family:monospace;font-weight:700;font-size:1rem;color:'+clr+'">'+(p.avg!=null?p.avg:'—')+'</td>';
      html+='<td style="padding:9px 12px;font-family:monospace;color:'+clr+';font-weight:700">'+gap+'</td>';
      html+='<td style="padding:9px 12px;color:#4b5563">'+(p.games||0)+'g</td>';
      html+='<td style="padding:9px 12px;font-family:monospace;font-size:.7rem;color:#4b5563;max-width:140px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis">'+(p.history||'—')+'</td>';
      html+='<td style="padding:9px 12px"><span style="color:'+clr+';font-weight:900;font-size:.95rem">'+pickTxt+'</span></td>';
      html+='</tr>';
    });
  }
  html+='</tbody></table></div>';
  html+='<p style="padding:8px 16px 12px;font-size:.72rem;color:#4b5563">';
  html+='<strong style="color:#f59e0b">Avg vs Opp</strong> = career H/A avg vs today\'s opponent &nbsp;|&nbsp;';
  html+='<strong style="color:#f59e0b">Pick</strong> = O (Over) if avg &gt; line, U (Under) if avg &lt; line';
  html+='</p></div>';

  el.innerHTML=html; el.style.display='block';
}
</script>
</body>
</html>"""

@app.get("/", response_class=HTMLResponse)
async def index(): return HTML
