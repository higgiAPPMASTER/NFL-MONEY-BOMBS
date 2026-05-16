"""
NFL Money Bombs — main.py
FastAPI + Hub JWT gate + date picker.
Props: The Odds API (lines) + ESPN (career H/A game logs).
"""

import os, re, asyncio, uuid, time, json, pathlib, time
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

# ── File-based cache ──────────────────────────────────────────────────────────
_CACHE_DIR=pathlib.Path("/tmp/mpa_cache"); _CACHE_DIR.mkdir(parents=True,exist_ok=True)
_CACHE_TTL=6*3600

def _cache_get(date_key):
    p=_CACHE_DIR/f"nfl_{date_key}.json"
    try:
        if p.exists() and (time.time()-p.stat().st_mtime)<_CACHE_TTL:
            return json.loads(p.read_text(encoding="utf-8"))
    except: pass
    return None

def _cache_set(date_key,result):
    try: (_CACHE_DIR/f"nfl_{date_key}.json").write_text(json.dumps(result,ensure_ascii=False),encoding="utf-8")
    except: pass



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

@app.get("/api/verify-token")
async def verify_token(request: Request):
    auth = request.headers.get("Authorization","")
    tok  = auth.replace("Bearer ","").strip()
    if not tok or len(tok.split(".")) != 3:
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
async def _espn_schedule(date_str: str) -> List[Dict]:
    """ESPN NFL schedule — works for any historical or upcoming date."""
    dc = date_str.replace("-","")
    try:
        async with httpx.AsyncClient(timeout=10) as c:
            r = await c.get("https://site.api.espn.com/apis/site/v2/sports/football/nfl/scoreboard",
                           params={"dates": dc})
            if not r.is_success: return []
            games = []
            for ev in r.json().get("events",[]):
                comp = ev.get("competitions",[{}])[0]
                teams = {t["homeAway"]: t["team"] for t in comp.get("competitors",[])}
                home = teams.get("home",{})
                away = teams.get("away",{})
                games.append({"id":"","home_team":home.get("displayName",""),
                    "away_team":away.get("displayName",""),
                    "game":f"{away.get('displayName','')} @ {home.get('displayName','')}"})
            print(f"[ESPN] {len(games)} NFL games for {date_str}")
            return games
    except Exception as e:
        print(f"[ESPN] {e}"); return []

async def get_nfl_events(date_str: str) -> List[Dict]:
    """Get NFL games from ESPN (reliable) + match Odds API event IDs for prop lines."""
    espn_games = await _espn_schedule(date_str)
    if not espn_games: return []
    if ODDS_API_KEY:
        try:
            today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
            tomorrow = (datetime.fromisoformat(date_str) + timedelta(days=1)).strftime("%Y-%m-%d")
            async with httpx.AsyncClient(timeout=15) as c:
                if date_str >= today:
                    r = await c.get(f"{ODDS_BASE}/sports/americanfootball_nfl/events",
                        params={"apiKey":ODDS_API_KEY,"dateFormat":"iso",
                                "commenceTimeFrom":f"{date_str}T00:00:00Z",
                                "commenceTimeTo":f"{tomorrow}T06:00:00Z"})
                    odds_evs = r.json() if r.is_success and isinstance(r.json(),list) else []
                else:
                    r = await c.get(f"{ODDS_BASE}/historical/sports/americanfootball_nfl/events",
                        params={"apiKey":ODDS_API_KEY,"date":f"{date_str}T12:00:00Z","dateFormat":"iso"})
                    data = r.json()
                    odds_evs = data.get("data",data) if isinstance(data,dict) else []
                    odds_evs = odds_evs if isinstance(odds_evs,list) else []
                for g in espn_games:
                    for ev in odds_evs:
                        if (_match(g["home_team"],ev.get("home_team","")) and
                                _match(g["away_team"],ev.get("away_team",""))):
                            g["id"] = ev.get("id",""); break
        except Exception as e:
            print(f"[OddsAPI] {e}")
    return espn_games

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
async def find_espn_pid(name:str)->Optional[str]:
    info=await find_espn_player(name); return info.get("pid") if info else None

_NFL_TEAMS={
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

async def find_espn_player(name: str) -> Optional[Dict]:
    pid=None
    try:
        async with httpx.AsyncClient(timeout=10) as c:
            r=await c.get("https://site.web.api.espn.com/apis/search/v2",
                         params={"query":name,"limit":8,"sport":"nfl"})
            for result in r.json().get("results",[]):
                if result.get("type")!="player": continue
                for item in result.get("contents",[]):
                    if _norm(item.get("displayName",""))==_norm(name):
                        m=re.search(r"a:(\d+)",item.get("uid",""))
                        if m: pid=m.group(1); break
                if pid: break
    except Exception: pass
    if not pid: return None
    # Get team from gamelog
    team_abbr=""
    try:
        async with httpx.AsyncClient(timeout=10) as c:
            for season in ESPN_SEASONS[:2]:
                r=await c.get(f"{ESPN_BASE}/athletes/{pid}/gamelog",params={"season":season})
                if not r.is_success: continue
                for eid,ev in r.json().get("events",{}).items():
                    a=ev.get("team",{}).get("abbreviation","")
                    if a: team_abbr=a; break
                if team_abbr: break
    except Exception: pass
    team_name=_NFL_TEAMS.get(team_abbr.upper(),"")
    return {"pid":pid,"team_abbr":team_abbr,"team":team_name}

async def get_logs_vs_opp(pid: str, opp: str, is_home, stat_key: str) -> List[float]:
    """Fetch game logs using ESPN box score API. is_home=True/False/None(all)."""
    ESPN_SUMMARY="https://site.api.espn.com/apis/site/v2/sports/football/nfl/summary"
    values=[]
    async def fetch_season(season):
        try:
            async with httpx.AsyncClient(timeout=20) as c:
                r=await c.get(f"{ESPN_BASE}/athletes/{pid}/gamelog",params={"season":season})
                if not r.is_success: return
                events=r.json().get("events",{})
                for eid,ev in events.items():
                    tid=str(ev.get("team",{}).get("id",""))
                    hid=str(ev.get("homeTeamId",""))
                    ph=(tid==hid and tid!="")
                    if is_home is not None and ph!=is_home: continue
                    if opp and not _match(ev.get("opponent",{}).get("displayName",""),opp): continue
                    try:
                        r2=await c.get(ESPN_SUMMARY,params={"event":eid},timeout=10)
                        if not r2.is_success: continue
                        for box in r2.json().get("boxscore",{}).get("players",[]):
                            for sg in box.get("statistics",[]):
                                keys=[_norm(k) for k in sg.get("keys",[])]
                                sk=_norm(stat_key)
                                if sk not in keys: continue
                                idx=keys.index(sk)
                                for athlete in sg.get("athletes",[]):
                                    if str(athlete.get("athlete",{}).get("id",""))==str(pid):
                                        stats=athlete.get("stats",[])
                                        if idx<len(stats):
                                            try: values.append(float(stats[idx]))
                                            except: pass
                    except Exception: pass
        except Exception as e:
            print(f"[ESPN] s{season} pid{pid}: {e}")
    await asyncio.gather(*[fetch_season(s) for s in ESPN_SEASONS])
    return values

# ── Pipeline ───────────────────────────────────────────────────────────
async def run_pipeline(date_str: str) -> Dict:
    cached=_cache_get(date_str)
    if cached: return cached
    if not ODDS_API_KEY:
        return {"picks":[],"all":[],"error":"ODDS_API_KEY not configured on this server"}
    events = await get_nfl_events(date_str)
    if not events:
        return {"picks":[],"all":[],"error":f"No NFL games found for {date_str} — NFL season runs Sept–Feb"}
    all_lines = []
    for ev in events:
        ev_id=ev.get("id","")
        lines = await get_prop_lines(ev_id, date_str) if ev_id else []
        for l in lines:
            l["home_team"]=ev.get("home_team","")
            l["away_team"]=ev.get("away_team","")
            l["game"]=ev.get("game",f"{ev.get('away_team','')} @ {ev.get('home_team','')}")
        all_lines.extend(lines)
    if not all_lines:
        return {"picks":[],"all":[],"error":"No prop lines posted yet — check back closer to game time"}
    all_results=[]
    async def analyze(pl):
        name=pl["name"]; line=pl["line"]; label=pl["label"]
        info = await find_espn_player(name)
        if not info or not info.get("pid"): return
        pid=info["pid"]; ptm=info.get("team",""); pab=info.get("team_abbr","")
        home_team=pl.get("home_team",""); away_team=pl.get("away_team","")
        is_home=bool((ptm and _match(ptm,home_team)) or (pab and _match(pab,home_team)))
        opp=away_team if is_home else home_team; side="HOME" if is_home else "AWAY"
        # Sanity: player cannot play FOR the opponent
        if (ptm and _match(ptm,opp)) or (pab and _match(pab,opp)): return
        values = await get_logs_vs_opp(pid, opp, is_home, pl.get("stat_key",""))
        if not values: values = await get_logs_vs_opp(pid, opp, None, pl.get("stat_key",""))
        if not values:
            all_results.append({"name":name,"label":label,"line":line,"side":side,
                "opp":opp,"game":pl.get("game",""),"avg":None,"games":0,"history":"—",
                "pick":None,"pick_note":f"No H/A history vs {opp}",
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
    result={"picks":picks,"all":all_results,"date":date_str,"games":len(events)}
    _cache_set(date_str,result)
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
nav{position:fixed;top:0;width:100%;background:rgba(10,10,10,.95);backdrop-filter:blur(12px);border-bottom:1px solid #1c1c1c;z-index:100;padding:0 28px;height:80px;display:flex;align-items:center;justify-content:space-between}
.logo{font-family:'Playfair Display',serif;font-size:36px;font-weight:900;color:#f59e0b;letter-spacing:.02em;line-height:1}
.logo span{color:#fff}
.logo-right{display:none}
main{max-width:900px;margin:0 auto;padding:100px 20px 60px}
.hero{text-align:center;margin-bottom:32px}
.hero h1{font-family:'Playfair Display',serif;font-size:clamp(2rem,5vw,3rem);font-weight:900;margin-bottom:8px}
.hero h1 span{color:#f59e0b}
.hero p{color:#6b7280;font-size:14px}
.card{background:#161616;border:1px solid #262626;border-radius:16px;padding:24px;margin-bottom:20px}
.controls{display:flex;gap:12px;align-items:center}
.date-input{background:#0a0a0a;border:1px solid #2a2a2a;border-radius:10px;padding:11px 16px;color:#fff;font-size:14px;font-family:'Source Sans Pro',sans-serif;outline:none;transition:border .2s}
input[type=date]::-webkit-calendar-picker-indicator{filter:invert(1);opacity:.7;cursor:pointer}
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
footer{border-top:1px solid #1a1a1a;padding:24px;text-align:center;color:#374151;font-size:11px;margin-top:40px}
</style>
</head>
<body>
<nav>
  <div class="logo">Money <span>Picks</span> Arena</div>
</nav>
<main style="padding-top:24px">
  <div style="text-align:center;margin-bottom:32px">
    <h1 style="font-family:'Playfair Display',serif;font-size:2.6rem;font-weight:900;color:#fff;margin-bottom:6px">NFL <span style="color:#f59e0b">Money Bombs</span></h1>
    <p style="font-size:.85rem;color:#6b7280;letter-spacing:.15em;text-transform:uppercase">Player Props &middot; Daily Picks</p>
  </div>
  <div class="card" style="text-align:center;max-width:600px;margin:0 auto 20px">
    <h2 style="font-family:'Playfair Display',serif;font-size:1.5rem;font-weight:700;color:#fff;margin-bottom:20px">Run Today&#39;s Picks</h2>
    <div style="display:flex;align-items:center;justify-content:center;gap:12px;margin-bottom:20px">
      <label style="color:#9ca3af;font-weight:600;font-size:.85rem;letter-spacing:.08em;text-transform:uppercase">Date</label>
      <input type="date" id="datePicker" class="date-input" style="max-width:200px" value="__TODAY__" max="__TODAY__">
    </div>
    <div style="text-align:center">
      <button class="btn" id="runBtn" onclick="runPicks()">Run Picks</button>
    </div>
    <div class="status-msg" id="statusMsg" style="margin-top:12px;color:#6b7280;font-size:.85rem"></div>
  </div>
  <div id="results" style="display:none"></div>
</main>
<footer style="text-align:center;padding:32px 24px;color:#4b5563;font-size:.78rem;border-top:1px solid #1c1c1c;margin-top:24px;font-family:'Source Sans Pro',sans-serif">
  <div style="font-family:'Playfair Display',serif;color:#f59e0b;font-weight:700;font-size:.95rem;margin-bottom:6px">Money Picks Arena</div>
  <div>NFL Money Bombs &middot; Player Props &middot; Daily Picks</div>
  <div style="margin-top:8px;font-size:.7rem">For entertainment only. Not a betting service. Must be 18+. Please gamble responsibly.</div>
</footer>

<script>
// Hub JWT Token Gate
(function(){
  var HUB='https://www.moneypicksarena.com';
  var KEY='__mpa_token';
  var p=new URLSearchParams(window.location.search);
  var t=p.get('token');
  if(t){localStorage.setItem(KEY,t);window.history.replaceState({},'',window.location.pathname);}
  var tok=localStorage.getItem(KEY);
  if(!tok){window.location.href=HUB;return;}
  fetch('/api/verify-token',{headers:{'Authorization':'Bearer '+tok}})
    .then(function(r){if(!r.ok){localStorage.removeItem(KEY);window.location.href=HUB;}})
    .catch(function(){localStorage.removeItem(KEY);window.location.href=HUB;});
})();
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
// Date set server-side via __TODAY__

var jobId=null, pollTimer=null;

async function runPicks(){
  var date=document.getElementById('datePicker').value;
  if(!date){alert('Please select a date');return;}
  var btn=document.getElementById('runBtn');
  var status=document.getElementById('statusMsg');
  btn.disabled=true;
  btn.textContent='Running...';
  status.textContent='Fetching prop lines for '+date+'...';
  document.getElementById('results').style.display='none';
  try{
    const r=await fetch('/api/run',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({date:date})});
    const d=await r.json();
    jobId=d.job_id;
    pollTimer=setInterval(pollJob,2000);
  }catch(e){
    status.textContent='Error starting picks. Try again.';
    btn.disabled=false; btn.textContent='Run Picks';
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
      document.getElementById('runBtn').innerHTML='🔄 REFRESH';
      document.getElementById('statusMsg').textContent='';
    }else if(d.status==='error'){
      clearInterval(pollTimer);
      document.getElementById('statusMsg').textContent='❌ '+(d.error||'Unknown error');
      document.getElementById('runBtn').disabled=false;
      document.getElementById('runBtn').textContent='Run Picks';
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
    el.innerHTML='<div class="card" style="text-align:center;padding:40px"><h3 style="color:#6b7280;font-family:Playfair Display,serif">'+data.error+'</h3></div>';
    el.style.display='block';return;
  }
  var all=data.all||[];
  var html='<div style="background:#161616;border:1px solid #262626;border-radius:14px;overflow:hidden;margin-bottom:16px">';
  html+='<div style="padding:14px 20px;border-bottom:1px solid #262626">';
  html+='<span style="color:#f59e0b;font-size:.72rem;font-weight:900;letter-spacing:.18em;text-transform:uppercase">Player Props vs Opponent History</span>';
  html+='</div><div style="overflow-x:auto">';
  html+='<table style="width:100%;border-collapse:collapse;font-size:.82rem;background:#161616">';
  html+='<thead><tr style="border-bottom:1px solid rgba(245,158,11,.2)">';
  ["#","Player","Stat","H/A","Opponent","Line","Avg vs Opp","Gap","Games","History","Pick"].forEach(function(c){
    html+='<th style="padding:11px 12px;text-align:left;color:#f59e0b;font-size:.7rem;font-weight:700;text-transform:uppercase;letter-spacing:.1em;background:#1a1a1a;white-space:nowrap">'+c+'</th>';
  });
  html+='</tr></thead><tbody>';
  if(!all.length){
    html+='<tr><td colspan="11" style="text-align:center;padding:28px;color:#4b5563">No prop lines available yet. Check back closer to game time.</td></tr>';
  }else{
    all.forEach(function(p,i){
      var isO=p.pick==='OVER'||p.pick==='O';
      var isU=p.pick==='UNDER'||p.pick==='U';
      var clr=isO?'#4ade80':isU?'#f87171':'#4b5563';
      var pickTxt=p.pick==='OVER'?'O':p.pick==='UNDER'?'U':(p.pick||'--');
      var gap=p.gap!=null?(p.gap>0?'+':'')+p.gap:'--';
      var sideBg=p.side==='HOME'?'rgba(245,158,11,.12)':'rgba(99,102,241,.12)';
      var sideClr=p.side==='HOME'?'#f59e0b':'#818cf8';
      var rowBg=i%2===0?'#161616':'#141414';
      html+='<tr style="border-bottom:1px solid #1c1c1c;background:'+rowBg+'">';
      html+='<td style="padding:9px 12px;color:#4b5563">'+(i+1)+'</td>';
      html+='<td style="padding:9px 12px;font-weight:700;color:#fff;white-space:nowrap">'+p.name+'</td>';
      html+='<td style="padding:9px 12px;color:#f59e0b;font-size:.78rem;white-space:nowrap">'+p.label+'</td>';
      html+='<td style="padding:9px 12px"><span style="background:'+sideBg+';color:'+sideClr+';padding:2px 8px;border-radius:4px;font-size:.72rem;font-weight:700">'+(p.side||'--')+'</span></td>';
      html+='<td style="padding:9px 12px;color:#9ca3af;font-size:.78rem;white-space:nowrap">'+(p.opp||'--')+'</td>';
      html+='<td style="padding:9px 12px;font-family:monospace;font-weight:700;color:#fff">'+p.line+'</td>';
      html+='<td style="padding:9px 12px;font-family:monospace;font-weight:700;font-size:1rem;color:'+clr+'">'+(p.avg!=null?p.avg:'--')+'</td>';
      html+='<td style="padding:9px 12px;font-family:monospace;color:'+clr+';font-weight:700">'+gap+'</td>';
      html+='<td style="padding:9px 12px;color:#4b5563">'+(p.games||0)+'g</td>';
      html+='<td style="padding:9px 12px;font-family:monospace;font-size:.7rem;color:#4b5563;max-width:140px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis">'+(p.history||'--')+'</td>';
      html+='<td style="padding:9px 12px"><span style="color:'+clr+';font-weight:900;font-size:.95rem">'+pickTxt+'</span></td>';
      html+='</tr>';
    });
  }
  html+='</tbody></table></div>';
  html+='<p style="padding:8px 16px 12px;font-size:.72rem;color:#4b5563">';
  html+='<strong style="color:#f59e0b">Avg vs Opp</strong> = career H/A avg vs opponent &nbsp;|&nbsp;';
  html+='<strong style="color:#f59e0b">Pick</strong> = O if avg &gt; line, U if avg &lt; line';
  html+='</p></div>';
  el.innerHTML=html; el.style.display='block';
}
</script>
</body>
</html>"""

@app.get("/api/verify-token")
async def verify_token(request: Request):
    auth=request.headers.get("Authorization",""); tok=auth.replace("Bearer ","").strip()
    if not tok or len(tok.split("."))!=3: raise HTTPException(status_code=401,detail="Invalid token")
    return {"ok":True}

@app.get("/api/warm")
async def api_warm():
    today=datetime.now(timezone.utc).strftime("%Y-%m-%d")
    cached=_cache_get(today)
    if cached: return {"ok":True,"source":"cache","date":today,"picks":len(cached.get("picks",[]))}
    result=await run_pipeline(today)
    return {"ok":True,"source":"computed","date":today,"picks":len(result.get("picks",[])),"error":result.get("error")}

@app.post("/api/clear-cache")
async def clear_cache():
    for p in _CACHE_DIR.glob("nfl_*.json"): p.unlink(missing_ok=True)
    return {"ok":True}

@app.get("/", response_class=HTMLResponse)
async def index():
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    return HTMLResponse(HTML.replace("__TODAY__", today))
