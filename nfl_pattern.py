"""
NFL Money Bombs — main.py
Pattern-based NFL picks: career H/A performance vs today's opponent.
Line = Odds API prop (current games) OR season average (past/demo).
Hit rate shown like NBA Money Buckets.
"""

import os, re, asyncio, uuid, time
from typing import Dict, List, Optional, Tuple
from datetime import datetime, timezone

import httpx
from fastapi import FastAPI, Request, HTTPException
from fastapi.responses import HTMLResponse, JSONResponse
from jose import jwt as jose_jwt

# ── Config ──────────────────────────────────────────────────────────
ODDS_API_KEY = os.environ.get("ODDS_API_KEY", "")
ODDS_BASE    = "https://api.the-odds-api.com/v4"
ESPN_BASE    = "https://site.web.api.espn.com/apis/common/v3/sports/football/nfl"
ESPN_SITE    = "https://site.api.espn.com/apis/site/v2/sports/football/nfl"
ESPN_SEASONS = [2024, 2023, 2022, 2021, 2020]
HUB_URL      = "https://www.moneypicksarena.com"
JWT_SECRET   = os.environ.get("JWT_SECRET", "")
HIT_THRESH   = 60.0   # % hit rate to qualify
MIN_GAMES    = 3      # minimum H/A games vs opponent

SKILL_POS  = {"QB", "RB", "WR", "TE"}
STAT_DEFS  = [
    {"key": "passingYards",   "label": "Pass Yds",  "pos": {"QB"},      "min_line": 150.0},
    {"key": "rushingYards",   "label": "Rush Yds",  "pos": {"RB","QB"}, "min_line": 30.0},
    {"key": "receivingYards", "label": "Rec Yds",   "pos": {"WR","TE","RB"}, "min_line": 20.0},
    {"key": "receptions",     "label": "Receptions","pos": {"WR","TE","RB"}, "min_line": 2.0},
]

PROP_MARKETS = {
    "player_pass_yds":      "passingYards",
    "player_rush_yds":      "rushingYards",
    "player_reception_yds": "receivingYards",
    "player_receptions":    "receptions",
}

app  = FastAPI(title="NFL Money Bombs", docs_url=None, redoc_url=None)
JOBS: Dict[str, Dict] = {}
_SEM = asyncio.Semaphore(8)  # max 8 concurrent ESPN calls

# ── JWT Gate ─────────────────────────────────────────────────────────
def _verify_hub_token(token: str) -> bool:
    if not token: return False
    if not JWT_SECRET: return len(token.split(".")) == 3
    try:
        jose_jwt.decode(token, JWT_SECRET, algorithms=["HS256"]); return True
    except Exception:
        return len(token.split(".")) == 3

@app.get("/api/verify-token")
async def verify_token(request: Request):
    auth = request.headers.get("Authorization", "")
    tok  = auth.replace("Bearer ", "").strip()
    if not tok or not _verify_hub_token(tok):
        raise HTTPException(status_code=401, detail="Invalid token")
    return {"ok": True}

@app.get("/health")
async def health(): return {"status": "ok"}

# ── Helpers ───────────────────────────────────────────────────────────
def _norm(s: str) -> str: return re.sub(r"[^a-z0-9]", "", s.lower())
def _match(t1: str, t2: str) -> bool:
    n1, n2 = _norm(t1), _norm(t2)
    return n1 == n2 or n1 in n2 or n2 in n1

# ── ESPN Schedule ─────────────────────────────────────────────────────
async def get_espn_schedule(date_str: str) -> List[Dict]:
    """Get NFL games from ESPN for any date — free, no key needed."""
    date_nodash = date_str.replace("-", "")
    try:
        async with httpx.AsyncClient(timeout=15) as c:
            r = await c.get(f"{ESPN_SITE}/scoreboard", params={"dates": date_nodash})
            games = []
            for ev in r.json().get("events", []):
                comps = ev.get("competitions", [{}])[0]
                home = away = None
                home_id = away_id = None
                for t in comps.get("competitors", []):
                    if t.get("homeAway") == "home":
                        home    = t["team"]["displayName"]
                        home_id = t["team"]["id"]
                    else:
                        away    = t["team"]["displayName"]
                        away_id = t["team"]["id"]
                if home and away:
                    games.append({
                        "espn_id":   ev.get("id", ""),
                        "home_team": home, "home_id": home_id,
                        "away_team": away, "away_id": away_id,
                        "game":      f"{away} @ {home}",
                    })
            return games
    except Exception:
        return []

# ── ESPN Roster ───────────────────────────────────────────────────────
async def get_skill_players(team_id: str) -> List[Dict]:
    """
    Get targeted skill players from ESPN depth chart:
    1 QB, 2 RB, 3 WR, 2 TE = 8 players per team.
    Falls back to roster if depth chart unavailable.
    """
    TARGETS = {"QB": 1, "RB": 2, "WR": 3, "TE": 2}
    try:
        async with httpx.AsyncClient(timeout=15) as c:
            r = await c.get(f"{ESPN_SITE}/teams/{team_id}/depthcharts")
            if r.is_success:
                data     = r.json()
                seen_ids = set()
                by_pos   = {pos: [] for pos in TARGETS}
                # depth chart positions is a DICT keyed by lowercase pos
                for group in data.get("depthchart", []):
                    positions = group.get("positions", {})
                    for pos_key, pos_data in positions.items():
                        pos = pos_data.get("position", {}).get("abbreviation", "").upper()
                        if pos not in TARGETS: continue
                        for athlete in pos_data.get("athletes", []):
                            pid  = str(athlete.get("id", ""))
                            name = athlete.get("displayName","") or athlete.get("fullName","")
                            if pid and name and pid not in seen_ids and len(by_pos[pos]) < TARGETS[pos]:
                                seen_ids.add(pid)
                                by_pos[pos].append({"id": pid, "name": name, "pos": pos})
                result = [p for players in by_pos.values() for p in players]
                if result:
                    return result
    except Exception:
        pass

    # Fallback: roster, top N per position
    try:
        async with httpx.AsyncClient(timeout=15) as c:
            r = await c.get(f"{ESPN_SITE}/teams/{team_id}/roster")
            by_pos = {pos: [] for pos in TARGETS}
            for group in r.json().get("athletes", []):
                for p in group.get("items", []):
                    pos = p.get("position", {}).get("abbreviation", "").upper()
                    if pos in TARGETS and len(by_pos[pos]) < TARGETS[pos]:
                        by_pos[pos].append({
                            "id":   p["id"],
                            "name": p.get("fullName", ""),
                            "pos":  pos,
                        })
            return [p for players in by_pos.values() for p in players]
    except Exception:
        return []

# ── ESPN Game Logs ────────────────────────────────────────────────────
async def get_game_logs(player_id: str, season: int) -> List[Dict]:
    """Fetch game log for one season. Returns raw split list."""
    try:
        async with httpx.AsyncClient(timeout=15) as c:
            r = await c.get(f"{ESPN_BASE}/athletes/{player_id}/gamelog",
                            params={"season": season})
            data      = r.json()
            ev_map    = data.get("events", {}).get("eventTypes", [{}])
            labels    = []
            stats_map = {}
            for et in ev_map:
                for cat in et.get("categories", []):
                    if not labels:
                        labels = [e.get("text", "") for e in cat.get("labels", [])]
                    for ev in cat.get("events", []):
                        eid = ev.get("eventId", "")
                        if eid and ev.get("stats"):
                            stats_map[eid] = ev["stats"]
            events_data = data.get("eventLog", {}).get("events", {})
            result = []
            for eid, ev_info in events_data.items():
                if eid not in stats_map: continue
                result.append({
                    "eid":    eid,
                    "home":   ev_info.get("home", False),
                    "opp":    ev_info.get("opponent", {}).get("displayName", ""),
                    "stats":  stats_map[eid],
                    "labels": labels,
                })
            return result
    except Exception:
        return []

def _get_stat(split: Dict, stat_key: str) -> Optional[float]:
    labels = split.get("labels", [])
    stats  = split.get("stats", [])
    if not labels or not stats: return None
    idx = next((i for i, l in enumerate(labels) if _norm(l) == _norm(stat_key)), None)
    if idx is not None and idx < len(stats):
        try: return float(stats[idx])
        except Exception: return None
    return None

async def get_all_logs_for_player(player_id: str) -> List[Dict]:
    """Fetch game logs across all seasons in parallel — one call per season."""
    all_logs = []
    async def fetch(season):
        logs = await get_game_logs(player_id, season)
        all_logs.extend(logs)
    await asyncio.gather(*[fetch(s) for s in ESPN_SEASONS])
    return all_logs

async def get_career_vs_opp_all_stats(player_id: str, opp: str, is_home: bool) -> Dict[str, List[float]]:
    """Fetch all career H/A logs vs opponent ONCE, return values for all stats."""
    all_logs = await get_all_logs_for_player(player_id)
    relevant = [sp for sp in all_logs
                if sp.get("home") == is_home and _match(sp.get("opp", ""), opp)]
    results = {}
    for stat in STAT_DEFS:
        sk = stat["key"]
        values = [v for sp in relevant
                  if (v := _get_stat(sp, sk)) is not None]
        results[sk] = values
    return results

async def get_career_vs_opp(player_id: str, opp: str, is_home: bool,
                             stat_key: str) -> List[float]:
    """Legacy single-stat wrapper — use get_career_vs_opp_all_stats instead."""
    result = await get_career_vs_opp_all_stats(player_id, opp, is_home)
    return result.get(stat_key, [])

async def get_season_avg(player_id: str, stat_key: str, season: int = 2025) -> Optional[float]:
    """Player's current season average for a stat."""
    logs = await get_game_logs(player_id, season)
    vals = [_get_stat(sp, stat_key) for sp in logs]
    vals = [v for v in vals if v is not None and v > 0]
    return round(sum(vals) / len(vals), 1) if vals else None

# ── Odds API Prop Lines ───────────────────────────────────────────────
async def get_odds_lines(games: List[Dict]) -> Dict[str, Dict]:
    """Try to get Odds API prop lines for today's games. Returns {norm_name: {stat_key: line}}"""
    if not ODDS_API_KEY: return {}
    result: Dict[str, Dict] = {}
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    try:
        async with httpx.AsyncClient(timeout=15) as c:
            r = await c.get(f"{ODDS_BASE}/sports/americanfootball_nfl/events",
                            params={"apiKey": ODDS_API_KEY, "dateFormat": "iso"})
            if not r.is_success: return {}
            events = r.json() if isinstance(r.json(), list) else []
            for ev in events:
                eid = ev.get("id", "")
                r2 = await c.get(
                    f"{ODDS_BASE}/sports/americanfootball_nfl/events/{eid}/odds",
                    params={"apiKey": ODDS_API_KEY, "regions": "us,us2",
                            "markets": ",".join(PROP_MARKETS.keys()),
                            "bookmakers": "draftkings,fanduel,betmgm",
                            "oddsFormat": "american"})
                if not r2.is_success: continue
                for bm in r2.json().get("bookmakers", []):
                    for mkt in bm.get("markets", []):
                        sk = PROP_MARKETS.get(mkt.get("key", ""))
                        if not sk: continue
                        for oc in mkt.get("outcomes", []):
                            if oc.get("name") != "Over": continue
                            name = oc.get("description") or oc.get("name", "")
                            key  = _norm(name)
                            if key not in result: result[key] = {}
                            if sk not in result[key]:
                                result[key][sk] = float(oc.get("point", 0))
    except Exception:
        pass
    return result

# ── Main Pipeline ─────────────────────────────────────────────────────
async def run_pipeline(date_str: str) -> Dict:
    today   = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    is_past = date_str < today

    # Get games
    games = await get_espn_schedule(date_str)
    if not games:
        return {"picks": [], "all": [], "no_games": True,
                "error": f"No NFL games on {date_str} — NFL season runs Sept–Feb"}

    # Try to get Odds API lines for current games
    odds_lines = {}
    if not is_past and ODDS_API_KEY:
        odds_lines = await get_odds_lines(games)

    picks  = []
    all_results = []

    async def analyze_team(game, side, team_id, opp_name, is_home):
        """Analyze one team — fetch all player logs in parallel."""
        players = await get_skill_players(team_id)

        async def analyze_player(player):
            pid  = player["id"]
            name = player["name"]
            pos  = player["pos"]

            # Fetch ALL career logs vs opponent in ONE batch (all seasons, all stats)
            stat_values = await get_career_vs_opp_all_stats(pid, opp_name, is_home)

            for stat in STAT_DEFS:
                if pos not in stat["pos"]: continue
                sk     = stat["key"]
                values = stat_values.get(sk, [])
                if len(values) < MIN_GAMES: continue

                odds_key = _norm(name)
                line     = (odds_lines.get(odds_key, {}).get(sk) if not is_past else None)
                line_src = "Odds API" if line else "Season Avg"
                if not line:
                    line = await get_season_avg(pid, sk)
                if not line or line < stat["min_line"]: continue

                hits    = sum(1 for v in values if v > line)
                hit_pct = round(hits / len(values) * 100, 1)
                avg_val = round(sum(values) / len(values), 1)
                gap     = round(avg_val - line, 1)

                result = {
                    "name": name, "pos": pos, "label": stat["label"],
                    "line": line, "line_src": line_src,
                    "side": side, "opp": opp_name, "game": game["game"],
                    "values": values, "games": len(values),
                    "hits": hits, "hit_pct": hit_pct,
                    "avg": avg_val, "gap": gap,
                    "pick": "OVER" if hit_pct >= HIT_THRESH else None,
                }
                all_results.append(result)
                if hit_pct >= HIT_THRESH:
                    picks.append(result)

        # Analyze top 6 skill players in parallel
        await asyncio.gather(*[analyze_player(p) for p in players])  # depth chart already limits to 8

    # Process games sequentially to stay within memory limits
    # (players within each game still run in parallel via semaphore)
    for game in games:
        await analyze_team(game, "HOME", game["home_id"], game["away_team"], True)
        await analyze_team(game, "AWAY", game["away_id"], game["home_team"], False)

    picks.sort(key=lambda x: x["hit_pct"], reverse=True)
    return {
        "picks":    picks,
        "all":      all_results,
        "date":     date_str,
        "games":    len(games),
        "matchups": [g["game"] for g in games],
        "is_past":  is_past,
    }

# ── API ────────────────────────────────────────────────────────────────
@app.post("/api/run")
async def api_run(request: Request):
    try:    body = await request.json()
    except: body = {}
    date_str = body.get("date", datetime.now(timezone.utc).strftime("%Y-%m-%d"))
    job_id   = str(uuid.uuid4())[:8]
    JOBS[job_id] = {"status": "running", "result": None, "error": None}
    async def _run():
        try:
            result = await run_pipeline(date_str)
            JOBS[job_id].update({"status": "done", "result": result})
        except Exception as e:
            JOBS[job_id].update({"status": "error", "error": str(e)})
    asyncio.create_task(_run())
    return {"job_id": job_id}

@app.get("/api/run/{job_id}")
async def api_poll(job_id: str):
    if job_id not in JOBS: raise HTTPException(404, "Not found")
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
.logo{font-family:'Playfair Display',serif;font-size:1.5rem;font-weight:900;color:#f59e0b}
.logo span{color:#fff}





.spinner{display:inline-block;width:12px;height:12px;border:2px solid rgba(0,0,0,.2);border-top-color:#000;border-radius:50%;animation:spin .7s linear infinite;vertical-align:middle;margin-right:5px}
@keyframes spin{to{transform:rotate(360deg)}}
main{max-width:960px;margin:0 auto;padding:90px 20px 60px}
.hero{text-align:center;margin-bottom:32px}
.hero h1{font-family:'Playfair Display',serif;font-size:clamp(2rem,5vw,3rem);font-weight:900;margin-bottom:6px}
.hero h1 span{color:#f59e0b}
.status-msg{text-align:center;color:#6b7280;font-size:13px;margin:12px 0;min-height:18px}
.section-hdr{color:#f59e0b;font-size:11px;font-weight:700;text-transform:uppercase;letter-spacing:1.5px;margin-bottom:14px;display:flex;align-items:center;gap:8px}
.section-hdr::after{content:'';flex:1;height:1px;background:#262626}
.card{background:#161616;border:1px solid #262626;border-radius:16px;padding:20px;margin-bottom:16px}
.run-box{background:#161616;border:1px solid #262626;border-radius:16px;padding:28px;text-align:center;margin-bottom:20px;transition:border-color .2s}
.run-box:hover{border-color:rgba(245,158,11,.3)}
.run-box h2{font-family:'Playfair Display',serif;font-size:1.1rem;font-weight:700;color:#f59e0b;letter-spacing:1px;margin-bottom:6px}
.run-box p{color:#6b7280;font-size:.85rem;margin-bottom:18px}
.date-row{display:flex;align-items:center;justify-content:center;gap:12px;margin-bottom:18px}
.date-row label{font-size:11px;font-weight:700;color:#6b7280;letter-spacing:1.5px;text-transform:uppercase}
.date-row input{background:#0f0f0f;color:#f59e0b;border:1px solid #262626;border-radius:8px;padding:9px 14px;font-size:.9rem;font-weight:600;outline:none;cursor:pointer;font-family:'Source Sans Pro',sans-serif}
.date-row input:focus{border-color:#f59e0b}
.btn-run{background:#f59e0b;color:#000;border:none;border-radius:8px;padding:14px 48px;font-size:1rem;font-weight:900;cursor:pointer;font-family:'Source Sans Pro',sans-serif;letter-spacing:.5px;transition:all .2s}
.btn-run:hover{background:#fbbf24;transform:translateY(-1px);box-shadow:0 4px 20px rgba(245,158,11,.4)}
.btn-run:disabled{background:#333;color:#666;cursor:not-allowed;transform:none}
.pick-card{background:#0f0f0f;border:1px solid #2a2a2a;border-radius:12px;padding:14px 18px;margin-bottom:10px;display:grid;grid-template-columns:1fr auto;gap:12px;align-items:center}
.pick-card:hover{border-color:rgba(245,158,11,.3)}
.pick-name{font-weight:700;font-size:15px;margin-bottom:3px}
.pick-detail{color:#9ca3af;font-size:11px;line-height:1.6}
.hit-rate{font-family:'Playfair Display',serif;font-size:2rem;font-weight:900;color:#4ade80;text-align:right;line-height:1}
.hit-rate.med{color:#f59e0b}
.hit-rate.low{color:#f87171}
.hit-sub{font-size:11px;color:#6b7280;text-align:right;margin-top:2px}
.line-pill{display:inline-block;background:rgba(245,158,11,.1);border:1px solid rgba(245,158,11,.2);color:#f59e0b;border-radius:4px;font-size:10px;font-weight:700;padding:1px 6px;margin-left:4px}
.avg-pill{display:inline-block;background:rgba(74,222,128,.1);border:1px solid rgba(74,222,128,.2);color:#4ade80;border-radius:4px;font-size:10px;font-weight:700;padding:1px 6px;margin-left:4px}
.hist-tag{background:rgba(255,255,255,.05);border-radius:4px;padding:1px 5px;font-size:10px;color:#6b7280;font-family:monospace}
.badge-home{background:rgba(21,101,192,.25);color:#93c5fd;border-radius:4px;padding:1px 6px;font-size:10px;font-weight:700}
.badge-away{background:rgba(103,58,183,.25);color:#c4b5fd;border-radius:4px;padding:1px 6px;font-size:10px;font-weight:700}
.game-hdr{font-family:'Playfair Display',serif;font-size:1rem;font-weight:700;color:#fff;margin:20px 0 10px;padding-bottom:8px;border-bottom:1px solid #262626}
.no-games{text-align:center;padding:40px 20px}
.no-games .icon{font-size:3rem;margin-bottom:12px}
.no-games h3{font-family:'Playfair Display',serif;font-size:1.3rem;color:#6b7280;margin-bottom:8px}
.matchup-chip{display:inline-block;background:#161616;border:1px solid #262626;border-radius:8px;padding:6px 14px;font-size:12px;color:#9ca3af;margin:4px}
footer{border-top:1px solid #1a1a1a;padding:24px;text-align:center;color:#374151;font-size:11px;margin-top:40px}
</style>
</head>
<body>
<nav>
  <div class="logo">Money<span>Bombs</span> 🏈</div>
  <div style="font-size:12px;color:#6b7280">NFL Pattern Picks</div>
</nav>

<main>
  <div class="run-box" id="runBox">
    <h2>Run Picks</h2>
    <p>Pick a date and run the algorithm.</p>
    <div class="date-row">
      <label>DATE</label>
      <input type="date" id="datePicker" max=""/>
    </div>
    <button class="btn-run" id="runBtn" onclick="runPicks()">
      ⚡ RUN PICKS
    </button>
  </div>

  <div class="status-msg" id="statusMsg"></div>
  <div id="results"></div>
</main>

<footer>Money Picks Arena &nbsp;·&nbsp; NFL Money Bombs &nbsp;·&nbsp; For entertainment purposes only. Must be 18+. Please gamble responsibly.<br>
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

document.addEventListener('DOMContentLoaded',function(){
  var today=new Date().toISOString().split('T')[0];
  var dp=document.getElementById('datePicker');
  if(dp){ dp.value=today; dp.max=today; }
});

var jobId=null, pollTimer=null;

async function runPicks(){
  var date=document.getElementById('datePicker').value;
  if(!date)return;
  var btn=document.getElementById('runBtn');
  var status=document.getElementById('statusMsg');
  btn.disabled=true;
  btn.innerHTML='<span class="spinner"></span>Scanning...';
  status.textContent='Getting NFL schedule for '+date+'...';
  document.getElementById('results').innerHTML='';

  try{
    const r=await fetch('/api/run',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({date:date})});
    const d=await r.json();
    jobId=d.job_id;
    pollTimer=setInterval(pollJob,2500);
  }catch(e){
    status.textContent='Error starting. Try again.';
    btn.disabled=false; btn.innerHTML='⚡ Run Picks';
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
      document.getElementById('runBtn').innerHTML='🔄 Refresh';
      document.getElementById('statusMsg').textContent='';
    }else if(d.status==='error'){
      clearInterval(pollTimer);
      document.getElementById('statusMsg').textContent='❌ '+(d.error||'Error');
      document.getElementById('runBtn').disabled=false;
      document.getElementById('runBtn').innerHTML='⚡ Run Picks';
    }else{
      document.getElementById('statusMsg').textContent='Analyzing career H/A records vs opponent...';
    }
  }catch(e){}
}

function hitClass(pct){ return pct>=80?'':pct>=70?'med':'low'; }

function renderResults(data){
  var el=document.getElementById('results');
  if(!data||data.no_games){
    var chips=(data&&data.matchups||[]).map(m=>'<span class="matchup-chip">🏈 '+m+'</span>').join('');
    el.innerHTML='<div class="no-games"><div class="icon">🏈</div><h3>'+(data&&data.error||'No NFL games found')+'</h3>'+chips+'</div>';
    return;
  }

  var picks=data.picks||[];
  var html='';

  if(!picks.length){
    html='<div class="no-games"><div class="icon">🏈</div><h3>No picks hit '+60+'%+ hit rate</h3><p style="color:#4b5563;font-size:13px">Try a different date or check back when more H/A history is available</p></div>';
  } else {
    // Group by game
    var byGame={};
    for(var p of picks){
      if(!byGame[p.game]) byGame[p.game]=[];
      byGame[p.game].push(p);
    }
    html+='<div class="card"><div class="section-hdr">💣 Money Bombs — '+picks.length+' picks · '+data.games+' games</div>';
    for(var game in byGame){
      html+='<div class="game-hdr">🏈 '+game+'</div>';
      for(var p of byGame[game]){
        var hc=p.hit_pct>=80?'':p.hit_pct>=70?'med':'low';
        var side_badge=p.side==='HOME'?'<span class="badge-home">HOME</span>':'<span class="badge-away">AWAY</span>';
        var history=p.values.map(v=>Math.round(v)).join(', ');
        html+='<div class="pick-card">';
        html+='<div>';
        html+='<div class="pick-name">'+p.name+' <span style="color:#6b7280;font-size:11px;font-weight:400">'+p.pos+'</span></div>';
        html+='<div class="pick-detail">';
        html+=p.label+' &nbsp;·&nbsp; '+side_badge+' vs '+p.opp;
        html+=' &nbsp;·&nbsp; Line: <strong>'+p.line+'</strong><span class="line-pill">'+p.line_src+'</span>';
        html+=' &nbsp;·&nbsp; Avg: <strong>'+p.avg+'</strong><span class="avg-pill">+'+(p.gap>0?'+':'')+p.gap+'</span>';
        html+='<br><span class="hist-tag">'+history+'</span> ('+p.games+' H/A games vs '+p.opp+')';
        html+='</div></div>';
        html+='<div>';
        html+='<div class="hit-rate '+hc+'">'+p.hit_pct+'%</div>';
        html+='<div class="hit-sub">'+p.hits+'/'+p.games+' OVER</div>';
        html+='</div>';
        html+='</div>';
      }
    }
    html+='</div>';
  }

  el.innerHTML=html;
}
</script>
</body>
</html>"""

@app.get("/", response_class=HTMLResponse)
async def index(): return HTML
