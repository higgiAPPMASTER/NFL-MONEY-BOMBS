"""
NFL Money Bombs — main.py
FastAPI server + HTML frontend + Hub JWT gate.
Props logic: The Odds API (lines) + ESPN (career H/A game logs).
"""

import os, re, asyncio, uuid, time
from typing import Dict, List, Optional
from datetime import datetime, timedelta, timezone

import httpx
from fastapi import FastAPI, Request, HTTPException
from fastapi.responses import HTMLResponse, JSONResponse
from jose import jwt as jose_jwt

# ── Config ────────────────────────────────────────────────────────────
ODDS_API_KEY = os.environ.get("ODDS_API_KEY", "")
ODDS_BASE    = "https://api.the-odds-api.com/v4"
ESPN_BASE    = "https://site.web.api.espn.com/apis/common/v3/sports/football/nfl"
ESPN_SEASONS = [2024, 2023, 2022, 2021, 2020]
HUB_URL      = "https://www.moneypicksarena.com"
JWT_SECRET   = os.environ.get("JWT_SECRET", "")

PROP_MARKETS = [
    "player_rush_yds", "player_reception_yds", "player_pass_yds",
    "player_anytime_td", "player_receptions", "player_pass_tds",
]
PROP_LABELS = {
    "player_rush_yds":      "Rush Yds",
    "player_reception_yds": "Rec Yds",
    "player_pass_yds":      "Pass Yds",
    "player_anytime_td":    "Anytime TD",
    "player_receptions":    "Receptions",
    "player_pass_tds":      "Pass TDs",
}
PROP_STAT_KEY = {
    "player_rush_yds":      "rushingYards",
    "player_reception_yds": "receivingYards",
    "player_pass_yds":      "passingYards",
    "player_anytime_td":    "touchdowns",
    "player_receptions":    "receptions",
    "player_pass_tds":      "passingTouchdowns",
}

# ── App ───────────────────────────────────────────────────────────────
app = FastAPI(title="NFL Money Bombs", docs_url=None, redoc_url=None)

# In-memory job store
JOBS: Dict[str, Dict] = {}

# ── JWT Gate ──────────────────────────────────────────────────────────
def _verify_hub_token(token: str) -> bool:
    if not token:
        return False
    if not JWT_SECRET:
        return len(token.split(".")) == 3
    try:
        jose_jwt.decode(token, JWT_SECRET, algorithms=["HS256"])
        return True
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
async def health():
    return {"status": "ok", "app": "NFL Money Bombs"}

# ── Helpers ───────────────────────────────────────────────────────────
def _normalize(s: str) -> str:
    return re.sub(r"[^a-z0-9]", "", s.lower())

def _teams_match(t1: str, t2: str) -> bool:
    n1, n2 = _normalize(t1), _normalize(t2)
    if n1 == n2 or n1 in n2 or n2 in n1:
        return True
    return bool(set(n1.split()) & set(n2.split()))

# ── Odds API ──────────────────────────────────────────────────────────
async def get_nfl_events() -> List[Dict]:
    if not ODDS_API_KEY:
        return []
    try:
        async with httpx.AsyncClient(timeout=15) as c:
            r = await c.get(f"{ODDS_BASE}/sports/americanfootball_nfl/events",
                            params={"apiKey": ODDS_API_KEY, "dateFormat": "iso"})
            return r.json() if r.is_success and isinstance(r.json(), list) else []
    except Exception:
        return []

async def get_prop_lines_for_event(event_id: str) -> List[Dict]:
    if not ODDS_API_KEY:
        return []
    try:
        async with httpx.AsyncClient(timeout=15) as c:
            r = await c.get(
                f"{ODDS_BASE}/sports/americanfootball_nfl/events/{event_id}/odds",
                params={
                    "apiKey":     ODDS_API_KEY,
                    "regions":    "us,us2",
                    "markets":    ",".join(PROP_MARKETS),
                    "bookmakers": "draftkings,fanduel,betmgm",
                    "oddsFormat": "american",
                })
            if not r.is_success:
                return []
            lines = {}
            for bm in r.json().get("bookmakers", []):
                for mkt in bm.get("markets", []):
                    mk = mkt.get("key", "")
                    if mk not in PROP_MARKETS:
                        continue
                    for oc in mkt.get("outcomes", []):
                        name  = oc.get("description") or oc.get("name", "")
                        side  = oc.get("name", "")
                        point = oc.get("point")
                        price = oc.get("price")
                        if not name or point is None:
                            continue
                        key = f"{_normalize(name)}_{mk}"
                        if key not in lines:
                            lines[key] = {
                                "name":       name,
                                "market":     mk,
                                "label":      PROP_LABELS.get(mk, mk),
                                "stat_key":   PROP_STAT_KEY.get(mk, ""),
                                "line":       float(point),
                                "over_odds":  None,
                                "under_odds": None,
                            }
                        if side == "Over":   lines[key]["over_odds"]  = price
                        elif side == "Under": lines[key]["under_odds"] = price
            return list(lines.values())
    except Exception:
        return []

# ── ESPN ──────────────────────────────────────────────────────────────
async def find_espn_player_id(full_name: str) -> Optional[str]:
    try:
        async with httpx.AsyncClient(timeout=10) as c:
            r = await c.get("https://site.web.api.espn.com/apis/search/v2",
                            params={"query": full_name, "limit": 5, "sport": "nfl"})
            for result in r.json().get("results", []):
                if result.get("type") != "player":
                    continue
                for item in result.get("contents", []):
                    if _normalize(item.get("displayName","")) == _normalize(full_name):
                        uid = item.get("uid","")
                        m = re.search(r"a:(\d+)", uid)
                        if m: return m.group(1)
                        m2 = re.search(r"/id/(\d+)", item.get("link",{}).get("web",""))
                        if m2: return m2.group(1)
    except Exception:
        pass
    return None

async def get_player_logs_vs_opp(player_id: str, opp_name: str,
                                  side: str, stat_key: str) -> List[float]:
    is_home = (side == "HOME")
    values  = []
    async def fetch_season(season: int):
        try:
            async with httpx.AsyncClient(timeout=15) as c:
                r = await c.get(f"{ESPN_BASE}/athletes/{player_id}/gamelog",
                                params={"season": season})
                if not r.is_success: return
                data      = r.json()
                ev_map    = data.get("events",{}).get("eventTypes",[{}])
                labels    = []
                stats_map = {}
                for et in ev_map:
                    for cat in et.get("categories",[]):
                        if not labels:
                            labels = [e.get("text","") for e in cat.get("labels",[])]
                        for ev in cat.get("events",[]):
                            eid = ev.get("eventId","")
                            if eid and ev.get("stats"):
                                stats_map[eid] = ev["stats"]
                for eid, ev_info in data.get("eventLog",{}).get("events",{}).items():
                    if eid not in stats_map: continue
                    if ev_info.get("home", False) != is_home: continue
                    opp = ev_info.get("opponent",{}).get("displayName","")
                    if not _teams_match(opp, opp_name): continue
                    raw = stats_map[eid]
                    if not labels or not raw: continue
                    try:
                        idx = next((i for i,l in enumerate(labels)
                                    if _normalize(l)==_normalize(stat_key)), None)
                        if idx is not None and idx < len(raw):
                            values.append(float(raw[idx]))
                    except Exception: pass
        except Exception: pass
    await asyncio.gather(*[fetch_season(s) for s in ESPN_SEASONS])
    return values

# ── Pipeline ──────────────────────────────────────────────────────────
async def run_nfl_props() -> Dict:
    if not ODDS_API_KEY:
        return {"picks":[], "all":[], "error":"ODDS_API_KEY not set on this server"}
    events = await get_nfl_events()
    if not events:
        return {"picks":[], "all":[], "error":"No NFL games found — season may be off or no games this week"}
    all_lines = []
    for event in events:
        lines = await get_prop_lines_for_event(event["id"])
        for l in lines:
            l["home_team"] = event.get("home_team","")
            l["away_team"] = event.get("away_team","")
        all_lines.extend(lines)
    if not all_lines:
        return {"picks":[], "all":[], "error":"No prop lines posted yet — check back closer to game time"}

    all_results = []
    async def analyze(pl: Dict):
        name    = pl["name"]
        line    = pl["line"]
        label   = pl["label"]
        side    = "AWAY"
        opp     = pl["home_team"]
        pid = await find_espn_player_id(name)
        if not pid: return
        values = await get_player_logs_vs_opp(pid, opp, side, pl.get("stat_key",""))
        if not values:
            all_results.append({
                "name":name,"label":label,"line":line,"side":side,"opp":opp,
                "avg":None,"games":0,"history":"—","pick":None,
                "pick_note":f"No H/A history vs {opp}",
                "over_odds":pl.get("over_odds"),"under_odds":pl.get("under_odds"),
            })
            return
        avg     = round(sum(values)/len(values), 1)
        history = ", ".join(str(int(v)) for v in values)
        gap     = round(avg - line, 1)
        pick    = "OVER" if avg > line else ("UNDER" if avg < line else None)
        note    = f"avg {avg} {'>' if avg>line else '<'} line {line} ({'+' if gap>0 else ''}{gap})"
        all_results.append({
            "name":name,"label":label,"line":line,"side":side,"opp":opp,
            "avg":avg,"games":len(values),"history":history,"gap":gap,
            "pick":pick,"pick_note":note,
            "over_odds":pl.get("over_odds"),"under_odds":pl.get("under_odds"),
        })
    await asyncio.gather(*[analyze(pl) for pl in all_lines])
    picks   = sorted([r for r in all_results if r["pick"]],
                     key=lambda x: abs(x.get("gap",0)), reverse=True)
    return {"picks":picks, "all":all_results}

# ── API Endpoints ─────────────────────────────────────────────────────
@app.post("/api/run")
async def api_run():
    job_id = str(uuid.uuid4())[:8]
    JOBS[job_id] = {"status":"running","result":None,"error":None,"started":time.time()}
    async def _run():
        try:
            result = await run_nfl_props()
            JOBS[job_id].update({"status":"done","result":result})
        except Exception as e:
            JOBS[job_id].update({"status":"error","error":str(e)})
    asyncio.create_task(_run())
    return {"job_id": job_id}

@app.get("/api/run/{job_id}")
async def api_poll(job_id: str):
    if job_id not in JOBS:
        raise HTTPException(status_code=404, detail="Job not found")
    return JOBS[job_id]

# ── Frontend ──────────────────────────────────────────────────────────
HTML = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>NFL Money Bombs</title>
<link href="https://fonts.googleapis.com/css2?family=Playfair+Display:wght@700;900&family=Source+Sans+Pro:wght@400;600;700&display=swap" rel="stylesheet">
<style>
*{margin:0;padding:0;box-sizing:border-box}
body{background:#0f0f0f;color:#fff;font-family:'Source Sans Pro',sans-serif;min-height:100vh}
nav{position:fixed;top:0;width:100%;background:rgba(10,10,10,.95);backdrop-filter:blur(12px);border-bottom:1px solid #1c1c1c;z-index:100;padding:0 28px;height:72px;display:flex;align-items:center;justify-content:space-between}
.logo{font-family:'Playfair Display',serif;font-size:1.4rem;font-weight:900;color:#f59e0b}
.logo span{color:#fff}
.nav-right{font-size:12px;color:#6b7280}
main{max-width:900px;margin:0 auto;padding:100px 20px 60px}
.hero{text-align:center;margin-bottom:40px}
.hero h1{font-family:'Playfair Display',serif;font-size:clamp(2rem,5vw,3.2rem);font-weight:900;margin-bottom:8px}
.hero h1 span{color:#f59e0b}
.hero p{color:#6b7280;font-size:15px}
.card{background:#161616;border:1px solid #262626;border-radius:16px;padding:24px;margin-bottom:20px}
.btn{background:#f59e0b;color:#000;font-weight:700;padding:12px 32px;border:none;border-radius:8px;font-size:15px;cursor:pointer;font-family:'Source Sans Pro',sans-serif;transition:all .2s;width:100%}
.btn:hover{background:#fbbf24;transform:translateY(-1px);box-shadow:0 4px 20px rgba(245,158,11,.4)}
.btn:disabled{opacity:.5;cursor:not-allowed;transform:none}
.spinner{display:inline-block;width:16px;height:16px;border:2px solid rgba(255,255,255,.2);border-top-color:#f59e0b;border-radius:50%;animation:spin .7s linear infinite;vertical-align:middle;margin-right:8px}
@keyframes spin{to{transform:rotate(360deg)}}
.status-msg{text-align:center;color:#6b7280;font-size:13px;margin-top:12px;min-height:20px}
.picks-grid{display:flex;flex-direction:column;gap:12px;margin-top:8px}
.pick-card{background:#0f0f0f;border:1px solid #2a2a2a;border-radius:12px;padding:16px 20px;display:grid;grid-template-columns:1fr auto;gap:8px;align-items:center}
.pick-card:hover{border-color:rgba(245,158,11,.3)}
.pick-name{font-weight:700;font-size:15px;margin-bottom:2px}
.pick-detail{color:#9ca3af;font-size:12px}
.pick-badge{font-family:'Playfair Display',serif;font-size:1.6rem;font-weight:900;text-align:right}
.over{color:#4ade80}
.under{color:#f87171}
.pick-line{font-size:11px;color:#6b7280;text-align:right}
.odds-pill{display:inline-block;background:rgba(245,158,11,.1);border:1px solid rgba(245,158,11,.25);color:#f59e0b;border-radius:4px;font-size:11px;font-weight:700;padding:2px 7px;margin-left:6px}
.section-hdr{color:#f59e0b;font-size:11px;font-weight:700;text-transform:uppercase;letter-spacing:1.5px;margin-bottom:14px;display:flex;align-items:center;gap:8px}
.section-hdr::after{content:'';flex:1;height:1px;background:#262626}
.no-games{text-align:center;padding:40px 20px;color:#4b5563}
.no-games .icon{font-size:3rem;margin-bottom:12px}
.no-games h3{font-family:'Playfair Display',serif;font-size:1.4rem;color:#6b7280;margin-bottom:8px}
.history-tag{background:rgba(255,255,255,.05);border-radius:4px;padding:2px 6px;font-size:11px;color:#6b7280;font-family:monospace}
footer{border-top:1px solid #1a1a1a;padding:24px;text-align:center;color:#374151;font-size:11px;margin-top:40px}
</style>
</head>
<body>
<nav>
  <div class="logo">Money <span>Bombs</span> 🏈</div>
  <div class="nav-right">NFL Player Props</div>
</nav>

<main>
  <div class="hero">
    <h1>NFL <span>Money Bombs</span></h1>
    <p>Player props vs career H/A history — powered by The Odds API &amp; ESPN</p>
  </div>

  <div class="card">
    <button class="btn" id="runBtn" onclick="runPicks()">⚡ RUN NFL PICKS</button>
    <div class="status-msg" id="statusMsg"></div>
  </div>

  <div id="results" style="display:none"></div>
</main>

<footer>
  Money Picks Arena &nbsp;·&nbsp; NFL Money Bombs &nbsp;·&nbsp; For entertainment purposes only. Must be 18+. Please gamble responsibly.
  <br><a href="https://www.ncpgambling.org" style="color:#374151">National Council on Problem Gambling: 1-800-522-4700</a>
</footer>

<script>
// ── Hub Token Gate ─────────────────────────────────────────────────
(function(){
  const HUB = 'https://www.moneypicksarena.com';
  const KEY = '__mpa_token';
  const params = new URLSearchParams(window.location.search);
  const urlTok = params.get('token');
  if(urlTok){ localStorage.setItem(KEY,urlTok); window.history.replaceState({},'',window.location.pathname); }
  const tok = localStorage.getItem(KEY);
  if(!tok){ window.location.href = HUB; return; }
  fetch('/api/verify-token',{headers:{'Authorization':'Bearer '+tok}})
    .then(r=>{ if(!r.ok){ localStorage.removeItem(KEY); window.location.href=HUB; }})
    .catch(()=>{ localStorage.removeItem(KEY); window.location.href=HUB; });
})();

let jobId = null;
let pollTimer = null;

async function runPicks(){
  const btn = document.getElementById('runBtn');
  const status = document.getElementById('statusMsg');
  const results = document.getElementById('results');
  btn.disabled = true;
  btn.innerHTML = '<span class="spinner"></span>Running NFL picks...';
  status.textContent = 'Fetching prop lines from sportsbooks...';
  results.style.display = 'none';

  try {
    const r = await fetch('/api/run', {method:'POST'});
    const d = await r.json();
    jobId = d.job_id;
    pollTimer = setInterval(pollJob, 2000);
  } catch(e) {
    status.textContent = 'Error starting picks. Try again.';
    btn.disabled = false;
    btn.innerHTML = '⚡ RUN NFL PICKS';
  }
}

async function pollJob(){
  if(!jobId) return;
  try {
    const r = await fetch('/api/run/'+jobId);
    const d = await r.json();
    if(d.status === 'done'){
      clearInterval(pollTimer);
      renderResults(d.result);
      document.getElementById('runBtn').disabled = false;
      document.getElementById('runBtn').innerHTML = '🔄 REFRESH PICKS';
      document.getElementById('statusMsg').textContent = '';
    } else if(d.status === 'error'){
      clearInterval(pollTimer);
      document.getElementById('statusMsg').textContent = '❌ ' + (d.error || 'Unknown error');
      document.getElementById('runBtn').disabled = false;
      document.getElementById('runBtn').innerHTML = '⚡ RUN NFL PICKS';
    } else {
      document.getElementById('statusMsg').textContent = 'Analyzing player histories...';
    }
  } catch(e){}
}

function fmtOdds(o){
  if(o == null) return '';
  return (o > 0 ? '+' : '') + o;
}

function renderResults(data){
  const el = document.getElementById('results');
  if(!data){ el.style.display='none'; return; }

  if(data.error){
    el.innerHTML = `<div class="card no-games">
      <div class="icon">🏈</div>
      <h3>${data.error}</h3>
      <p style="color:#4b5563;font-size:13px">NFL season runs September through February</p>
    </div>`;
    el.style.display='block';
    return;
  }

  const picks = data.picks || [];
  const all   = data.all   || [];
  const nopick = all.filter(r => !r.pick);

  let html = '';

  if(picks.length === 0){
    html += `<div class="card no-games">
      <div class="icon">🏈</div>
      <h3>No strong picks found</h3>
      <p style="color:#4b5563;font-size:13px">No prop lines posted yet or no clear over/under signals today</p>
    </div>`;
  } else {
    html += `<div class="card">
      <div class="section-hdr">💣 Money Bombs — ${picks.length} picks</div>
      <div class="picks-grid">`;
    for(const p of picks){
      const isOver = p.pick === 'OVER';
      const cls    = isOver ? 'over' : 'under';
      const odds   = isOver ? fmtOdds(p.over_odds) : fmtOdds(p.under_odds);
      html += `<div class="pick-card">
        <div>
          <div class="pick-name">${p.name}</div>
          <div class="pick-detail">
            ${p.label} &nbsp;·&nbsp; vs ${p.opp} (${p.side})
            &nbsp;·&nbsp; Line: <strong>${p.line}</strong>
            &nbsp;·&nbsp; Avg: <strong>${p.avg}</strong>
            &nbsp;·&nbsp; <span class="history-tag">${p.history}</span>
            &nbsp;(${p.games}g)
          </div>
        </div>
        <div>
          <div class="pick-badge ${cls}">${p.pick}${odds ? `<span class="odds-pill">${odds}</span>` : ''}</div>
          <div class="pick-line">${p.pick_note}</div>
        </div>
      </div>`;
    }
    html += `</div></div>`;
  }

  if(nopick.length > 0){
    html += `<div class="card">
      <div class="section-hdr">No Clear Signal (${nopick.length})</div>
      <div style="display:flex;flex-wrap:wrap;gap:8px">`;
    for(const p of nopick){
      html += `<div style="background:#0a0a0a;border:1px solid #222;border-radius:8px;padding:8px 12px;font-size:12px">
        <span style="font-weight:700">${p.name}</span>
        <span style="color:#4b5563;margin-left:6px">${p.label} ${p.line}</span>
        <span style="color:#374151;margin-left:6px">${p.pick_note}</span>
      </div>`;
    }
    html += `</div></div>`;
  }

  el.innerHTML = html;
  el.style.display = 'block';
}
</script>
</body>
</html>"""

@app.get("/", response_class=HTMLResponse)
async def index():
    return HTML
