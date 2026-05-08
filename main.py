# NFL Money Bombs — main.py
# Pattern-based NFL picks: 75%+ hit rate vs today's specific opponent (H/A)
# 100% ESPN API — no blocked APIs, no auth needed

import asyncio, json, os, hashlib
from datetime import date, datetime
from typing import Dict, List, Optional, Any

import httpx
from fastapi import FastAPI, Request
from fastapi.responses import HTMLResponse, RedirectResponse

app = FastAPI(title="NFL Money Bombs")

# ─── Auth ─────────────────────────────────────────────────────────────────────
USERS_RAW = os.environ.get("USERS", "admin:bombs")
USERS: Dict[str, str] = {}
for _pair in USERS_RAW.split(","):
    if ":" in _pair.strip():
        _u, _p = _pair.strip().split(":", 1)
        USERS[_u.strip()] = _p.strip()
SECRET = os.environ.get("SECRET_KEY", "nfl-money-bombs-2026")

def make_token(u: str) -> str:
    return hashlib.sha256(f"{u}:{SECRET}".encode()).hexdigest()

def get_user(request: Request) -> Optional[str]:
    t = request.cookies.get("session")
    for u in USERS:
        if t == make_token(u): return u
    return None

# ─── Stat Config ──────────────────────────────────────────────────────────────
# Thresholds tested high → low; highest with 75%+ hit rate wins
STAT_CONFIG = {
    'PASS_YDS': {'label': 'Pass Yards',   'emoji': '🏈', 'thresholds': [350,325,300,275,250,225,200,175,150,125,100]},
    'RUSH_YDS': {'label': 'Rush Yards',   'emoji': '💨', 'thresholds': [120,100,90,80,70,60,50,40,30,20,10]},
    'REC_YDS':  {'label': 'Rec Yards',    'emoji': '🎯', 'thresholds': [120,100,90,80,70,60,50,40,30,20,10]},
    'REC':      {'label': 'Receptions',   'emoji': '🙌', 'thresholds': [9,8,7,6,5,4,3,2,1]},
    'TD':       {'label': 'Touchdowns',   'emoji': '💣', 'thresholds': [2,1]},
}

HIT_RATE_MIN = 0.75
MIN_GAMES    = 2
ESPN_SEASONS = [2025, 2024]          # NFL: 2 seasons is plenty, keeps load time fast
TOP_N        = 10

# ─── Cache ────────────────────────────────────────────────────────────────────
_cache: Dict[str, Any] = {}

# ─── Helpers ──────────────────────────────────────────────────────────────────
def safe_int(val) -> int:
    s = str(val).strip()
    if not s or s in ('-', '--', ''): return 0
    try: return int(float(s))
    except: return 0

def parse_nfl_stats(labels: List[str], stats: List[str]) -> Dict[str, int]:
    """Label-aware parser — handles QB, RB, WR, TE formats correctly."""
    result = {'PASS_YDS': 0, 'RUSH_YDS': 0, 'REC_YDS': 0, 'REC': 0, 'TD': 0}
    if not labels or not stats or len(labels) < 2:
        return result

    # ── Passing section: CMP/ATT → before CAR ──────────────────────────────
    if 'CMP' in labels or 'ATT' in labels:
        start = labels.index('CMP') if 'CMP' in labels else labels.index('ATT')
        end   = labels.index('CAR') if 'CAR' in labels and labels.index('CAR') > start else len(labels)
        ps, ss = labels[start:end], stats[start:end]
        if 'YDS' in ps: result['PASS_YDS'] = safe_int(ss[ps.index('YDS')])
        if 'TD'  in ps: result['TD']       += safe_int(ss[ps.index('TD')])

    # ── Rushing section: CAR → before REC (or end) ─────────────────────────
    if 'CAR' in labels:
        car_i = labels.index('CAR')
        rec_after = next((i for i in range(car_i+1, len(labels)) if labels[i]=='REC'), None)
        end = rec_after if rec_after else len(labels)
        rs, ss = labels[car_i:end], stats[car_i:end]
        if 'YDS' in rs: result['RUSH_YDS'] = safe_int(ss[rs.index('YDS')])
        if 'TD'  in rs: result['TD']       += safe_int(ss[rs.index('TD')])

    # ── Receiving section: REC → before CAR (or end) ───────────────────────
    if 'REC' in labels:
        rec_i = labels.index('REC')
        result['REC'] = safe_int(stats[rec_i])
        car_after = next((i for i in range(rec_i+1, len(labels)) if labels[i]=='CAR'), None)
        end = car_after if car_after else len(labels)
        rs, ss = labels[rec_i:end], stats[rec_i:end]
        if 'YDS' in rs: result['REC_YDS'] = safe_int(ss[rs.index('YDS')])
        if 'TD'  in rs: result['TD']      += safe_int(ss[rs.index('TD')])

    return result

def find_best_threshold(values: List[float], thresholds: List[int]) -> Optional[Dict]:
    n = len(values)
    if n < MIN_GAMES: return None
    for t in thresholds:
        hits = sum(1 for v in values if v >= t)
        rate = hits / n
        if rate >= HIT_RATE_MIN:
            return {'threshold': t, 'hits': hits, 'games': n,
                    'hit_rate': rate, 'pct': round(rate * 100, 1)}
    return None

# ─── ESPN API ─────────────────────────────────────────────────────────────────
async def get_today_games(date_str: str = None) -> List[Dict]:
    fmt = datetime.strptime(date_str, '%Y-%m-%d').strftime('%Y%m%d') if date_str \
          else date.today().strftime('%Y%m%d')
    url = f"https://site.api.espn.com/apis/site/v2/sports/football/nfl/scoreboard?dates={fmt}"
    async with httpx.AsyncClient(timeout=30) as c:
        r = await c.get(url)
        data = r.json()
    games = []
    for event in data.get('events', []):
        comps = event['competitions'][0]['competitors']
        home = next((c for c in comps if c['homeAway']=='home'), None)
        away = next((c for c in comps if c['homeAway']=='away'), None)
        if not home or not away: continue
        games.append({
            'home': home['team']['abbreviation'], 'away': away['team']['abbreviation'],
            'home_id': home['team']['id'], 'away_id': away['team']['id'],
            'home_name': home['team']['displayName'], 'away_name': away['team']['displayName'],
        })
    return games

async def get_team_roster_espn(team_id: str) -> List[Dict]:
    """Fetch skill-position players only (QB/RB/WR/TE) — cuts roster from 80 → ~22."""
    url = f"https://site.api.espn.com/apis/site/v2/sports/football/nfl/teams/{team_id}/roster"
    SKILL = {'QB', 'RB', 'WR', 'TE'}
    try:
        async with httpx.AsyncClient(timeout=20) as c:
            await asyncio.sleep(0.1)
            r = await c.get(url)
            data = r.json()
        players = []
        for group in data.get('athletes', []):
            if not isinstance(group, dict): continue
            if 'items' in group:
                # Position-grouped format
                for p in group.get('items', []):
                    pos = p.get('position', {}).get('abbreviation', '') if isinstance(p.get('position'), dict) else ''
                    if pos in SKILL:
                        players.append({'id': p['id'], 'name': p.get('displayName', ''), 'pos': pos})
            elif 'id' in group:
                # Flat format
                pos = group.get('position', {}).get('abbreviation', '') if isinstance(group.get('position'), dict) else ''
                if pos in SKILL:
                    players.append({'id': group['id'], 'name': group.get('displayName', ''), 'pos': pos})
        return players
    except Exception as e:
        print(f"  Roster error {team_id}: {e}")
        return []

async def get_player_gamelogs_espn(player_id: str, season: int,
                                    sem: asyncio.Semaphore) -> List[Dict]:
    url = (f"https://site.web.api.espn.com/apis/common/v3/sports/"
           f"football/nfl/athletes/{player_id}/gamelog")
    async with sem:
        try:
            async with httpx.AsyncClient(timeout=20) as c:
                r = await c.get(url, params={'season': season})
                if r.status_code != 200: return []
                gl = r.json()
        except Exception:
            return []

    labels = gl.get('labels', [])
    events = gl.get('events', {})

    # Build eventId → stats map
    stats_map: Dict[str, List] = {}
    for st in gl.get('seasonTypes', []):
        for cat in st.get('categories', []):
            if cat is None: continue
            for ev in cat.get('events', []):
                eid = ev.get('eventId')
                if eid and ev.get('stats') and eid not in stats_map:
                    stats_map[eid] = ev['stats']

    games = []
    for eid, ev_info in events.items():
        if eid not in stats_map: continue
        raw = stats_map[eid]
        parsed = parse_nfl_stats(labels, raw)

        # Skip games with no meaningful stats (DNP / special teams only)
        if all(v == 0 for v in parsed.values()): continue

        opp_info = ev_info.get('opponent', {})
        opp_abbr = opp_info.get('abbreviation', '') if isinstance(opp_info, dict) else ''
        location = 'Away' if ev_info.get('atVs', '') == '@' else 'Home'

        games.append({'opp': opp_abbr, 'location': location, **parsed})
    return games

# ─── Analysis ─────────────────────────────────────────────────────────────────
async def run_analysis(selected_date: str = None) -> Dict:
    today_str = selected_date if selected_date else date.today().isoformat()
    if _cache.get('date') == today_str and _cache.get('picks') is not None:
        return _cache

    log = []
    log.append(f"📅 Fetching NFL schedule for {today_str}...")
    try:
        games = await get_today_games(today_str)
    except Exception as e:
        return {'date': today_str, 'picks': [], 'all_picks': [], 'games': [],
                'log': [f'ESPN error: {e}'], 'total': 0}

    if not games:
        return {'date': today_str, 'picks': [], 'all_picks': [], 'games': [],
                'log': [f'No NFL games found for {today_str}.'], 'total': 0}

    log.append("🏈 " + " | ".join(f"{g['away']} @ {g['home']}" for g in games))

    team_ids = list({g['home_id'] for g in games} | {g['away_id'] for g in games})
    log.append(f"👥 Loading rosters for {len(team_ids)} teams...")
    roster_results = await asyncio.gather(
        *[get_team_roster_espn(tid) for tid in team_ids], return_exceptions=True)
    rosters: Dict[str, List] = {}
    for tid, res in zip(team_ids, roster_results):
        rosters[tid] = res if isinstance(res, list) else []
    log.append(f"   → {sum(len(v) for v in rosters.values())} players loaded")

    all_pids = list({p['id'] for plist in rosters.values() for p in plist})
    log.append(f"📊 Fetching game logs: {len(all_pids)} players × {len(ESPN_SEASONS)} seasons...")

    sem = asyncio.Semaphore(15)

    async def fetch_logs(pid: str):
        results = await asyncio.gather(
            *[get_player_gamelogs_espn(pid, s, sem) for s in ESPN_SEASONS],
            return_exceptions=True)
        return pid, [g for r in results if isinstance(r, list) for g in r]

    log_results = await asyncio.gather(*[fetch_logs(pid) for pid in all_pids])
    logs_by_player = dict(log_results)
    total_entries = sum(len(v) for v in logs_by_player.values())
    log.append(f"📈 {total_entries:,} historical game entries loaded")

    log.append("🔍 Scanning matchup patterns (75%+ threshold)...")
    picks = []

    for game in games:
        h, a = game['home'], game['away']
        h_name, a_name = game['home_name'], game['away_name']

        for player in rosters.get(game['home_id'], []):
            pid, pname = player['id'], player['name']
            opp_logs = [l for l in logs_by_player.get(pid, [])
                        if l['location'] == 'Home' and l['opp'] == a]
            for sk, sc in STAT_CONFIG.items():
                vals = [float(l[sk]) for l in opp_logs]
                result = find_best_threshold(vals, sc['thresholds'])
                if result:
                    picks.append({**result, 'player': pname, 'team': h,
                                  'team_name': h_name, 'stat': sk,
                                  'stat_label': sc['label'], 'emoji': sc['emoji'],
                                  'location': 'Home', 'opp': a, 'opp_name': a_name,
                                  'matchup': f"{a_name} @ {h_name}"})

        for player in rosters.get(game['away_id'], []):
            pid, pname = player['id'], player['name']
            opp_logs = [l for l in logs_by_player.get(pid, [])
                        if l['location'] == 'Away' and l['opp'] == h]
            for sk, sc in STAT_CONFIG.items():
                vals = [float(l[sk]) for l in opp_logs]
                result = find_best_threshold(vals, sc['thresholds'])
                if result:
                    picks.append({**result, 'player': pname, 'team': a,
                                  'team_name': a_name, 'stat': sk,
                                  'stat_label': sc['label'], 'emoji': sc['emoji'],
                                  'location': 'Away', 'opp': h, 'opp_name': h_name,
                                  'matchup': f"{a_name} @ {h_name}"})

    picks.sort(key=lambda x: (x['hit_rate'], x['threshold']), reverse=True)
    top_picks = picks[:TOP_N]
    log.append(f"✅ {len(picks)} qualifying patterns → top {TOP_N} shown")

    result = {'date': today_str, 'picks': top_picks, 'all_picks': picks,
              'games': games, 'log': log, 'total': len(picks)}
    _cache.update(result)
    return result


# ─── HTML ─────────────────────────────────────────────────────────────────────
LOGIN_HTML = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>NFL Money Bombs</title>
<style>
*{box-sizing:border-box;margin:0;padding:0}
body{background:#060a06;background-image:radial-gradient(ellipse at 50% 0%,rgba(34,197,94,.08) 0%,transparent 55%);color:#e0e6f0;font-family:'Segoe UI',system-ui,sans-serif;min-height:100vh;display:flex;align-items:center;justify-content:center;flex-direction:column;gap:0}
.bomb{font-size:72px;margin-bottom:20px;animation:pulse 2s ease-in-out infinite;filter:drop-shadow(0 0 20px rgba(34,197,94,.5))}
@keyframes pulse{0%,100%{transform:scale(1)}50%{transform:scale(1.1)}}
.card{background:linear-gradient(145deg,rgba(10,20,10,.97),rgba(5,12,5,.99));border:1px solid rgba(34,197,94,.3);border-radius:24px;padding:40px 40px 36px;width:390px;text-align:center;box-shadow:0 30px 80px rgba(0,0,0,.7),0 0 0 1px rgba(34,197,94,.05),inset 0 1px 0 rgba(255,255,255,.03);position:relative;overflow:hidden}
.card::before{content:'';position:absolute;top:0;left:0;right:0;height:2px;background:linear-gradient(90deg,transparent,#22c55e 30%,#16a34a 70%,transparent)}
h1{font-size:1.65rem;font-weight:900;letter-spacing:-.5px;background:linear-gradient(135deg,#22c55e,#4ade80);-webkit-background-clip:text;-webkit-text-fill-color:transparent;background-clip:text;margin-bottom:4px}
.sub{color:#374151;font-size:.75rem;margin-bottom:30px;letter-spacing:1.5px;text-transform:uppercase}
.field{position:relative;margin-bottom:13px}
.fi{position:absolute;left:14px;top:50%;transform:translateY(-50%);opacity:.35;font-size:.9rem;pointer-events:none}
input{width:100%;background:rgba(10,20,10,.8);border:1px solid rgba(34,197,94,.2);color:#d1d5db;padding:13px 16px 13px 42px;border-radius:12px;font-size:.95rem;outline:none;transition:border-color .2s,box-shadow .2s}
input:focus{border-color:#22c55e;box-shadow:0 0 0 3px rgba(34,197,94,.12)}
input::placeholder{color:#374151}
.btn-in{width:100%;margin-top:8px;background:linear-gradient(135deg,#16a34a,#22c55e);color:#050a05;border:none;padding:14px;border-radius:12px;font-size:1rem;font-weight:900;letter-spacing:.5px;cursor:pointer;box-shadow:0 4px 20px rgba(34,197,94,.35);transition:transform .15s,box-shadow .15s}
.btn-in:hover{transform:translateY(-2px);box-shadow:0 8px 30px rgba(34,197,94,.45)}
.err{color:#f87171;font-size:.83rem;margin-top:14px;background:rgba(127,29,29,.3);padding:10px 14px;border-radius:10px;border:1px solid rgba(239,68,68,.2)}
.tagline{color:#0f2010;font-size:.68rem;margin-top:22px;letter-spacing:2px;text-transform:uppercase}
</style>
</head>
<body>
<div class="bomb">💣</div>
<div class="card">
  <h1>NFL Money Bombs</h1>
  <p class="sub">Pattern-Based Matchup Intelligence</p>
  <form method="post" action="/login">
    <div class="field"><span class="fi">👤</span><input name="username" type="text" placeholder="Username" required autocomplete="username"></div>
    <div class="field"><span class="fi">🔒</span><input name="password" type="password" placeholder="Password" required autocomplete="current-password"></div>
    <button class="btn-in" type="submit">Access Picks →</button>
    {error}
  </form>
  <p class="tagline">No Lines · Just Patterns · 75% Threshold</p>
</div>
</body>
</html>"""

MAIN_HTML = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>NFL Money Bombs</title>
<style>
*{box-sizing:border-box;margin:0;padding:0}
:root{--green:#22c55e;--lime:#4ade80;--dark:#050a05;--card:#0a140a;--border:rgba(34,197,94,.2);--text:#e0e6f0;--muted:#4b5563}
body{background:var(--dark);background-image:radial-gradient(ellipse 100% 35% at 50% 0%,rgba(34,197,94,.06) 0%,transparent 70%),linear-gradient(rgba(34,197,94,.06) 1px,transparent 1px),linear-gradient(90deg,rgba(34,197,94,.06) 1px,transparent 1px);background-size:100% 100%,52px 52px,52px 52px;color:var(--text);font-family:'Segoe UI',system-ui,sans-serif;padding:20px;min-height:100vh}
/* Header */
header{display:flex;align-items:center;justify-content:space-between;flex-wrap:wrap;gap:14px;margin-bottom:22px;padding:18px 26px;background:linear-gradient(135deg,rgba(8,18,8,.97),rgba(5,10,5,.99));border-radius:22px;border:1px solid var(--border);box-shadow:0 10px 50px rgba(0,0,0,.6),inset 0 1px 0 rgba(255,255,255,.02);position:relative;overflow:hidden}
header::before{content:'';position:absolute;top:0;left:0;right:0;height:2px;background:linear-gradient(90deg,transparent,#22c55e 30%,#16a34a 70%,transparent)}
.brand{display:flex;align-items:center;gap:14px}
.brand-ico{font-size:2.2rem;animation:wobble 3s ease-in-out infinite}
@keyframes wobble{0%,100%{transform:rotate(-5deg)}50%{transform:rotate(5deg)}}
.brand-text h1{font-size:1.38rem;font-weight:900;letter-spacing:-.5px;background:linear-gradient(135deg,#22c55e,#4ade80);-webkit-background-clip:text;-webkit-text-fill-color:transparent;background-clip:text}
.brand-text .sub{font-size:.7rem;color:#1a3020;letter-spacing:1.5px;text-transform:uppercase;margin-top:3px}
.actions{display:flex;align-items:center;gap:10px;flex-wrap:wrap}
.date-badge{background:rgba(34,197,94,.1);color:#22c55e;padding:7px 16px;border-radius:20px;font-size:.81rem;font-weight:600;border:1px solid rgba(34,197,94,.2)}
.btn{padding:10px 22px;border-radius:12px;font-size:.875rem;font-weight:800;cursor:pointer;border:none;transition:all .2s;text-decoration:none;display:inline-block;letter-spacing:.3px}
.btn-run{background:linear-gradient(135deg,#16a34a,#22c55e);color:#050a05;box-shadow:0 4px 18px rgba(34,197,94,.35)}
.btn-run:hover{transform:translateY(-2px);box-shadow:0 8px 28px rgba(34,197,94,.5)}
.btn-out{background:rgba(10,20,10,.8);color:#374151;border:1px solid rgba(34,197,94,.15)}
.btn-out:hover{color:#6b7280;border-color:rgba(34,197,94,.3)}
/* Games bar */
.games-bar{display:flex;gap:8px;overflow-x:auto;padding-bottom:4px;margin-bottom:20px;scrollbar-width:thin;scrollbar-color:var(--border) transparent}
.game-chip{background:linear-gradient(135deg,rgba(8,18,8,.9),rgba(5,10,5,.95));border:1px solid var(--border);border-radius:12px;padding:9px 18px;white-space:nowrap;font-size:.82rem;flex-shrink:0;transition:border-color .2s}
.game-chip:hover{border-color:rgba(34,197,94,.5)}
.game-chip b{color:#e0e6f0;font-weight:700}
.game-chip .sep{color:#1a3020;margin:0 5px}
/* Filters */
.filter-bar{display:flex;gap:8px;flex-wrap:wrap;margin-bottom:20px}
.filter-btn{padding:7px 18px;border-radius:20px;border:1px solid var(--border);background:rgba(8,18,8,.7);color:#374151;font-size:.81rem;cursor:pointer;transition:all .2s;font-weight:600}
.filter-btn.active,.filter-btn:hover{background:rgba(34,197,94,.1);color:#4ade80;border-color:rgba(34,197,94,.4);box-shadow:0 0 12px rgba(34,197,94,.1)}
/* Section headers */
.section-hdr{display:flex;align-items:center;justify-content:space-between;margin-bottom:18px}
.section-title{font-size:1rem;font-weight:900;letter-spacing:-.3px;display:flex;align-items:center;gap:8px;background:linear-gradient(135deg,#22c55e,#4ade80);-webkit-background-clip:text;-webkit-text-fill-color:transparent;background-clip:text}
.count-pill{background:rgba(34,197,94,.1);color:#22c55e;padding:4px 14px;border-radius:20px;font-size:.78rem;font-weight:700;border:1px solid rgba(34,197,94,.2)}
/* Pick Cards */
.picks-grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(300px,1fr));gap:16px;margin-bottom:10px}
.pick-card{background:linear-gradient(145deg,rgba(8,18,8,.96),rgba(5,10,5,.99));border:1px solid var(--border);border-radius:20px;padding:22px;position:relative;overflow:hidden;transition:border-color .25s,transform .22s,box-shadow .25s}
.pick-card:hover{border-color:rgba(34,197,94,.5);transform:translateY(-3px);box-shadow:0 14px 45px rgba(0,0,0,.5),0 0 22px rgba(34,197,94,.1)}
.pick-card::before{content:'';position:absolute;top:0;left:0;right:0;height:1px;background:linear-gradient(90deg,transparent,rgba(34,197,94,.3),transparent);opacity:0;transition:opacity .25s}
.pick-card:hover::before{opacity:1}
.pick-rank{position:absolute;top:14px;right:15px;width:32px;height:32px;border-radius:50%;display:flex;align-items:center;justify-content:center;font-size:.82rem;font-weight:900}
.rank-1{background:linear-gradient(135deg,#14532d,#22c55e);color:#050a05;box-shadow:0 0 14px rgba(34,197,94,.5)}
.rank-2{background:linear-gradient(135deg,#374151,#9ca3af);color:#050a05}
.rank-3{background:linear-gradient(135deg,#3b1a08,#ea580c);color:#fff}
.rank-other{background:rgba(10,20,10,.8);color:#1a3020;font-size:.75rem}
.pick-emoji{font-size:1.6rem;margin-bottom:10px;display:block}
.pick-player{font-size:1.08rem;font-weight:800;color:#f0f6f0;margin-bottom:3px;letter-spacing:-.3px;padding-right:38px}
.pick-team{font-size:.75rem;color:#374151;margin-bottom:12px;display:flex;align-items:center;gap:6px}
.loc-badge{background:rgba(10,20,10,.8);padding:2px 9px;border-radius:10px;font-size:.7rem;color:#4b5563;border:1px solid var(--border)}
.stat-strip{display:flex;gap:6px;margin-bottom:10px;flex-wrap:wrap}
.stat-tag{padding:3px 10px;border-radius:10px;font-size:.7rem;font-weight:700;letter-spacing:.3px}
.tag-PASS_YDS{background:rgba(59,130,246,.15);color:#60a5fa;border:1px solid rgba(59,130,246,.25)}
.tag-RUSH_YDS{background:rgba(234,88,12,.15);color:#fb923c;border:1px solid rgba(234,88,12,.25)}
.tag-REC_YDS{background:rgba(168,85,247,.15);color:#c084fc;border:1px solid rgba(168,85,247,.25)}
.tag-REC{background:rgba(20,184,166,.15);color:#2dd4bf;border:1px solid rgba(20,184,166,.25)}
.tag-TD{background:rgba(34,197,94,.15);color:#4ade80;border:1px solid rgba(34,197,94,.25)}
.pick-pattern{font-size:.9rem;color:#86efac;font-weight:700;margin-bottom:4px;line-height:1.4}
.pick-matchup{font-size:.72rem;color:#1a3020;margin-bottom:16px}
.bar-wrap{background:rgba(10,20,10,.7);border-radius:6px;height:8px;overflow:hidden;margin-bottom:10px;border:1px solid var(--border)}
.bar-fill{height:100%;border-radius:5px}
.bar-green{background:linear-gradient(90deg,#15803d,#22c55e)}
.bar-yellow{background:linear-gradient(90deg,#b45309,#f59e0b)}
.bar-orange{background:linear-gradient(90deg,#c2410c,#f97316)}
.stats-row{display:flex;justify-content:space-between;align-items:center}
.games-chip{background:rgba(10,20,10,.7);padding:4px 12px;border-radius:20px;font-size:.75rem;color:#1a3020;border:1px solid var(--border)}
.pct{font-size:1.2rem;font-weight:900;letter-spacing:-.5px}
.pct-green{color:#22c55e;text-shadow:0 0 14px rgba(34,197,94,.45)}
.pct-yellow{color:#f59e0b;text-shadow:0 0 14px rgba(245,158,11,.45)}
.pct-orange{color:#f97316;text-shadow:0 0 12px rgba(249,115,22,.35)}
/* Total Banner */
.total-banner{display:flex;align-items:center;justify-content:space-between;flex-wrap:wrap;gap:12px;background:linear-gradient(135deg,rgba(5,30,5,.8),rgba(3,18,3,.9));border:1px solid rgba(34,197,94,.25);border-radius:18px;padding:18px 24px;margin:32px 0 20px;box-shadow:0 0 40px rgba(34,197,94,.06)}
.tb-left{display:flex;align-items:center;gap:12px}
.tb-ico{font-size:1.5rem}
.tb-title{font-size:.95rem;font-weight:800;color:#4ade80;letter-spacing:-.2px}
.tb-sub{font-size:.72rem;color:#1a3020;margin-top:2px;letter-spacing:.8px;text-transform:uppercase}
.tb-count{font-size:2.2rem;font-weight:900;color:#22c55e;text-shadow:0 0 20px rgba(34,197,94,.5);letter-spacing:-1.5px}
/* All Patterns */
.all-section-hdr{display:flex;align-items:center;justify-content:space-between;margin-bottom:16px;flex-wrap:wrap;gap:10px}
.all-section-title{font-size:.95rem;font-weight:800;color:#22c55e;display:flex;align-items:center;gap:8px}
.game-group{margin-bottom:14px}
.game-group-hdr{display:flex;align-items:center;justify-content:space-between;background:linear-gradient(135deg,rgba(8,18,8,.9),rgba(5,10,5,.95));border:1px solid var(--border);border-radius:13px;padding:12px 18px;margin-bottom:6px;cursor:pointer;user-select:none;transition:border-color .2s}
.game-group-hdr:hover{border-color:rgba(34,197,94,.4)}
.gg-label{font-size:.88rem;font-weight:800;color:#4ade80;display:flex;align-items:center;gap:8px}
.gg-meta{display:flex;align-items:center;gap:8px}
.gg-chevron{color:#1a3020;font-size:.85rem;transition:transform .2s}
.compact-picks{display:flex;flex-direction:column;gap:5px;margin-bottom:4px}
.compact-row{display:flex;align-items:center;gap:12px;background:rgba(5,12,5,.8);border:1px solid rgba(20,40,20,.8);border-radius:11px;padding:10px 15px;transition:border-color .2s}
.compact-row:hover{border-color:rgba(34,197,94,.3)}
.cr-emoji{font-size:1.05rem;flex-shrink:0;width:22px;text-align:center}
.cr-info{flex:1;min-width:0}
.cr-player{font-size:.86rem;font-weight:700;color:#94a3b8}
.cr-pattern{font-size:.76rem;color:#22c55e;font-weight:600;margin-top:2px}
.cr-right{display:flex;flex-direction:column;align-items:flex-end;gap:3px;flex-shrink:0}
.cr-bar-wrap{background:rgba(10,20,10,.8);border-radius:4px;height:4px;width:68px;overflow:hidden}
.cr-bar-fill{height:100%;border-radius:4px}
.cr-pct{font-size:.9rem;font-weight:900}
.cr-sample{font-size:.65rem;color:#1a3020}
/* Messages */
.msg-card{background:linear-gradient(145deg,rgba(8,18,8,.95),rgba(5,10,5,.99));border:1px solid var(--border);border-radius:22px;padding:60px 30px;text-align:center;box-shadow:0 20px 70px rgba(0,0,0,.5)}
.msg-card .ico{font-size:3.8rem;margin-bottom:16px;display:block}
.msg-card h2{color:#e0e6f0;font-size:1.2rem;font-weight:800;margin-bottom:10px}
.msg-card p{color:#374151;font-size:.88rem;line-height:1.75}
.loading-bomb{font-size:60px;margin:0 auto 6px;animation:bombBounce .65s ease-in-out infinite;display:block;filter:drop-shadow(0 0 15px rgba(34,197,94,.4))}
@keyframes bombBounce{0%,100%{transform:translateY(0)}50%{transform:translateY(-22px)}}
.ball-shadow{width:38px;height:7px;background:rgba(0,0,0,.5);border-radius:50%;margin:0 auto 18px;animation:shadowPulse .65s ease-in-out infinite}
@keyframes shadowPulse{0%,100%{transform:scaleX(1);opacity:.5}50%{transform:scaleX(.55);opacity:.2}}
.log-box{background:rgba(3,8,3,.8);border:1px solid var(--border);border-radius:12px;padding:16px;font-size:.74rem;color:#1a3020;font-family:'Courier New',monospace;margin-top:20px;max-height:160px;overflow-y:auto;line-height:1.9;scrollbar-width:thin}
footer{text-align:center;margin-top:32px;color:#0a1a0a;font-size:.68rem;padding:10px;letter-spacing:1.5px;text-transform:uppercase}
</style>
</head>
<body>

<header>
  <div class="brand">
    <div class="brand-ico">💣</div>
    <div class="brand-text">
      <h1>NFL Money Bombs</h1>
      <div class="sub">Pattern Picks · Pass · Rush · Rec · TD</div>
    </div>
  </div>
  <div class="actions">
    <input type="date" id="datePicker" value="__TODAY__" style="background:rgba(34,197,94,.1);color:#22c55e;border:1px solid rgba(34,197,94,.3);border-radius:10px;padding:7px 12px;font-size:.82rem;font-weight:600;outline:none;cursor:pointer;">
    <button class="btn btn-run" onclick="runPicks()">⚡ Run Picks</button>
    <a href="/logout" class="btn btn-out">Sign Out</a>
  </div>
</header>

<div class="games-bar" id="gamesBar">
  <div class="game-chip" style="color:#1a3020">Hit Run Picks to load today's games →</div>
</div>

<div id="filterBar" style="display:none" class="filter-bar">
  <button class="filter-btn active" onclick="filterStat('ALL')">All Stats</button>
  <button class="filter-btn" onclick="filterStat('PASS_YDS')">🏈 Pass Yds</button>
  <button class="filter-btn" onclick="filterStat('RUSH_YDS')">💨 Rush Yds</button>
  <button class="filter-btn" onclick="filterStat('REC_YDS')">🎯 Rec Yds</button>
  <button class="filter-btn" onclick="filterStat('REC')">🙌 Receptions</button>
  <button class="filter-btn" onclick="filterStat('TD')">💣 TDs</button>
</div>

<div id="content">
  <div class="msg-card">
    <span class="ico">💣</span>
    <h2>Welcome to NFL Money Bombs</h2>
    <p>Hit <strong style="color:#22c55e">Run Picks</strong> to scan today's matchups.<br>
    Finds players hitting <strong style="color:#22c55e">75%+</strong> in Pass Yds, Rush Yds, Rec Yds, Receptions, or TDs<br>
    against today's specific opponent — home or away.</p>
  </div>
</div>

<div id="allPicksWrap" style="display:none">
  <div class="total-banner">
    <div class="tb-left">
      <div class="tb-ico">📋</div>
      <div>
        <div class="tb-title">All Qualifying Patterns</div>
        <div class="tb-sub">Every player hitting 75%+ · Grouped by game</div>
      </div>
    </div>
    <div class="tb-count" id="totalCount">0</div>
  </div>
  <div class="all-section-hdr">
    <div class="all-section-title">🎯 All Patterns by Game</div>
    <div style="display:flex;gap:8px;flex-wrap:wrap" id="allFilterBar">
      <button class="filter-btn active" onclick="filterAll('ALL')">All</button>
      <button class="filter-btn" onclick="filterAll('PASS_YDS')">🏈 Pass</button>
      <button class="filter-btn" onclick="filterAll('RUSH_YDS')">💨 Rush</button>
      <button class="filter-btn" onclick="filterAll('REC_YDS')">🎯 Rec</button>
      <button class="filter-btn" onclick="filterAll('REC')">🙌 Rec#</button>
      <button class="filter-btn" onclick="filterAll('TD')">💣 TD</button>
    </div>
  </div>
  <div id="allPicksSection"></div>
</div>

<footer>NFL Money Bombs · No Lines · Just Patterns · Powered by ESPN</footer>

<script>
let top10=[], allPicksData=[], activeTopStat='ALL', activeAllStat='ALL';

function pctClass(p){return p>=90?['pct-green','bar-green']:p>=80?['pct-yellow','bar-yellow']:['pct-orange','bar-orange']}
function statTag(s){
  const m={PASS_YDS:['tag-PASS_YDS','Pass Yds'],RUSH_YDS:['tag-RUSH_YDS','Rush Yds'],
           REC_YDS:['tag-REC_YDS','Rec Yds'],REC:['tag-REC','Receptions'],TD:['tag-TD','TDs']};
  const [c,l]=m[s]||['',''];
  return `<span class="stat-tag ${c}">${l}</span>`;
}
function rankClass(i){return i===0?'rank-1':i===1?'rank-2':i===2?'rank-3':'rank-other'}

function filterStat(stat){
  activeTopStat=stat;
  document.querySelectorAll('#filterBar .filter-btn').forEach(b=>{
    const t=b.textContent;
    b.classList.toggle('active',
      stat==='ALL'?t.includes('All'):stat==='PASS_YDS'?t.includes('Pass'):
      stat==='RUSH_YDS'?t.includes('Rush'):stat==='REC_YDS'?t.includes('Rec Yds'):
      stat==='REC'?t.includes('Rec')&&!t.includes('Yds'):t.includes('TD'));
  });
  renderTop10(stat==='ALL'?top10:top10.filter(p=>p.stat===stat));
}

function filterAll(stat){
  activeAllStat=stat;
  document.querySelectorAll('#allFilterBar .filter-btn').forEach(b=>{
    const t=b.textContent;
    b.classList.toggle('active',
      stat==='ALL'?t==='All':stat==='PASS_YDS'?t.includes('Pass'):
      stat==='RUSH_YDS'?t.includes('Rush'):stat==='REC_YDS'?t.includes('Rec'):
      stat==='REC'?t.includes('Rec#'):t.includes('TD'));
  });
  const filtered=stat==='ALL'?allPicksData:allPicksData.filter(p=>p.stat===stat);
  document.getElementById('totalCount').textContent=filtered.length;
  renderAllByGame(filtered);
}

function renderTop10(picks){
  if(!picks.length){document.getElementById('content').innerHTML='<div class="msg-card"><span class="ico">🔍</span><h2>No patterns</h2><p>Try "All Stats".</p></div>';return;}
  let html=`<div class="section-hdr"><div class="section-title">🏆 Top 10 Picks Today</div><span class="count-pill">${picks.length} pick${picks.length!==1?'s':''}</span></div><div class="picks-grid">`;
  picks.forEach((p,i)=>{
    const [pc,bc]=pctClass(p.pct);
    html+=`<div class="pick-card">
      <div class="pick-rank ${rankClass(i)}">${i+1}</div>
      <span class="pick-emoji">${p.emoji}</span>
      <div class="pick-player">${p.player}</div>
      <div class="pick-team">${p.team_name}<span class="loc-badge">${p.location==='Home'?'🏠 Home':'✈️ Away'}</span></div>
      <div class="stat-strip">${statTag(p.stat)}</div>
      <div class="pick-pattern">${p.threshold}+ ${p.stat_label} in ${p.hits} of ${p.games} ${p.location.toLowerCase()} games vs ${p.opp}</div>
      <div class="pick-matchup">📍 Today: ${p.matchup}</div>
      <div class="bar-wrap"><div class="bar-fill ${bc}" style="width:${Math.min(p.pct,100)}%"></div></div>
      <div class="stats-row"><span class="games-chip">${p.hits}/${p.games} games</span><span class="pct ${pc}">${p.pct}%</span></div>
    </div>`;
  });
  html+='</div>';
  document.getElementById('content').innerHTML=html;
}

function renderAllByGame(picks){
  const el=document.getElementById('allPicksSection');
  if(!picks.length){el.innerHTML='<div class="msg-card" style="padding:30px"><span class="ico">🔍</span><p>No patterns for this filter.</p></div>';return;}
  const groups={},order=[];
  for(const p of picks){if(!groups[p.matchup]){groups[p.matchup]=[];order.push(p.matchup);}groups[p.matchup].push(p);}
  let html='';
  for(const matchup of order){
    const gp=groups[matchup];
    const gameId='g_'+matchup.replace(/[^a-z0-9]/gi,'_');
    html+=`<div class="game-group">
      <div class="game-group-hdr" onclick="toggleGroup('${gameId}',this)">
        <span class="gg-label">🏈 ${matchup}</span>
        <div class="gg-meta"><span class="count-pill">${gp.length} pattern${gp.length!==1?'s':''}</span><span class="gg-chevron">▾</span></div>
      </div>
      <div class="compact-picks" id="${gameId}">`;
    for(const p of gp){
      const [pc,bc]=pctClass(p.pct);
      html+=`<div class="compact-row">
        <span class="cr-emoji">${p.emoji}</span>
        <div class="cr-info">
          <div class="cr-player">${p.player} <span style="color:#1a3020;font-size:.68rem">${p.team}·${p.location==='Home'?'🏠':'✈️'}</span></div>
          <div class="cr-pattern">${p.threshold}+ ${p.stat_label} · ${p.hits}/${p.games} ${p.location.toLowerCase()} vs ${p.opp}</div>
        </div>
        <div class="cr-right">
          <div class="cr-bar-wrap"><div class="cr-bar-fill ${bc}" style="width:${Math.min(p.pct,100)}%"></div></div>
          <div class="cr-pct ${pc}">${p.pct}%</div>
          <div class="cr-sample">${p.hits}/${p.games}</div>
        </div>
      </div>`;
    }
    html+='</div></div>';
  }
  el.innerHTML=html;
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
  document.getElementById('gamesBar').innerHTML=games.map(g=>`<div class="game-chip"><b>${g.away}</b><span class="sep">@</span><b>${g.home}</b></div>`).join('');
}

async function runPicks(){
  const dp=document.getElementById('datePicker').value;
  document.getElementById('content').innerHTML=`<div class="msg-card"><span class="loading-bomb">💣</span><div class="ball-shadow"></div><h2 style="color:#22c55e">Dropping Bombs...</h2><p>Pulling data for <strong style="color:#4ade80">${dp}</strong> from ESPN.<br><span style="color:#1a3020">Takes ~30-45 seconds.</span></p></div>`;
  document.getElementById('allPicksWrap').style.display='none';
  try{
    const r=await fetch('/run',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({date:dp})});
    if(!r.ok)throw new Error('Server error '+r.status);
    const data=await r.json();
    renderGames(data.games);
    top10=data.picks||[];
    allPicksData=data.all_picks||[];
    activeTopStat='ALL';activeAllStat='ALL';
    const log=data.log||[];
    if(!top10.length){
      document.getElementById('content').innerHTML=`<div class="msg-card"><span class="ico">🔍</span><h2>No Qualifying Patterns</h2><p>No 75%+ patterns for today's matchups.</p></div><div class="log-box">${log.join('<br>')}</div>`;
      return;
    }
    document.getElementById('filterBar').style.display='flex';
    renderTop10(top10);
    const lb=document.createElement('div');
    lb.className='log-box';
    lb.innerHTML=log.join('<br>')+`<br>📋 ${data.total} total patterns found`;
    document.getElementById('content').appendChild(lb);
    document.getElementById('totalCount').textContent=allPicksData.length;
    document.getElementById('allPicksWrap').style.display='block';
    renderAllByGame(allPicksData);
  }catch(e){
    document.getElementById('content').innerHTML=`<div class="msg-card"><span class="ico">❌</span><h2 style="color:#ef4444">Something went wrong</h2><p>${e.message}</p></div>`;
  }
}
</script>
</body>
</html>"""

# ─── Routes ───────────────────────────────────────────────────────────────────
@app.get("/", response_class=HTMLResponse)
async def index(request: Request):
    if not get_user(request): return RedirectResponse("/login")
    return HTMLResponse(MAIN_HTML.replace("__TODAY__", date.today().isoformat()))

@app.get("/login", response_class=HTMLResponse)
async def login_get():
    return HTMLResponse(LOGIN_HTML.replace('{error}', ''))

@app.post("/login")
async def login_post(request: Request):
    form = await request.form()
    u = form.get("username", "").strip()
    p = form.get("password", "").strip()
    if USERS.get(u) == p:
        resp = RedirectResponse("/", status_code=302)
        resp.set_cookie("session", make_token(u), httponly=True, samesite="lax", max_age=86400*7)
        return resp
    return HTMLResponse(LOGIN_HTML.replace('{error}', '<p class="err">⚠️ Invalid credentials</p>'), status_code=401)

@app.get("/logout")
async def logout():
    resp = RedirectResponse("/login")
    resp.delete_cookie("session")
    return resp

@app.post("/run")
async def run(request: Request):
    if not get_user(request): return {"error": "Unauthorized"}
    try:
        body = await request.json()
        selected_date = body.get('date', date.today().isoformat())
    except Exception:
        selected_date = date.today().isoformat()
    return await run_analysis(selected_date)

@app.get("/health")
async def health():
    return {"status": "ok", "date": date.today().isoformat()}
