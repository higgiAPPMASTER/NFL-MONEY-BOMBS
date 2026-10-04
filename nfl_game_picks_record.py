"""Independent 80–100% game-popup record, derived from frozen pregame boards.

No models, migrations, import-time jobs, or changes to existing sport records.
Storage/network callbacks are supplied by main.py and only used on request.
"""

import math
import re
import threading
from datetime import date, datetime, timedelta, timezone
from zoneinfo import ZoneInfo

_LOCK = threading.RLock()
_EASTERN = ZoneInfo("America/New_York")
_VERSION = 1


def _number(value):
    if value is None or value == "" or isinstance(value, bool):
        return None
    try:
        number = float(value)
        return number if math.isfinite(number) else None
    except (TypeError, ValueError):
        return None


def _first(row, *keys):
    for key in keys:
        if row.get(key) is not None:
            return row[key]
    return None


def _range(selected, period):
    day = date.fromisoformat(selected)
    if period == "day":
        return day, day
    if period == "week":
        first = day - timedelta(days=day.weekday())
        return first, first + timedelta(days=6)
    if period == "month":
        first = day.replace(day=1)
        after = (first.replace(day=28) + timedelta(days=4)).replace(day=1)
        return first, after - timedelta(days=1)
    if period == "year":
        return date(day.year, 1, 1), date(day.year, 12, 31)
    if period == "all":
        return date(2000, 1, 1), date(2100, 12, 31)
    raise ValueError("Unknown record period.")


def _read_pages(read, params):
    offset = 0
    while True:
        page = read("mpa_track_ledger", {
            **params, "limit": "1000", "offset": str(offset),
            "order": "date.asc,category.asc",
        })
        if page is None:
            raise RuntimeError("Could not read saved Game Picks records. Please retry Get Results.")
        if not isinstance(page, list) or any(not isinstance(r, dict) for r in page):
            raise RuntimeError("Saved Game Picks records could not be read.")
        yield from page
        if len(page) < 1000:
            return
        offset += 1000


def _games_from_source(snapshot, parse_start, labels, source_date):
    if not isinstance(snapshot, dict):
        raise RuntimeError("A saved game board is unreadable; no history was substituted.")
    captured = parse_start(snapshot.get("saved_board_captured_at"))
    if not captured:
        return [], "A saved board has no verifiable pregame capture time and was excluded."
    predictions = snapshot.get("game_predictions") or snapshot.get("games") or []
    raw = snapshot.get("all")
    if not isinstance(raw, list):
        return [], "A saved board lacks the full game-popup player pool and was excluded."
    games, seen = [], set()
    for prediction in predictions:
        if not isinstance(prediction, dict):
            continue
        start = _first(prediction, "game_start", "start")
        kickoff = parse_start(start)
        game = str(prediction.get("game") or "")
        if not game or not kickoff or captured >= kickoff:
            continue
        key = f"{game}|{kickoff.isoformat()}"
        if key in seen:
            continue
        seen.add(key)
        plays, identities = [], set()
        for pick in raw:
            if not isinstance(pick, dict) or str(pick.get("game") or "") != game:
                continue
            if parse_start(pick.get("game_start")) != kickoff:
                continue
            market = str(pick.get("market") or "")
            if market not in labels:
                continue
            # Exactly the percentage printed by _playRow, not score/Coach EV.
            a, b = _number(pick.get("rateA")), _number(pick.get("rateB"))
            rate = max(a if a is not None else 0, b if b is not None else 0)
            if not 80 <= rate <= 100:
                continue
            side = str(pick.get("pick") or "").upper()
            line = _number(_first(pick, "dispLine", "line", "realLine"))
            real_line = _number(pick.get("realLine"))
            odds = _number(_first(
                pick, *("realUnderOdds", "under_odds") if side == "UNDER"
                else ("realOdds", "over_odds")))
            # Prices must belong to this exact saved standard line and side.
            if (side not in ("OVER", "UNDER") or real_line is None
                    or line != real_line or odds is None or odds == 0 or odds < -1000):
                odds = None
            book = str(pick.get("under_book" if side == "UNDER" else "over_book") or "")
            identity = (str(pick.get("name") or "").strip().lower(), market, side, line)
            if identity in identities:
                continue
            identities.add(identity)  # Never deduplicate across a player's markets.
            plays.append({
                "name": str(pick.get("name") or ""), "team": str(pick.get("team") or ""),
                "position": str(_first(pick, "position", "roster_position") or ""),
                "category": labels[market] + (f" ({side.title()})" if side else ""),
                "market": market, "stat_label": labels[market],
                "side": side, "line": line, "odds": odds, "book": book,
                "rate": rate, "rateA": a, "rateB": b,
                "hitsA": pick.get("hitsA"), "totA": pick.get("totA"),
                "hitsB": pick.get("hitsB"), "totB": pick.get("totB"),
                "observation_only": market == "player_anytime_td",
                "actual": None, "profit_per_100": None,
                "result": "PENDING" if side in ("OVER", "UNDER") and line is not None else "NO PICK",
            })
        plays.sort(key=lambda p: (-p["rate"], p["category"], p["name"]))
        games.append({
            "version": _VERSION, "game_key": key, "game": game,
            "game_start": str(start), "date": kickoff.astimezone(_EASTERN).date().isoformat(),
            "captured_at": captured.isoformat(), "source_date": source_date,
            "plays": plays, "status": "PENDING" if plays else "NO QUALIFIED PICKS",
        })
    return games, None if games else "A saved board had no verified pre-kickoff game source."


def _settle(game, settle_snapshot):
    eligible = [p for p in game["plays"] if p["result"] != "NO PICK"]
    settled = settle_snapshot(game["date"], [
        {**play, "player": play["name"]} for play in eligible])
    if not isinstance(settled, list) or len(settled) != len(eligible):
        raise RuntimeError("Final player statistics could not be matched safely.")
    # Reuse existing NFL settlement: final games only, supported zero groups,
    # and VOID only after every event/box lookup for the date was confirmed.
    # This helper never writes to the Coach record; it only reads its parser.
    for play, graded in zip(eligible, settled):
        result = graded.get("result")
        if result not in ("WIN", "LOSS", "PUSH", "VOID"):
            continue
        actual = _number(graded.get("actual"))
        if actual is None and result != "VOID":
            continue
        play["actual"], play["result"] = actual, result
        odds = play["odds"]
        if odds is not None and not play["observation_only"]:
            play["profit_per_100"] = round(
                0 if result in ("PUSH", "VOID") else -100 if result == "LOSS" else
                odds if odds > 0 else 10000 / abs(odds), 4)
    pending = any(p["result"] == "PENDING" for p in game["plays"])
    game["status"] = ("PENDING" if pending else
                      "RESULTS AVAILABLE" if game["plays"] else "NO QUALIFIED PICKS")
    return not pending


def record_payload(cfg, selected, period, grade, read, write, settle_snapshot,
                   parse_start, labels):
    """Read frozen game sources and maintain only this independent thin record."""
    first, last = _range(selected, period)
    if not 2000 <= date.fromisoformat(selected).year <= 2100:
        raise ValueError("Choose a date between 2000 and 2100.")
    app = cfg["app"] + "_game_picks"
    bounded = f"(date.gte.{first.isoformat()},date.lte.{last.isoformat()})"
    warnings, candidates = [], {}
    now = datetime.now(timezone.utc)
    with _LOCK:
        saved = {}
        for row in _read_pages(read, {
            "app": f"eq.{app}", "category": f"like.{cfg['board']}*",
            "side": "eq.ALL", "and": bounded, "select": "date,category,locked,detail",
        }):
            detail = row.get("detail")
            if not isinstance(detail, dict) or detail.get("version") != _VERSION:
                raise RuntimeError("A saved Game Picks record is unreadable. Please retry.")
            source_key = (detail.get("source_date"), detail.get("source_category"))
            saved.setdefault(source_key, []).append(row)
            candidates[detail["game_key"]] = (detail, row["category"], bool(row.get("locked")))

        # A Full Week run may store Monday's board under Sunday's run date.
        # Use kickoff's Eastern date, never the run date, for record grouping.
        meta_first = max(date(2000, 1, 1), first - timedelta(days=7))
        meta_last = min(date(2100, 12, 31), last + timedelta(days=1))
        meta_bounds = f"(date.gte.{meta_first.isoformat()},date.lte.{meta_last.isoformat()})"
        for meta in _read_pages(read, {
            "app": f"eq.{cfg['app']}", "category": f"like.{cfg['board']}*",
            "side": "eq.ALL", "and": meta_bounds, "select": "date,category,locked_at",
        }):
            kickoff = parse_start(meta.get("locked_at"))
            actual_date = kickoff.astimezone(_EASTERN).date() if kickoff else None
            if actual_date and not first <= actual_date <= last:
                continue
            existing = saved.get((meta["date"], meta["category"]), [])
            if existing and all(row.get("locked") for row in existing):
                continue
            rows = read("mpa_track_ledger", {
                "app": f"eq.{cfg['app']}", "category": f"eq.{meta['category']}",
                "side": "eq.ALL", "date": f"eq.{meta['date']}", "select": "detail", "limit": "1",
            })
            if rows is None:
                raise RuntimeError("Could not confirm a saved pregame game board. Please retry.")
            if not rows:
                continue
            games, warning = _games_from_source(rows[0].get("detail"), parse_start, labels, meta["date"])
            if warning:
                warnings.append(f"{meta['date']}: {warning}")
            for game in games:
                if not first <= date.fromisoformat(game["date"]) <= last:
                    continue
                prior = candidates.get(game["game_key"])
                if prior and prior[0]["captured_at"] >= game["captured_at"]:
                    continue
                game["source_category"] = meta["category"]
                category = meta["category"] + "__gp80_" + re.sub(
                    r"[^0-9A-Za-z]+", "-", game["game_key"]).strip("-")
                candidates[game["game_key"]] = (game, category, False)

        daily = {}
        writes = []
        for game, category, locked in candidates.values():
            kickoff = parse_start(game["game_start"])
            if grade and not locked and kickoff and now >= kickoff:
                locked = _settle(game, settle_snapshot)
            # An explicit Get Results may save this record, never the source or other ledgers.
            if grade:
                game["updated_at"] = now.isoformat()
                countable = [p for p in game["plays"] if not p["observation_only"]]
                writes.append({
                    "app": app, "date": game["date"], "category": category, "side": "ALL",
                    "wins": sum(p["result"] == "WIN" for p in countable),
                    "losses": sum(p["result"] == "LOSS" for p in countable),
                    "locked": locked, "locked_at": now.isoformat() if locked else None, "detail": game,
                })
            daily.setdefault(game["date"], []).append(game)
        if writes and not write("mpa_track_ledger", writes,
                                on_conflict="app,date,category,side", timeout=30):
            warnings.append("Game Picks results could not be confirmed saved. Displayed results can be retried from the frozen sources.")
        dates = []
        for day, games in sorted(daily.items(), reverse=True):
            games.sort(key=lambda g: (g["game_start"], g["game"]))
            dates.append({"date": day, "games": games})
        return {
            "system": "NEW" if str(cfg["app"]).lower().find("new") >= 0 else "OLD",
            "updated_at": now.isoformat(), "dates": dates,
            "warnings": list(dict.fromkeys(warnings)),
        }


# Embedded display code: deployment needs this Python helper only.
_GAME_RECORD_HTML = r"""<style>.ngr-ov{position:fixed;inset:0;z-index:100000;background:rgba(2,6,23,.78);display:flex;align-items:center;justify-content:center;padding:12px}
.ngr-dlg{background:#0f172a;border:1px solid #334155;border-radius:12px;width:min(1100px,100%);max-height:calc(100dvh - 24px);display:flex;flex-direction:column;color:#e2e8f0;box-shadow:0 18px 50px rgba(0,0,0,.55);outline:0}
.ngr-head{display:flex;align-items:flex-start;justify-content:space-between;gap:10px;padding:12px 14px 8px;border-bottom:1px solid #1e293b}
.ngr-title{margin:0;font-size:1rem;font-weight:900;color:#fff}
.ngr-sub{color:#94a3b8;font-size:.72rem;margin-top:2px}
.ngr-sys{font-size:.68rem;font-weight:900;border:1px solid #475569;border-radius:99px;padding:2px 8px;white-space:nowrap}
.ngr-x{background:#1e293b;color:#cbd5e1;border:1px solid #334155;border-radius:8px;padding:5px 10px;font-weight:800;cursor:pointer}
.ngr-ctl{display:flex;flex-wrap:wrap;gap:7px;align-items:center;padding:8px 14px;border-bottom:1px solid #1e293b}
.ngr-ctl label{display:flex;align-items:center;gap:5px;color:#94a3b8;font-size:.7rem;font-weight:800}
.ngr-ctl input,.ngr-ctl select{background:#020617;color:#e2e8f0;border:1px solid #334155;border-radius:7px;padding:5px 7px;font-size:.78rem}
.ngr-ctl input.ngr-stake{width:76px}
.ngr-btn{background:#1e293b;color:#e2e8f0;border:1px solid #334155;border-radius:7px;padding:5px 10px;font-size:.74rem;font-weight:800;cursor:pointer}
.ngr-btn:hover{border-color:#64748b}
.ngr-btn.on{background:#1d4ed8;border-color:#3b82f6;color:#fff}
.ngr-btn:disabled{opacity:.5;cursor:default}
.ngr-btn:focus-visible,.ngr-x:focus-visible,.ngr-game:focus-visible{outline:2px solid #38bdf8;outline-offset:2px}
.ngr-body{overflow:auto;padding:10px 14px 16px;flex:1;min-height:160px}
.ngr-kpis{display:grid;grid-template-columns:repeat(auto-fit,minmax(104px,1fr));gap:6px;margin:6px 0 10px}
.ngr-kpi{background:#020617;border:1px solid #1e293b;border-radius:8px;padding:6px 8px}
.ngr-kpi b{display:block;font-size:.62rem;color:#64748b;text-transform:uppercase;letter-spacing:.06em}
.ngr-kpi span{font-family:monospace;font-weight:900;font-size:.95rem;color:#fff}
.ngr-pos{color:#4ade80!important}.ngr-neg{color:#f87171!important}.ngr-warn{color:#fbbf24!important}
.ngr-date{margin:12px 0 5px;color:#93c5fd;font-size:.76rem;font-weight:900;text-transform:uppercase;letter-spacing:.08em}
.ngr-games{display:grid;grid-template-columns:repeat(auto-fill,minmax(250px,1fr));gap:7px}
.ngr-game{text-align:left;background:#111c33;color:#e2e8f0;border:1px solid #334155;border-radius:9px;padding:8px 10px;cursor:pointer;font:inherit}
.ngr-game:hover{border-color:#38bdf8}
.ngr-game.cur{border-color:#facc15}
.ngr-game .g{font-weight:900;font-size:.86rem;color:#fff}
.ngr-game .m{font-size:.68rem;color:#94a3b8;margin-top:2px}
.ngr-game .r{font-family:monospace;font-size:.76rem;margin-top:4px;font-weight:800}
.ngr-note{background:rgba(245,158,11,.1);border:1px solid rgba(245,158,11,.35);border-radius:9px;padding:8px 11px;margin:8px 0;color:#fbbf24;font-size:.74rem;font-weight:700}
.ngr-empty{color:#94a3b8;text-align:center;padding:22px 10px;font-size:.82rem}
.ngr-err{background:rgba(127,29,29,.25);border:1px solid rgba(248,113,113,.4);border-radius:9px;padding:12px;color:#fecaca;font-size:.8rem}
.ngr-skel{height:44px;border-radius:8px;margin:8px 0;background:linear-gradient(90deg,#111c33,#1e293b,#111c33);background-size:200% 100%;animation:ngrsk 1.2s linear infinite}
@keyframes ngrsk{to{background-position:-200% 0}}
.ngr-scroll{overflow-x:auto}
.ngr-tbl td.n{font-weight:900;color:#fff}
.ngr-dlg .nfl-trk-result.void,.ngr-dlg .nfl-trk-result.no-pick{color:#94a3b8;background:rgba(148,163,184,.12)}
@media(max-width:640px){.ngr-ov{padding:0}.ngr-dlg{max-height:100dvh;height:100dvh;border-radius:0}.ngr-games{grid-template-columns:1fr}}
@media(prefers-reduced-motion:reduce){.ngr-skel{animation:none}}
</style><script>(function(){
'use strict';
var S={open:false,game:'',date:'',start:'',period:'day',data:null,loading:false,err:'',stake:100,view:'cat',sel:null,seq:0,ctl:null,sys:'OLD',lastFocus:null,entries:[]};
var ID='nflGameRecordOv';
function esc(v){return String(v==null?'':v).replace(/[&<>"']/g,function(c){return {'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c];});}
function $(id){return document.getElementById(id);}
function sysNow(){try{return typeof _nflSystem==='function'?_nflSystem():'OLD';}catch(e){return 'OLD';}}
function today(){var d=new Date();return d.getFullYear()+'-'+('0'+(d.getMonth()+1)).slice(-2)+'-'+('0'+d.getDate()).slice(-2);}
function validDate(s){
  var m=/^(\d{4})-(\d{2})-(\d{2})$/.exec(String(s||''));if(!m)return false;
  var y=+m[1],mo=+m[2],d=+m[3];if(y<2000||y>2100)return false;
  var dt=new Date(Date.UTC(y,mo-1,d));return dt.getUTCFullYear()===y&&dt.getUTCMonth()===mo-1&&dt.getUTCDate()===d;
}
function num(v){if(v==null||v==='')return null;var n=Number(v);return isFinite(n)?n:null;}
function validOdds(v){var o=num(v);return o!=null&&o!==0&&o>=-1000?o:null;}
function resOf(r){var x=String(r.result||'PENDING').toUpperCase().replace(/_/g,' ').trim();
  return ['WIN','LOSS','PUSH','VOID','PENDING','NO PICK'].indexOf(x)>=0?x:(x==='NO_PICK'?'NO PICK':'PENDING');}
function profitOf(r,stake){
  if(r.observation_only)return null;var res=resOf(r);
  var o=validOdds(r.odds);if(o==null)return null;
  if(res==='PUSH'||res==='VOID')return 0;
  if(res!=='WIN'&&res!=='LOSS')return null;
  if(res==='LOSS')return -stake;
  return o>0?stake*o/100:stake*100/Math.abs(o);
}
function rateOf(p){
  var v=p.rate;if(v==null||v==='')v=Math.max(num(p.rateA)||0,num(p.rateB)||0);
  if(v==null||v==='')return '';var s=String(v);return /%$/.test(s)?s:(isFinite(Number(s))?s+'%':s);
}
function money(v){return v==null||!isFinite(v)?'-':(v>=0?'+$':'-$')+Math.abs(v).toFixed(2);}
function implied(o){return o==null?null:(o>0?100/(o+100):Math.abs(o)/(Math.abs(o)+100))*100;}
function cls(v){return v>0?'ngr-pos':v<0?'ngr-neg':'';}
function stats(rows,stake){
  var s={w:0,l:0,push:0,voids:0,pend:0,nopick:0,obs:0,staked:0,net:0,gross:0,exp:0,pricedN:0,total:rows.length};
  rows.forEach(function(r){
    if(r.observation_only){s.obs++;return;}
    var res=resOf(r),o=validOdds(r.odds);
    if(res==='WIN')s.w++;else if(res==='LOSS')s.l++;else if(res==='PUSH')s.push++;else if(res==='VOID')s.voids++;
    else if(res==='NO PICK')s.nopick++;else{s.pend++;if(o!=null)s.exp+=stake;}
    var p=profitOf(r,stake);
    if(p!=null&&(res==='WIN'||res==='LOSS')){s.pricedN++;s.staked+=stake;s.net+=p;s.gross+=stake+p;}
  });
  s.dec=s.w+s.l;s.rate=s.dec?s.w/s.dec*100:null;s.roi=s.staked>0?s.net/s.staked*100:null;
  return s;
}
function kpis(s){
  function k(l,v,c){return '<div class="ngr-kpi"><b>'+l+'</b><span class="'+(c||'')+'">'+v+'</span></div>';}
  return '<div class="ngr-kpis">'+k('W / L',s.w+' / '+s.l)+k('Hit rate',s.rate==null?'-':s.rate.toFixed(1)+'%')
   +k('Staked','$'+s.staked.toFixed(2))+k('Pending exposure','$'+s.exp.toFixed(2),s.exp?'ngr-warn':'')
   +k('Gross return','$'+s.gross.toFixed(2))+k('Net profit',money(s.net),cls(s.net))
   +k('ROI',s.roi==null?'-':(s.roi>=0?'+':'')+s.roi.toFixed(1)+'%',s.roi==null?'':cls(s.roi))
   +k('Pending',s.pend)+k('Push / Void',s.push+' / '+s.voids)+k('TD observations',s.obs,s.obs?'ngr-warn':'')+'</div>'
   +'<div class="ngr-sub" style="margin-bottom:6px">$'+S.stake+' per play. ROI counts only settled WIN/LOSS plays with real odds (-1000 or longer). Push/Void are refunded and excluded. Anytime TD observations are shown but never counted.</div>';
}
function gid(g){return g.game_key||((g.game||'')+'|'+(g.game_start||''));}
function sameGame(a,b){
  if(a.game_key&&b.game_key)return a.game_key===b.game_key;
  if((a.game||'')!==(b.game||''))return false;
  return !(a.game_start&&b.game_start)||a.game_start===b.game_start||Date.parse(a.game_start)===Date.parse(b.game_start);
}
function buildEntries(){
  var out=[],data=S.data;if(!data)return out;
  var dates=(data.dates||[]).map(function(d){return {date:d.date,games:(d.games||[]).slice()};});
  var byDate={};dates.forEach(function(d){byDate[d.date]=d;});
  if(S.period==='day'&&validDate(S.date)&&!byDate[S.date]){var nd={date:S.date,games:[]};dates.push(nd);byDate[S.date]=nd;}
  var st=window._nflState,bd=st&&st.d&&st.d.date,bg=(st&&st.d&&st.d.games)||[];
  function addMissing(dt,name,start){
    if(!name)return;var probe={game:name,game_start:start||''};
    if(dt.games.some(function(g){return sameGame(g,probe);}))return;
    dt.games.push({game:name,game_start:start||'',plays:[],status:'MISSING_SOURCE',_missing:true});
  }
  if(bd&&!window.__ngrNoBoard&&(!st.d.system||String(st.d.system).toUpperCase()===S.sys))bg.forEach(function(g){
    var start=g.game_start||g.start||g.start_time||g.commence_time||'',day=window.nflGameRecordDate(start,bd);
    if(byDate[day])addMissing(byDate[day],g.game||((g.away_abbr||g.away_team||'?')+' @ '+(g.home_abbr||g.home_team||'?')),start);
  });
  if(S.game&&byDate[S.date])addMissing(byDate[S.date],S.game,S.start);
  dates.sort(function(a,b){return String(b.date).localeCompare(String(a.date));});
  dates.forEach(function(d){d.games.forEach(function(g){
    var rows=(g.plays||[]).map(function(p){var c={};for(var k in p)c[k]=p[k];c._date=d.date;c._game=g.game;return c;});
    out.push({date:d.date,game:g,rows:rows,idx:out.length});
  });});
  return out;
}
function isCur(e){return S.game&&e.date===S.date&&sameGame(e.game,{game:S.game,game_start:S.start});}
function missingMsg(e){
  var g=e.game,st=String(g.status||'');
  if(g._missing||/missing|no.?source|unavailable/i.test(st))
    return 'No saved pregame source exists for this game on '+e.date+'. Nothing is substituted from the current board, so no official 80-100% history can be shown.';
  return 'No qualified 80-100% picks were saved for this game.';
}
function resultCell(r,stake){
  var res=resOf(r),p=profitOf(r,stake);
  return '<span class="nfl-trk-result '+esc(res.toLowerCase().replace(/ /g,'-'))+'">'+esc(res)+'</span><br><small style="font-family:monospace" class="'+(r.observation_only?'ngr-warn':p==null?'':cls(p))+'">'+(r.observation_only?'OBSERVATION':money(p))+'</small>';
}
function tableHtml(rows,stake){
  var b=rows.map(function(r){
    var o=validOdds(r.odds),odds=o==null?'-':(o>0?'+':'')+o,ip=implied(o);
    return '<tr><td data-label="Date" style="font-family:monospace;color:#94a3b8">'+esc(r._date)+'</td>'
     +'<td class="n" data-label="Player">'+esc(r.name)+'</td><td data-label="Team" style="color:#c4b5fd">'+esc(r.team)+'</td>'
      +'<td data-label="Market">'+esc(r.stat_label||r.category||r.market)+(r.position?'<br><small style="color:#64748b">'+esc(r.position)+'</small>':'')+'</td>'
     +'<td data-label="Pick">'+esc((r.side||'')+(r.line!=null&&r.line!==''?' '+r.line:''))+'</td>'
     +'<td data-label="Historical" style="font-family:monospace;font-weight:800">'+esc(rateOf(r)||'-')+'</td>'
     +'<td data-label="Odds / Book" style="font-family:monospace">'+esc(odds)+'<br><small style="color:#64748b">'+esc(r.book||'Book unavailable')+'</small></td>'
      +'<td data-label="Implied / Bet" style="font-family:monospace">'+(ip==null?'-':ip.toFixed(1)+'%')+'<br><small>'+(r.observation_only?'Observation':o==null||resOf(r)==='NO PICK'?'Unpriced':'$'+stake.toFixed(2))+'</small></td>'
     +'<td data-label="Actual">'+(r.actual!=null&&r.actual!==''?esc(r.actual):'-')+'</td>'
     +'<td data-label="Result / P&amp;L">'+resultCell(r,stake)+'</td></tr>';
  }).join('');
  return '<div class="nfl-trk-table-scroll ngr-scroll"><table class="nfl-trk-tbl nfl-trk-compact ngr-tbl"><thead><tr><th>Date</th><th>Player</th><th>Team</th><th>Market</th><th>Pick</th><th>Hist %</th><th>Odds / Book</th><th>Implied / Bet</th><th>Actual</th><th>Result / P&amp;L</th></tr></thead><tbody>'+b+'</tbody></table></div>';
}
function catHtml(rows,stake){
  var cats={},order=[];
  rows.forEach(function(r){var c=r.category||r.market||'Other';if(!cats[c]){cats[c]=[];order.push(c);}cats[c].push(r);});
  return order.map(function(c){
    var l=cats[c],s=stats(l,stake),acc=s.rate==null?'#94a3b8':s.rate>=70?'#4ade80':s.rate>=55?'#facc15':'#f87171';
    return '<details class="nfl-trk-group" open style="--trk-accent:'+acc+'"><summary class="nfl-trk-group-head"><div class="nfl-trk-group-title"><span class="nfl-trk-group-kicker">Category</span><span class="nfl-trk-group-name">'+esc(c)+'</span></div>'
     +'<div class="nfl-trk-group-summary"><span>'+s.w+'W · '+s.l+'L'+(s.pend?' · '+s.pend+' pending':'')+(s.obs?' · '+s.obs+' observations':'')+'</span><span class="nfl-trk-group-rate">'+(s.rate==null?'-':s.rate.toFixed(1)+'%')+'</span>'
     +'<span class="nfl-trk-group-pl '+cls(s.net)+'">'+money(s.net)+'</span><span class="'+(s.roi==null?'':cls(s.roi))+'">'+(s.roi==null?'-':(s.roi>=0?'+':'')+s.roi.toFixed(1)+'% ROI')+'</span><span class="nfl-trk-group-toggle" aria-hidden="true"></span></div></summary>'
     +tableHtml(l,stake)+'</details>';
  }).join('');
}
function playsHtml(rows,stake){return S.view==='list'?tableHtml(rows,stake):catHtml(rows,stake);}
function scopeRows(){
  if(S.sel!=null){var e=S.entries[S.sel];return e?e.rows:[];}
  var a=[];S.entries.forEach(function(e){a=a.concat(e.rows);});return a;
}
function bodyHtml(){
  if(S.loading)return '<div class="ngr-skel"></div><div class="ngr-skel"></div><div class="ngr-skel"></div>';
  if(S.err)return '<div class="ngr-err" role="alert">'+esc(S.err)+'<div style="margin-top:8px"><button class="ngr-btn" data-ngr="retry">Retry</button></div></div>';
  if(!S.data)return '<div class="ngr-empty">Press Get Results to load saved plays.</div>';
  var stake=S.stake,h='';
  (S.data.warnings||[]).forEach(function(w){h+='<div class="ngr-note">'+esc(w)+'</div>';});
  if(S.sel!=null){
    var e=S.entries[S.sel];
    if(!e)return h+'<div class="ngr-empty">That game is not in the loaded results.</div>';
    h+='<div class="ngr-date">'+esc(e.game.game)+' · '+esc(e.date)+(e.game.game_start?' · '+esc(e.game.game_start):'')+'</div>';
    if(e.game.captured_at)h+='<div class="ngr-sub">Saved pregame at '+esc(e.game.captured_at)+(e.game.status?' · '+esc(e.game.status):'')+'</div>';
    if(!e.rows.length)return h+'<div class="ngr-empty">'+esc(missingMsg(e))+'</div>';
    return h+kpis(stats(e.rows,stake))+playsHtml(e.rows,stake);
  }
  if(!S.entries.length)return h+'<div class="ngr-empty">No saved games for this period.</div>';
  var all=scopeRows();h+=kpis(stats(all,stake));
  if(!all.length)h+='<div class="ngr-note">No qualified 80-100% picks in this period. Games below show their saved status.</div>';
  var last=null;
  S.entries.forEach(function(e){
    if(e.date!==last){if(last!==null)h+='</div>';h+='<div class="ngr-date">'+esc(e.date)+'</div><div class="ngr-games">';last=e.date;}
    var s=stats(e.rows,stake),line;
    if(!e.rows.length)line='<span style="color:#94a3b8">'+(e.game._missing||/missing/i.test(e.game.status||'')?'No saved source':'No qualified picks')+'</span>';
    else line=s.w+'-'+s.l+(s.pend?' · '+s.pend+' pending':'')+' · <span class="'+cls(s.net)+'">'+money(s.net)+'</span>';
    h+='<button type="button" class="ngr-game'+(isCur(e)?' cur':'')+'" data-ngr="game" data-i="'+e.idx+'"><div class="g">'+esc(e.game.game||'Game')+'</div><div class="m">'+esc(e.game.game_start||'')+' · '+e.rows.length+' plays</div><div class="r">'+line+'</div></button>';
  });
  return h+'</div>';
}
function render(){
  var b=$('ngrBody');if(!b)return;
  S.entries=S.data?buildEntries():[];
  b.innerHTML=bodyHtml();
  var back=$('ngrBack');if(back)back.style.display=S.sel!=null?'':'none';
  ['cat','list'].forEach(function(v){var x=$('ngrV'+v);if(x){x.classList.toggle('on',S.view===v);x.setAttribute('aria-pressed',S.view===v?'true':'false');}});
  var t=$('ngrTitle');if(t)t.textContent=S.sel!=null&&S.entries[S.sel]?S.entries[S.sel].game.game:(S.game&&!S.data?S.game:'Game Picks Record');
  var sub=$('ngrSub');if(sub)sub.textContent='Historical 80-100% plays'+(S.data&&S.data.updated_at?' · updated '+S.data.updated_at:'');
  var sy=$('ngrSys');if(sy){sy.textContent='SYSTEM: '+S.sys;sy.style.color=S.sys==='NEW'?'#67e8f9':'#fbbf24';}
  var gb=$('ngrGet');if(gb)gb.disabled=S.loading;
}
function load(grade){
  var d=$('ngrDate'),p=$('ngrPeriod');
  if(d)S.date=d.value.trim();if(p)S.period=p.value;
  if(S.ctl){try{S.ctl.abort();}catch(e){}}
  var seq=++S.seq;
  if(!validDate(S.date)){S.loading=false;S.data=null;S.err='Enter a valid date (YYYY-MM-DD, years 2000-2100).';render();return;}
  var sys=sysNow(),gen=typeof _nflSystemGeneration==='number'?_nflSystemGeneration:0;
  S.sys=sys;S.loading=true;S.err='';render();
  var ctl=typeof AbortController==='function'?new AbortController():null;S.ctl=ctl;
  if(ctl&&typeof _nflTrackController==='function')_nflTrackController(ctl);
  var url='/api/game-picks-record?date_str='+encodeURIComponent(S.date)+'&period='+encodeURIComponent(S.period)+'&system='+sys+'&grade='+(grade?'true':'false');
  function fresh(){
    if(seq!==S.seq||!S.open)return false;
    if(typeof _nflRequestCurrent==='function'&&!_nflRequestCurrent(gen,sys)){
      S.loading=false;S.data=null;S.sys=sysNow();S.err='The system changed while loading. Press Retry to load the '+S.sys+' record.';render();return false;
    }
    return true;
  }
  fetch(url,{credentials:'include',signal:ctl?ctl.signal:undefined}).then(function(r){
    return r.text().then(function(t){
      var j=null;try{j=t?JSON.parse(t):null;}catch(e){}
      if(!r.ok){var m=j&&(j.error||j.detail||j.message);throw new Error('Record request failed ('+r.status+')'+(m?': '+(typeof m==='string'?m:JSON.stringify(m)):'.'));}
      if(!j||typeof j!=='object'||!Array.isArray(j.dates))throw new Error('The server returned an unreadable record response.');
      return j;
    });
  }).then(function(j){
    if(ctl&&typeof _nflUntrackController==='function')_nflUntrackController(ctl);
    if(!fresh())return;
    if(j.system&&String(j.system).toUpperCase()!==sys){S.loading=false;S.data=null;S.err='Server returned the '+j.system+' record instead of '+sys+'. Press Retry.';render();return;}
    S.data=j;S.loading=false;S.err='';
    if(S.sel!=null)S.sel=null;
    S.entries=buildEntries();
    var keep=null;
    S.entries.forEach(function(e){if(isCur(e)&&S.selKeep)keep=e.idx;});
    S.sel=keep;S.selKeep=false;render();
  }).catch(function(e){
    if(ctl&&typeof _nflUntrackController==='function')_nflUntrackController(ctl);
    if(e&&e.name==='AbortError')return;
    if(!fresh())return;
    S.loading=false;S.data=null;S.err=(e&&e.message)||'Could not reach the record endpoint.';render();
  });
}
function csvDownload(){
  var rows=scopeRows(),stake=S.stake;
  var head=['Date','Game','Player','Team','Market','Side','Line','Historical %','Odds','Book','Stake','Actual','Result','Profit','Observation','Implied %'];
  var out=[head].concat(rows.map(function(r){
    var p=profitOf(r,stake),o=validOdds(r.odds),res=resOf(r);
    var st=(!r.observation_only&&o!=null&&res!=='NO PICK')?stake:'';
    return [r._date,r._game,r.name,r.team,r.stat_label||r.category||r.market,r.side,r.line,rateOf(r),o,r.book,st,r.actual,res,p==null?'':p.toFixed(2),r.observation_only?'OBSERVATION':'',implied(o)];
  }));
  var csv=out.map(function(r){return r.map(function(v){return '"'+String(v==null?'':v).replace(/"/g,'""')+'"';}).join(',');}).join('\r\n');
  var blob=new Blob(['\ufeff'+csv],{type:'text/csv;charset=utf-8;'}),url=URL.createObjectURL(blob),a=document.createElement('a');
  a.href=url;a.download='nfl-game-picks-record-'+S.date+'-'+S.period+'.csv';document.body.appendChild(a);a.click();document.body.removeChild(a);
  setTimeout(function(){URL.revokeObjectURL(url);},1000);
}
function onKey(e){
  var ov=$(ID);if(!ov)return;
  if(e.key==='Escape'){e.stopPropagation();e.preventDefault();window.closeNflGamePicksRecord();return;}
  if(e.key==='Tab'){
    var f=[].slice.call(ov.querySelectorAll('button:not([disabled]),input,select,summary,[tabindex="0"]')).filter(function(x){return x.offsetParent!==null;});
    if(!f.length)return;var a=f[0],z=f[f.length-1];
    if(!ov.contains(document.activeElement)){e.preventDefault();a.focus();}
    else if(e.shiftKey&&document.activeElement===a){e.preventDefault();z.focus();}
    else if(!e.shiftKey&&document.activeElement===z){e.preventDefault();a.focus();}
  }
}
function shell(){
  var ov=document.createElement('div');ov.className='ngr-ov';ov.id=ID;
  ov.innerHTML='<div class="ngr-dlg" role="dialog" aria-modal="true" aria-labelledby="ngrTitle" tabindex="-1">'
   +'<div class="ngr-head"><div><h3 class="ngr-title" id="ngrTitle">Game Picks Record</h3><div class="ngr-sub" id="ngrSub"></div></div>'
   +'<div style="display:flex;gap:6px;align-items:center"><span class="ngr-sys" id="ngrSys"></span><button type="button" class="ngr-x" id="ngrClose" aria-label="Close">Close</button></div></div>'
   +'<div class="ngr-ctl"><button type="button" class="ngr-btn" id="ngrBack" style="display:none">Back / All Games</button>'
   +'<label>Date <input id="ngrDate" type="date" min="2000-01-01" max="2100-12-31"></label>'
   +'<label>Period <select id="ngrPeriod"><option value="day">Day</option><option value="week">Week</option><option value="month">Month</option><option value="year">Year</option><option value="all">All</option></select></label>'
   +'<label>Stake $ <input id="ngrStake" class="ngr-stake" type="number" min="0.01" step="any" inputmode="decimal"></label>'
   +'<button type="button" class="ngr-btn" id="ngrVcat" aria-pressed="true">Category</button><button type="button" class="ngr-btn" id="ngrVlist" aria-pressed="false">Full List</button>'
   +'<button type="button" class="ngr-btn" id="ngrGet">Get Results</button><button type="button" class="ngr-btn" id="ngrCsv">CSV</button></div>'
   +'<div class="ngr-body" id="ngrBody" aria-live="polite"></div></div>';
  document.body.appendChild(ov);
  ov.addEventListener('mousedown',function(e){ov._down=e.target===ov;});
  ov.addEventListener('click',function(e){
    if(e.target===ov&&ov._down){window.closeNflGamePicksRecord();return;}
    var t=e.target.closest&&e.target.closest('[data-ngr]');if(!t||!ov.contains(t))return;
    var a=t.getAttribute('data-ngr');
    if(a==='game'){S.sel=+t.getAttribute('data-i');render();$('ngrBody').scrollTop=0;}
    else if(a==='retry')load(false);
  });
  $('ngrClose').onclick=function(){window.closeNflGamePicksRecord();};
  $('ngrBack').onclick=function(){S.sel=null;render();};
  $('ngrGet').onclick=function(){var keepE=S.sel!=null?S.entries[S.sel]:null;S.selKeep=!!keepE;if(keepE){S.game=keepE.game.game;S.start=keepE.game.game_start||'';S.date=keepE.date;$('ngrDate').value=S.date;}load(true);};
  $('ngrDate').onchange=function(){S.game='';S.start='';S.selKeep=false;S.sel=null;load(false);};
  $('ngrPeriod').onchange=function(){S.game='';S.start='';S.selKeep=false;S.sel=null;load(false);};
  $('ngrVcat').onclick=function(){S.view='cat';render();};
  $('ngrVlist').onclick=function(){S.view='list';render();};
  $('ngrCsv').onclick=function(){if(!S.data){return;}csvDownload();};
  $('ngrStake').oninput=function(){var n=parseFloat(this.value);if(isFinite(n)&&n>0){S.stake=n;var b=$('ngrBody');if(b&&S.data&&!S.loading&&!S.err){var st=b.scrollTop;b.innerHTML=bodyHtml();b.scrollTop=st;}}};
  $('ngrStake').onblur=function(){this.value=S.stake;};
  return ov;
}
window.nflGameRecordDate=function(start,fallback){
  if(start&&isFinite(Date.parse(start))){try{
    var parts=new Intl.DateTimeFormat('en-CA',{timeZone:'America/New_York',year:'numeric',month:'2-digit',day:'2-digit'}).formatToParts(new Date(start)),v={};
    parts.forEach(function(p){v[p.type]=p.value;});return v.year+'-'+v.month+'-'+v.day;
  }catch(e){}}
  return fallback||today();
};
window.openNflGamePicksRecord=function(game,date,gameStart){
  window.closeNflGamePicksRecord(true);
  S.lastFocus=document.activeElement;
  S.game=game?String(game):'';S.start=gameStart?String(gameStart):'';
  var st=window._nflState,bd=st&&st.d&&st.d.date,tp=$('nflTrkDate');
  S.date=gameStart?window.nflGameRecordDate(gameStart,date||bd):date||bd||(tp&&tp.value)||today();S.period='day';S.sel=null;S.selKeep=!!S.game;
  S.data=null;S.err='';S.sys=sysNow();S.open=true;
  shell();
  $('ngrDate').value=S.date;$('ngrPeriod').value='day';$('ngrStake').value=S.stake;
  document.addEventListener('keydown',onKey,true);
  var dlg=document.querySelector('#'+ID+' .ngr-dlg');if(dlg)dlg.focus();
  load(true);
};
window.closeNflGamePicksRecord=function(keepFocus){
  S.seq++;if(S.ctl){try{S.ctl.abort();}catch(e){}S.ctl=null;}
  var ov=$(ID);if(ov)ov.remove();
  document.removeEventListener('keydown',onKey,true);
  var was=S.open;S.open=false;S.loading=false;
  if(was&&keepFocus!==true&&S.lastFocus&&S.lastFocus.focus&&document.contains(S.lastFocus)){try{S.lastFocus.focus();}catch(e){}}
};
window.bindNflGameRecordButtons=function(root){
  (root||document).querySelectorAll('[data-nfl-game-record]').forEach(function(b){
    if(b.__ngrBound)return;b.__ngrBound=true;
    b.addEventListener('click',function(e){e.preventDefault();window.openNflGamePicksRecord(b.getAttribute('data-game')||'',b.getAttribute('data-date')||'',b.getAttribute('data-start')||'');});
  });
};
})();
</script>"""


def record_ui():
    """Return the complete inline UI without reading deployment asset files."""
    return _GAME_RECORD_HTML
