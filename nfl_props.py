"""
nfl_props.py — NFL Player Props vs Opponent History
=====================================================
Step 1 : Get today's NFL player prop lines from The Odds API.
Step 2 : Pull career H/A game logs vs today's opponent from ESPN.
Step 3 : Calculate avg performance vs that team and compare to the line.
Pick   : OVER if avg > line, UNDER if avg < line.
         Shows history even if only 1 game available.
"""

import os, re, asyncio
from typing import Dict, List, Optional
import httpx

ODDS_API_KEY = os.environ.get("ODDS_API_KEY", "")
ODDS_BASE    = "https://api.the-odds-api.com/v4"
ESPN_BASE    = "https://site.web.api.espn.com/apis/common/v3/sports/football/nfl"
ESPN_SEASONS = [2024, 2023, 2022, 2021, 2020]

# NFL prop market keys on The Odds API
PROP_MARKETS = [
    "player_rush_yds",
    "player_reception_yds",
    "player_pass_yds",
    "player_anytime_td",
    "player_receptions",
    "player_pass_tds",
]

PROP_LABELS = {
    "player_rush_yds":      "Rush Yds",
    "player_reception_yds": "Rec Yds",
    "player_pass_yds":      "Pass Yds",
    "player_anytime_td":    "Anytime TD",
    "player_receptions":    "Receptions",
    "player_pass_tds":      "Pass TDs",
}

# ESPN stat keys per prop type
PROP_STAT_KEY = {
    "player_rush_yds":      "rushingYards",
    "player_reception_yds": "receivingYards",
    "player_pass_yds":      "passingYards",
    "player_anytime_td":    "touchdowns",
    "player_receptions":    "receptions",
    "player_pass_tds":      "passingTouchdowns",
}


# ─────────────────────────────────────────────────────────────────────
# Helpers
# ─────────────────────────────────────────────────────────────────────

def _normalize(s: str) -> str:
    return re.sub(r"[^a-z0-9]", "", s.lower())


def _teams_match(t1: str, t2: str) -> bool:
    n1, n2 = _normalize(t1), _normalize(t2)
    if n1 == n2 or n1 in n2 or n2 in n1:
        return True
    w1 = set(n1.split())
    w2 = set(n2.split())
    return len(w1 & w2) >= 1


# ─────────────────────────────────────────────────────────────────────
# Odds API
# ─────────────────────────────────────────────────────────────────────

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
    """Returns list of {name, market, line, over_odds, under_odds}"""
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
                        if side == "Over":
                            lines[key]["over_odds"] = price
                        elif side == "Under":
                            lines[key]["under_odds"] = price
            return list(lines.values())
    except Exception:
        return []


# ─────────────────────────────────────────────────────────────────────
# ESPN — player search + game logs
# ─────────────────────────────────────────────────────────────────────

async def find_espn_player_id(full_name: str) -> Optional[str]:
    try:
        async with httpx.AsyncClient(timeout=10) as c:
            r = await c.get(
                "https://site.web.api.espn.com/apis/search/v2",
                params={"query": full_name, "limit": 5, "sport": "nfl"})
            for result in r.json().get("results", []):
                if result.get("type") != "player":
                    continue
                for item in result.get("contents", []):
                    if _normalize(item.get("displayName", "")) == _normalize(full_name):
                        uid = item.get("uid", "")
                        m = re.search(r"a:(\d+)", uid)
                        if m:
                            return m.group(1)
                        link = item.get("link", {}).get("web", "")
                        m2 = re.search(r"/id/(\d+)", link)
                        if m2:
                            return m2.group(1)
    except Exception:
        pass
    return None


async def get_player_logs_vs_opp(player_id: str, opp_name: str,
                                  side: str, stat_key: str) -> List[float]:
    """Career H/A game logs vs specific opponent for one stat."""
    is_home = (side == "HOME")
    values  = []

    async def fetch_season(season: int):
        try:
            async with httpx.AsyncClient(timeout=15) as c:
                r = await c.get(f"{ESPN_BASE}/athletes/{player_id}/gamelog",
                                params={"season": season})
                if not r.is_success:
                    return
                data = r.json()
                events    = data.get("events", {})
                ev_map    = events.get("eventTypes", [{}])
                labels    = []
                stats_map = {}

                for et in ev_map:
                    for cat in et.get("categories", []):
                        if not labels:
                            labels = [e.get("text","") for e in cat.get("labels", [])]
                        for ev in cat.get("events", []):
                            eid = ev.get("eventId", "")
                            if eid and ev.get("stats"):
                                stats_map[eid] = ev["stats"]

                events_data = data.get("eventLog", {}).get("events", {})
                for eid, ev_info in events_data.items():
                    if eid not in stats_map:
                        continue
                    # Check home/away
                    home = ev_info.get("home", False)
                    if home != is_home:
                        continue
                    # Check opponent
                    opp = ev_info.get("opponent", {}).get("displayName", "")
                    if not _teams_match(opp, opp_name):
                        continue
                    # Get stat value
                    raw = stats_map[eid]
                    if not labels or not raw:
                        continue
                    try:
                        idx = next((i for i, l in enumerate(labels)
                                    if _normalize(l) == _normalize(stat_key)), None)
                        if idx is not None and idx < len(raw):
                            val = float(raw[idx])
                            values.append(val)
                    except Exception:
                        pass
        except Exception:
            pass

    await asyncio.gather(*[fetch_season(s) for s in ESPN_SEASONS])
    return values


# ─────────────────────────────────────────────────────────────────────
# Main entry point
# ─────────────────────────────────────────────────────────────────────

async def run_nfl_props(team_schedule: Dict) -> Dict:
    """
    Run NFL Props pipeline.
    team_schedule: {team_name: {"side": "HOME"|"AWAY", "opponent": "..."}}
    Returns {"picks": [...], "all": [...]}
    """
    if not ODDS_API_KEY:
        return {"picks": [], "all": [], "error": "No ODDS_API_KEY set"}

    # Get today's events
    events = await get_nfl_events()
    if not events:
        return {"picks": [], "all": [], "error": "No NFL games today"}

    # Collect all prop lines
    all_lines = []
    for event in events:
        lines = await get_prop_lines_for_event(event["id"])
        for l in lines:
            l["home_team"] = event.get("home_team", "")
            l["away_team"] = event.get("away_team", "")
        all_lines.extend(lines)

    if not all_lines:
        return {"picks": [], "all": [],
                "error": "No NFL prop lines posted yet — check back closer to game time"}

    # Analyze each player prop
    all_results = []

    async def analyze(pl: Dict):
        name   = pl["name"]
        line   = pl["line"]
        market = pl["market"]
        label  = pl["label"]

        # Determine H/A
        # Find which team the player is on via schedule
        side = "HOME"
        opp  = pl["away_team"]
        for team, info in team_schedule.items():
            if (_teams_match(team, pl["home_team"]) or
                    _teams_match(team, pl["away_team"])):
                if _teams_match(team, pl["home_team"]):
                    side = "HOME"
                    opp  = pl["away_team"]
                else:
                    side = "AWAY"
                    opp  = pl["home_team"]
                break

        # Get ESPN player ID
        pid = await find_espn_player_id(name)
        if not pid:
            return

        # Get career H/A logs vs opponent
        stat_key = pl.get("stat_key", "")
        values   = await get_player_logs_vs_opp(pid, opp, side, stat_key)

        if not values:
            all_results.append({
                "name": name, "market": market, "label": label,
                "line": line, "side": side, "opp": opp,
                "avg": None, "games": 0, "history": "—",
                "pick": None, "pick_note": f"No H/A history vs {opp}",
                "over_odds": pl.get("over_odds"),
                "under_odds": pl.get("under_odds"),
            })
            return

        avg     = round(sum(values) / len(values), 1)
        history = ", ".join(str(int(v)) for v in values)
        gap     = round(avg - line, 1)

        if avg > line:
            pick      = "OVER"
            pick_note = f"avg {avg} > line {line} (+{gap})"
        elif avg < line:
            pick      = "UNDER"
            pick_note = f"avg {avg} < line {line} ({gap})"
        else:
            pick      = None
            pick_note = f"avg exactly on the line ({line})"

        all_results.append({
            "name":       name,
            "market":     market,
            "label":      label,
            "line":       line,
            "side":       side,
            "opp":        opp,
            "avg":        avg,
            "games":      len(values),
            "history":    history,
            "gap":        gap,
            "pick":       pick,
            "pick_note":  pick_note,
            "over_odds":  pl.get("over_odds"),
            "under_odds": pl.get("under_odds"),
        })

    await asyncio.gather(*[analyze(pl) for pl in all_lines])

    # Sort: picks first (by biggest gap), then no-pick
    picks   = sorted([r for r in all_results if r["pick"]],
                     key=lambda x: abs(x.get("gap", 0)), reverse=True)
    no_pick = [r for r in all_results if not r["pick"]]

    return {"picks": picks, "all": all_results, "no_pick": no_pick}
