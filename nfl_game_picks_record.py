"""Independent 80–100% game-popup record, derived from frozen pregame boards.

No models, migrations, import-time jobs, or changes to existing sport records.
Storage/network callbacks are supplied by main.py and only used on request.
"""

import math
import re
import threading
from datetime import date, datetime, timedelta, timezone
from zoneinfo import ZoneInfo
from pathlib import Path

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


def record_ui():
    """Inline the packaged UI assets; no extra routes or browser requests."""
    root = Path(__file__).resolve().parent
    css = (root / "nfl_game_picks_record.css").read_text(encoding="utf-8")
    js = (root / "nfl_game_picks_record.js").read_text(encoding="utf-8")
    return f"<style>{css}</style><script>{js}</script>"