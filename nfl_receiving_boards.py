"""Receiving-board presentation and forward record partitioning only.

No model changes, HTTP calls, database operations, or import-time jobs.
"""
from collections import defaultdict, deque
import math


RECEIVING_MARKETS = frozenset(("player_reception_yds", "player_receptions"))
RECEIVING_POSITIONS = ("WR", "TE", "RB")
RECEIVING_BOARD_VERSION = 1


def receiving_position(pick):
    for key in ("position", "roster_position", "positionGroup", "defPositionGroup"):
        position = str(pick.get(key) or "").upper().strip()
        if position in ("HB", "FB"):
            position = "RB"
        if position in RECEIVING_POSITIONS:
            return position
    return "UNVERIFIED"


def mark_receiving_picks(picks):
    """Opt newly generated receiving picks into the new forward record layout."""
    for pick in picks or []:
        if pick.get("market") in RECEIVING_MARKETS:
            pick["receivingBoardVersion"] = RECEIVING_BOARD_VERSION


def _number(value):
    try:
        number = float(value)
        return number if math.isfinite(number) else None
    except (TypeError, ValueError):
        return None


def _identity(row):
    side = str(row.get("pick") or row.get("side") or "OVER").upper()
    odds = (row.get("over_odds") if side == "OVER" else row.get("under_odds")
            ) if "pick" in row else row.get("odds")
    return (
        row.get("market") or row.get("mkt") or "", side,
        str(row.get("name") or "").lower().strip(),
        _number(row.get("line") or row.get("realLine")), _number(odds),
    )


def _board_edge(pick):
    gap = _number(pick.get("gap")) or 0.0
    return -gap if str(pick.get("pick") or "OVER").upper() == "UNDER" else gap


def split_receiving_records(main_rows, overflow_rows, snapshot, labels):
    """Repartition only new receiving records after existing grading completes.

    Legacy snapshots, other markets, Locks and line-movement records are kept
    unchanged. The existing grader still evaluates its full candidate pool;
    only the receiving Main/Overflow rows get the requested position quotas.
    """
    metadata = defaultdict(deque)
    for index, pick in enumerate(snapshot or []):
        if (pick.get("market") in RECEIVING_MARKETS
                and pick.get("receivingBoardVersion") == RECEIVING_BOARD_VERSION):
            metadata[_identity(pick)].append((index, pick))
    if not metadata:
        return main_rows, overflow_rows

    groups = defaultdict(list)
    kept_main, kept_overflow = [], []
    for rows, kept in ((main_rows, kept_main), (overflow_rows, kept_overflow)):
        for row in rows:
            market = row.get("market")
            side = str(row.get("side") or "OVER").upper()
            original_category = f"{labels.get(market, market)} ({side.title()})"
            matches = metadata.get(_identity(row))
            # Movement/Locks have their own category despite sharing a market.
            if (market not in RECEIVING_MARKETS
                    or row.get("category") != original_category or not matches):
                kept.append(row)
                continue
            index, pick = matches.popleft()
            position = receiving_position(pick)
            groups[(market, side, position)].append((index, pick, row))

    for (market, side, position), candidates in groups.items():
        # Match the unchanged browser ranking: directional cushion, stable
        # ties in the original complete-pick order.
        candidates.sort(key=lambda item: (-_board_edge(item[1]), item[0]))
        position_label = position if position != "UNVERIFIED" else "Position Unverified"
        category = f"{position_label} {labels[market]} ({side.title()})"
        for rank, (_, pick, row) in enumerate(candidates[:20], 1):
            record = {
                **row, "category": category, "position": position,
                "receivingBoardVersion": RECEIVING_BOARD_VERSION, "rank": rank,
            }
            if rank <= 10:
                record.pop("pool", None)
                kept_main.append(record)
            else:
                record["pool"] = "NFL Overflow"
                kept_overflow.append(record)
    return kept_main, kept_overflow