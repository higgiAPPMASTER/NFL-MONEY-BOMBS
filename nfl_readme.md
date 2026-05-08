# NFL Money Bombs 💣

Pattern-based NFL daily picks. Finds players hitting 75%+ in Pass Yds, Rush Yds, Rec Yds, Receptions, or TDs against today's specific opponent (home/away context).

## Stack
- FastAPI + Python 3.11
- 100% ESPN API (schedule + rosters + player game logs)
- No blocked APIs, no auth needed

## Algorithm
1. ESPN scoreboard → today's NFL games
2. ESPN roster → players for each team
3. ESPN game log → 3 seasons of historical data per player
4. Filter by: today's opponent + home/away context
5. Find highest threshold hit at ≥75% rate (min 2 games)
6. Rank → Top 10 picks + All Patterns by game

## Deploy on Render
**Build:** `pip install --no-cache-dir -r requirements.txt`
**Start:** `uvicorn main:app --host 0.0.0.0 --port $PORT`

## Env Vars
| Key | Value |
|-----|-------|
| `USERS` | `username:password` |
| `SECRET_KEY` | any random string |
