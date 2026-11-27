"""The controller's local state (docs/RESEARCH_PROTOCOL.md, section 7.1): one SQLite database
under `SIGABA_HOME/state/`. Nothing here is published; it maps tasks to PRs and worktrees, and
holds the queues, episodes, progress, the outbox, events and the goal-result cache."""

from __future__ import annotations

import json
import sqlite3
from pathlib import Path

SCHEMA = """
CREATE TABLE IF NOT EXISTS meta (key TEXT PRIMARY KEY, value TEXT);
CREATE TABLE IF NOT EXISTS tasks (
  task_id TEXT PRIMARY KEY, repo TEXT, goal TEXT, domain TEXT, operation TEXT,
  descriptor TEXT, branch TEXT, worktree TEXT, push_remote TEXT, pr INTEGER, pr_url TEXT,
  state TEXT, reason TEXT, outcome TEXT, created REAL, seq INTEGER DEFAULT 0,
  last_checkpoint REAL, status_comment INTEGER, last_activity REAL, checkpoint_due INTEGER DEFAULT 0);
CREATE TABLE IF NOT EXISTS progress (id INTEGER PRIMARY KEY AUTOINCREMENT, task_id TEXT, time REAL,
  record TEXT);
CREATE TABLE IF NOT EXISTS artifacts (id INTEGER PRIMARY KEY AUTOINCREMENT, task_id TEXT,
  time REAL, paths TEXT, digest TEXT, state TEXT, result TEXT);
CREATE TABLE IF NOT EXISTS verifications (id INTEGER PRIMARY KEY AUTOINCREMENT, task_id TEXT,
  time REAL, digest TEXT, ok INTEGER, statuses TEXT);
CREATE TABLE IF NOT EXISTS queue (seq INTEGER PRIMARY KEY AUTOINCREMENT, key TEXT UNIQUE,
  pair TEXT, goal TEXT, task_id TEXT, proposal TEXT, state TEXT, reason TEXT);
CREATE TABLE IF NOT EXISTS runs (run_id TEXT PRIMARY KEY, config TEXT, started REAL,
  deadline REAL, state TEXT, pid INTEGER, used REAL DEFAULT 0);
CREATE TABLE IF NOT EXISTS episodes (episode_id TEXT PRIMARY KEY, task_id TEXT, run_id TEXT,
  backend TEXT, started REAL, deadline REAL, ended REAL, outcome TEXT, pid INTEGER,
  result TEXT, usage TEXT);
CREATE TABLE IF NOT EXISTS outbox (id INTEGER PRIMARY KEY AUTOINCREMENT, key TEXT UNIQUE,
  task_id TEXT, kind TEXT, payload TEXT, attempts INTEGER DEFAULT 0, next_try REAL DEFAULT 0,
  done INTEGER DEFAULT 0, error TEXT);
CREATE TABLE IF NOT EXISTS events (id INTEGER PRIMARY KEY AUTOINCREMENT, time REAL, kind TEXT,
  task_id TEXT, session TEXT, data TEXT);
CREATE TABLE IF NOT EXISTS cache (id INTEGER PRIMARY KEY AUTOINCREMENT, theorem TEXT, env TEXT,
  context TEXT, outcome TEXT, time REAL, detail TEXT);
CREATE TABLE IF NOT EXISTS approvals (digest TEXT PRIMARY KEY, dir TEXT, time REAL, who TEXT);
CREATE TABLE IF NOT EXISTS remote (key TEXT PRIMARY KEY, data TEXT, time REAL);
"""


class State:
    def __init__(self, path: Path):
        path.parent.mkdir(parents=True, exist_ok=True)
        self.db = sqlite3.connect(str(path), timeout=30, isolation_level=None)
        self.db.row_factory = sqlite3.Row
        self.db.execute("PRAGMA journal_mode=WAL")
        self.db.executescript(SCHEMA)

    def x(self, sql: str, *args):
        return self.db.execute(sql, args)

    def one(self, sql: str, *args) -> dict | None:
        r = self.db.execute(sql, args).fetchone()
        return dict(r) if r else None

    def all(self, sql: str, *args) -> list[dict]:
        return [dict(r) for r in self.db.execute(sql, args).fetchall()]

    def get(self, key: str, default=None):
        r = self.one("SELECT value FROM meta WHERE key=?", key)
        return json.loads(r["value"]) if r else default

    def put(self, key: str, value) -> None:
        self.x("INSERT INTO meta(key,value) VALUES(?,?) ON CONFLICT(key) DO UPDATE SET "
               "value=excluded.value", key, json.dumps(value))

    def transaction(self):
        return _Tx(self.db)

    # -- tasks -----------------------------------------------------------------------------------
    def task(self, task_id: str) -> dict | None:
        t = self.one("SELECT * FROM tasks WHERE task_id=?", task_id)
        if t is None:
            # a unique prefix is accepted
            ts = self.all("SELECT * FROM tasks WHERE task_id LIKE ?", task_id + "%")
            t = ts[0] if len(ts) == 1 else None
        if t:
            t["descriptor"] = json.loads(t["descriptor"])
        return t

    def tasks(self, where: str = "1", *args) -> list[dict]:
        out = self.all(f"SELECT * FROM tasks WHERE {where} ORDER BY created", *args)
        for t in out:
            t["descriptor"] = json.loads(t["descriptor"])
        return out

    def update_task(self, task_id: str, **kw) -> None:
        cols = ", ".join(f"{k}=?" for k in kw)
        self.x(f"UPDATE tasks SET {cols} WHERE task_id=?", *kw.values(), task_id)

    def latest_progress(self, task_id: str) -> dict | None:
        r = self.one("SELECT * FROM progress WHERE task_id=? ORDER BY id DESC LIMIT 1", task_id)
        if r:
            r["record"] = json.loads(r["record"])
        return r

    def event(self, now: float, kind: str, task_id: str | None, session: str | None,
              data: dict) -> None:
        self.x("INSERT INTO events(time,kind,task_id,session,data) VALUES(?,?,?,?,?)",
               now, kind, task_id, session, json.dumps(data)[:20000])


class _Tx:
    def __init__(self, db):
        self.db = db

    def __enter__(self):
        self.db.execute("BEGIN IMMEDIATE")
        return self

    def __exit__(self, et, ev, tb):
        self.db.execute("ROLLBACK" if et else "COMMIT")
        return False
