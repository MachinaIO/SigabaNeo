#!/usr/bin/env python3
"""The research controller's CLI (docs/RESEARCH_PROTOCOL.md, section 11). JSON on standard
output. Exit status: 0 success, 2 usage or protocol error, 3 permission, 4 network or provider,
5 verification failure.

    python3 python/sigaba_research.py [--home DIR] [--repo OWNER/NAME] COMMAND ...

The repository defaults to the one in DAG_REPO_URL; the home to $SIGABA_HOME or ~/.sigaba.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from research import controller as C  # noqa: E402
from research.remote import RemoteError  # noqa: E402

CORE = Path(__file__).resolve().parents[1]


def default_repo() -> str | None:
    p = CORE / "DAG_REPO_URL"
    if not p.exists():
        return None
    for line in p.read_text().splitlines():
        line = line.strip()
        if line and not line.startswith("#"):
            return line.removeprefix("https://github.com/").removesuffix(".git").strip("/")
    return None


def load(path: str):
    return json.loads(Path(path).read_text() if path != "-" else sys.stdin.read())


def parser() -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(prog="sigaba_research.py", description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--home", default=os.environ.get("SIGABA_HOME", "~/.sigaba"))
    ap.add_argument("--repo", default=None)
    sub = ap.add_subparsers(dest="cmd", required=True)

    sub.add_parser("doctor")
    sub.add_parser("sync")

    g = sub.add_parser("goals").add_subparsers(dest="sub", required=True)
    g.add_parser("list")
    x = g.add_parser("show")
    x.add_argument("fingerprint")

    g = sub.add_parser("goal").add_subparsers(dest="sub", required=True)
    x = g.add_parser("prepare")
    x.add_argument("--file", required=True, help="the goal contract (JSON)")
    x.add_argument("--dir")
    x.add_argument("--distinct", metavar="REASON",
                   help="the user confirmed this is a different goal from those naming the same "
                        "nodes; the reason is recorded in the bundle")
    x = g.add_parser("review")
    x.add_argument("--dir", required=True)
    x = g.add_parser("approve")
    x.add_argument("--dir", required=True)
    x.add_argument("--digest", required=True)
    x = g.add_parser("register")
    x.add_argument("--dir", required=True)

    t = sub.add_parser("task").add_subparsers(dest="sub", required=True)
    x = t.add_parser("create")
    x.add_argument("--file", required=True, help="the task descriptor (JSON)")
    t.add_parser("list")
    for name in ("show", "verify", "checkpoint", "ready", "resume"):
        x = t.add_parser(name)
        x.add_argument("id")
        if name == "verify":
            x.add_argument("--with-deps", action="store_true")
        if name == "checkpoint":
            x.add_argument("--kind", default="progress", choices=["progress", "heartbeat"])
    for name in ("draft", "pause", "block"):
        x = t.add_parser(name)
        x.add_argument("id")
        x.add_argument("--reason", default=None)
    x = t.add_parser("finalize")
    x.add_argument("id")
    x.add_argument("--outcome", required=True)
    x.add_argument("--file", required=True, help="the summary's prose (Markdown)")
    x.add_argument("--close", action="store_true", help="close instead of marking ready")

    sub.add_parser("checkpoint-due")
    x = sub.add_parser("artifact")
    x.add_argument("action", choices=["propose"])
    x.add_argument("id")
    x.add_argument("paths", nargs="+")
    x = sub.add_parser("progress")
    x.add_argument("action", choices=["record"])
    x.add_argument("--task", required=True)
    x.add_argument("--file", required=True)
    for name in ("plan", "candidate"):
        x = sub.add_parser(name)
        x.add_argument("action", choices=["add"])
        x.add_argument("--task", required=True)
        x.add_argument("--file", required=True)
    x = sub.add_parser("pr")
    x.add_argument("action", choices=["fetch"])
    x.add_argument("--task", required=True)
    x.add_argument("--pr", type=int, required=True)

    w = sub.add_parser("work").add_subparsers(dest="sub", required=True)
    x = w.add_parser("propose")
    x.add_argument("--file", required=True, help="a JSON list of task proposals")
    x = w.add_parser("derive")
    x.add_argument("--goal", required=True)
    w.add_parser("list")
    sub.add_parser("graph")

    r = sub.add_parser("run").add_subparsers(dest="sub", required=True)
    x = r.add_parser("start")
    x.add_argument("--backend", choices=["interactive", "claude", "codex"])
    x.add_argument("--domains", help="comma-separated: design,cryptanalysis")
    for k in ("max_parallel_workers", "checkpoint_seconds", "episode_seconds",
              "falsification_seconds", "max_run_seconds", "max_worker_seconds",
              "retry_backoff_seconds", "max_proposals", "grace_seconds"):
        x.add_argument("--" + k.replace("_", "-"), type=int, dest=k)
    x.add_argument("--worker-arg", action="append", dest="worker_args",
                   help="extra arguments for supervised worker CLIs (repeatable)")
    x.add_argument("--no-watchdog", action="store_true",
                   help="do not start the background watchdog")
    r.add_parser("status")
    x = r.add_parser("stop")
    x.add_argument("--reason", default="stopped by the user")
    r.add_parser("next")
    r.add_parser("tick")
    x = sub.add_parser("watchdog")
    x.add_argument("--interval", type=float, default=15.0)

    e = sub.add_parser("episode").add_subparsers(dest="sub", required=True)
    x = e.add_parser("start")
    x.add_argument("id")
    x = e.add_parser("end")
    x.add_argument("id", help="episode or task ID")
    x.add_argument("--outcome", required=True)
    x.add_argument("--file", help="the worker's result (JSON)")

    c = sub.add_parser("cache").add_subparsers(dest="sub", required=True)
    x = c.add_parser("lookup")
    x.add_argument("--theorem", required=True)
    x = c.add_parser("record")
    x.add_argument("--theorem", required=True)
    x.add_argument("--outcome", required=True)
    x.add_argument("--detail", default="")
    x.add_argument("--env")
    x.add_argument("--context")

    x = sub.add_parser("hook")
    x.add_argument("--event", required=True)
    x = sub.add_parser("hooks")
    x.add_argument("action", choices=["install"])
    x.add_argument("--provider", required=True, choices=["claude", "codex"])
    x.add_argument("--task", help="install into this task's worktree (default: the current "
                   "directory)")
    x = sub.add_parser("skills")
    x.add_argument("action", choices=["sync", "check"])
    return ap


def dispatch(ctl: C.Controller, a) -> object:
    cmd, sub = a.cmd, getattr(a, "sub", None)
    if cmd == "doctor":
        return ctl.doctor()
    if cmd == "sync":
        return ctl.sync()
    if cmd == "goals":
        if sub == "list":
            return ctl.goals_overview()
        return ctl.goal_show(a.fingerprint)
    if cmd == "goal":
        if sub == "prepare":
            return ctl.goal_prepare(load(a.file), Path(a.dir) if a.dir else None, a.distinct)
        if sub == "review":
            return ctl.goal_review(Path(a.dir))
        if sub == "approve":
            return ctl.goal_approve(Path(a.dir), a.digest)
        return ctl.goal_register(Path(a.dir))
    if cmd == "task":
        if sub == "create":
            return ctl.task_create(load(a.file))
        if sub == "list":
            return [ctl.task_summary(t) for t in ctl.st.tasks()]
        if sub == "show":
            t = ctl.need(a.id)
            return {**ctl.task_summary(t), "descriptor": t["descriptor"],
                    "latest_progress": ctl.st.latest_progress(t["task_id"]),
                    "episodes": ctl.st.all("SELECT * FROM episodes WHERE task_id=?",
                                           t["task_id"]),
                    "dependencies": ctl.st.get(f"deps:{t['task_id']}", [])}
        if sub == "verify":
            res = ctl.task_verify(a.id, a.with_deps)
            if not res["ok"]:
                raise C.VerificationError(json.dumps(res))
            return res
        if sub == "checkpoint":
            return ctl.checkpoint(a.id, a.kind)
        if sub == "ready":
            return ctl.task_ready(a.id)
        if sub == "resume":
            return ctl.task_resume(a.id)
        if sub == "draft":
            return ctl.task_draft(a.id, a.reason or "back to work")
        if sub == "pause":
            return ctl.task_pause(a.id, a.reason or "paused by the user")
        if sub == "block":
            return ctl.task_block(a.id, a.reason or "blocked")
        if sub == "finalize":
            return ctl.task_finalize(a.id, a.outcome, Path(a.file).read_text(), a.close)
    if cmd == "checkpoint-due":
        return ctl.checkpoint_due()
    if cmd == "artifact":
        return ctl.artifact_propose(a.id, a.paths)
    if cmd == "progress":
        return ctl.progress_record(a.task, load(a.file))
    if cmd == "plan":
        return ctl.plan_add(a.task, load(a.file))
    if cmd == "candidate":
        return ctl.candidate_add(a.task, load(a.file))
    if cmd == "pr":
        return ctl.pr_fetch(a.task, a.pr)
    if cmd == "work":
        if sub == "propose":
            items = load(a.file)
            return ctl.work_propose(items if isinstance(items, list) else [items])
        if sub == "derive":
            return ctl.work_derive(a.goal)
        return ctl.work_list()
    if cmd == "graph":
        return ctl.st.get("graph", {})
    if cmd == "run":
        if sub == "start":
            cfg = {k: getattr(a, k) for k in (
                "backend", "max_parallel_workers", "checkpoint_seconds", "episode_seconds",
                "falsification_seconds", "max_run_seconds", "max_worker_seconds",
                "retry_backoff_seconds", "max_proposals", "grace_seconds", "worker_args")}
            if a.domains:
                cfg["allowed_domains"] = [d.strip() for d in a.domains.split(",") if d.strip()]
            out = ctl.run_start(cfg)
            if not a.no_watchdog:
                logd = ctl.path("state", "runs", out["run_id"])
                log = open(logd / "watchdog.log", "ab")
                p = subprocess.Popen([sys.executable, str(Path(__file__).resolve()), "--home",
                                      str(ctl.home), "--repo", ctl.repo, "watchdog"],
                                     stdout=log, stderr=subprocess.STDOUT,
                                     stdin=subprocess.DEVNULL, start_new_session=True)
                ctl.st.x("UPDATE runs SET pid=? WHERE run_id=?", p.pid, out["run_id"])
                out["watchdog_pid"] = p.pid
                out["stop"] = f"python3 {Path(__file__).resolve()} run stop"
            return out
        if sub == "status":
            return ctl.run_status()
        if sub == "stop":
            return ctl.run_stop(a.reason)
        if sub == "next":
            return ctl.run_next()
        return ctl.watchdog_step()
    if cmd == "watchdog":
        ctl.watchdog(a.interval)
        return {"watchdog": "stopped"}
    if cmd == "episode":
        if sub == "start":
            return ctl.episode_start(a.id)
        return ctl.episode_end(a.id, a.outcome, load(a.file) if a.file else None)
    if cmd == "cache":
        if sub == "lookup":
            return ctl.cache_lookup(a.theorem)
        return ctl.cache_record(a.theorem, a.outcome, a.detail, a.env, a.context)
    if cmd == "hook":
        raw = sys.stdin.read() if not sys.stdin.isatty() else ""
        try:
            data = json.loads(raw) if raw.strip() else {}
        except json.JSONDecodeError:
            data = {}
        ctl.hook(a.event, data if isinstance(data, dict) else {})
        return None
    if cmd == "hooks":
        where = Path(ctl.need(a.task)["worktree"]) if a.task else Path.cwd()
        return ctl.hooks_install(a.provider, where)
    if cmd == "skills":
        return {"changed": C.skills_sync()} if a.action == "sync" else \
            {"differ": C.skills_diff()}
    raise SystemExit(f"unknown command {cmd}")


def main(argv: list[str] | None = None) -> int:
    a = parser().parse_args(argv)
    repo = a.repo or os.environ.get("SIGABA_REPO") or default_repo()
    if not repo:
        print(json.dumps({"error": "no DAG repository: set --repo or DAG_REPO_URL"}))
        return 2
    try:
        ctl = C.Controller(Path(a.home), repo)
        out = dispatch(ctl, a)
    except C.ProtocolError as e:
        print(json.dumps({"error": str(e), "kind": "protocol"}))
        return 2
    except C.VerificationError as e:
        try:
            detail = json.loads(str(e))
        except json.JSONDecodeError:
            detail = str(e)
        print(json.dumps({"error": "verification failed", "kind": "verification",
                          "detail": detail}, indent=1))
        return 5
    except RemoteError as e:
        print(json.dumps({"error": str(e), "kind": e.kind}))
        return 3 if e.kind == "permission" else 4
    if out is not None:
        print(json.dumps(out, indent=1, default=str))
    return 0


if __name__ == "__main__":
    sys.exit(main())
