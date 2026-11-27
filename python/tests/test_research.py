"""The research controller (docs/RESEARCH_PROTOCOL.md) with a fake GitHub, real Git on local
repositories, a fake verifier and a fake clock. No Lean, no network.

    python3 -m unittest discover -s python/tests -p 'test_research.py' -v
"""

from __future__ import annotations

import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

import common  # noqa: F401  (puts python/ on the path)
import dag as D
import dag_tools as T
from research import controller as C
from research import records as R
from research.remote import FakeGitHub

REPO = Path(__file__).resolve().parents[2]
ENV = {"id": "e1", "lean": "leanprover/lean4:v4.36.0-rc2", "core": "v1",
       "core_url": "https://github.com/MachinaIO/Sigaba-Neo", "state": "default", "std": "v1",
       "image": "ghcr.io/x/sigaba-neo-env@sha256:" + "0" * 64}
GOAL = {"schema": "sigaba.goal.v1", "kind": "primitive", "targets": ["theorem:A.main"],
        "definitions": ["definition:Prim"], "objective": {"kind": "minimize_cost"},
        "policy": {"forbidden_routes": ["iO"], "intent": "classical proofs only"},
        "title": "A toy primitive"}
THM = "import Definitions.Def_Prim\n\ntheorem A.{n} : True := by sorry\n"


def git(cwd, *args, **kw):
    return subprocess.run(["git", "-C", str(cwd), *args], check=True, capture_output=True,
                          text=True, **kw).stdout


def thm_files(name: str) -> dict[str, str]:
    slug = name.replace(".", "_")
    return {f"dag/Theorems/Thm_{slug}.lean": THM.replace("A.{n}", name),
            f"dag/Theorems/Thm_{slug}.json": json.dumps({"name": name, "title": name,
                                                          "statement": "True"})}


class Clock:
    def __init__(self, t=1_800_000_000.0):
        self.t = t

    def __call__(self):
        return self.t


def ok_verifier(calls):
    def v(base, new, records, out):
        files = sorted(str(p.relative_to(new)) for p in new.rglob("*") if p.is_file())
        calls.append(files)
        items = [{"path": f, "kind": D.classify(f)[0], "status": "FAILED" if "Bad" in f else "OK"}
                 for f in files if f.endswith((".lean", ".md"))]
        return {"ok": all(i["status"] == "OK" for i in items), "env": "e1", "items": items}
    return v


class Base(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        os.environ.update(GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@e", GIT_COMMITTER_NAME="t",
                          GIT_COMMITTER_EMAIL="t@e")
        self.bare = self.tmp / "remote.git"
        subprocess.run(["git", "init", "-q", "--bare", "-b", "main", str(self.bare)], check=True)
        seed = self.tmp / "seed"
        subprocess.run(["git", "init", "-q", "-b", "main", str(seed)], check=True)
        files = {
            "env/environments.json": json.dumps({"environments": [ENV]}),
            "meta/trusted.json": json.dumps({"mode": "collaborators", "accept": ["alice"],
                                             "automerge": ["alice"]}),
            "dag/Definitions/Def_Prim.lean": "def Prim : Nat := 1\n",
            "dag/Definitions/Def_Prim.json": json.dumps({"name": "Prim", "title": "Prim",
                                                         "tags": ["primitive"]}),
            **thm_files("A.main"),
        }
        gp, gt = R.goal_note(GOAL)
        files[gp] = gt
        self.goal_fp = R.goal_fingerprint(GOAL)
        for f, t in files.items():
            (seed / f).parent.mkdir(parents=True, exist_ok=True)
            (seed / f).write_text(t)
        git(seed, "add", "-A")
        git(seed, "commit", "-q", "-m", "seed")
        git(seed, "push", "-q", str(self.bare), "main")
        self.seed = seed
        self.gh = FakeGitHub("o/dag")
        self.clock = Clock()
        self.calls = []
        self.ctl = self.make()

    def make(self, **kw):
        return C.Controller(self.tmp / "home", "o/dag", gh=self.gh, clock=self.clock,
                            verifier=kw.get("verifier", ok_verifier(self.calls)),
                            remote_url=lambda r: str(self.bare), is_tty=lambda: False)

    def desc(self, **kw):
        d = {"goal": self.goal_fp, "domain": "design", "operation": "deepen",
             "title": "Prove A.main", "scope": "Prove the main theorem.",
             "targets": ["theorem:A.main"]}
        d.update(kw)
        return d

    def write(self, t, files: dict[str, str]):
        for f, text in files.items():
            p = Path(t["worktree"]) / f
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(text)

    def remote_files(self, branch):
        return git(self.bare, "ls-tree", "-r", "--name-only", branch).split()


class TestRecords(Base):
    def test_fingerprint_ignores_title_and_order(self):
        g2 = dict(GOAL, title="other", approved_by="x", targets=list(reversed(GOAL["targets"])))
        self.assertEqual(R.goal_fingerprint(GOAL), R.goal_fingerprint(g2))
        g3 = dict(GOAL, objective={"kind": "prove"})
        self.assertNotEqual(R.goal_fingerprint(GOAL), R.goal_fingerprint(g3))
        with self.assertRaises(ValueError):
            R.canonical({"x": 1.5})

    def test_goal_note_and_precheck(self):
        path, text = R.goal_note(GOAL)
        self.assertEqual(R.goal_note_problems(path, text), [])
        self.assertTrue(R.goal_note_problems("dag/Notes/goal-" + "0" * 64 + ".md", text))
        bad = text.replace('"iO"', '"iO", "x"')
        self.assertTrue(R.goal_note_problems(path, bad))      # contract no longer matches the name
        # dag_tools precheck: a goal note is validated, a mislabelled one is refused
        dag = D.Dag(self.seed)
        g4 = dict(GOAL, objective={"kind": "prove"})
        p4, t4 = R.goal_note(g4)
        d = self.tmp / "pc"
        (d / p4).parent.mkdir(parents=True)
        (d / p4).write_text(t4)
        rows = [{"filename": p4, "status": "added", "type": "blob", "mode": "100644",
                 "size": len(t4)}]
        self.assertEqual(T.precheck(dag, rows, d, "alice", permission="write")["problems"], [])
        (d / p4).write_text(t4.replace("tags: [research-goal]", "tags: []"))
        self.assertTrue(T.precheck(dag, rows, d, "alice", permission="write")["problems"])

    def test_index_lists_goals(self):
        ix = T.index(D.Dag(self.seed), {})
        self.assertEqual([g["fingerprint"] for g in ix["goals"]], [self.goal_fp])
        self.assertIn("A.main", json.dumps(ix["goals"][0]["targets"]))
        self.assertIn("Research goals", T.index_markdown(ix))

    def test_blocks(self):
        text = "x\n```sigaba-plan-v1\n{\"a\": 1}\n```\n```sigaba-plan-v1\nnot json\n```\n"
        bl = R.find_blocks(text, "plan")
        self.assertEqual(bl[0], ({"a": 1}, None))
        self.assertIsNotNone(bl[1][1])
        self.assertIsNone(R.one_block(text, "plan"))


class TestTasks(Base):
    def test_create_is_idempotent_and_one_pr(self):
        d = self.desc()
        t = self.ctl.task_create(d)
        self.assertEqual(t["state"], "active")
        self.assertEqual(len(self.gh.prs), 1)
        pr = self.gh.prs[1]
        self.assertTrue(pr["isDraft"])
        self.assertEqual(R.one_block(pr["body"], "task")["task_id"], t["task_id"])
        self.assertIn(f"research/{t['task_id']}", git(self.bare, "branch", "--list",
                                                       "research/*"))
        comments = self.gh.comments(1)
        self.assertEqual(len(comments), 1)
        self.assertIn(R.STATUS_MARKER, comments[0]["body"])
        # a retry, also after the local state lost the PR number, finds the same PR
        again = self.ctl.task_create({**d, "task_id": t["task_id"]})
        self.assertEqual(again["pr"], 1)
        self.ctl.st.update_task(t["task_id"], pr=None, status_comment=None)
        self.ctl.task_open(t["task_id"])
        self.assertEqual(len(self.gh.prs), 1)
        self.assertEqual(len(self.gh.comments(1)), 1)

    def test_task_needs_a_known_goal(self):
        with self.assertRaises(C.ProtocolError):
            self.ctl.task_create(self.desc(goal="1" * 64))
        self.assertEqual(self.gh.prs, {})
        self.assertIn("no goal", self.ctl.work_propose([self.desc(goal="1" * 64)])
                      ["rejected"][0]["reason"])
        # a goal whose registration PR is still open is enough
        g = dict(GOAL, objective={"kind": "explore"}, parent=self.goal_fp)
        path, text = R.goal_note(g)
        sha = C.git_blob_sha(text.encode())
        self.gh.prs[5] = {"number": 5, "url": "u", "state": "OPEN", "isDraft": True,
                          "headRefName": "register/y", "headRefOid": "f" * 40,
                          "author": {"login": "bob"}, "title": "Register", "body": "",
                          "mergedAt": None}
        self.gh.files[5] = [{"filename": path, "status": "added", "sha": sha}]
        self.gh.blobs[sha] = text.encode()
        t = self.ctl.task_create(self.desc(goal=R.goal_fingerprint(g)))
        self.assertEqual(t["state"], "active")

    def test_bad_descriptor(self):
        with self.assertRaises(C.ProtocolError):
            self.ctl.task_create(self.desc(domain="maths"))

    def test_publish_exact_verified_bytes(self):
        t = self.ctl.task_create(self.desc())
        tt = self.ctl.st.task(t["task_id"])
        self.write(tt, thm_files("A.lemma"))
        self.ctl.artifact_propose(t["task_id"], ["dag/Theorems/Thm_A_lemma.lean"])
        # the companion .json is added automatically
        a = self.ctl.st.one("SELECT paths FROM artifacts")
        self.assertIn("dag/Theorems/Thm_A_lemma.json", a["paths"])
        out = self.ctl.publish(t["task_id"])
        self.assertEqual(out["pushed"], ["dag/Theorems/Thm_A_lemma.json",
                                         "dag/Theorems/Thm_A_lemma.lean"])
        branch = f"research/{t['task_id']}"
        self.assertIn("dag/Theorems/Thm_A_lemma.lean", self.remote_files(branch))
        # the worktree is clean apart from untracked work, and its files are untouched
        wt = Path(tt["worktree"])
        self.assertEqual(git(wt, "status", "--porcelain"), "")
        # a scratch file under dag/ that was not proposed is never published
        self.write(tt, {"dag/Notes/scratch-idea.md": "---\ntitle: x\n---\n"})
        self.ctl.checkpoint(t["task_id"])
        self.assertNotIn("dag/Notes/scratch-idea.md", self.remote_files(branch))

    def test_publish_refuses_failed_or_unsafe(self):
        t = self.ctl.task_create(self.desc())
        tt = self.ctl.st.task(t["task_id"])
        self.write(tt, thm_files("A.Bad"))
        self.ctl.artifact_propose(t["task_id"], ["dag/Theorems/Thm_A_Bad.lean"])
        out = self.ctl.publish(t["task_id"])
        self.assertEqual(out["pushed"], [])
        self.assertNotIn("dag/Theorems/Thm_A_Bad.lean",
                         self.remote_files(f"research/{t['task_id']}"))
        for bad in ("../x.lean", "README.md", "dag/Definitions/Def_Prim.lean",
                    "dag/Theorems/Thm_nothing.lean"):
            with self.assertRaises(C.ProtocolError):
                self.ctl.artifact_propose(t["task_id"], [bad])
        os.symlink("/etc/passwd", Path(tt["worktree"]) / "dag" / "Notes" / "link.md")
        with self.assertRaises(C.ProtocolError):
            self.ctl.artifact_propose(t["task_id"], ["dag/Notes/link.md"])

    def test_snapshot_race(self):
        """Bytes changed after the snapshot are not pushed: the commit is made from the staged
        copy, whatever the worktree holds."""
        t = self.ctl.task_create(self.desc())
        tt = self.ctl.st.task(t["task_id"])
        self.write(tt, thm_files("A.race"))
        self.ctl.artifact_propose(t["task_id"], ["dag/Theorems/Thm_A_race.lean"])
        real = self.ctl.verifier

        def verifier(base, new, records, out):
            # the worker edits the file while verification runs
            (Path(tt["worktree"]) / "dag/Theorems/Thm_A_race.lean").write_text("changed\n")
            return real(base, new, records, out)
        self.ctl.verifier = verifier
        self.ctl.publish(t["task_id"])
        pushed = git(self.bare, "show", f"research/{t['task_id']}:dag/Theorems/Thm_A_race.lean")
        self.assertIn("theorem A.race", pushed)

    def test_ready_refuses_missing_import_then_finalize(self):
        t = self.ctl.task_create(self.desc())
        tt = self.ctl.st.task(t["task_id"])
        files = thm_files("A.dep")
        files["dag/Theorems/Thm_A_dep.lean"] = "import Theorems.Thm_X_missing\n" + \
            files["dag/Theorems/Thm_A_dep.lean"]
        self.write(tt, files)
        self.ctl.artifact_propose(t["task_id"], ["dag/Theorems/Thm_A_dep.lean"])
        with self.assertRaises(C.VerificationError):
            self.ctl.task_ready(t["task_id"])
        self.assertTrue(self.gh.prs[1]["isDraft"])

    def test_finalize_ready_with_summary_note(self):
        t = self.ctl.task_create(self.desc())
        tt = self.ctl.st.task(t["task_id"])
        self.write(tt, thm_files("A.part"))
        self.ctl.artifact_propose(t["task_id"], ["dag/Theorems/Thm_A_part.lean"])
        out = self.ctl.task_finalize(t["task_id"], "handoff", "Stated the key lemma.\n")
        self.assertFalse(self.gh.prs[1]["isDraft"])
        files = self.remote_files(f"research/{t['task_id']}")
        note = [f for f in files if f.startswith("dag/Notes/task-")]
        self.assertEqual(len(note), 1)
        text = git(self.bare, "show", f"research/{t['task_id']}:{note[0]}")
        self.assertIn(f"note:goal-{self.goal_fp}", text)
        self.assertIn("theorem:A.part", text)
        self.assertEqual(R.one_block(D.front_matter(text)[1], "summary")["outcome"], "handoff")
        self.assertEqual(self.ctl.st.task(t["task_id"])["state"], "ready")
        self.assertIn("statuses", out)
        self.assertIn("final", [R.one_block(c["body"], "checkpoint")["kind"]
                                for c in self.gh.comments(1)
                                if R.one_block(c["body"], "checkpoint")])

    def test_close(self):
        t = self.ctl.task_create(self.desc())
        self.ctl.task_finalize(t["task_id"], "inconclusive", "Dead end: ...", close=True)
        self.assertEqual(self.gh.prs[1]["state"], "CLOSED")
        self.assertEqual(self.ctl.st.task(t["task_id"])["state"], "closed")


class TestCheckpoints(Base):
    def test_every_checkpoint_is_a_comment_and_status_shows_latest(self):
        t = self.ctl.task_create(self.desc())
        tid = t["task_id"]
        self.ctl.progress_record(tid, {"summary": "First idea", "blockers": ["B1"]})
        self.clock.t += 600
        self.ctl.checkpoint_due()
        self.ctl.progress_record(tid, {"summary": "Second idea", "next_steps": ["N2"]})
        self.clock.t += 600
        self.ctl.checkpoint_due()
        self.clock.t += 600
        self.ctl.checkpoint_due()          # no new report: a heartbeat
        cs = self.gh.comments(1)
        cps = [R.one_block(c["body"], "checkpoint") for c in cs[1:]]
        self.assertEqual([c["sequence"] for c in cps], [1, 2, 3])
        self.assertEqual([c["kind"] for c in cps], ["progress", "progress", "heartbeat"])
        self.assertTrue(cps[2]["stale_report"])
        status = cs[0]["body"]
        self.assertIn(R.STATUS_MARKER, status)
        self.assertIn("checkpoint 3", status)
        self.assertNotIn("First idea", status)          # only the latest state
        self.assertIn("Second idea", status)
        self.assertIn("No fresh research report", status)

    def test_not_due_before_period(self):
        t = self.ctl.task_create(self.desc())
        self.clock.t += 100
        self.assertEqual(self.ctl.checkpoint_due(), [])
        self.ctl.hook("Stop", {"cwd": self.ctl.st.task(t["task_id"])["worktree"]})
        self.assertEqual(len(self.ctl.checkpoint_due()), 1)    # the hook made it due

    def test_outbox_retries_idempotently(self):
        t = self.ctl.task_create(self.desc())
        self.gh.fail = 2
        out = self.ctl.checkpoint(t["task_id"])
        self.assertGreaterEqual(out["outbox"]["failed"], 1)
        self.assertEqual(len(self.gh.comments(1)), 1)
        self.clock.t += 3600
        self.ctl.flush_outbox()
        self.ctl.flush_outbox()
        bodies = [c["body"] for c in self.gh.comments(1)]
        self.assertEqual(sum("sigaba-checkpoint " in b for b in bodies), 1)
        self.assertIn("checkpoint 1", bodies[0])

    def test_pause_resume(self):
        t = self.ctl.task_create(self.desc())
        self.ctl.task_pause(t["task_id"])
        self.assertEqual(self.ctl.st.task(t["task_id"])["state"], "paused")
        self.ctl.task_resume(t["task_id"])
        self.assertEqual(self.ctl.st.task(t["task_id"])["state"], "active")
        self.assertEqual(len(self.ctl.work_list()), 1)


class TestWorkerFiles(Base):
    """Workers write only in their worktree; the orchestrator's controller takes it in."""

    def test_worker_verify_touches_nothing_outside_the_worktree(self):
        t = self.ctl.task_create(self.desc())
        tt = self.ctl.st.task(t["task_id"])
        wt = Path(tt["worktree"])
        self.write(tt, thm_files("A.w"))
        head = git(wt, "rev-parse", "HEAD")
        ver = self.ctl.st.one("SELECT COUNT(*) AS n FROM verifications")["n"]
        worker = self.make()                   # a fresh controller, as in the worker's process
        worker.refresh_base = lambda: (_ for _ in ()).throw(AssertionError("no network"))
        worker.gh = None                       # no GitHub
        res = worker.worker_verify(wt / "dag")
        self.assertTrue(res["ok"])
        self.assertIn("dag/Theorems/Thm_A_w.lean", res["files"])
        self.assertTrue((wt / ".sigaba" / "verify").is_dir())
        self.assertEqual(git(wt, "rev-parse", "HEAD"), head)
        self.assertEqual(self.ctl.st.one("SELECT COUNT(*) AS n FROM verifications")["n"], ver)
        self.assertEqual(git(wt, "status", "--porcelain", "--", ".sigaba"), "")  # excluded

    def test_inbox_is_taken_in_and_published(self):
        self.ctl.run_start({})
        self.ctl.work_propose([self.desc()])
        d = self.ctl.run_next()["dispatch"]
        tid = d["task"]["task_id"]
        wt = Path(d["task"]["worktree"])
        self.write(self.ctl.st.task(tid), thm_files("A.inbox"))
        (wt / ".sigaba").mkdir(exist_ok=True)
        (wt / ".sigaba" / "progress.json").write_text(json.dumps(
            {"summary": "stated a lemma", "artifacts": ["dag/Theorems/Thm_A_inbox.lean"]}))
        (wt / ".sigaba" / "result.json").write_text(json.dumps(
            {"outcome": "done", "summary": "finished"}))
        out = self.ctl.episode_end(tid)        # the orchestrator, after the worker returned
        self.assertEqual(out["outcome"], "done")
        self.assertIn("dag/Theorems/Thm_A_inbox.lean",
                      self.remote_files(f"research/{tid}"))
        self.assertFalse((wt / ".sigaba" / "result.json").exists())   # taken once
        self.assertEqual(self.ctl.st.latest_progress(tid)["record"]["summary"], "stated a lemma")

    def test_watchdog_takes_in_a_result(self):
        self.ctl.run_start({})
        self.ctl.work_propose([self.desc()])
        d = self.ctl.run_next()["dispatch"]
        wt = Path(d["task"]["worktree"])
        (wt / ".sigaba").mkdir(exist_ok=True)
        (wt / ".sigaba" / "result.json").write_text(json.dumps({"outcome": "unresolved"}))
        self.ctl.watchdog_step()
        self.assertIsNone(self.ctl.live_episode(d["task"]["task_id"]))
        self.assertEqual(len(self.ctl.work_list()), 1)             # back in its queue


class TestScheduling(Base):
    def proposals(self):
        out = []
        for d in ("design", "cryptanalysis"):
            for o in ("expand", "deepen", "organize"):
                for i in range(2):
                    out.append(self.desc(domain=d, operation=o, title=f"{d} {o} {i}",
                                         scope=f"scope {d} {o} {i}"))
        return out

    def test_round_robin_and_persistence(self):
        self.ctl.run_start({"max_proposals": 100})
        self.assertEqual(len(self.ctl.work_propose(self.proposals())["enqueued"]), 12)
        self.assertEqual(self.ctl.work_propose([self.proposals()[0]])["rejected"][0]["reason"],
                         "duplicate")
        order = []
        for i in range(6):
            it = self.ctl.next_item(["design", "cryptanalysis"])
            order.append(it["pair"])
            if i == 2:      # a restart: a new controller on the same state continues the cycle
                self.ctl = self.make()
        self.assertEqual(order, [f"{d}/{o}" for d, o in R.PAIRS])
        self.assertEqual(self.ctl.next_item(["design"])["pair"], "design/deepen")

    def test_dispatch_creates_task_pr_and_requeues(self):
        self.ctl.run_start({"max_parallel_workers": 1})
        self.ctl.work_propose([self.desc(title="one", scope="s1"),
                               self.desc(title="two", scope="s2")])
        d = self.ctl.run_next()["dispatch"]
        self.assertIsNotNone(d)
        self.assertEqual(len(self.gh.prs), 1)
        prompt = Path(d["prompt_file"]).read_text()
        self.assertIn("worker-verify", prompt)
        self.assertNotIn("episode end", prompt)            # workers never call the controller
        self.assertEqual(self.ctl.run_next()["dispatch"], None)   # one slot
        self.clock.t += 60
        self.ctl.episode_end(d["episode_id"], "unresolved")
        d2 = self.ctl.run_next()["dispatch"]
        self.assertNotEqual(d2["task"]["task_id"], d["task"]["task_id"])
        self.ctl.episode_end(d2["episode_id"], "unresolved")
        d3 = self.ctl.run_next()["dispatch"]
        self.assertEqual(d3["task"]["task_id"], d["task"]["task_id"])   # back from the tail
        self.assertEqual(len(self.gh.prs), 2)                           # same PR reused

    def test_budget_and_stop(self):
        self.ctl.run_start({"max_run_seconds": 100, "episode_seconds": 1800})
        self.ctl.work_propose([self.desc()])
        d = self.ctl.run_next()["dispatch"]
        self.assertEqual(d["budget_seconds"], 100)
        self.clock.t += 101
        self.ctl.watchdog_step()        # interactive worker past its deadline; run spent
        self.assertIsNone(self.ctl.active_run())

    def test_derive_open_leaves(self):
        # an accepted sketch of A.main through two open leaves
        self.ctl.run_start({})
        self.ctl.refresh_base()
        orig = D.read_records

        def fake_records(d):
            return {"e1": [
                {"kind": "theorem", "path": "dag/Theorems/Thm_A_main.lean", "name": "A.main",
                 "env": "e1", "status": "OK", "id": "a" * 64, "time": "1"},
                {"kind": "definition", "path": "dag/Definitions/Def_Prim.lean", "name": "Prim",
                 "env": "e1", "status": "OK", "id": "b" * 64, "time": "1"},
                {"kind": "solution", "path": "dag/Solutions/A_main/Sub_s.lean", "name": "A.main",
                 "env": "e1", "status": "SKETCH_ACCEPTED", "hash": "c" * 64, "theorem": "A.main",
                 "proof_type": "prove", "uses": ["A.l1", "A.l2"], "std": {}, "time": "2"}]}
        D.read_records = fake_records
        try:
            st = D.status(D.Dag(self.ctl.base), fake_records(None), ENV)
            leaves = D.open_leaves(st, "A.main")
            out = self.ctl.work_derive(self.goal_fp)
            again = self.ctl.work_derive(self.goal_fp)
        finally:
            D.read_records = orig
        self.assertEqual(sorted(out["enqueued"]), leaves)
        self.assertEqual(again["enqueued"], [])

    def test_plans_alternatives_cycles(self):
        a, b, c = R.new_uuid(), R.new_uuid(), R.new_uuid()
        p1 = {"plan_id": "1" + R.new_uuid()[1:], "goal": self.goal_fp,
              "target": {"kind": "goal", "id": self.goal_fp}, "required": [a, b],
              "rationale": "route A"}
        p2 = {**p1, "plan_id": "2" + R.new_uuid()[1:], "required": [c, b], "rationale": "route B"}
        p3 = {**p1, "plan_id": "3" + R.new_uuid()[1:], "target": {"kind": "task", "id": a},
              "required": [c]}
        p4 = {**p1, "plan_id": "4" + R.new_uuid()[1:], "target": {"kind": "task", "id": c},
              "required": [a]}
        g = C.build_graph([p4, p3, p2, p1], {a, b})
        self.assertEqual(sorted(g["alternatives"][self.goal_fp]),
                         sorted([p1["plan_id"], p2["plan_id"]]))
        self.assertEqual(g["dropped"], [p4["plan_id"]])
        self.assertEqual(g["unresolved"][p2["plan_id"]], [c])
        # posting through the controller
        t = self.ctl.task_create(self.desc())
        self.ctl.plan_add(t["task_id"], {k: v for k, v in p1.items() if k != "goal"})
        self.assertTrue(any("sigaba-plan-v1" in x["body"] for x in self.gh.comments(1)))
        with self.assertRaises(C.ProtocolError):
            self.ctl.plan_add(t["task_id"], {**p1, "plan_id": R.new_uuid(), "required": [a, a]})

    def test_sync_reads_task_prs(self):
        t = self.ctl.task_create(self.desc())
        self.ctl.progress_record(t["task_id"], {"summary": "s"})
        self.ctl.checkpoint(t["task_id"])
        out = self.ctl.sync()
        self.assertEqual(out["tasks"], 1)
        rt = self.ctl.remote_tasks()[0]
        self.assertEqual(rt["descriptor"]["task_id"], t["task_id"])
        self.assertEqual(rt["latest_checkpoint"]["sequence"], 1)
        self.gh.prs[1]["state"] = "MERGED"
        self.gh.prs[1]["mergedAt"] = "2026-01-01"
        self.ctl.sync()
        self.assertEqual(self.ctl.st.task(t["task_id"])["state"], "merged")


class TestExistingGoals(Base):
    def test_prepare_reuses_or_refuses(self):
        body = {k: v for k, v in GOAL.items() if k != "schema"}
        out = self.ctl.goal_prepare(dict(body, title="another title"), self.tmp / "b0")
        self.assertEqual(out["existing"]["fingerprint"], self.goal_fp)   # same goal: reused
        self.assertFalse((self.tmp / "b0").exists())
        changed = dict(body, policy={"forbidden_routes": [], "intent": "anything"})
        with self.assertRaises(C.ProtocolError) as e:                     # same nodes
            self.ctl.goal_prepare(changed, self.tmp / "b1")
        self.assertIn(self.goal_fp, str(e.exception))
        v2 = self.ctl.goal_prepare(dict(changed, parent=self.goal_fp), self.tmp / "b2")
        self.assertEqual(v2["related_goals"], [])
        other = self.ctl.goal_prepare(changed, self.tmp / "b3", distinct="the user wants both")
        self.assertEqual(other["related_goals"][0]["fingerprint"], self.goal_fp)
        self.assertTrue((self.tmp / "b3" / "distinct.md").exists())

    def test_pending_registration(self):
        g = dict(GOAL, targets=[], definitions=["definition:Prim"], objective={"kind": "explore"},
                 parent=self.goal_fp)
        path, text = R.goal_note(g)
        sha = C.git_blob_sha(text.encode())
        self.gh.prs[9] = {"number": 9, "url": "u", "state": "OPEN", "isDraft": False,
                          "headRefName": "register/x", "headRefOid": "f" * 40,
                          "author": {"login": "bob"}, "title": "Register", "body": "",
                          "mergedAt": None}
        self.gh.files[9] = [{"filename": path, "status": "added", "sha": sha}]
        self.gh.blobs[sha] = text.encode()
        ov = self.ctl.goals_overview()
        self.assertEqual(ov["pending"][0]["pending_pr"], 9)
        out = self.ctl.goal_prepare({k: v for k, v in g.items() if k != "schema"},
                                    self.tmp / "b4")
        self.assertEqual(out["existing"]["pending_pr"], 9)


class TestAuthoring(Base):
    def test_digest_approval_register(self):
        d = self.tmp / "bundle"
        g = dict(GOAL, objective={"kind": "prove"}, parent=self.goal_fp)   # a new version
        out = self.ctl.goal_prepare({k: v for k, v in g.items() if k != "schema"}, d)
        digest = out["digest"]
        with self.assertRaises(C.ProtocolError):       # no terminal: an agent cannot approve
            self.ctl.goal_approve(d, digest)
        with self.assertRaises(C.ProtocolError):       # not approved
            self.ctl.goal_register(d)
        rv = self.ctl.goal_review(d)
        self.assertTrue(rv["ok"])
        self.assertTrue((d / "review.md").exists())
        # the user approves at a terminal (simulated), then a change voids it
        self.ctl.st.x("INSERT INTO approvals(digest,dir,time,who) VALUES(?,?,?,?)", digest,
                      str(d.resolve()), 0, "u")
        (d / "dag/Notes/extra.md").write_text("---\ntitle: x\n---\n")
        with self.assertRaises(C.ProtocolError):
            self.ctl.goal_register(d)
        (d / "dag/Notes/extra.md").unlink()
        r = self.ctl.goal_register(d)
        self.assertFalse(self.gh.prs[r["pr"]]["isDraft"])
        self.assertEqual(r["files"], [out["goal_note"]])
        again = self.ctl.goal_register(d)
        self.assertEqual(again["pr"], r["pr"])


class TestMisc(Base):
    def test_hooks_install_and_bind(self):
        t = self.ctl.task_create(self.desc())
        wt = Path(self.ctl.st.task(t["task_id"])["worktree"])
        f = wt / ".claude" / "settings.local.json"
        f.parent.mkdir(parents=True)
        f.write_text(json.dumps({"hooks": {"Stop": [{"hooks": [{"type": "command",
                                                                "command": "echo mine"}]}]}}))
        self.ctl.hooks_install("claude", wt)
        self.ctl.hooks_install("claude", wt)
        cfg = json.loads(f.read_text())
        cmds = [h["command"] for g in cfg["hooks"]["Stop"] for h in g["hooks"]]
        self.assertEqual(len(cmds), 2)
        self.assertIn("echo mine", cmds)
        self.ctl.hooks_install("codex", wt)
        self.assertTrue((wt / ".codex" / "hooks.json").exists())
        self.assertEqual(git(wt, "status", "--porcelain"), "")       # excluded from Git
        self.ctl.hook("PostToolUse", {"cwd": str(wt / "dag"), "session_id": "s"})
        ev = self.ctl.st.one("SELECT * FROM events WHERE kind='hook:PostToolUse'")
        self.assertEqual(ev["task_id"], t["task_id"])
        self.ctl.hook("Stop", {"cwd": "/"})          # unrelated session: recorded, no task

    def test_pr_fetch_pins_blobs(self):
        t = self.ctl.task_create(self.desc())
        data = b"theorem X : True := by sorry\n"
        sha = C.git_blob_sha(data)
        self.gh.prs[7] = {"number": 7, "url": "u", "state": "OPEN", "isDraft": True,
                          "headRefName": "x", "headRefOid": "f" * 40, "author": {"login": "bob"},
                          "title": "t", "body": "", "mergedAt": None}
        self.gh.files[7] = [{"filename": "dag/Theorems/Thm_X.lean", "status": "added",
                             "sha": sha},
                            {"filename": ".github/workflows/x.yml", "status": "added",
                             "sha": "0" * 40}]
        self.gh.blobs[sha] = data
        out = self.ctl.pr_fetch(t["task_id"], 7)
        self.assertEqual(out["paths"], ["dag/Theorems/Thm_X.lean"])
        self.gh.blobs[sha] = b"tampered"
        with self.assertRaises(C.ProtocolError):
            self.ctl.pr_fetch(t["task_id"], 7)

    def test_cache(self):
        self.ctl.refresh_base()
        self.ctl.cache_record("A.main", "timeout", "tried induction")
        out = self.ctl.cache_lookup("A.main")
        self.assertEqual(out["attempts"][0]["outcome"], "timeout")

    def test_skills_in_sync(self):
        self.assertEqual(C.skills_diff(), [])

    def test_plugin_manifests(self):
        """The plugin for Claude Code and Codex: manifests agree, the launcher is executable, and
        the shipped skills point at the installed core, never at core-relative paths."""
        cc = json.loads((REPO / "plugin/.claude-plugin/plugin.json").read_text())
        cx = json.loads((REPO / "plugin/.codex-plugin/plugin.json").read_text())
        mk = json.loads((REPO / ".claude-plugin/marketplace.json").read_text())
        cm = json.loads((REPO / ".agents/plugins/marketplace.json").read_text())
        self.assertEqual(cc["name"], cx["name"])
        self.assertEqual(cc["version"], cx["version"])
        self.assertEqual(mk["plugins"][0]["version"], cc["version"])
        self.assertEqual(mk["plugins"][0]["source"], "./plugin")
        self.assertEqual(cm["plugins"][0]["source"], {"source": "local", "path": "./plugin"})
        self.assertEqual(cx["skills"], "./skills/")
        self.assertTrue(os.access(REPO / "plugin/scripts/sigaba", os.X_OK))
        self.assertIn("url", json.loads((REPO / "plugin/core.json").read_text()))
        for p in (REPO / "plugin/skills").rglob("*.md"):
            text = p.read_text()
            self.assertNotIn("python3 python/", text, p)
            self.assertNotIn("](../../../", text, p)
            self.assertNotIn("plugin:install", text, p)
        self.assertIn("scripts/sigaba\" install",
                      (REPO / "plugin/skills/sigaba-research/SKILL.md").read_text())

    def test_gate_skips_drafts(self):
        text = (REPO / "templates/dag/.github/workflows/gate.yml").read_text()
        self.assertIn("ready_for_review", text)
        self.assertIn("converted_to_draft", text)
        self.assertIn("!github.event.pull_request.draft", text)
        self.assertIn("needs.precheck.result != 'skipped'", text)
        self.assertIn("dequeuePullRequest", text)
        self.assertRegex(text, r"isDraft,headRefOid")

    def test_cli_parses(self):
        import sigaba_research as S
        p = S.parser()
        for argv in (["doctor"], ["task", "create", "--file", "x"], ["run", "start", "--backend",
                     "codex", "--domains", "design"], ["episode", "end", "x", "--outcome",
                     "done"], ["hooks", "install", "--provider", "claude"], ["skills", "check"]):
            p.parse_args(argv)

    def test_cli_end_to_end_errors(self):
        import contextlib
        import io
        import sigaba_research as S
        with contextlib.redirect_stdout(io.StringIO()):
            code = S.main(["--home", str(self.tmp / "h2"), "--repo", "o/dag", "task", "show",
                           "nope"])
        self.assertEqual(code, 2)


if __name__ == "__main__":
    unittest.main()
