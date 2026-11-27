"""The DAG's tools that run no Lean (`dag.py`, `dag_tools.py`): hashes, the precheck, decisions,
records and statuses, the index, `init`, and the import of the retired server's database.

    python3 -m unittest discover -s python/tests -p 'test_dag_tools.py' -v
"""

from __future__ import annotations

import json
import shutil
import sqlite3
import tempfile
import unittest
from pathlib import Path

import common  # noqa: F401  (puts python/ on the path)
import dag as D
import dag_tools as T

ENV = {"id": "e1", "lean": "leanprover/lean4:v4.36.0-rc2", "core": "v1",
       "core_url": "https://github.com/MachinaIO/Sigaba-Neo", "state": "default", "std": "v1",
       "image": "ghcr.io/x/sigaba-neo-env@sha256:" + "0" * 64}


def write(root: Path, files: dict[str, str]) -> None:
    for rel, text in files.items():
        p = root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)


def thm(name: str, stmt: str = "True", imports: str = "") -> dict[str, str]:
    s = D.slug(name)
    return {f"dag/Theorems/Thm_{s}.lean": f"{imports}\n\ntheorem {name} : {stmt} := by sorry\n",
            f"dag/Theorems/Thm_{s}.json": json.dumps({"name": name, "title": name})}


def sol(name: str, sid: str, uses: list[str] = (), proof_type: str = "prove") -> dict[str, str]:
    s = D.slug(name)
    imports = "".join(f"import Theorems.Thm_{D.slug(u)}\n" for u in uses)
    return {f"dag/Solutions/{s}/Sub_{sid}.lean": f"{imports}\ntheorem solution : True := trivial\n",
            f"dag/Solutions/{s}/Sub_{sid}.json": json.dumps({"theorem": name,
                                                             "proof_type": proof_type})}


def rec(kind: str, path: str, name: str, env: str = "e1", **kw) -> dict:
    return {"kind": kind, "path": path, "name": name, "env": env,
            "status": kw.pop("status", "OK" if kind != "solution" else "ACCEPTED"), **kw}


class Tmp(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="sigaba-neo-dag-"))

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)


class HashTest(Tmp):
    def test_strip_comments(self):
        text = 'def a := "-- not a comment /- nor this -/" -- gone\n/- gone /- nested -/ still -/\n' \
               "def c := '-'\n/-- docstring -/\ndef d := 1\n"
        out = D.strip_comments(text)
        self.assertIn('"-- not a comment /- nor this -/"', out)
        self.assertNotIn("gone", out)
        self.assertNotIn("nested", out)
        self.assertNotIn("docstring", out)
        self.assertIn("def c := '-'", out)

    def test_imports_ignore_comments(self):
        text = ("import Mathlib -- arithmetic lemmas\n/- import Evil -/\n"
                "import Definitions.Def_Two /- two -/\n\ntheorem x : True := trivial\n")
        self.assertEqual(D.imports_of(text), ["Mathlib", "Definitions.Def_Two"])

    def test_split_header(self):
        """The body starts right after the header, whatever its form."""
        for text in ("public import Mathlib\nimport Definitions.Def_Two\ntheorem x : True := trivial\n",
                     "import Mathlib /- arithmetic\n  lemmas -/\nimport Definitions.Def_Two\n"
                     "theorem x : True := trivial\n",
                     "-- header\nimport Mathlib\nimport Definitions.Def_Two -- two\n\n"
                     "theorem x : True := trivial\n"):
            with self.subTest(text=text):
                imports, rest = D.split_header(text)
                self.assertEqual(imports, ["Mathlib", "Definitions.Def_Two"])
                self.assertEqual(D.strip_comments(rest).strip(), "theorem x : True := trivial")

    def test_solution_hash(self):
        a = "import X\n\ntheorem solution : True := by\n  trivial\n"
        b = "import X   \n-- a comment\n\n\ntheorem solution : True := by\n  trivial -- done\n"
        c = "import X\n\ntheorem solution : True := by\n    trivial\n"
        self.assertEqual(D.solution_hash(a), D.solution_hash(b))
        self.assertNotEqual(D.solution_hash(a), D.solution_hash(c))   # indentation is kept

    def test_std_manifest_is_a_merkle_hash(self):
        core = self.tmp / "core"
        write(core, {"SigabaNeoStd.lean": "import SigabaNeoStd.A\nimport SigabaNeoStd.C\n",
                     "SigabaNeoStd/A.lean": "import SigabaNeoStd.B\ndef a := 1\n",
                     "SigabaNeoStd/B.lean": "import Mathlib\ndef b := 1\n",
                     "SigabaNeoStd/C.lean": "def c := 1\n"})
        before = D.std_manifest(core)
        self.assertEqual(sorted(before), ["SigabaNeoStd", "SigabaNeoStd.A", "SigabaNeoStd.B",
                                          "SigabaNeoStd.C"])
        write(core, {"SigabaNeoStd/B.lean": "import Mathlib\n-- a comment only\ndef b := 1\n"})
        self.assertEqual(D.std_manifest(core), before)
        write(core, {"SigabaNeoStd/B.lean": "import Mathlib\ndef b := 2\n"})
        after = D.std_manifest(core)
        self.assertNotEqual(after["SigabaNeoStd.B"], before["SigabaNeoStd.B"])
        self.assertNotEqual(after["SigabaNeoStd.A"], before["SigabaNeoStd.A"])   # imports B
        self.assertEqual(after["SigabaNeoStd.C"], before["SigabaNeoStd.C"])
        self.assertEqual(D.std_closure(["SigabaNeoStd.A", "Mathlib"], core),
                         ["SigabaNeoStd.A", "SigabaNeoStd.B"])

    def test_std_manifest_of_the_core(self):
        m = D.std_manifest()
        self.assertIn("SigabaNeoStd", m)
        self.assertGreater(len(m), 100)

    def test_semantic_id(self):
        data = {"kind": "theorem", "root": {"form": "theorem-node 0\nC Foo\nstatement 0",
                                            "refs": ["Foo"]},
                "units": {"Foo": {"form": "def Foo", "refs": ["Bar", "block:Nat"]},
                          "Bar": {"form": "def Bar", "refs": ["block:Nat"]},
                          "block:Nat": {"form": "block Nat", "refs": []}}}
        a = D.semantic_id(data)
        reordered = json.loads(json.dumps(data))
        reordered["units"] = dict(reversed(list(reordered["units"].items())))
        self.assertEqual(D.semantic_id(reordered), a)
        changed = json.loads(json.dumps(data))
        changed["units"]["block:Nat"]["form"] = "block Nat'"
        self.assertNotEqual(D.semantic_id(changed), a)        # a leaf, two levels down
        cyclic = json.loads(json.dumps(data))
        cyclic["units"]["block:Nat"]["refs"] = ["Foo"]
        with self.assertRaises(ValueError):
            D.semantic_id(cyclic)


class NotesTest(unittest.TestCase):
    def test_front_matter(self):
        meta, body = D.front_matter("---\ntitle: A plan\nrefs: [theorem:A.b, note:x-y]\n"
                                    "tags: [strategy]\n---\nBody\n")
        self.assertEqual(meta, {"title": "A plan", "refs": ["theorem:A.b", "note:x-y"],
                                "tags": ["strategy"]})
        self.assertEqual(body, "Body\n")
        for bad in ("no front matter", "---\ntitle: x\n", "---\nTitle x\n---\n"):
            with self.assertRaises(ValueError):
                D.front_matter(bad)
        self.assertEqual(D.validate({"title": "x", "evil": 1}, D.schema("note")),
                         ["$: unknown key `evil`"])


class PrecheckTest(Tmp):
    def setUp(self):
        super().setUp()
        self.base = self.tmp / "base"
        write(self.base, {
            "meta/trusted.json": json.dumps({"mode": "allowlist", "accept": ["alice", "bob"],
                                             "automerge": ["alice"]}),
            "env/environments.json": json.dumps({"environments": [ENV]}),
            "dag/Definitions/Def_Two.lean": "def two := 2\n",
            "dag/Definitions/Def_Two.json": json.dumps({"name": "Two", "title": "two"}),
            **thm("A.b", "two = 2", "import Definitions.Def_Two")})
        self.dag = D.Dag(self.base)

    def run_pre(self, files: dict[str, str], author: str = "alice",
                status: dict[str, str] | None = None) -> dict:
        content = self.tmp / "fetched"
        shutil.rmtree(content, ignore_errors=True)
        write(content, files)
        rows = [{"filename": f, "status": (status or {}).get(f, "added"), "type": "blob",
                 "mode": "100644", "size": len(t.encode())} for f, t in files.items()]
        return T.precheck(self.dag, rows, content, author)

    def test_ok(self):
        files = {**thm("A.c", "two = 2", "import Definitions.Def_Two"), **sol("A.b", "x1"),
                 **sol("A.c", "x2", ["A.b"]),
                 "dag/Notes/plan.md": "---\ntitle: plan\nrefs: [theorem:A.b, theorem:A.c, "
                                      "definition:Two, solution:A_b/Sub_x1]\n---\ntext\n"}
        r = self.run_pre(files)
        self.assertEqual(r["problems"], [])
        self.assertTrue(r["ok"] and r["automerge"])
        self.assertFalse(self.run_pre(files, author="bob")["automerge"])

    def test_not_accepted(self):
        r = self.run_pre(sol("A.b", "x1"), author="mallory")
        self.assertFalse(r["accepted"])
        d = T.decide(r, None, "mallory", "pull_request_target")
        self.assertEqual((d["conclusion"], d["labels"]), ("failure", ["not-accepted"]))
        self.assertNotIn("close", d)                      # a decision never closes a PR

    def test_collaborators_mode(self):
        """`collaborators`: those with write access (GitHub's admin, maintain or write) are
        accepted and merged automatically; those listed in `accept` too; nobody else, and an
        unknown permission accepts nobody unlisted."""
        (self.base / "meta/trusted.json").write_text(json.dumps(
            {"mode": "collaborators", "accept": ["bot[bot]"], "automerge": []}))
        self.dag = D.Dag(self.base)
        files = sol("A.b", "x1")
        content = self.tmp / "fetched"
        write(content, files)
        rows = [{"filename": f, "status": "added", "type": "blob", "mode": "100644",
                 "size": len(x.encode())} for f, x in files.items()]
        for perm in ("admin", "maintain", "write"):
            r = T.precheck(self.dag, rows, content, "carol", permission=perm)
            self.assertTrue(r["accepted"] and r["ok"] and r["automerge"], perm)
        for perm in ("read", "triage", "none", None):
            r = T.precheck(self.dag, rows, content, "mallory", permission=perm)
            self.assertFalse(r["accepted"], perm)
            self.assertIn("no write access", r["problems"][0])
        r = T.precheck(self.dag, rows, content, "bot[bot]", permission="none")
        self.assertTrue(r["accepted"] and r["ok"])
        self.assertFalse(r["automerge"])
        self.assertEqual(D.validate({"mode": "collaborators", "accept": [], "automerge": []},
                                    D.schema("trusted")), [])
        # The permission matters only in `collaborators` mode.
        (self.base / "meta/trusted.json").write_text(json.dumps(
            {"mode": "allowlist", "accept": [], "automerge": []}))
        self.dag = D.Dag(self.base)
        self.assertFalse(T.precheck(self.dag, rows, content, "carol", permission="admin")
                         ["accepted"])

    def test_commented_import(self):
        """A trailing comment on an import line is not an import."""
        files = thm("A.c", "two = 2", "import Definitions.Def_Two -- the number two")
        self.assertEqual(self.run_pre(files)["problems"], [])

    def test_rejections(self):
        cases = {
            "modified": ({"dag/Definitions/Def_Two.lean": "def two := 3\n"},
                         {"dag/Definitions/Def_Two.lean": "modified"}, "may only add files"),
            "workflow": ({".github/workflows/gate.yml": "on: push"}, None, "not a path"),
            "meta": ({"meta/trusted.json": "{}"}, None, "not a path"),
            "no json": ({"dag/Theorems/Thm_X.lean": "theorem X : True := by sorry\n"}, None,
                        "metadata file (.json) is missing"),
            "json name": ({**thm("X.y"), "dag/Theorems/Thm_X_y.json":
                           json.dumps({"name": "X.z", "title": "t"})}, None, "has the slug"),
            "json schema": ({**thm("X.y"), "dag/Theorems/Thm_X_y.json":
                             json.dumps({"name": "X.y", "title": "t", "evil": True})}, None,
                            "unknown key"),
            "not sorry": ({"dag/Theorems/Thm_X.lean": "theorem X : True := trivial\n",
                           "dag/Theorems/Thm_X.json": json.dumps({"name": "X", "title": "x"})},
                          None, "must end with"),
            "orphan solution": (sol("Nope.x", "a"), None, "no theorem with the slug"),
            "import": ({**thm("X.y", imports="import SigabaNeo.Platform")}, None, "not allowed"),
            "import solutions": ({**thm("X.y", imports="import Solutions.A_b.Sub_x")}, None,
                                 "not allowed"),
            "missing import": ({**thm("X.y", imports="import Definitions.Def_Nope")}, None,
                               "no such node"),
            "disproof imports": (sol("A.b", "d", ["A.b"], "disprove"), None,
                                 "a disproof may not import theorems"),
            "note refs": ({"dag/Notes/n.md": "---\ntitle: t\nrefs: [theorem:Nope]\n---\n"}, None,
                          "does not exist"),
            "note format": ({"dag/Notes/n.md": "no front matter"}, None, "front matter"),
            "bad note name": ({"dag/Notes/Bad_Name.md": "---\ntitle: t\n---\n"}, None, "not a path"),
        }
        for label, (files, status, expect) in cases.items():
            with self.subTest(label):
                r = self.run_pre(files, status=status)
                self.assertFalse(r["ok"], label)
                self.assertTrue(any(expect in p for p in r["problems"]), (label, r["problems"]))

    def test_size(self):
        big = "-- " + "x" * (D.LIMITS["file_bytes"] + 10) + "\n"
        r = self.run_pre({"dag/Definitions/Def_Big.lean": big,
                          "dag/Definitions/Def_Big.json": json.dumps({"name": "Big", "title": "b"})})
        self.assertTrue(any("larger than" in p for p in r["problems"]))


class DecideTest(unittest.TestCase):
    ADDED = ["dag/Theorems/Thm_A.json", "dag/Theorems/Thm_A.lean", "dag/Notes/n.md"]
    PRE = {"ok": True, "accepted": True, "automerge": True, "problems": [], "added": ADDED}
    REV = "a" * 40

    def result(self, status: str = "OK", **kw) -> dict:
        items = [{"path": "dag/Theorems/Thm_A.lean", "kind": "theorem", "name": "A",
                  "status": status, **({"message": "x"} if status != "OK" else {})},
                 {"path": "dag/Notes/n.md", "kind": "note", "name": "n", "status": "OK"}]
        return {"ok": status in ("OK", "ACCEPTED"), "env": "e1", "std": "v1",
                "revision": self.REV, "items": items, **kw}

    def decide(self, result, pre=None, author="alice", event="pull_request_target", code=None):
        ok = result is not None and result.get("ok")
        return T.decide(pre or self.PRE, result, author, event, "e1", self.REV,
                        (0 if ok else 1) if code is None else code)

    def test_decisions(self):
        d = self.decide(self.result("OK"))
        self.assertEqual((d["conclusion"], d["automerge"], d["labels"]), ("success", True, []))
        d = self.decide(self.result("OK"), pre={**self.PRE, "automerge": False}, author="bob")
        self.assertEqual((d["conclusion"], d["automerge"], d["labels"]),
                         ("success", False, ["needs-maintainer"]))
        d = self.decide(self.result("CE"))
        self.assertEqual((d["conclusion"], d["automerge"]), ("failure", False))
        self.assertIn("`CE`", d["comment"])
        d = self.decide(None, pre={**self.PRE, "ok": False, "problems": ["bad"]}, event="merge_group")
        self.assertEqual(d["conclusion"], "failure")

    def test_unusable_results(self):
        """A result counts only if it is about this commit and environment, covers exactly the
        added nodes, agrees with itself, and came from a verifier that exited normally."""
        r = self.result()
        cases = {
            "missing item": {**r, "items": r["items"][:1]},
            "extra item": {**r, "items": r["items"] + [{**r["items"][0], "path": "dag/X.lean"}]},
            "repeated item": {**r, "items": r["items"] + r["items"][:1]},
            "empty": {**r, "items": []},
            "other env": {**r, "env": "e2"},
            "other revision": {**r, "revision": "b" * 40},
            "ok contradicts": {**self.result("CE"), "ok": True},
        }
        pre = {**self.PRE, "revision": "d" * 40}           # the precheck read another commit
        d = T.decide(pre, r, "alice", "pull_request_target", "e1", self.REV, 0)
        self.assertIn("the precheck read", d["comment"])
        d = T.decide(self.PRE, r, "alice", "pull_request_target", "e1", None, 0)
        self.assertIn("no commit to bind", d["comment"])
        for label, res in cases.items():
            with self.subTest(label):
                d = T.decide(self.PRE, res, "alice", "pull_request_target", "e1", self.REV, 0)
                self.assertEqual(d["conclusion"], "failure", d["comment"])
                self.assertIn("not usable", d["comment"])
        for code in (None, 2, 137):
            with self.subTest(exit=code):
                d = T.decide(self.PRE, r, "alice", "pull_request_target", "e1", self.REV, code)
                self.assertEqual(d["conclusion"], "failure")
        d = T.decide(self.PRE, self.result("CE"), "alice", "pull_request_target", "e1", self.REV, 0)
        self.assertIn("exit status contradicts", d["comment"])

    def test_result_schema(self):
        tmp = Path(tempfile.mkdtemp())
        try:
            good = self.result("OK")
            (tmp / "r.json").write_text(json.dumps(good))
            self.assertEqual(T.check_result(tmp / "r.json"), good)
            for bad in ({**good, "items": [{**good["items"][0], "exec": "rm -rf /"}]},
                        {**good, "env": "../../etc/x"}, {**good, "items": []}):
                (tmp / "r.json").write_text(json.dumps(bad))
                with self.assertRaises(SystemExit):
                    T.check_result(tmp / "r.json")
        finally:
            shutil.rmtree(tmp)


class StatusTest(Tmp):
    def setUp(self):
        super().setUp()
        self.root = self.tmp / "dag"
        write(self.root, {
            "env/environments.json": json.dumps({"environments": [
                ENV, {**ENV, "id": "e2", "state": "active", "std": "v1"}]}),
            "env/std.json": json.dumps({"releases": {"v1": {"SigabaNeoStd.A": "a" * 64}}}),
            **thm("A"), **thm("B"), **thm("C"), **thm("D"), **thm("E"), **thm("F"),
            **sol("A", "1", ["B"]), **sol("B", "1"), **sol("C", "1", ["D"]), **sol("D", "1", ["C"]),
            **sol("E", "1", proof_type="disprove"), **sol("F", "1")})
        self.dag = D.Dag(self.root)

    def records(self) -> dict:
        p = lambda t: f"dag/Solutions/{t}/Sub_1.lean"  # noqa: E731
        e1 = [rec("theorem", f"dag/Theorems/Thm_{t}.lean", t, id=str(i) * 64)
              for i, t in enumerate("ABCDEF")]
        e1 += [rec("solution", p("A"), "A", theorem="A", uses=["B"], status="SKETCH_ACCEPTED",
                   std={"SigabaNeoStd.A": "a" * 64}),
               rec("solution", p("B"), "B", theorem="B", uses=[]),
               rec("solution", p("C"), "C", theorem="C", uses=["D"], status="SKETCH_ACCEPTED"),
               rec("solution", p("D"), "D", theorem="D", uses=["C"], status="SKETCH_ACCEPTED"),
               rec("solution", p("E"), "E", theorem="E", proof_type="disprove"),
               rec("solution", p("F"), "F", theorem="F", std={"SigabaNeoStd.A": "b" * 64})]
        e2 = [rec("theorem", "dag/Theorems/Thm_B.lean", "B", env="e2", id="9" * 64,
                  author="reverify"),
              rec("solution", p("B"), "B", env="e2", theorem="B", author="reverify")]
        return {"e1": e1, "e2": e2}

    def test_status(self):
        st = D.status(self.dag, self.records(), D.Dag(self.root).environment("e1"))
        s = {n: t["status"] for n, t in st.theorems.items()}
        self.assertEqual(s, {"A": "Proved", "B": "Proved", "C": "Open", "D": "Open",
                             "E": "Disproved", "F": "Open"})
        self.assertEqual(st.stale, ["dag/Solutions/F/Sub_1.lean"])       # other std hashes
        self.assertEqual(D.open_leaves(st, "C"), [])

    def test_drift_and_port(self):
        st = D.status(self.dag, self.records(), self.dag.environment("e2"))
        self.assertEqual(st.theorems["B"]["status"], "Drifted")        # another semantic ID
        self.assertIn("dag/Solutions/A/Sub_1.lean", st.needs_port)
        self.assertEqual(T.reverify_plan(self.dag, self.records(), "e2")[:1],
                         ["dag/Theorems/Thm_A.lean"])

    def test_drift_baseline_is_the_introduction(self):
        """The ID a theorem was introduced with is the baseline, whatever the environments' names:
        a later environment that sorts first does not make the original drift."""
        recs = self.records()
        early = rec("theorem", "dag/Theorems/Thm_B.lean", "B", env="e1", id="1" * 64,
                    time="2026-01-01T00:00:00Z", author="alice")
        late = rec("theorem", "dag/Theorems/Thm_B.lean", "B", env="a0", id="9" * 64,
                   time="2026-06-01T00:00:00Z", author="reverify")
        recs = {"a0": [late], "e1": [early] + [r for r in recs["e1"] if r["name"] != "B"]}
        st = D.status(self.dag, recs, self.dag.environment("e1"))
        self.assertFalse(st.theorems["B"]["drifted"])

    def test_drift_baseline_tie(self):
        """Two introductions at the same time with other IDs: no baseline, so the theorem is
        drifted (no solution counts for it) rather than whichever file is read first."""
        recs = self.records()
        t = "2026-01-01T00:00:00Z"
        recs["e1"] = [r for r in recs["e1"] if r["name"] != "B"] + [
            rec("theorem", "dag/Theorems/Thm_B.lean", "B", id="1" * 64, time=t, author="a")]
        recs["e2"] = [rec("theorem", "dag/Theorems/Thm_B.lean", "B", env="e2", id="9" * 64,
                          time=t, author="b")]
        for env in ("e1", "e2"):
            st = D.status(self.dag, recs, self.dag.environment(env))
            self.assertEqual(st.theorems["B"]["status"], "Drifted", env)

    def test_missing_std_release(self):
        """Without the environment's std release, a proof that used std does not count."""
        write(self.root, {"env/std.json": json.dumps({"releases": {}})})
        st = D.status(D.Dag(self.root), self.records(), D.Dag(self.root).environment("e1"))
        self.assertIn("dag/Solutions/A/Sub_1.lean", st.stale)
        self.assertEqual(st.theorems["A"]["status"], "Open")
        self.assertEqual(st.theorems["B"]["status"], "Proved")      # used no std module

    def test_reverify_plan_tries_everything(self):
        """Failing nodes do not keep the others from their turn: never-tried nodes first, then
        failed ones, least recently tried first; a failed attempt counts for nothing else."""
        recs = self.records()
        p = lambda t: f"dag/Solutions/{t}/Sub_1.lean"  # noqa: E731
        recs["e2"] += [rec("solution", p("C"), "C", env="e2", status="CE", time="2026-02-01T00:00:00Z"),
                       rec("solution", p("A"), "A", env="e2", status="CE", time="2026-01-01T00:00:00Z"),
                       rec("theorem", "dag/Theorems/Thm_C.lean", "C", env="e2", status="CE",
                           time="2026-01-15T00:00:00Z")]
        plan = T.reverify_plan(self.dag, recs, "e2")
        tried = [p("A"), "dag/Theorems/Thm_C.lean", p("C")]
        self.assertEqual(plan[-3:], tried)
        self.assertTrue(set(plan[:-3]).isdisjoint(tried))
        self.assertIn("dag/Theorems/Thm_A.lean", plan[:-3])
        st = D.status(self.dag, recs, self.dag.environment("e2"))
        self.assertEqual(st.theorems["C"]["status"], "Unchecked")

    def test_failed_attempt_establishes_no_id(self):
        """A DUPLICATE (or any failed) theorem in a re-verification carries an ID in its record,
        but establishes nothing: it is still planned, and its ID is not the environment's."""
        res = {"ok": False, "env": "e2", "items": [
            {"path": "dag/Theorems/Thm_C.lean", "kind": "theorem", "name": "C",
             "status": "DUPLICATE", "id": "7" * 64, "duplicate_of": "dag/Theorems/Thm_D.lean"}]}
        T.append_records(res, self.tmp / "rec", {"author": "reverify", "run": "r1"}, "e2")
        published = D.read_records(self.tmp / "rec")["e2"]
        self.assertEqual(published[0]["id"], "7" * 64)
        recs = self.records()
        recs["e2"] = recs["e2"] + published
        self.assertIn("dag/Theorems/Thm_C.lean", T.reverify_plan(self.dag, recs, "e2"))
        st = D.status(self.dag, recs, self.dag.environment("e2"))
        self.assertIsNone(st.theorems["C"]["id"])
        self.assertFalse(st.theorems["C"]["drifted"])
        self.assertFalse(D.id_record(published[0]))

    def test_unchecked_statement_proves_nothing(self):
        """A theorem whose statement has no OK ID here (its check failed, say as a DUPLICATE) is
        Unchecked even if a solution of it passed, and a proof that uses it does not count."""
        p = lambda t: f"dag/Solutions/{t}/Sub_1.lean"  # noqa: E731
        e2 = [rec("theorem", "dag/Theorems/Thm_A.lean", "A", env="e2", id="0" * 64, author="reverify"),
              rec("theorem", "dag/Theorems/Thm_B.lean", "B", env="e2", id="7" * 64,
                  status="DUPLICATE", author="reverify"),
              rec("solution", p("B"), "B", env="e2", theorem="B", author="reverify"),
              rec("solution", p("A"), "A", env="e2", theorem="A", uses=["B"],
                  status="SKETCH_ACCEPTED", author="reverify")]
        recs = {**self.records(), "e2": e2}
        st = D.status(self.dag, recs, self.dag.environment("e2"))
        self.assertEqual(st.theorems["B"]["status"], "Unchecked")
        self.assertEqual(st.theorems["A"]["status"], "Open")

    def test_compatible(self):
        self.assertEqual(D.compatible([{"M": "1", "N": "2"}, {"M": "1"}]), {})
        self.assertEqual(D.compatible([{"M": "1"}, {"M": "2"}]), {"M": ("1", "2")})

    def test_records_and_index(self):
        res = {"ok": True, "env": "e1", "std": "v1", "items": [
            {"path": "dag/Theorems/Thm_A.lean", "kind": "theorem", "name": "A", "status": "OK",
             "id": "1" * 64},
            {"path": "dag/Notes/x.md", "kind": "note", "name": "x", "status": "OK"},
            {"path": "dag/Solutions/A/Sub_1.lean", "kind": "solution", "name": "A",
             "status": "CE", "message": "no"}]}
        recs = T.append_records(res, self.tmp / "records", {"author": "alice", "pr": 3,
                                                           "commit": "abc", "run": None}, "e1")
        for env, result_env in (("../x", "../x"), ("/tmp/x", "/tmp/x"), ("e2", "e1")):
            with self.assertRaises(SystemExit):
                T.append_records({**res, "env": result_env}, self.tmp / "records", {}, env)
        self.assertEqual([(r["path"], r["status"]) for r in recs],     # failures are attempts
                         [("dag/Theorems/Thm_A.lean", "OK"), ("dag/Solutions/A/Sub_1.lean", "CE")])
        self.assertEqual(len(D.read_records(self.tmp / "records")["e1"]), 2)
        again = T.append_records(res, self.tmp / "records", {"author": "alice", "pr": 3,
                                                            "commit": "abc", "run": None}, "e1")
        self.assertEqual(again, [])                         # a retried publication adds nothing
        self.assertEqual(len(D.read_records(self.tmp / "records")["e1"]), 2)
        records = self.records()
        ix = T.index(self.dag, records)
        self.assertEqual(ix["environments"]["e1"]["counts"],
                         {"Proved": 2, "Disproved": 1, "Open": 3, "Drifted": 0, "Unchecked": 0})
        self.assertIn("## Environment `e1`", T.index_markdown(ix))
        self.assertEqual(ix["std_candidates"][0]["name"], "B")


class InitTest(Tmp):
    def test_init(self):
        d = self.tmp / "new-dag"
        T.init(d, "https://github.com/MachinaIO/Sigaba-Neo", "v1",
               "ghcr.io/machinaio/sigaba-neo-env@sha256:" + "1" * 64, "maintainers", "e1")
        for f in (".github/workflows/gate.yml", ".github/CODEOWNERS", "SKILL.md", "README.md",
                  "lakefile.toml", "lean-toolchain", "env/environments.json", "env/std.json",
                  "meta/trusted.json", "dag/Notes/.gitkeep"):
            self.assertTrue((d / f).exists(), f)
        for f in d.rglob("*"):
            if f.is_file():
                self.assertNotRegex(f.read_text(), r"\{\{[A-Z_]+\}\}", f)
        for name, f in (("environments", "env/environments.json"), ("std", "env/std.json"),
                        ("trusted", "meta/trusted.json"), ("assumptions", "meta/assumptions.json"),
                        ("promotions", "meta/promotions.json")):
            self.assertEqual(D.validate(json.loads((d / f).read_text()), D.schema(name)), [], f)
        self.assertIn('rev = "v1"', (d / "lakefile.toml").read_text())
        env = D.Dag(d).environment()
        self.assertEqual(env["id"], "e1")
        pins = {p["name"].strip("«»"): p["rev"]
                for p in json.loads((D.CORE / "lake-manifest.json").read_text())["packages"]}
        self.assertEqual(env["mathlib"], pins["mathlib"])
        self.assertEqual(env["cslib_frontier"], pins["cslib-frontier"])


class ImportServerTest(Tmp):
    def test_import(self):
        data = self.tmp / "server-data"
        data.mkdir()
        db = sqlite3.connect(data / "platform.sqlite")
        db.executescript("""
CREATE TABLE theorems (id TEXT, name TEXT, slug TEXT, title TEXT, status TEXT, preamble TEXT,
  statement TEXT, nl TEXT, source TEXT, tags TEXT, created_by TEXT, created_at REAL, deprecated_at REAL);
CREATE TABLE definitions (id TEXT, name TEXT, title TEXT, code TEXT, nl TEXT, source TEXT, tags TEXT,
  created_by TEXT, created_at REAL, deprecated_at REAL);
CREATE TABLE submissions (id TEXT, theorem_id TEXT, user TEXT, status TEXT, proof_type TEXT,
  content TEXT, explanation TEXT, error TEXT, created_at REAL, updated_at REAL, accepted_at REAL,
  deprecated_at REAL);
CREATE TABLE assumption_meta (theorem_id TEXT, tags TEXT, proposed_year INTEGER, source TEXT);
INSERT INTO definitions VALUES ('d1','Two','two','def two := 2\n',NULL,NULL,'[]','a',0,NULL);
INSERT INTO theorems VALUES ('t1','A.b','A_b','A b','Proved','import Definitions.Def_Two',
  'theorem A.b : two = 2 := by sorry',NULL,NULL,'["attack"]','a',0,NULL);
INSERT INTO submissions VALUES ('0123456789abcdef0123','t1','a','ACCEPTED','prove',
  'import Definitions.Def_Two\ntheorem solution : two = 2 := rfl\n',NULL,'',0,0,0,NULL);
INSERT INTO submissions VALUES ('s2','t1','a','CE','prove','bad',NULL,'',0,0,NULL,NULL);
INSERT INTO assumption_meta VALUES ('t1','["well-established"]',2005,'paper');
""")
        db.commit()
        out = self.tmp / "out"
        self.assertEqual(T.import_server(data, out), {"definition": 1, "theorem": 1, "solution": 1})
        dag = D.Dag(out)
        self.assertEqual([n.path for n in dag.nodes()],
                         ["dag/Definitions/Def_Two.lean",
                          "dag/Solutions/A_b/Sub_0123456789abcdef.lean",
                          "dag/Theorems/Thm_A_b.lean"])
        for n in dag.nodes():
            m = D.classify(n.path)[1]
            self.assertEqual(D.node_meta_problems(n.kind, n.path, n.meta, m), [], n.path)
        self.assertTrue(dag.theorem("A.b").text.rstrip().endswith(":= by sorry"))
        self.assertEqual(json.loads((out / "meta/assumptions.json").read_text())["claims"]["A.b"]
                         ["proposed_year"], 2005)


class FetchTest(Tmp):
    def test_fetch_large(self):
        """A pull request with more files than the compare API lists is listed from the full trees
        of the merge base and the head, and its contents come from one archive of the head."""
        base, head, mb = "b" * 40, "c" * 40, "d" * 40
        n = 400
        head_tree = [{"path": f"dag/Notes/n{i}.md", "type": "blob", "mode": "100644",
                      "sha": f"h{i}"} for i in range(n)]
        head_tree += [{"path": "README.md", "type": "blob", "mode": "100644", "sha": "r2"}]
        base_tree = [{"path": "README.md", "type": "blob", "mode": "100644", "sha": "r1"}]
        calls = []

        def fake_api(path, token, accept=None):
            calls.append(path)
            if path == f"/repos/o/r/compare/{base}...{head}":
                return {"files": [{"filename": "x", "status": "added"}] * 300,
                        "merge_base_commit": {"sha": mb}}
            if path.startswith("/repos/o/r/git/commits/"):
                return {"tree": {"sha": "T" + path.rsplit("/", 1)[1]}}
            if path == f"/repos/o/r/git/trees/T{mb}?recursive=1":
                return {"tree": base_tree}
            if path == f"/repos/o/r/git/trees/T{head}?recursive=1":
                return {"tree": head_tree}
            if path.startswith("/repos/o/r/git/trees/T" + head):
                return {"tree": [{"path": "dag", "type": "tree", "sha": "t-dag"}]}
            if path == "/repos/o/r/git/trees/t-dag":
                return {"tree": [{"path": "Notes", "type": "tree", "sha": "t-notes"}]}
            if path == "/repos/o/r/git/trees/t-notes":
                return {"tree": [{"path": f"n{i}.md", "type": "blob", "mode": "100644",
                                  "sha": f"h{i}"} for i in range(n)]}
            raise AssertionError(path)

        old_api, old_arch = T.api, T.head_archive
        T.api = fake_api
        T.head_archive = lambda repo, token, sha: {f"dag/Notes/n{i}.md": b"note" for i in range(n)}
        try:
            rows = T.fetch("o/r", self.tmp / "f", "token", base, head)
        finally:
            T.api, T.head_archive = old_api, old_arch
        added = [r for r in rows if r["status"] == "added"]
        self.assertEqual(len(added), n)
        self.assertEqual([r["status"] for r in rows if r["filename"] == "README.md"], ["modified"])
        self.assertEqual((self.tmp / "f/files/dag/Notes/n7.md").read_bytes(), b"note")
        self.assertFalse(any("/git/blobs/" in c for c in calls))

    def test_fetch(self):
        """The event's commits are read, never a moving head. Only added regular files of the
        layout are downloaded, as data; their mode and blob come from the head commit's tree, so
        a symbolic link (whose blob looks like a file) is reported, and the precheck rejects it."""
        import base64
        base, head = "b" * 40, "c" * 40
        blobs = {"s1": b"theorem X : True := by sorry\n", "s4": b"dag/Theorems/Thm_X.lean"}
        trees = {
            "root": [{"path": "dag", "type": "tree", "sha": "t-dag"},
                     {"path": ".github", "type": "tree", "sha": "t-gh"}],
            "t-dag": [{"path": "Theorems", "type": "tree", "sha": "t-thm"}],
            "t-thm": [{"path": "Thm_X.lean", "type": "blob", "mode": "100644", "sha": "s1"},
                      {"path": "Thm_Y.lean", "type": "blob", "mode": "100644", "sha": "s3"},
                      {"path": "Thm_L.lean", "type": "blob", "mode": "120000", "sha": "s4"}]}
        calls = []

        def fake_api(path, token, accept=None):
            calls.append(path)
            if path == f"/repos/o/r/compare/{base}...{head}":
                return {"files": [
                    {"filename": "dag/Theorems/Thm_X.lean", "status": "added", "sha": "s1"},
                    {"filename": ".github/workflows/x.yml", "status": "added", "sha": "s2"},
                    {"filename": "dag/Theorems/Thm_Y.lean", "status": "modified", "sha": "s3"},
                    {"filename": "dag/Theorems/Thm_L.lean", "status": "added", "sha": "s4"}]}
            if path == f"/repos/o/r/git/commits/{head}":
                return {"tree": {"sha": "root"}}
            if "/git/trees/" in path:
                return {"tree": trees[path.rsplit("/", 1)[1]]}
            sha = path.rsplit("/", 1)[1]
            return {"encoding": "base64", "content": base64.b64encode(blobs[sha]).decode()}

        old, T.api = T.api, fake_api
        try:
            rows = T.fetch("o/r", self.tmp / "f", "token", base, head)
            with self.assertRaises(SystemExit):
                T.fetch("o/r", self.tmp / "g", "token", base, "main")
        finally:
            T.api = old
        self.assertFalse(any("/pulls/" in c for c in calls))
        self.assertEqual([r["status"] for r in rows], ["added", "added", "modified", "added"])
        self.assertEqual((self.tmp / "f/files/dag/Theorems/Thm_X.lean").read_bytes(), blobs["s1"])
        self.assertFalse((self.tmp / "f/files/.github").exists())
        self.assertFalse((self.tmp / "f/files/dag/Theorems/Thm_L.lean").exists())
        self.assertEqual(sum("/git/blobs/" in c for c in calls), 1)
        self.assertEqual(json.loads((self.tmp / "f/files.json").read_text())["revision"], head)
        repo = self.tmp / "base"
        write(repo, {"meta/trusted.json": json.dumps({"mode": "open", "accept": [], "automerge": []})})
        pre = T.precheck(D.Dag(repo), [r for r in rows if "Thm_L" in r["filename"]],
                         self.tmp / "f/files", "x", head)
        self.assertTrue(any("mode 120000" in p for p in pre["problems"]), pre)
        self.assertEqual(pre["revision"], head)


class WorkflowTest(unittest.TestCase):
    def test_workflows(self):
        """No workflow has default permissions, and no checkout keeps its credentials."""
        try:
            import yaml
        except ImportError:
            self.skipTest("PyYAML is not installed")
        files = sorted((D.CORE / "templates/dag/.github/workflows").glob("*.yml")) + \
            sorted((D.CORE / ".github/workflows").glob("*.yml"))
        self.assertGreaterEqual(len(files), 7)
        for f in files:
            d = yaml.safe_load(f.read_text())
            self.assertIn("permissions", d, f)
            for name, job in d["jobs"].items():
                for step in job.get("steps", []):
                    if str(step.get("uses", "")).startswith("actions/checkout"):
                        self.assertIs(step["with"].get("persist-credentials"), False, (f, name))
        for name in ("records.yml", "reverify.yml"):
            w = yaml.safe_load((D.CORE / "templates/dag/.github/workflows" / name).read_text())
            groups = [w.get("concurrency", {}).get("group")] + \
                [j.get("concurrency", {}).get("group") for j in w["jobs"].values()]
            self.assertIn("records-branch", groups, name)
            conc = [w.get("concurrency")] + [j.get("concurrency") for j in w["jobs"].values()]
            self.assertTrue(any(c and c.get("group") == "records-branch" and c.get("queue") == "max"
                                for c in conc), name)
            self.assertIn("for attempt in", yaml.dump(w), name)
        rv = yaml.safe_load((D.CORE / "templates/dag/.github/workflows/reverify.yml").read_text())
        records_steps = yaml.dump(rv["jobs"]["records"]["steps"])
        self.assertNotIn("|| true", records_steps)          # no lost result goes unnoticed
        self.assertIn("Every planned environment has its result", records_steps)
        download = next(s for s in rv["jobs"]["records"]["steps"]
                        if str(s.get("uses", "")).startswith("actions/download-artifact"))
        self.assertNotIn("continue-on-error", download)
        gate = yaml.safe_load((D.CORE / "templates/dag/.github/workflows/gate.yml").read_text())
        self.assertEqual(gate["permissions"], {})
        self.assertIn("pull_request_target", gate[True])            # `on:` parses as True
        verify = gate["jobs"]["verify"]
        self.assertEqual(verify["permissions"], {"contents": "read"})
        run = next(s["run"] for s in verify["steps"] if s.get("name") == "Verify in the sandbox")
        for flag in ("--network none", "--read-only", "--cap-drop ALL", "--cap-add SETUID",
                     "SIGABA_LEAN_UID=1000", "--out -", "echo $? > out/exit"):
            self.assertIn(flag, run)
        self.assertNotIn("-v \"$PWD/out", run)             # nothing the container can write
        decide = gate["jobs"]["decide"]
        step = next(s["run"] for s in decide["steps"] if s.get("name") == "Decide")
        for flag in ("--exit-code result/exit", '--env "$ENV_ID"', '--revision "$REVISION"'):
            self.assertIn(flag, step)
        self.assertEqual(decide["permissions"], {"contents": "read"})
        rep = gate["jobs"]["report"]
        self.assertIn("pull_request_target", rep["if"])
        self.assertEqual(set(rep["permissions"]), {"pull-requests", "issues"})
        self.assertNotIn("GATE_APP", yaml.dump(rep))
        self.assertNotIn("environment", rep)
        report = next(s["run"] for s in rep["steps"] if s.get("name") == "Report on the pull request")
        # Only the merge job (passing pull requests of automerge authors) and the unqueue job (a
        # ready pull request turned back into a draft) hold the App's key; they run no step but
        # the token's and the merge-queue calls.
        merge = gate["jobs"]["merge"]
        self.assertEqual(merge["environment"], "gate")
        self.assertEqual(merge["permissions"], {})
        self.assertIn("pull_request_target", merge["if"])
        self.assertIn("needs.decide.outputs.automerge == '1'", merge["if"])
        self.assertEqual([j for j, job in gate["jobs"].items() if "GATE_APP" in yaml.dump(job)],
                         ["merge", "unqueue"])
        unq = gate["jobs"]["unqueue"]
        self.assertEqual((unq["environment"], unq["permissions"]), ("gate", {}))
        self.assertIn("converted_to_draft", unq["if"])
        self.assertFalse(any("checkout" in str(s.get("uses", "")) for s in unq["steps"]))
        # Drafts are not checked (docs/RESEARCH_PROTOCOL.md, D1): every job is skipped for them.
        self.assertIn("ready_for_review", gate[True]["pull_request_target"]["types"])
        self.assertIn("!github.event.pull_request.draft", gate["jobs"]["precheck"]["if"])
        self.assertIn("needs.precheck.result != 'skipped'", gate["jobs"]["decide"]["if"])
        self.assertIn("needs.precheck.result != 'skipped'", gate["jobs"]["report"]["if"])
        self.assertFalse(any("checkout" in str(s.get("uses", "")) for s in merge["steps"]))
        merge_run = next(s["run"] for s in merge["steps"] if "run" in s)
        self.assertIn('--match-head-commit "$REVISION"', merge_run)
        self.assertNotIn("gh pr merge", report)
        self.assertIn("gh label create", report)
        self.assertNotIn("|| true", report)                 # labelling never fails silently
        readme = (D.CORE / "docs/GITHUB_PLATFORM.md").read_text()
        for label in ("not-accepted", "rejected", "needs-maintainer"):
            self.assertIn(label, readme)
        fetch = next(s for s in gate["jobs"]["precheck"]["steps"]
                     if s.get("name") == "Fetch the added files (as data)")
        self.assertIn("pull_request.head.sha", fetch["env"]["HEAD_SHA"])


class GateScriptTest(Tmp):
    def test_decide_and_conclusion_steps(self):
        """The gate's shell steps read the decision under `bash -e`: a success concludes with
        success, and every label is read."""
        try:
            import yaml
        except ImportError:
            self.skipTest("PyYAML is not installed")
        import subprocess
        gate = yaml.safe_load((D.CORE / "templates/dag/.github/workflows/gate.yml").read_text())
        steps = {s.get("name"): s["run"] for s in gate["jobs"]["decide"]["steps"] if "run" in s}
        decide = steps["Decide"]
        script = decide[decide.index("python3 - <<'PY'"):]
        for conclusion, labels in (("success", []), ("failure", ["rejected", "needs-maintainer"])):
            with self.subTest(conclusion):
                (self.tmp / "decision.json").write_text(json.dumps(
                    {"conclusion": conclusion, "automerge": conclusion == "success",
                     "labels": labels, "comment": "c"}))
                subprocess.run(["bash", "-e", "-c", script], cwd=self.tmp, check=True)
                read = subprocess.run(["bash", "-e", "-c",
                                       'n=0; while read -r l; do n=$((n+1)); done < labels.txt; '
                                       'echo $n; read -r c a < flags.txt; echo "$c $a"'],
                                      cwd=self.tmp, text=True, capture_output=True, check=True)
                self.assertEqual(read.stdout.split("\n")[:2],
                                 [str(len(labels)), f"{conclusion} {int(conclusion == 'success')}"])
                r = subprocess.run(["bash", "-e", "-c", steps["Conclusion"]], cwd=self.tmp)
                self.assertEqual(r.returncode == 0, conclusion == "success")

    def test_labels_follow_the_latest_decision(self):
        """The Report step on one pull request: a failing commit, then a passing one by an author
        not on the automerge list, then a passing one that merges. The gate's labels follow each
        decision; another label stays; the merge names the verified commit."""
        try:
            import yaml
        except ImportError:
            self.skipTest("PyYAML is not installed")
        import os
        import subprocess
        self.assertEqual(T.label_changes(["bug", "rejected"], ["needs-maintainer"]),
                         [("add", "needs-maintainer"), ("remove", "rejected")])
        gate = yaml.safe_load((D.CORE / "templates/dag/.github/workflows/gate.yml").read_text())
        steps = {s.get("name"): s["run"] for job in ("decide", "report")
                 for s in gate["jobs"][job]["steps"] if "run" in s}
        decide = steps["Decide"]
        prepare = decide[decide.index("python3 - <<'PY'"):]
        work = self.tmp / "job"
        (work / "bin").mkdir(parents=True)
        (work / "core").symlink_to(D.CORE)
        state = work / "labels.json"
        state.write_text('["bug"]')
        log = work / "gh.log"
        fake = work / "bin" / "gh"
        fake.write_text(f"""#!/usr/bin/env python3
import json, sys
a = sys.argv[1:]
open({str(log)!r}, "a").write(" ".join(a) + "\\n")
labels = json.load(open({str(state)!r}))
if a[:2] == ["pr", "view"] and "isDraft,headRefOid" in a:
    print(open({str(work / 'pr-state')!r}).read().strip())
elif a[:2] == ["pr", "view"]:
    print(json.dumps(labels))
elif a[:2] == ["pr", "edit"]:
    i = a.index("--add-label") if "--add-label" in a else a.index("--remove-label")
    l = a[i + 1]
    labels = labels + [l] if a[i] == "--add-label" else [x for x in labels if x != l]
    json.dump(labels, open({str(state)!r}, "w"))
""")
        fake.chmod(0o755)
        env = {**os.environ, "PATH": f"{work / 'bin'}:{os.environ['PATH']}", "PR": "7",
               "REVISION": "e" * 40, "GITHUB_REPOSITORY": "o/r", "GH_TOKEN": "t"}
        for conclusion, labels, automerge, expect in (
                ("failure", ["rejected"], False, ["bug", "rejected"]),
                ("success", ["needs-maintainer"], False, ["bug", "needs-maintainer"]),
                ("success", [], True, ["bug"])):
            (work / "decision.json").write_text(json.dumps(
                {"conclusion": conclusion, "automerge": automerge, "labels": labels,
                 "comment": "c"}))
            subprocess.run(["bash", "-e", "-c", prepare], cwd=work, check=True)
            subprocess.run(["bash", "-e", "-c", steps["Report on the pull request"]], cwd=work,
                           env=env, check=True)
            self.assertEqual(json.loads(state.read_text()), expect, conclusion)
        self.assertNotIn("pr merge", log.read_text())        # the merge job's, not report's
        merge = next(s["run"] for s in gate["jobs"]["merge"]["steps"] if "run" in s)
        # a pull request that became a draft again, or moved on, is not merged
        for st in (f"true {'e' * 40}", f"false {'f' * 40}"):
            (work / "pr-state").write_text(st)
            subprocess.run(["bash", "-e", "-c", merge], cwd=work, env=env, check=True)
            self.assertNotIn("pr merge", log.read_text())
        (work / "pr-state").write_text(f"false {'e' * 40}")
        subprocess.run(["bash", "-e", "-c", merge], cwd=work, env=env, check=True)
        self.assertIn(f"--match-head-commit {'e' * 40}", log.read_text())
        self.assertEqual(log.read_text().count("pr merge"), 1)

    def test_reverify_requires_every_result(self):
        """reverify's records job: an environment with planned work must have a well-formed
        result, and every environment must report."""
        try:
            import yaml
        except ImportError:
            self.skipTest("PyYAML is not installed")
        import os
        import subprocess
        rv = yaml.safe_load((D.CORE / "templates/dag/.github/workflows/reverify.yml").read_text())
        script = next(s["run"] for s in rv["jobs"]["records"]["steps"]
                      if s.get("name") == "Every planned environment has its result")
        work = self.tmp / "rv"
        (work / "results").mkdir(parents=True)
        (work / "core").symlink_to(D.CORE)
        good = {"ok": True, "env": "e1", "items": [
            {"path": "dag/Theorems/Thm_A.lean", "kind": "theorem", "status": "OK"}]}

        def report(env: str, planned: str, result: str | None) -> None:
            d = work / "results" / f"result-{env}"
            d.mkdir(exist_ok=True)
            (d / "planned").write_text(planned + "\n")
            if result is not None:
                (d / "result.json").write_text(result)

        def run(envs: list[str]) -> int:
            env = {**os.environ, "ENVS": json.dumps([{"id": e} for e in envs])}
            return subprocess.run(["bash", "-e", "-c", script], cwd=work, env=env,
                                  capture_output=True).returncode

        report("e1", "1", json.dumps(good))
        report("e2", "0", None)
        self.assertEqual(run(["e1", "e2"]), 0)
        report("e3", "1", "")                                # the container failed
        self.assertNotEqual(run(["e1", "e3"]), 0)
        self.assertNotEqual(run(["e1", "e4"]), 0)            # no report at all

    def test_decide_without_artifacts(self):
        """When an earlier job left no artifact at all, the Decide step still writes a failing
        decision with a comment (and the Conclusion step fails)."""
        try:
            import yaml
        except ImportError:
            self.skipTest("PyYAML is not installed")
        import os
        import subprocess
        gate = yaml.safe_load((D.CORE / "templates/dag/.github/workflows/gate.yml").read_text())
        steps = {s.get("name"): s["run"] for s in gate["jobs"]["decide"]["steps"] if "run" in s}
        work = self.tmp / "job"
        work.mkdir()
        (work / "core").symlink_to(D.CORE)
        env = {**os.environ, "AUTHOR": "alice", "EVENT": "pull_request_target", "ENV_ID": "e1",
               "REVISION": ""}
        subprocess.run(["bash", "-e", "-c", steps["Decide"]], cwd=work, env=env, check=True,
                       capture_output=True)
        self.assertIn("did not finish", (work / "comment.md").read_text())
        r = subprocess.run(["bash", "-e", "-c", steps["Conclusion"]], cwd=work)
        self.assertNotEqual(r.returncode, 0)


class SchemaTest(unittest.TestCase):
    def test_schemas_load(self):
        for p in sorted(D.SCHEMA_DIR.glob("*.schema.json")):
            json.loads(p.read_text())
        self.assertEqual(D.validate({"mode": "open", "accept": [], "automerge": ["a-b[bot]"]},
                                    D.schema("trusted")), [])
        self.assertTrue(D.validate({"mode": "everyone", "accept": [], "automerge": []},
                                   D.schema("trusted")))


if __name__ == "__main__":
    unittest.main()
