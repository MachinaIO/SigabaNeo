"""The DAG's verifier (`dag_verify.py`) on a small DAG, with Lean.

1. The base's nodes are checked again (`--reverify`) and recorded: their semantic IDs, and the
   proof of `T.two_eq`, which makes it `Proved`.
2. A pull request with good and bad nodes: every status the gate reports, semantic duplicates
   (another text of a statement, another name), duplicate proofs (the same text up to comments),
   the syntactic filter, sketches and complete proofs (through the records).

    python3 -m unittest discover -s python/tests -p 'test_dag_verify.py' -v
"""

from __future__ import annotations

import json
import shutil
import tempfile
import unittest
from pathlib import Path

import common  # noqa: F401  (puts python/ on the path)
import dag as D
import dag_tools as T
import dag_verify as V

ENV = {"id": "e1", "lean": "local", "core": "local", "core_url": "https://github.com/x/y",
       "image": "local", "state": "default", "std": None}


def node(kind: str, name: str, text: str, sid: str = "", proof_type: str = "prove") -> dict:
    if kind == "definition":
        p = f"dag/Definitions/Def_{name}"
        meta = {"name": name, "title": name}
    elif kind == "theorem":
        p = f"dag/Theorems/Thm_{D.slug(name)}"
        meta = {"name": name, "title": name}
    else:
        p = f"dag/Solutions/{D.slug(name)}/Sub_{sid}"
        meta = {"theorem": name, "proof_type": proof_type}
    return {p + ".lean": text, p + ".json": json.dumps(meta)}


def write(root: Path, files: dict[str, str]) -> None:
    for rel, text in files.items():
        (root / rel).parent.mkdir(parents=True, exist_ok=True)
        (root / rel).write_text(text)


BASE = {
    **node("definition", "Two", "namespace T\n\ndef two : Nat := 2\n\nend T\n"),
    **node("theorem", "T.two_eq", "import Definitions.Def_Two\n\ntheorem T.two_eq : T.two = 2 := by sorry\n"),
    **node("theorem", "T.two_pos", "import Definitions.Def_Two\n\ntheorem T.two_pos : 0 < T.two := by sorry\n"),
    **node("solution", "T.two_eq", "import Definitions.Def_Two\n\ntheorem solution : T.two = 2 := rfl\n", "base"),
}

PR = {
    # Good: a definition, a theorem, an open lemma, a sketch on it, a complete proof through a
    # proved theorem, a disproof.
    **node("definition", "Three", "namespace T3\n\ndef three : Nat := 3\n\nend T3\n"),
    **node("theorem", "T3.three_eq", "import Definitions.Def_Three\n\ntheorem T3.three_eq : T3.three = 3 := by sorry\n"),
    **node("theorem", "T3.aux", "import Definitions.Def_Three\n\ntheorem T3.aux : T3.three = 1 + 2 := by sorry\n"),
    **node("solution", "T3.three_eq", "import Definitions.Def_Three\nimport Theorems.Thm_T3_aux\n\n"
           "theorem solution : T3.three = 3 := T3.aux\n", "sketch"),
    **node("solution", "T.two_pos", "import Definitions.Def_Two\nimport Theorems.Thm_T_two_eq\n\n"
           "theorem solution : 0 < T.two := by rw [T.two_eq]; decide\n", "full"),
    **node("theorem", "T.two_three", "import Definitions.Def_Two\n\ntheorem T.two_three : T.two = 3 := by sorry\n"),
    **node("solution", "T.two_three", "import Definitions.Def_Two\n\n"
           "theorem solution : ¬ T.two = 3 := by decide\n", "no", "disprove"),
    # Semantic duplicates: T.two_eq again under another name; two texts of one Real statement.
    **node("theorem", "T.two_eq_again", "import Definitions.Def_Two\n\n"
           "theorem T.two_eq_again : T.two = (2 : Nat) := by\n  sorry\n"),
    **node("theorem", "R.one", "import Mathlib.Data.Real.Basic\n\n"
           "theorem R.one : ∀ x : ℝ, x ≤ x + 1 → (0 : ℝ) < 1 := by sorry\n"),
    **node("theorem", "R.one_again", "import Mathlib.Data.Real.Basic\n\n"
           "-- the same proposition\ntheorem R.one_again : ∀ y : ℝ, y ≤ y + 1 → 0 < (1 : ℝ) := by sorry\n"),
    # A proof inside a statement, as a named theorem and as a λ: proofs are irrelevant to the ID.
    **node("theorem", "S.lam", "theorem S.lam : (⟨fun n => n, fun n => Nat.le_refl n⟩ : "
           "{f : Nat → Nat // ∀ n, f n ≤ n}).val 0 = 0 := by sorry\n"),
    **node("theorem", "S.named", "theorem S.named : (⟨fun n => n, Nat.le_refl⟩ : "
           "{f : Nat → Nat // ∀ n, f n ≤ n}).val 0 = 0 := by sorry\n"),
    # A duplicate proof: the base's, with a comment.
    **node("solution", "T.two_eq", "import Definitions.Def_Two\n-- again\n\n"
           "theorem solution : T.two = 2 := rfl\n", "again"),
    # The same proof twice in one pull request (another id, a comment): the second is a duplicate.
    **node("solution", "T.two_pos", "import Definitions.Def_Two\nimport Theorems.Thm_T_two_eq\n\n"
           "-- again\ntheorem solution : 0 < T.two := by rw [T.two_eq]; decide\n", "full2"),
    # Bad ones.
    **node("solution", "T.two_eq", "import Definitions.Def_Two\n\ntheorem solution : T.two = 2 := rfl rfl\n", "ce"),
    **node("solution", "T.two_eq", "import Definitions.Def_Two\n\ntheorem solution : True := trivial\n", "wa"),
    **node("solution", "T.two_eq", "import Definitions.Def_Two\n\ntheorem solution : T.two = 2 := sorry\n", "sorry"),
    **node("solution", "T.two_eq", "import Definitions.Def_Two\n\naxiom cheat : T.two = 2\n\n"
           "theorem solution : T.two = 2 := cheat\n", "axiom"),
    **node("solution", "T.two_eq", "import Definitions.Def_Two\n\n#eval (2 : Nat)\n\n"
           "theorem solution : T.two = 2 := rfl\n", "eval"),
    **node("solution", "T.two_eq", "import Definitions.Def_Two\nimport Lean\n\n"
           "set_option debug.skipKernelTC true in\ntheorem solution : T.two = 2 := rfl\n", "skip"),
    **node("solution", "T.two_eq", "import Definitions.Def_Two\nimport SigabaNeo.Platform\n\n"
           "theorem solution : T.two = 2 := rfl\n", "platform"),
    **node("solution", "T.two_pos", "import Definitions.Def_Two\nimport Theorems.Thm_T_two_pos\n\n"
           "theorem solution : 0 < T.two := T.two_pos\n", "self"),
    # Recursion and inductive types: Lean's compiler code for them (`f._unsafe_rec`, `T.ctorIdx`,
    # `T.ctorIdx._impl`) is allowed; `partial`, `unsafe` and `implemented_by` are not, also under
    # those names (the syntactic filter rejects them first).
    **node("definition", "Rec", "inductive Tree | leaf | node (l r : Tree)\n\n"
           "def Tree.size : Tree → Nat\n  | .leaf => 1\n  | .node l r => l.size + r.size + 1\n\n"
           "def halve : Nat → Nat\n  | 0 => 0\n  | n+1 => halve ((n+1) / 2) + 1\ndecreasing_by omega\n\n"
           "class inductive Two | a | b\n"),
    **node("definition", "Partial", "partial def loop (n : Nat) : Nat := loop n\n"),
    **node("definition", "ImplBy", "def impl (n : Nat) : Nat := n\n\n"
           "@[implemented_by impl] def f (n : Nat) : Nat := 0\n"),
    **node("definition", "FakeRec", "def g (n : Nat) : Nat := n\n\n"
           "unsafe def g._unsafe_rec (n : Nat) : Nat := 0\n"),
    **node("definition", "FakeCtorIdx", "inductive P : Prop | a | b\n\n"
           "unsafe def P.ctorIdx._impl : P → Nat := fun _ => 0\n\n"
           "@[implemented_by P.ctorIdx._impl] def P.ctorIdx : P → Nat := fun _ => 0\n"),
    **node("definition", "Sorry", "def sorryNat : Nat := sorry\n"),
    **node("theorem", "T.extra", "import Definitions.Def_Two\n\ndef helper : Nat := 1\n\n"
           "theorem T.extra : T.two = 2 := by sorry\n"),
}

EXPECTED = {
    "dag/Definitions/Def_Three.lean": "OK",
    "dag/Theorems/Thm_T3_three_eq.lean": "OK",
    "dag/Theorems/Thm_T3_aux.lean": "OK",
    "dag/Solutions/T3_three_eq/Sub_sketch.lean": "SKETCH_ACCEPTED",
    "dag/Solutions/T_two_pos/Sub_full.lean": "ACCEPTED",
    "dag/Solutions/T_two_pos/Sub_full2.lean": "DUPLICATE",
    "dag/Theorems/Thm_T_two_three.lean": "OK",
    "dag/Solutions/T_two_three/Sub_no.lean": "ACCEPTED",
    "dag/Theorems/Thm_T_two_eq_again.lean": "DUPLICATE",
    "dag/Theorems/Thm_R_one.lean": "OK",
    "dag/Theorems/Thm_R_one_again.lean": "DUPLICATE",
    "dag/Solutions/T_two_eq/Sub_again.lean": "DUPLICATE",
    "dag/Theorems/Thm_S_lam.lean": "OK",
    "dag/Theorems/Thm_S_named.lean": "DUPLICATE",
    "dag/Solutions/T_two_eq/Sub_ce.lean": "CE",
    "dag/Solutions/T_two_eq/Sub_wa.lean": "WA",
    "dag/Solutions/T_two_eq/Sub_sorry.lean": "SORRY",
    "dag/Solutions/T_two_eq/Sub_axiom.lean": "FAILED",
    "dag/Solutions/T_two_eq/Sub_eval.lean": "LINT",
    "dag/Solutions/T_two_eq/Sub_skip.lean": "LINT",
    "dag/Solutions/T_two_eq/Sub_platform.lean": "FAILED",
    "dag/Solutions/T_two_pos/Sub_self.lean": "FAILED",
    "dag/Definitions/Def_Rec.lean": "OK",
    "dag/Definitions/Def_Partial.lean": "LINT",
    "dag/Definitions/Def_ImplBy.lean": "LINT",
    "dag/Definitions/Def_FakeRec.lean": "LINT",
    "dag/Definitions/Def_FakeCtorIdx.lean": "LINT",
    "dag/Definitions/Def_Sorry.lean": "FAILED",
    "dag/Theorems/Thm_T_extra.lean": "FAILED",
}

state: dict = {}


def setUpModule():
    tmp = Path(tempfile.mkdtemp(prefix="sigaba-neo-verify-"))
    base = tmp / "base"
    write(base, BASE)
    write(base, {"env/environments.json": json.dumps({"environments": [ENV]})})
    # 1. The base, checked again and recorded.
    plan = sorted(p for p in BASE if p.endswith(".lean"))
    again = V.verify(base, None, "e1", None, tmp / "w0", reverify=plan)
    T.append_records(again, tmp / "records", {"author": "test"}, "e1")
    # 2. The pull request.
    write(tmp / "new", PR)
    out = V.verify(base, tmp / "new", "e1", tmp / "records", tmp / "w1", revision="f" * 40)
    state.update(tmp=tmp, base=base, again=again, out=out)


def tearDownModule():
    shutil.rmtree(state["tmp"], ignore_errors=True)


class VerifyTest(unittest.TestCase):
    def test_reverify(self):
        r = state["again"]
        self.assertTrue(r["ok"], json.dumps(r, indent=1))
        self.assertEqual({i["path"]: i["status"] for i in r["items"]}, {
            "dag/Definitions/Def_Two.lean": "OK", "dag/Theorems/Thm_T_two_eq.lean": "OK",
            "dag/Theorems/Thm_T_two_pos.lean": "OK",
            "dag/Solutions/T_two_eq/Sub_base.lean": "ACCEPTED"})
        self.assertTrue(all(i.get("id") for i in r["items"] if i["kind"] != "solution"))

    def test_statuses(self):
        r = state["out"]
        got = {i["path"]: i["status"] for i in r["items"]}
        detail = json.dumps(r, indent=1)
        self.assertEqual(got, EXPECTED, detail)
        self.assertFalse(r["ok"])
        self.assertEqual(T.check_result.__name__, "check_result")
        self.assertEqual(D.validate(r, D.schema("result")), [])

    def test_details(self):
        items = {i["path"]: i for i in state["out"]["items"]}
        self.assertEqual(items["dag/Theorems/Thm_T_two_eq_again.lean"]["duplicate_of"],
                         "dag/Theorems/Thm_T_two_eq.lean")
        self.assertEqual(items["dag/Theorems/Thm_R_one_again.lean"]["duplicate_of"],
                         "dag/Theorems/Thm_R_one.lean")
        self.assertEqual(items["dag/Solutions/T_two_eq/Sub_again.lean"]["duplicate_of"],
                         "dag/Solutions/T_two_eq/Sub_base.lean")
        self.assertEqual(items["dag/Theorems/Thm_S_named.lean"]["duplicate_of"],
                         "dag/Theorems/Thm_S_lam.lean")
        self.assertEqual(state["out"]["revision"], "f" * 40)
        self.assertEqual(items["dag/Solutions/T_two_pos/Sub_full2.lean"]["duplicate_of"],
                         "dag/Solutions/T_two_pos/Sub_full.lean")
        self.assertEqual(items["dag/Solutions/T3_three_eq/Sub_sketch.lean"]["uses"], ["T3.aux"])
        self.assertEqual(items["dag/Solutions/T_two_pos/Sub_full.lean"]["uses"], ["T.two_eq"])
        self.assertIn("#eval", items["dag/Solutions/T_two_eq/Sub_eval.lean"]["message"])
        self.assertIn("debug.skipKernelTC", items["dag/Solutions/T_two_eq/Sub_skip.lean"]["message"])
        self.assertIn("SigabaNeo.Platform", items["dag/Solutions/T_two_eq/Sub_platform.lean"]["message"])
        self.assertIn("its own target", items["dag/Solutions/T_two_pos/Sub_self.lean"]["message"])
        for name, why in [("Partial", "`partial`"), ("ImplBy", "`implemented_by`"),
                          ("FakeRec", "`unsafe`"), ("FakeCtorIdx", "`unsafe`")]:
            self.assertIn(why, items[f"dag/Definitions/Def_{name}.lean"]["message"])

    def test_decision(self):
        pre = {"ok": True, "accepted": True, "automerge": True, "problems": [], "added": sorted(PR)}
        d = T.decide(pre, state["out"], "alice", "pull_request_target", "e1", "f" * 40, 1)
        self.assertEqual(d["conclusion"], "failure")
        self.assertIn("`LINT`", d["comment"])


class UnrecordedBaseTest(unittest.TestCase):
    def test_duplicate_without_records(self):
        """Without any record (they lag behind merges), a statement of the base under another name
        is still a duplicate: the base's IDs are computed."""
        tmp = state["tmp"]
        write(tmp / "new-dup", node("theorem", "T.two_eq_other", "import Definitions.Def_Two\n\n"
                                    "theorem T.two_eq_other : T.two = 2 := by sorry\n"))
        out = V.verify(state["base"], tmp / "new-dup", "e1", None, tmp / "w3")
        (item,) = out["items"]
        self.assertEqual(item["status"], "DUPLICATE", item)
        self.assertEqual(item["duplicate_of"], "dag/Theorems/Thm_T_two_eq.lean")


class BaseIdErrorTest(unittest.TestCase):
    def test_base_id_failure_is_an_error(self):
        """If a base theorem builds but its semantic ID cannot be computed, an added theorem is
        not judged (ERROR, naming the base node): duplicates cannot be decided."""
        tmp = state["tmp"]
        write(tmp / "new-err", node("theorem", "T.two_eq_err", "import Definitions.Def_Two\n\n"
                                    "theorem T.two_eq_err : T.two = 2 := by sorry\n"))
        orig = V.Workspace.platform

        def failing(ws, cmd):
            if "semantic" in cmd and "Thm_T_two_eq\"" in cmd:
                return {"status": "ERROR", "message": "timed out"}
            return orig(ws, cmd)

        V.Workspace.platform = failing
        try:
            out = V.verify(state["base"], tmp / "new-err", "e1", None, tmp / "w4")
        finally:
            V.Workspace.platform = orig
        (item,) = out["items"]
        self.assertEqual(item["status"], "ERROR", item)
        self.assertIn("dag/Theorems/Thm_T_two_eq.lean", item["message"])
        self.assertFalse(out["ok"])


class BaseTimeoutTest(unittest.TestCase):
    def test_base_timeout_is_an_error(self):
        """A base theorem whose build times out decides nothing: an added theorem is ERROR."""
        tmp = state["tmp"]
        write(tmp / "new-to", node("theorem", "T.two_eq_to", "import Definitions.Def_Two\n\n"
                                   "theorem T.two_eq_to : T.two = 2 := by sorry\n"))
        orig = V.Workspace.build

        def slow(ws, modules):
            if modules == ["Theorems.Thm_T_two_eq"]:
                return V.subprocess.CompletedProcess(modules, 124, "", "error: timed out")
            return orig(ws, modules)

        V.Workspace.build = slow
        try:
            out = V.verify(state["base"], tmp / "new-to", "e1", None, tmp / "w5")
        finally:
            V.Workspace.build = orig
        (item,) = out["items"]
        self.assertEqual(item["status"], "ERROR", item)
        self.assertIn("Thm_T_two_eq.lean: its check did not finish", item["message"])
        self.assertIn("timed out", item["message"])


class OwnerTest(unittest.TestCase):
    def test_owner_does_not_depend_on_batches(self):
        """Two base theorems that mean the same, no records: re-verified together or one at a
        time, the first by path owns the ID and the other is its DUPLICATE."""
        tmp = state["tmp"]
        base = tmp / "base-owner"
        write(base, BASE)
        write(base, {"env/environments.json": json.dumps({"environments": [ENV]})})
        write(base, node("theorem", "T.two_eq_z", "import Definitions.Def_Two\n\n"
                         "theorem T.two_eq_z : T.two = 2 := by sorry\n"))
        a, z = "dag/Theorems/Thm_T_two_eq.lean", "dag/Theorems/Thm_T_two_eq_z.lean"
        runs = {"both": [a, z], "a": [a], "z": [z]}
        got = {}
        for label, plan in runs.items():
            out = V.verify(base, None, "e1", None, tmp / f"w-own-{label}", reverify=plan)
            got.update({(label, i["path"]): i["status"] for i in out["items"]})
        self.assertEqual(got, {("both", a): "OK", ("both", z): "DUPLICATE",
                               ("a", a): "OK", ("z", z): "DUPLICATE"})

    def test_owner_does_not_depend_on_build_order(self):
        """M and Z state the same; A imports Z, so Z is built first when all three are checked.
        Together or one at a time, M (first by path) owns the ID."""
        tmp = state["tmp"]
        base = tmp / "base-order"
        write(base, {"env/environments.json": json.dumps({"environments": [ENV]})})
        write(base, node("theorem", "T.m", "theorem T.m : True := by sorry\n"))
        write(base, node("theorem", "T.z", "theorem T.z : True := by sorry\n"))
        write(base, node("theorem", "T.a", "import Theorems.Thm_T_z\n\n"
                         "theorem T.a : 1 = 1 := by sorry\n"))
        m, z, a = ("dag/Theorems/Thm_T_m.lean", "dag/Theorems/Thm_T_z.lean",
                   "dag/Theorems/Thm_T_a.lean")
        runs = {"all": [a, m, z], "m": [m], "z": [z], "a": [a]}
        got = {}
        for label, plan in runs.items():
            out = V.verify(base, None, "e1", None, tmp / f"w-ord-{label}", reverify=plan)
            got.update({(label, i["path"]): i["status"] for i in out["items"]})
        self.assertEqual(got, {("all", a): "OK", ("all", m): "OK", ("all", z): "DUPLICATE",
                               ("m", m): "OK", ("z", z): "DUPLICATE", ("a", a): "OK"})

    def test_ineligible_candidate_owns_nothing(self):
        """M is first by path but fails the checks (the filter rejects it) while it still builds;
        Z states the same. Checked together or Z alone, Z owns the ID: a base node is a candidate
        only if it passes the same checks."""
        tmp = state["tmp"]
        base = tmp / "base-elig"
        write(base, {"env/environments.json": json.dumps({"environments": [ENV]})})
        write(base, node("theorem", "T.m", "#eval (1 : Nat)\n\ntheorem T.m : True := by sorry\n"))
        write(base, node("theorem", "T.z", "theorem T.z : True := by sorry\n"))
        m, z = "dag/Theorems/Thm_T_m.lean", "dag/Theorems/Thm_T_z.lean"
        got = {}
        for label, plan in {"both": [m, z], "z": [z]}.items():
            out = V.verify(base, None, "e1", None, tmp / f"w-elig-{label}", reverify=plan)
            got.update({(label, i["path"]): i["status"] for i in out["items"]})
        self.assertEqual(got, {("both", m): "LINT", ("both", z): "OK", ("z", z): "OK"})

    def test_undecided_candidate_in_any_role(self):
        """A and Z state the same; A's check does not finish (ERROR). Whether A is re-verified
        with Z or only scanned as a shadow, Z is ERROR, naming A: ownership is undecided."""
        tmp = state["tmp"]
        base = tmp / "base-und"
        write(base, {"env/environments.json": json.dumps({"environments": [ENV]})})
        write(base, node("theorem", "T.a", "theorem T.a : True := by sorry\n"))
        write(base, node("theorem", "T.z", "theorem T.z : True := by sorry\n"))
        a, z = "dag/Theorems/Thm_T_a.lean", "dag/Theorems/Thm_T_z.lean"
        orig = V.check_item

        def undecided(it, *args, **kw):
            if it["path"] == a:
                return {"path": a, "kind": "theorem", "status": "ERROR", "message": "timed out"}
            return orig(it, *args, **kw)

        V.check_item = undecided
        try:
            for label, plan in {"z": [z], "az": [a, z]}.items():
                out = V.verify(base, None, "e1", None, tmp / f"w-und-{label}", reverify=plan)
                zr = next(i for i in out["items"] if i["path"] == z)
                self.assertEqual(zr["status"], "ERROR", (label, zr))
                self.assertIn(a, zr["message"], label)
        finally:
            V.check_item = orig

    def test_failing_import_owns_nothing(self):
        """M (first by path) imports a definition A that fails its checks; Z states what M states.
        Whatever is re-verified together, M fails with its import and Z owns the ID."""
        tmp = state["tmp"]
        base = tmp / "base-imp"
        write(base, {"env/environments.json": json.dumps({"environments": [ENV]})})
        write(base, node("definition", "A", "#eval (1 : Nat)\n\ndef aDef : Nat := 1\n"))
        write(base, node("theorem", "T.m", "import Definitions.Def_A\n\n"
                         "theorem T.m : True := by sorry\n"))
        write(base, node("theorem", "T.z", "theorem T.z : True := by sorry\n"))
        a, m, z = ("dag/Definitions/Def_A.lean", "dag/Theorems/Thm_T_m.lean",
                   "dag/Theorems/Thm_T_z.lean")
        got = {}
        for label, plan in {"all": [a, m, z], "z": [z], "m": [m], "mz": [m, z]}.items():
            out = V.verify(base, None, "e1", None, tmp / f"w-imp-{label}", reverify=plan)
            got.update({(label, i["path"]): i["status"] for i in out["items"]})
        self.assertEqual(got, {("all", a): "LINT", ("all", m): "FAILED", ("all", z): "OK",
                               ("z", z): "OK", ("m", m): "FAILED",
                               ("mz", m): "FAILED", ("mz", z): "OK"})


class LintTimeoutTest(unittest.TestCase):
    def test_base_lint_timeout_is_an_error(self):
        """The filter not finishing on a base theorem decides nothing: an added theorem is ERROR."""
        tmp = state["tmp"]
        write(tmp / "new-lt", node("theorem", "T.two_eq_lt", "import Definitions.Def_Two\n\n"
                                   "theorem T.two_eq_lt : T.two = 2 := by sorry\n"))
        orig = V.Workspace.lint

        def slow(ws, path, imports):
            if path == "dag/Theorems/Thm_T_two_eq.lean":
                return {"status": "ERROR", "message": "error: timed out"}
            return orig(ws, path, imports)

        V.Workspace.lint = slow
        try:
            out = V.verify(state["base"], tmp / "new-lt", "e1", None, tmp / "w6")
        finally:
            V.Workspace.lint = orig
        (item,) = out["items"]
        self.assertEqual(item["status"], "ERROR", item)
        self.assertIn("Thm_T_two_eq.lean: its check did not finish", item["message"])


class TamperTest(unittest.TestCase):
    def test_changed_outputs_fail(self):
        """A step that changes the build outputs of another node (here, a theorem's .olean, as a
        solution's build could) fails its item, whatever its own checks said."""
        tmp = state["tmp"]
        write(tmp / "new-tamper", node("solution", "T.two_eq", "import Definitions.Def_Two\n\n"
                                       "theorem solution : T.two = 2 := by rfl\n", "t"))
        orig = V.Workspace.build

        def tampering(ws, modules):
            r = orig(ws, modules)
            if any(m.startswith("Solutions.") for m in modules):   # as the solution's code could
                olean = ws.dir / ".lake/build/lib/lean/Theorems/Thm_T_two_eq.olean"
                olean.write_bytes(olean.read_bytes() + b"x")
            return r

        V.Workspace.build = tampering
        try:
            out = V.verify(state["base"], tmp / "new-tamper", "e1", None, tmp / "w2", timeout=600)
        finally:
            V.Workspace.build = orig
        (item,) = out["items"]
        self.assertEqual(item["status"], "FAILED", item)
        self.assertIn("changed the build outputs", item["message"])
        self.assertFalse(out["ok"])


if __name__ == "__main__":
    unittest.main()
