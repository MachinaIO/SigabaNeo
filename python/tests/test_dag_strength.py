"""Registered assumptions and strength versions in the DAG's verifier, with Lean.

The base registers two toy assumptions and proves a lowering of the first one. Pull requests then
add strength versions and registrations, good and bad:

1. a version whose lowering is proved and states the right functions (`OK`); a version whose
   lowering is about another assumption (`WA`); a re-registration of the same problem with another
   `H` (`DUPLICATE`); a registration of a constant that is not an assumption (`FAILED`);
2. a version whose lowering is not proved, and one that skips a number (`FAILED`);
3. after the first version is merged, a version stated from the assumption's own `H` again: it is
   stale, since the previous function is now `H_v1` (`WA`).

    python3 -m unittest discover -s python/tests -p 'test_dag_strength.py' -v
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
from test_dag_verify import ENV, node, write

TOY = """import SigabaNeo.Trusted.Assumption

namespace Toy

open SigabaNeo

/-- A toy decision problem: tell `[true]` from `[false]`. -/
noncomputable def asm : Assumption :=
  { Params := Unit, problem := fun _ => .decision (PMF.pure [true]) (PMF.pure [false]),
    H := fun _ => 100 }

def H1 : asm.Params → ℕ := fun _ => 100
def H2 : asm.Params → ℕ := fun _ => 100

/-- The same problem with the decision swapped: another assumption. -/
noncomputable def swapped : Assumption :=
  { Params := Unit, problem := fun _ => .decision (PMF.pure [false]) (PMF.pure [true]),
    H := fun _ => 100 }

def S1 : swapped.Params → ℕ := fun _ => 100

end Toy
"""

AGAIN = """import SigabaNeo.Trusted.Assumption

/-- `Toy.asm`'s problem again, with another security function. -/
noncomputable def ToyAgain.asm : SigabaNeo.Assumption :=
  { Params := Unit, problem := fun _ => .decision (PMF.pure [true]) (PMF.pure [false]),
    H := fun _ => 7 }
"""

PROOF = "fun _ => ⟨le_rfl, fun h => absurd h (lt_irrefl _)⟩"


def asm(name: str, module: str) -> dict[str, str]:
    return {f"dag/Assumptions/{D.slug(name)}/Asm.json": json.dumps(
        {"name": name, "module": module, "title": name, "rationale": "a test"})}


def version(slug: str, n: int, h: str, lowering: str) -> dict[str, str]:
    return {f"dag/Assumptions/{slug}/H_v{n}.json": json.dumps({"H": h, "lowering": lowering})}


def lowering(name: str, statement: str, proof: str | None) -> dict[str, str]:
    files = node("theorem", name, "import Definitions.Def_Toy\n\n"
                 f"theorem {name} : {statement} := by sorry\n")
    if proof:
        files |= node("solution", name, f"import Definitions.Def_Toy\n\n"
                      f"theorem solution : {statement} := {proof}\n", "p")
    return files


BASE = {
    **node("definition", "Toy", TOY),
    **asm("Toy.asm", "Definitions.Def_Toy"),
    **asm("Toy.swapped", "Definitions.Def_Toy"),
    **lowering("Toy.lower1", "SigabaNeo.Assumption.Lowering Toy.asm Toy.asm.H Toy.H1", PROOF),
    **lowering("Toy.lower_open", "SigabaNeo.Assumption.Lowering Toy.swapped Toy.swapped.H Toy.S1",
               None),
    **lowering("Toy.lower2", "SigabaNeo.Assumption.Lowering Toy.asm Toy.H1 Toy.H2", PROOF),
}

PR1 = {
    **version("Toy_asm", 1, "Toy.H1", "Toy.lower1"),
    **version("Toy_swapped", 1, "Toy.S1", "Toy.lower1"),
    **node("definition", "ToyAgain", AGAIN),
    **asm("ToyAgain.asm", "Definitions.Def_ToyAgain"),
    **asm("Toy.H1", "Definitions.Def_Toy"),
}
EXPECTED1 = {
    "dag/Assumptions/Toy_asm/H_v1.json": "OK",
    "dag/Assumptions/Toy_swapped/H_v1.json": "WA",
    "dag/Definitions/Def_ToyAgain.lean": "OK",
    "dag/Assumptions/ToyAgain_asm/Asm.json": "DUPLICATE",
    "dag/Assumptions/Toy_H1/Asm.json": "FAILED",
}

PR2 = {
    **version("Toy_swapped", 1, "Toy.S1", "Toy.lower_open"),
    **version("Toy_asm", 2, "Toy.H2", "Toy.lower2"),
}
EXPECTED2 = {
    "dag/Assumptions/Toy_swapped/H_v1.json": "FAILED",
    "dag/Assumptions/Toy_asm/H_v2.json": "FAILED",
}

state: dict = {}


def statuses(out: dict) -> dict[str, str]:
    return {it["path"]: it["status"] for it in out["items"]}


def setUpModule():
    tmp = Path(tempfile.mkdtemp(prefix="sigaba-neo-strength-"))
    base = tmp / "base"
    write(base, BASE)
    write(base, {"env/environments.json": json.dumps({"environments": [ENV]})})
    plan = sorted(p for p in BASE if D.is_node_file(p))
    again = V.verify(base, None, "e1", None, tmp / "w0", reverify=plan)
    T.append_records(again, tmp / "records", {"author": "test"}, "e1")
    outs = []
    for i, pr in enumerate((PR1, PR2), 1):
        write(tmp / f"new{i}", pr)
        outs.append(V.verify(base, tmp / f"new{i}", "e1", tmp / "records", tmp / f"w{i}"))
    # 3. The first version is merged; the same lowering from the assumption's own `H` is stale.
    merged = tmp / "merged"
    shutil.copytree(base, merged)
    write(merged, version("Toy_asm", 1, "Toy.H1", "Toy.lower1"))
    write(tmp / "new3", version("Toy_asm", 2, "Toy.H1", "Toy.lower1"))
    outs.append(V.verify(merged, tmp / "new3", "e1", tmp / "records", tmp / "w3"))
    write(tmp / "new4", version("Toy_asm", 2, "Toy.H2", "Toy.lower2"))
    outs.append(V.verify(merged, tmp / "new4", "e1", tmp / "records", tmp / "w4"))
    state.update(tmp=tmp, base=base, merged=merged, again=again, outs=outs)


def tearDownModule():
    shutil.rmtree(state["tmp"], ignore_errors=True)


class StrengthTest(unittest.TestCase):
    def test_base(self):
        st = statuses(state["again"])
        self.assertTrue(all(s in ("OK", "ACCEPTED") for s in st.values()), state["again"])
        ids = {it["path"]: it.get("id") for it in state["again"]["items"]}
        self.assertTrue(ids["dag/Assumptions/Toy_asm/Asm.json"])
        self.assertNotEqual(ids["dag/Assumptions/Toy_asm/Asm.json"],
                            ids["dag/Assumptions/Toy_swapped/Asm.json"])

    def test_first_pull_request(self):
        out = state["outs"][0]
        self.assertEqual(statuses(out), EXPECTED1, json.dumps(out, indent=1))
        ok = next(it for it in out["items"] if it["path"].endswith("Toy_asm/H_v1.json"))
        self.assertEqual((ok["assumption"], ok["version"], ok["H"], ok["lowering"]),
                         ("Toy.asm", 1, "Toy.H1", "Toy.lower1"))
        dup = next(it for it in out["items"] if it["path"].endswith("ToyAgain_asm/Asm.json"))
        self.assertEqual(dup["duplicate_of"], "dag/Assumptions/Toy_asm/Asm.json")
        self.assertFalse(D.validate(out, D.schema("result")))

    def test_second_pull_request(self):
        out = state["outs"][1]
        self.assertEqual(statuses(out), EXPECTED2, json.dumps(out, indent=1))
        msgs = {it["path"]: it.get("message", "") for it in out["items"]}
        self.assertIn("not proved", msgs["dag/Assumptions/Toy_swapped/H_v1.json"])
        self.assertIn("next one is H_v1", msgs["dag/Assumptions/Toy_asm/H_v2.json"])

    def test_stale_after_merge(self):
        self.assertEqual(statuses(state["outs"][2]), {"dag/Assumptions/Toy_asm/H_v2.json": "WA"})
        self.assertEqual(statuses(state["outs"][3]), {"dag/Assumptions/Toy_asm/H_v2.json": "OK"})

    def test_strength_and_index(self):
        dag = D.Dag(state["merged"])
        self.assertEqual(dag.strength("Toy_asm")["H"], "Toy.H1")
        self.assertEqual(dag.strength("Toy_swapped")["version"], 0)
        ix = T.index(dag, D.read_records(state["tmp"] / "records"))
        a = {x["name"]: x for x in ix["assumptions"]}
        self.assertEqual((a["Toy.asm"]["version"], a["Toy.asm"]["H"]), (1, "Toy.H1"))
        self.assertEqual(a["Toy.swapped"]["H"], "Toy.swapped.H")
        self.assertIn("## Assumptions", T.index_markdown(ix))


if __name__ == "__main__":
    unittest.main()
