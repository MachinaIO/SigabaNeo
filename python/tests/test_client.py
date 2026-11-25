"""`sigaba_neo.py` on a DAG checkout: `submit` writes the claim's nodes, and `check` assembles and
checks the proofs the DAG holds, whatever they claim to be.

The claim is the echo case (`¬ TestCase.Echo.target` holds).

    python3 -m unittest discover -s python/tests -p 'test_client.py' -v
"""

from __future__ import annotations

import json
import shutil
import tempfile
import unittest
from pathlib import Path

from common import load, make_claim
from sigaba_neo import Claim, DagSource, check, submit

TARGET = "TestCase.Echo.target"
OPENS = "open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM"

DEF_ECHO = f"""import CslibFrontier.Crypto.Computational.PseudorandomFunction

namespace TestCase.EchoP2M
{OPENS}

/-- Query once, output the first bit of the reply. -/
noncomputable def echo : OracleDistinguisher := fun _ _ =>
  (fun reply : List Bool => reply.headD false) <$>
    (List.take 1 <$> ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool) ((), []))

end TestCase.EchoP2M
"""

CHILD_PREAMBLE = f"import Definitions.Def_EchoP2M\n{OPENS}"
CHILD_STATEMENT = "theorem TestCase.EchoP2M.echo_ppt : IsOraclePPT encBool TestCase.EchoP2M.echo := by sorry"
CHILD_SOLUTION = f"""import Definitions.Def_EchoP2M
import CslibFrontier.Tactic.PPT
{OPENS}

theorem solution : IsOraclePPT encBool TestCase.EchoP2M.echo := by
  ppt [TestCase.EchoP2M.echo]
"""

ROOT_SOLUTION = f"""import Definitions.Def_Echo
import Definitions.Def_EchoP2M
import Theorems.Thm_TestCase_EchoP2M_echo_ppt
import CslibFrontier.Crypto.Negligible.Basic

namespace TestCase.EchoSol
{OPENS}

theorem game_echo (b : Bool) (n : ℕ) :
    ProbComp.eval (TestCase.Echo.game b TestCase.EchoP2M.echo n) = PMF.pure b := by
  simp [TestCase.Echo.game, TestCase.EchoP2M.echo]

end TestCase.EchoSol

{OPENS}

theorem solution : ¬ TestCase.Echo.target := by
  intro h
  have hneg := h TestCase.EchoP2M.echo TestCase.EchoP2M.echo_ppt
  simp only [TestCase.EchoSol.game_echo] at hneg
  have hadv : Game.advantage (PMF.pure false) (PMF.pure true) = 1 := by
    simp [Game.advantage, Game.succProbability, NNReal.nndist_eq]
  rw [hadv] at hneg
  exact not_negligible_const one_ne_zero hneg
"""

AXIOM_SOLUTION = """import Definitions.Def_Echo

axiom cheat : ¬ TestCase.Echo.target

theorem solution : ¬ TestCase.Echo.target := cheat
"""

WRONG_SOLUTION = """import Definitions.Def_Echo

theorem solution : True := trivial
"""


state: dict = {}


def setUpModule():
    state["tmp"] = Path(tempfile.mkdtemp(prefix="sigaba-neo-client-"))
    state["claim"] = load("echo").claim


def tearDownModule():
    shutil.rmtree(state["tmp"], ignore_errors=True)


def write(root: Path, rel: str, text: str, meta: dict) -> None:
    p = root / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text)
    p.with_suffix(".json").write_text(json.dumps(meta))


def solution(root: Path, theorem: str, sid: str, text: str, proof_type: str = "prove") -> None:
    write(root, f"dag/Solutions/{theorem.replace('.', '_')}/Sub_{sid}.lean", text,
          {"theorem": theorem, "proof_type": proof_type})


class DagTest(unittest.TestCase):
    def dag(self, name: str) -> tuple[Path, DagSource]:
        """A DAG with the echo claim's definitions and cards (written by `submit`)."""
        root = state["tmp"] / name / "dag"
        root.mkdir(parents=True)
        src = DagSource(root)
        out = submit(src, state["claim"])
        self.assertEqual(len(out["written"]), 3, out)        # the definition and two cards
        return root, DagSource(root)

    def run_check(self, name: str, root: Path) -> dict:
        return check(DagSource(root), state["claim"], state["tmp"] / name / "work")

    def test_submit_twice(self):
        root, src = self.dag("submit")
        self.assertEqual(submit(src, state["claim"])["written"], [])      # already there
        card = src.theorem(state["claim"].name("refute"))
        self.assertTrue(card["formal_statement"].endswith(":= by sorry"))
        self.assertEqual(card["preamble"].strip(), "import Definitions.Def_Echo")

    def test_reduction_proof(self):
        """The refute card is proved by a sketch whose child lemma is proved."""
        root, _ = self.dag("reduction")
        claim = state["claim"]
        write(root, "dag/Definitions/Def_EchoP2M.lean", DEF_ECHO, {"name": "EchoP2M", "title": "e"})
        write(root, "dag/Theorems/Thm_TestCase_EchoP2M_echo_ppt.lean",
              CHILD_PREAMBLE + "\n\n" + CHILD_STATEMENT + "\n",
              {"name": "TestCase.EchoP2M.echo_ppt", "title": "ppt"})
        solution(root, claim.name("refute"), "root", ROOT_SOLUTION)
        solution(root, "TestCase.EchoP2M.echo_ppt", "ppt", CHILD_SOLUTION)
        r = self.run_check("reduction", root)
        self.assertEqual(r["outcome"], "refuted", json.dumps(r, indent=1))
        refute = next(c for c in r["cards"] if c["polarity"] == "refute")
        self.assertTrue(refute["verified"])
        self.assertIn(f"established: ¬ {TARGET}", refute["report"])
        self.assertEqual(refute["nodes"], [refute["theorem_name"], "TestCase.EchoP2M.echo_ppt"])
        prove = next(c for c in r["cards"] if c["polarity"] == "prove")
        self.assertFalse(prove["verified"])

    def test_command_line_as_documented(self):
        """`python3 sigaba_neo.py check CLAIM --dag DAG`, run from python/ as the README says, with
        the default work directory, checks a proof."""
        import subprocess
        import sys
        root, _ = self.dag("cli")
        claim = state["claim"]
        write(root, "dag/Definitions/Def_EchoP2M.lean", DEF_ECHO, {"name": "EchoP2M", "title": "e"})
        write(root, "dag/Theorems/Thm_TestCase_EchoP2M_echo_ppt.lean",
              CHILD_PREAMBLE + "\n\n" + CHILD_STATEMENT + "\n",
              {"name": "TestCase.EchoP2M.echo_ppt", "title": "ppt"})
        solution(root, claim.name("refute"), "root", ROOT_SOLUTION)
        solution(root, "TestCase.EchoP2M.echo_ppt", "ppt", CHILD_SOLUTION)
        python = Path(__file__).resolve().parents[1]
        r = subprocess.run([sys.executable, "sigaba_neo.py", "check", str(claim.dir), "--dag",
                            str(root)], cwd=python, text=True, capture_output=True)
        self.assertEqual(r.returncode, 0, r.stderr[-2000:])
        self.assertIn("== outcome: refuted", r.stdout)
        self.assertFalse((python / "sigaba-neo-work").exists())

    def test_open_child(self):
        """A sketch whose child lemma has no proof is no proof."""
        root, _ = self.dag("open-child")
        claim = state["claim"]
        write(root, "dag/Definitions/Def_EchoP2M.lean", DEF_ECHO, {"name": "EchoP2M", "title": "e"})
        write(root, "dag/Theorems/Thm_TestCase_EchoP2M_echo_ppt.lean",
              CHILD_PREAMBLE + "\n\n" + CHILD_STATEMENT + "\n",
              {"name": "TestCase.EchoP2M.echo_ppt", "title": "ppt"})
        solution(root, claim.name("refute"), "root", ROOT_SOLUTION)
        r = self.run_check("open-child", root)
        self.assertEqual(r["outcome"], "open", json.dumps(r, indent=1))
        refute = next(c for c in r["cards"] if c["polarity"] == "refute")
        self.assertEqual(refute["problems"], ["no complete proof could be assembled from the DAG"])

    def test_axiom_and_wrong_type(self):
        """The DAG's files are not trusted: an axiom, and a solution of another type."""
        root, _ = self.dag("axiom")
        claim = state["claim"]
        solution(root, claim.name("prove"), "wrong", WRONG_SOLUTION)
        solution(root, claim.name("refute"), "axiom", AXIOM_SOLUTION)
        r = self.run_check("axiom", root)
        self.assertEqual(r["outcome"], "open", json.dumps(r, indent=1))
        prove = next(c for c in r["cards"] if c["polarity"] == "prove")
        refute = next(c for c in r["cards"] if c["polarity"] == "refute")
        self.assertFalse(prove["verified"])
        self.assertFalse(refute["verified"])
        self.assertIn("depends on the axiom", refute["report"])


class LayoutTest(unittest.TestCase):
    def test_header_forms(self):
        """The assembled solution keeps its imports above the namespace and its body inside,
        whatever form its header has (a comment spanning lines after an import, `public`)."""
        from sigaba_neo import Download
        claim = state["claim"]
        row = {"theorem_name": claim.name("refute"), "preamble": "", "formal_statement": ""}
        for header in ("import Definitions.Def_Echo /- echo\n  lemmas -/\n",
                       "public import Definitions.Def_Echo\n"):
            with self.subTest(header=header):
                content = header + "\ntheorem solution : ¬ TestCase.Echo.target := sorry\n"
                dl = Download(None, claim, [(row, content)], {})
                files = dl.layout(refute=True)
                sol = next(v for k, v in files.items() if k.startswith("Solutions/"))
                head, _, body = sol.partition("namespace ")
                self.assertEqual(head, "import Definitions.Def_Echo\n")
                import dag as D
                self.assertNotIn("-/", D.strip_comments(body))      # no comment cut in two
                self.assertIn("theorem solution", body)


class ResultFileTest(unittest.TestCase):
    def test_result_is_read_without_following_links(self):
        """The check's result is read only from a regular file in the check directory: a symbolic
        link (to a host file the sandbox cannot see) is not followed."""
        from sigaba_neo import read_regular
        tmp = state["tmp"] / "result-file"
        tmp.mkdir()
        (tmp / "host.json").write_text('{"verdict": "verified"}')
        (tmp / "result.json").symlink_to(tmp / "host.json")
        self.assertIsNone(read_regular(tmp / "result.json"))
        (tmp / "plain.json").write_text('{"verdict": "rejected"}')
        self.assertEqual(read_regular(tmp / "plain.json"), '{"verdict": "rejected"}')
        (tmp / "big.json").write_text("x" * 100)
        self.assertIsNone(read_regular(tmp / "big.json", limit=10))


class SelectTest(unittest.TestCase):
    def test_selectors(self):
        """Hypotheses chosen in the DAG by the maintainers' metadata (meta/assumptions.json)."""
        tmp = state["tmp"] / "select"
        root = tmp / "dag"
        root.mkdir(parents=True)
        src = DagSource(root)
        h = make_claim(tmp / "h", "TestCase.Sel.h", [], {"Sel": "namespace TestCase.Sel\n"
                       "def h : Prop := True\ndef t : Prop := True\nend TestCase.Sel\n"})
        submit(src, h)
        (root / "meta").mkdir()
        (root / "meta" / "assumptions.json").write_text(json.dumps({"claims": {
            h.name("prove"): {"tags": ["well-established"], "proposed_year": 2000}}}))
        c = make_claim(tmp / "c", "TestCase.Sel.t", [], {"Sel": h.definitions["Sel"]})
        cj = json.loads((c.dir / "claim.json").read_text())
        cj["select"] = [{"tag": "well-established", "minYears": 10}]
        (c.dir / "claim.json").write_text(json.dumps(cj))
        submit(DagSource(root), Claim.load(c.dir))
        resolved = Claim.load(c.dir)
        self.assertEqual(resolved.hypotheses, ["TestCase.Sel.h"])
        self.assertEqual(resolved.cards, {"TestCase.Sel.h": h.name("prove")})


if __name__ == "__main__":
    unittest.main()
