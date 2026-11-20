"""The trusted check `#sigaba_neo_check` (through `sigaba_neo.verify`) on the cases and on bad proofs.

    python3 -m unittest discover -s python/tests -p 'test_check.py' -v
"""

from __future__ import annotations

import re
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

from common import cases, load, make_claim
from sigaba_neo import Claim, dev, verify

state: dict = {}


def setUpModule():
    state["tmp"] = Path(tempfile.mkdtemp(prefix="sigaba-neo-check-"))


def tearDownModule():
    shutil.rmtree(state["tmp"], ignore_errors=True)


def run(name: str, claim: Claim, files: dict, theorem: str = "TestCase.Vacuous.refutation") -> dict:
    return verify(state["tmp"] / name, claim, files, "Solution", theorem)


VACUOUS = load("vacuous").claim


def vac(body: str, header: str = "") -> dict:
    return {"Solution.lean": f"import Definitions.Def_Vacuous\n{header}\nnamespace TestCase.Vacuous\n"
                             f"{body}\nend TestCase.Vacuous\n"}


def other(claim: Claim, target: str, hyps: list[str] = (), defs: dict | None = None) -> Claim:
    """Another claim on the same (or the given) definitions."""
    name = re.sub(r"[^A-Za-z0-9_-]", "_", "claim-" + "-".join([target, *hyps]))
    return make_claim(state["tmp"] / name, target, list(hyps), defs or claim.definitions)


class Cases(unittest.TestCase):
    """Every case's proof or refutation is verified, with the expected outcome and referenced
    hypotheses."""

    def test_cases(self):
        for case in cases():
            with self.subTest(case=case.name):
                r = run(case.name, case.claim, case.solution, case.theorem)
                self.assertEqual(r["verdict"], "verified", r)
                self.assertEqual(r["outcome"], case.outcome)
                self.assertEqual(r["referencedHypotheses"], case.referenced)
                self.assertIn("sigaba-neo: verified", r["report"])


class Dev(unittest.TestCase):
    """`sigaba_neo.py dev` makes a claim directory a Lake project in which its files build."""

    def test_dev(self):
        d = state["tmp"] / "dev-claim"
        shutil.copytree(load("vacuous-hyp").claim.dir, d,
                        ignore=shutil.ignore_patterns(".lake", "lake*", "lean-toolchain"))
        dev(d)
        r = subprocess.run(["lake", "build", "Solution"], cwd=d, text=True, capture_output=True)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)


class Negative(unittest.TestCase):
    def rejected(self, name: str, files: dict, why: str, claim: Claim = VACUOUS,
                 theorem: str = "TestCase.Vacuous.refutation"):
        r = run(name, claim, files, theorem)
        self.assertEqual(r["verdict"], "rejected", r)
        self.assertIn(why, r["report"])

    def test_axiom(self):
        self.rejected("axiom", vac("axiom cheat : ¬ TestCase.Vacuous.target\n"
                                   "theorem refutation : ¬ TestCase.Vacuous.target := cheat"),
                      "TestCase.Vacuous.cheat")

    def test_sorry(self):
        self.rejected("sorry", vac("theorem refutation : ¬ TestCase.Vacuous.target := by sorry"),
                      "sorryAx")

    def test_native_decide(self):
        self.rejected("native", vac("theorem refutation : ¬ TestCase.Vacuous.target := by\n"
                                    "  have : (2 : Nat) ^ 10 = 1024 := by native_decide\n"
                                    "  exact fun h => h"), "native_decide")

    def test_weakened(self):
        self.rejected("weakened", vac("theorem refutation : TestCase.Vacuous.strong := trivial"),
                      "none of the claims")

    def test_tampered_definitions(self):
        """The workspace's copies of the claim's definitions must be the claim's files."""
        d = state["tmp"] / "tampered"
        r = run("tampered", VACUOUS, vac("theorem refutation : ¬ TestCase.Vacuous.target := "
                                         "fun h => h"))
        self.assertEqual(r["verdict"], "verified", r)
        copy = d / "Definitions" / "Def_Vacuous.lean"
        copy.write_text(copy.read_text() + "\n-- changed\n")
        out = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=d, text=True,
                             capture_output=True, input="import SigabaNeo.Trusted.Check\n"
                             f'#sigaba_neo_check "{VACUOUS.dir}" "Solution" "TestCase.Vacuous.refutation"\n')
        self.assertIn("is not the claim's", out.stdout)

    def test_missing(self):
        self.rejected("missing", vac("theorem refutation' : ¬ TestCase.Vacuous.target := "
                                     "fun h => h"), "no theorem TestCase.Vacuous.refutation")

    def test_text_macro(self):
        """The claim is an expression built from names: a macro in the solution, or one in the
        submitter's definitions that turns `¬ t` into `True` when elaborated from text, cannot
        weaken it."""
        self.rejected("macro", vac("theorem refutation : TestCase.Vacuous.strong := trivial",
                                   header="syntax \"#sigaba_neo_check\" : command\n"
                                          "macro_rules | `(#sigaba_neo_check) => `(section end)"),
                      "none of the claims")
        echo = load("echo").claim
        macro = other(echo, echo.target, [], {**echo.definitions, "Macro":
                                              "import Definitions.Def_Echo\n"
                                              "macro_rules | `(¬ $_t) => `(True)\n"})
        self.rejected("submission-macro", {"Solution.lean": "import Definitions.Def_Macro\n"
                                           "theorem TestCase.Echo.refutation : ¬ TestCase.Echo.target "
                                           ":= trivial\n"}, "none of the claims", claim=macro,
                      theorem="TestCase.Echo.refutation")

    def test_target_from_solution(self):
        """The claim's constants must come from the submitter's definitions."""
        self.rejected("target-elsewhere", vac(
            "def _root_.TestCase.Vacuous.nothere : Prop := False\n"
            "theorem refutation : ¬ TestCase.Vacuous.nothere := fun h => h"),
            "not declared by the claim's definitions",
            claim=other(VACUOUS, "TestCase.Vacuous.nothere"))

    def test_kernel_bypass(self):
        """A declaration added without the kernel's check, in a downloaded definition module (not
        the submitter's), is caught by the replay."""
        files = {"Definitions/Def_Evil.lean":
                 "import Lean\nopen Lean in\nset_option debug.skipKernelTC true in\n"
                 "run_meta addDecl (Declaration.thmDecl { name := `TestCase.Evil.bad, levelParams := [], "
                 "type := mkConst ``False, value := mkConst ``True.intro })\n",
                 **vac("theorem refutation : ¬ TestCase.Vacuous.strong := TestCase.Evil.bad.elim",
                       header="import Definitions.Def_Evil")}
        self.rejected("bypass", files, "kernel", claim=other(VACUOUS, "TestCase.Vacuous.strong"))

    def test_eta_and_negated(self):
        """A constant proof (not a λ) of a claim with two hypotheses, and a disproof."""
        claim = other(VACUOUS, "TestCase.Vacuous.strong",
                      ["TestCase.Vacuous.target", "TestCase.Echo.target"])
        r = run("eta", claim, vac(
            "theorem aux (h₀ : TestCase.Vacuous.target) (h₁ : TestCase.Echo.target) : "
            "¬ TestCase.Vacuous.strong := fun _ => h₀.elim\n"
            "theorem refutation : ∀ (h₀ : TestCase.Vacuous.target) (h₁ : TestCase.Echo.target),"
            " ¬ TestCase.Vacuous.strong := aux"))
        self.assertEqual(r["verdict"], "verified", r)
        self.assertEqual(r["referencedHypotheses"], ["h₀", "h₁"])
        r = run("negated", other(VACUOUS, "TestCase.Vacuous.target", ["TestCase.Vacuous.strong"]),
                vac("theorem refutation : ¬ (TestCase.Vacuous.strong → TestCase.Vacuous.target) "
                    ":= fun h => h trivial"))
        self.assertEqual(r["verdict"], "verified", r)
        self.assertEqual(r["established"],
                         "¬ (TestCase.Vacuous.strong → TestCase.Vacuous.target)")
        self.assertEqual(r["outcome"], "refuted")


    def test_hypothesis_axioms(self):
        """An assembled proof states a hypothesis card as an axiom: an axiom whose type is a
        hypothesis (`H` or `¬ H`) is the hypothesis, in a claim that is not negated."""
        claim = other(VACUOUS, "TestCase.Vacuous.strong", ["TestCase.Vacuous.target"])
        r = run("hyp-axiom", claim, vac(
            "axiom hyp : TestCase.Vacuous.target\n"
            "theorem refutation (h₀ : TestCase.Vacuous.target) : ¬ TestCase.Vacuous.strong :="
            " fun _ => hyp.elim"))
        self.assertEqual(r["verdict"], "verified", r)
        self.assertEqual(r["referencedHypotheses"], ["h₀"])
        self.assertEqual(r["hypothesisAxioms"], ["TestCase.Vacuous.hyp"])
        self.assertIn("hypothesis axioms: TestCase.Vacuous.hyp", r["report"])
        neg = other(VACUOUS, "TestCase.Vacuous.strong", ["¬ TestCase.Vacuous.strong"])
        r = run("hyp-axiom-neg", neg, vac(
            "axiom hyp : ¬ TestCase.Vacuous.strong\n"
            "theorem refutation (h₀ : ¬ TestCase.Vacuous.strong) : ¬ TestCase.Vacuous.strong := hyp"))
        self.assertEqual(r["verdict"], "verified", r)
        self.assertEqual(r["established"], "(¬ TestCase.Vacuous.strong) → ¬ TestCase.Vacuous.strong")
        self.assertEqual(r["outcome"], "refuted")
        # Not in a negated claim: `¬ (H → C)` does not follow from an axiom `H`.
        self.rejected("hyp-axiom-negated", vac(
            "axiom hyp : TestCase.Vacuous.strong\n"
            "theorem refutation : ¬ (TestCase.Vacuous.strong → TestCase.Vacuous.target) := "
            "fun h => h hyp"), "depends on the axiom TestCase.Vacuous.hyp",
            claim=other(VACUOUS, "TestCase.Vacuous.target", ["TestCase.Vacuous.strong"]))
        # Nor of another type.
        self.rejected("hyp-axiom-other", vac(
            "axiom hyp : False\n"
            "theorem refutation (h₀ : TestCase.Vacuous.target) : ¬ TestCase.Vacuous.strong :="
            " fun _ => hyp.elim"), "depends on the axiom TestCase.Vacuous.hyp", claim=claim)


if __name__ == "__main__":
    unittest.main()
