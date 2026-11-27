"""The trusted checks of certified task generators (`SigabaNeo.Trusted.GeneratorCheck`) on the
bootstrap fixtures of `tests/generators/` and of `SigabaNeoStd.Benchmarks.Families`.

    python3 -m unittest discover -s python/tests -p 'test_benchmark.py' -v

A temporary Lake workspace requires this core and holds the fixture generators (`Generators.*`)
and, once a task is sampled, a solver's modules (`Solvers.*`). The commands run outside the
workspace's configuration, with the core's Lean and search path (`sigaba_neo.trusted_lean`) and the
workspace's build outputs, in the workspace (whose modules are therefore local and replayed).
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

from common import REPO
from sigaba_neo import CORE, trusted_lean

GENERATORS = REPO / "tests" / "generators"
DESIGN = "SigabaNeo.Benchmark.Fixture.avoidDesignFamily"
ATTACK = "SigabaNeo.Benchmark.Fixture.avoidAttackFamily"

state: dict = {}


def lean_env(ws: Path) -> dict:
    _, path = trusted_lean()
    env = {k: v for k, v in os.environ.items() if k not in ("LEAN_PATH", "LEAN_SRC_PATH")}
    return {**env, "LEAN_PATH": path + os.pathsep + str(ws / ".lake" / "build" / "lib" / "lean")}


def make_workspace(d: Path) -> Path:
    """A Lake workspace that requires the core and holds the fixture generators."""
    d.mkdir(parents=True)
    (d / "lakefile.toml").write_text(
        f'name = "bench"\n\n[[require]]\nname = "SigabaNeo"\npath = {json.dumps(str(CORE))}\n\n'
        '[[lean_lib]]\nname = "Generators"\n\n[[lean_lib]]\nname = "Solvers"\n')
    manifest = json.loads((CORE / "lake-manifest.json").read_text())
    manifest.update(name="bench", packages=[
        {"type": "path", "scope": "", "name": "SigabaNeo", "manifestFile": "lake-manifest.json",
         "inherited": False, "dir": str(CORE), "configFile": "lakefile.toml"},
        *[dict(p, inherited=True) for p in manifest["packages"]]])
    (d / "lake-manifest.json").write_text(json.dumps(manifest, indent=1))
    (d / "lean-toolchain").write_text((CORE / "lean-toolchain").read_text())
    (d / ".lake" / "packages").mkdir(parents=True)
    for p in (CORE / ".lake" / "packages").iterdir():
        (d / ".lake" / "packages" / p.name).symlink_to(p)
    shutil.copy(GENERATORS / "Generators.lean", d / "Generators.lean")
    shutil.copytree(GENERATORS / "Generators", d / "Generators")
    return d


def build(ws: Path, *targets: str) -> None:
    env = {k: v for k, v in os.environ.items() if k not in ("LEAN_PATH", "LEAN_SRC_PATH")}
    b = subprocess.run(["lake", "build", *targets], cwd=ws, env=env, text=True,
                       capture_output=True)
    if b.returncode != 0:
        raise AssertionError("build failed:\n" + (b.stdout + b.stderr)[-4000:])


BATCH = 4     # commands per Lean process: each import holds a whole environment in memory


def run_commands(commands: list[str], result_file: str | None = None) -> list[dict]:
    """Run trusted commands, a few per Lean process; one parsed report per command (and, with
    `result_file`, the last command's JSON file as `file`)."""
    out = []
    for i in range(0, len(commands), BATCH):
        last = i + BATCH >= len(commands)
        out += _run_batch(commands[i:i + BATCH], result_file if last else None)
    return out


def _run_batch(commands: list[str], result_file: str | None) -> list[dict]:
    ws = state["ws"]
    lean, _ = trusted_lean()
    if result_file:
        (ws / result_file).unlink(missing_ok=True)
    r = subprocess.run([lean, "--stdin"], cwd=ws, env=lean_env(ws), text=True,
                       capture_output=True, timeout=1800,
                       input="import SigabaNeo.Trusted.GeneratorCheck\n" + "\n".join(commands) + "\n")
    out = r.stdout
    if r.returncode != 0 and "sigaba-neo:" not in out:
        raise AssertionError(f"the check did not run (exit {r.returncode}):\n"
                             f"{(out + r.stderr)[-4000:]}")
    chunks = [c for c in re.split(r"(?m)^sigaba-neo: ", out) if c.strip()]
    if len(chunks) != len(commands):
        raise AssertionError(f"expected {len(commands)} reports:\n{out[-4000:]}")
    reports = []
    for c in chunks:
        verdict, _, rest = c.partition("\n")
        rep = {"verdict": verdict.strip(), "report": rest}
        if verdict.strip() != "rejected":
            rep.update(json.loads(rest))
        reports.append(rep)
    if result_file:
        reports[-1]["file"] = json.loads((ws / result_file).read_text())
    return reports


def gen_check(module: str, family: str, gen: str, cert: str, L: int, k: int, h: int) -> str:
    return (f"#sigaba_generator_check {json.dumps(module)} {json.dumps(family)} {json.dumps(gen)} "
            f"{json.dumps(cert)} {L} {k} {h}")


def sample(module: str, family: str, gen: str, L: int, k: int, level: int, seed: str,
           heartbeats: int | None = None) -> str:
    hb = f" {heartbeats}" if heartbeats is not None else ""
    return (f"#sigaba_generator_sample {json.dumps(module)} {json.dumps(family)} {json.dumps(gen)} "
            f"{L} {k} {level} {json.dumps(seed)}{hb}")


def link(module: str, family: str, gen: str, L: int, k: int, level: int, seed: str,
         bits: str) -> str:
    return (f"#sigaba_generator_link {json.dumps(module)} {json.dumps(family)} {json.dumps(gen)} "
            f"{L} {k} {level} {json.dumps(seed)} {json.dumps(bits)}")


def task_check(module: str, family: str, bits: str, thm: str, forbidden: list[str]) -> str:
    return (f"#sigaba_task_check {json.dumps(module)} {json.dumps(family)} {json.dumps(bits)} "
            f"{json.dumps(thm)}" + "".join(f" {json.dumps(p)}" for p in forbidden))


def setUpModule():
    state["tmp"] = Path(tempfile.mkdtemp(prefix="sigaba-neo-bench-"))
    state["ws"] = make_workspace(state["tmp"] / "ws")
    build(state["ws"], "Generators")


def tearDownModule():
    shutil.rmtree(state["tmp"], ignore_errors=True)


class Certificates(unittest.TestCase):
    """`#sigaba_generator_check`: the exact statement `Certified F L k h gen`, built from the
    policy's family and numbers."""

    @classmethod
    def setUpClass(cls):
        D, A = "Generators.AvoidDesign", "Generators.AvoidAttack"
        dgen, agen = f"{D}.generate", f"{A}.generate"
        cls.cases = {
            # Valid: design (two levels), attack (one level), bounded fiber at h = 4.
            "design": gen_check(D, DESIGN, dgen, f"{D}.certified", 2, 8, 8),
            "attack": gen_check(A, ATTACK, agen, f"{A}.certified", 1, 8, 8),
            "prefix": gen_check("Generators.Prefix", DESIGN, "Generators.Prefix.generate",
                                "Generators.Prefix.certified", 1, 8, 4),
            # Rejected.
            "prefix-h8": gen_check("Generators.Prefix", DESIGN, "Generators.Prefix.generate",
                                   "Generators.Prefix.certified", 1, 8, 8),
            "constant-h8": gen_check("Generators.Constant", DESIGN, "Generators.Constant.generate",
                                     "Generators.Constant.certified0", 1, 8, 8),
            "design-h4": gen_check(D, DESIGN, dgen, f"{D}.certified", 2, 8, 4),
            "design-one-level": gen_check(D, DESIGN, dgen, f"{D}.certified", 1, 8, 8),
            "attack-missing-level": gen_check(A, ATTACK, agen, f"{A}.certified", 2, 8, 8),
            "wrong-family": gen_check("Generators.WrongFamily", DESIGN, dgen,
                                      "Generators.WrongFamily.certified", 2, 8, 8),
            "own-family": gen_check("Generators.OwnFamily", "Generators.OwnFamily.permissive", dgen,
                                    "Generators.OwnFamily.certified", 2, 8, 8),
            "sorry": gen_check("Generators.Sorry", DESIGN, dgen, "Generators.Sorry.certified",
                               2, 8, 8),
            "axiom": gen_check("Generators.Axiom", DESIGN, dgen, "Generators.Axiom.certified",
                               2, 8, 8),
            "sampled-only": gen_check("Generators.SampledOnly", DESIGN, dgen,
                                      "Generators.SampledOnly.certified", 2, 8, 8),
            "not-a-family": gen_check(D, f"{D}.word", dgen, f"{D}.certified", 2, 8, 8),
        }
        names = list(cls.cases)
        cls.results = dict(zip(names, run_commands([cls.cases[n] for n in names],
                                                   "generator-result.json")))

    def verdict(self, name: str) -> dict:
        return self.results[name]

    def test_valid(self):
        for name, (L, k, h) in {"design": (2, 8, 8), "attack": (1, 8, 8),
                                "prefix": (1, 8, 4)}.items():
            with self.subTest(name):
                r = self.verdict(name)
                self.assertEqual(r["verdict"], "certified", r)
                self.assertEqual((r["levels"], r["seedBits"], r["diversityBits"]), (L, k, h))
                self.assertLessEqual(set(r["axioms"]), {"propext", "Classical.choice",
                                                        "Quot.sound"})

    def test_result_file(self):
        """The last command's result is written to `generator-result.json`."""
        r = self.results["not-a-family"]
        self.assertEqual(r["file"]["verdict"], "rejected")

    def rejected(self, name: str, why: str):
        r = self.verdict(name)
        self.assertEqual(r["verdict"], "rejected", r)
        self.assertIn(why, r["report"])

    def test_constant_generator(self):
        """A constant generator is certified at h = 0 only (L11); the policy's h = 8 rejects it."""
        self.rejected("constant-h8", "is not SigabaNeo.Benchmark.Certified")

    def test_wrong_diversity(self):
        """The certificate's h is the policy's: neither more (prefix at 8) nor less (design at 4)."""
        self.rejected("prefix-h8", "is not SigabaNeo.Benchmark.Certified")
        self.rejected("design-h4", "is not SigabaNeo.Benchmark.Certified")

    def test_levels(self):
        """Every advertised level is covered: a generator of one level does not pass a policy of two
        levels, nor two levels one (L09, L12)."""
        self.rejected("attack-missing-level", "is not SigabaNeo.Benchmark.Certified")
        self.rejected("design-one-level", "is not SigabaNeo.Benchmark.Certified")

    def test_family(self):
        """The family is the policy's: a true certificate for another family, or for a family the
        generator defines itself (its own `Solvable` and `SameProblem`), is rejected."""
        self.rejected("wrong-family", "is not SigabaNeo.Benchmark.Certified")
        self.rejected("own-family", "is declared in the workspace")
        self.rejected("not-a-family", "is not a family")

    def test_sorry_and_axioms(self):
        self.rejected("sorry", "sorryAx")
        self.rejected("axiom", "Generators.Axiom.cheat")

    def test_sampled_only(self):
        """Solvability at one sampled seed is not the universal certificate (L09)."""
        self.rejected("sampled-only", "is not SigabaNeo.Benchmark.Certified")


class Sampling(unittest.TestCase):
    """`#sigaba_generator_sample`: the evaluated descriptor, linked by the kernel (L13)."""

    @classmethod
    def setUpClass(cls):
        D, A = "Generators.AvoidDesign", "Generators.AvoidAttack"
        dgen, agen = f"{D}.generate", f"{A}.generate"
        slow = ("Generators.Slow", DESIGN, "Generators.Slow.generate", 1, 8, 0, "10110011")
        cls.cases = {
            "design-1": sample(D, DESIGN, dgen, 2, 8, 1, "10110010"),
            "design-1-again": sample(D, DESIGN, dgen, 2, 8, 1, "10110010"),
            "design-0": sample(D, DESIGN, dgen, 2, 8, 0, "10110010"),
            "design-other-seed": sample(D, DESIGN, dgen, 2, 8, 1, "00000001"),
            "attack": sample(A, ATTACK, agen, 1, 8, 0, "11111111"),
            "level-out-of-range": sample(D, DESIGN, dgen, 2, 8, 2, "10110010"),
            "seed-width": sample(D, DESIGN, dgen, 2, 8, 1, "1011001"),
            "seed-digits": sample(D, DESIGN, dgen, 2, 8, 1, "1011001x"),
            "mismatch": sample("Generators.Mismatch", DESIGN, "Generators.Mismatch.generate",
                               1, 8, 0, "10110011"),
            "timeout": sample(*slow, heartbeats=1000),
            "slow-in-budget": sample(*slow),
        }
        names = list(cls.cases)
        cls.results = dict(zip(names, run_commands([cls.cases[n] for n in names],
                                                   "sample-result.json")))

    def test_linked(self):
        r = self.results["design-1"]
        self.assertEqual(r["verdict"], "linked", r)
        # Level 1: one zero, a one, then the seed bits.
        self.assertEqual(r["descriptor"], "0" + "1" + "10110010")
        self.assertEqual(self.results["design-0"]["descriptor"], "1" + "10110010")
        self.assertEqual(self.results["design-other-seed"]["descriptor"], "0100000001")
        self.assertEqual(self.results["attack"]["descriptor"], "111111111")
        self.assertEqual(self.results["slow-in-budget"]["descriptor"], "110110011")

    def test_deterministic(self):
        a, b = self.results["design-1"], self.results["design-1-again"]
        self.assertEqual(a["descriptor"], b["descriptor"])

    def test_result_file(self):
        self.assertEqual(self.results["slow-in-budget"]["file"]["verdict"], "linked")

    def rejected(self, name: str, why: str):
        r = self.results[name]
        self.assertEqual(r["verdict"], "rejected", r)
        self.assertIn(why, r["report"])

    def test_rejected(self):
        self.rejected("level-out-of-range", "is not supported")
        self.rejected("seed-width", "has 7 bits, not 8")
        self.rejected("seed-digits", "not a string of 0 and 1")
        # The compiled code (`implemented_by`) disagrees with the definition.
        self.rejected("mismatch", "the kernel does not confirm")
        self.rejected("timeout", "deterministic timeout")


class Linking(unittest.TestCase):
    """`#sigaba_generator_link`: the kernel's check of a given descriptor, with no generator code
    run (the runner links the sampler's output in a separate process)."""

    @classmethod
    def setUpClass(cls):
        D, M = "Generators.AvoidDesign", "Generators.Mismatch"
        cls.cases = {
            "good": link(D, DESIGN, f"{D}.generate", 2, 8, 1, "10110010", "0110110010"),
            "wrong-bits": link(D, DESIGN, f"{D}.generate", 2, 8, 1, "10110010", "1110110010"),
            "bad-digits": link(D, DESIGN, f"{D}.generate", 2, 8, 1, "10110010", "01x"),
            "level": link(D, DESIGN, f"{D}.generate", 2, 8, 2, "10110010", "0110110010"),
            # The compiled code would print 0 then the seed; the definition gives 1 then the seed.
            "mismatch-compiled": link(M, DESIGN, f"{M}.generate", 1, 8, 0, "10110011",
                                      "010110011"),
            "mismatch-definition": link(M, DESIGN, f"{M}.generate", 1, 8, 0, "10110011",
                                        "110110011"),
        }
        names = list(cls.cases)
        cls.results = dict(zip(names, run_commands([cls.cases[n] for n in names],
                                                   "link-result.json")))

    def test_link(self):
        r = self.results["good"]
        self.assertEqual(r["verdict"], "linked", r)
        self.assertEqual(r["descriptor"], "0110110010")
        self.assertFalse(r["evaluated"])
        self.assertEqual(self.results["mismatch-definition"]["verdict"], "linked")
        self.assertEqual(self.results["mismatch-definition"]["file"]["verdict"], "linked")

    def test_rejected(self):
        for name, why in (("wrong-bits", "the kernel does not confirm"),
                          ("bad-digits", "not a string of 0 and 1"),
                          ("level", "is not supported"),
                          ("mismatch-compiled", "the kernel does not confirm")):
            r = self.results[name]
            self.assertEqual(r["verdict"], "rejected", (name, r))
            self.assertIn(why, r["report"])


class Solutions(unittest.TestCase):
    """`#sigaba_task_check`: a solver's theorem of `Target F <descriptor>`, without the generator's
    modules (L18)."""

    @classmethod
    def setUpClass(cls):
        (s,) = run_commands([sample("Generators.AvoidDesign", DESIGN,
                                    "Generators.AvoidDesign.generate", 2, 8, 1, "01100111")])
        assert s["verdict"] == "linked", s
        cls.bits = s["descriptor"]
        lit = "[" + ", ".join("true" if c == "1" else "false" for c in cls.bits) + "]"
        other = "[" + ", ".join(["true"] * len(cls.bits)) + "]"
        ws = state["ws"]
        (ws / "Solvers").mkdir(exist_ok=True)
        body = ("open SigabaNeo.Benchmark SigabaNeo.Benchmark.Fixture\n\n"
                "theorem solve : Target avoidDesignFamily {lit} :=\n"
                "  avoidDesign_target (by decide) (by simp)\n")
        (ws / "Solvers" / "Good.lean").write_text(
            "import SigabaNeoStd.Benchmarks.Families.AvoidWordDesign\n\n"
            "namespace Solvers.Good\n\n" + body.format(lit=lit) + "\nend Solvers.Good\n")
        (ws / "Solvers" / "Leaky.lean").write_text(
            "import Generators.AvoidDesign\n\nnamespace Solvers.Leaky\n\n" + body.format(lit=lit)
            + "\nend Solvers.Leaky\n")
        (ws / "Solvers" / "WrongTarget.lean").write_text(
            "import SigabaNeoStd.Benchmarks.Families.AvoidWordDesign\n\n"
            "namespace Solvers.WrongTarget\n\n" + body.format(lit=other)
            + "\nend Solvers.WrongTarget\n")
        (ws / "Solvers" / "Sorry.lean").write_text(
            "import SigabaNeoStd.Benchmarks.Families.AvoidWordDesign\n\n"
            "namespace Solvers.Sorry\n\nopen SigabaNeo.Benchmark SigabaNeo.Benchmark.Fixture\n\n"
            f"theorem solve : Target avoidDesignFamily {lit} := by sorry\n\nend Solvers.Sorry\n")
        build(ws, "Solvers.Good", "Solvers.Leaky", "Solvers.WrongTarget", "Solvers.Sorry")
        forbid = ["Generators"]
        cls.cases = {
            "good": task_check("Solvers.Good", DESIGN, cls.bits, "Solvers.Good.solve", forbid),
            "leaky": task_check("Solvers.Leaky", DESIGN, cls.bits, "Solvers.Leaky.solve", forbid),
            "wrong-target": task_check("Solvers.WrongTarget", DESIGN, cls.bits,
                                       "Solvers.WrongTarget.solve", forbid),
            "wrong-family": task_check("Solvers.Good", ATTACK, cls.bits, "Solvers.Good.solve",
                                       forbid),
            "sorry": task_check("Solvers.Sorry", DESIGN, cls.bits, "Solvers.Sorry.solve", forbid),
        }
        names = list(cls.cases)
        cls.results = dict(zip(names, run_commands([cls.cases[n] for n in names],
                                                   "task-result.json")))

    def test_sampled_descriptor(self):
        self.assertEqual(self.bits, "0" + "1" + "01100111")

    def test_good(self):
        r = self.results["good"]
        self.assertEqual(r["verdict"], "solved", r)
        self.assertEqual(r["descriptor"], self.bits)

    def rejected(self, name: str, why: str):
        r = self.results[name]
        self.assertEqual(r["verdict"], "rejected", r)
        self.assertIn(why, r["report"])

    def test_rejected(self):
        self.rejected("leaky", "forbidden module Generators.AvoidDesign")
        self.rejected("wrong-target", "is not SigabaNeo.Benchmark.Target")
        self.rejected("wrong-family", "is not SigabaNeo.Benchmark.Target")
        self.rejected("sorry", "sorryAx")
        self.assertEqual(self.results["sorry"]["file"]["verdict"], "rejected")


if __name__ == "__main__":
    unittest.main()
