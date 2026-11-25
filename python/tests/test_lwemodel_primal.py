"""Cross-language primal costs and optional pinned Sage estimator regression checks."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from common import REPO
from lwemodel import fx, nd
from lwemodel.params import LWE
from lwemodel.primal_bdd import primal_bdd
from lwemodel.primal_hybrid import cost_bdd, cost_mitm


def costs(n):
    e = nd.cbd(3 if n == 512 else 2)
    p = LWE(n, 3329, e, e, n)
    return [attack(p) for attack in (primal_bdd, cost_bdd, cost_mitm)]


class TestPrimal(unittest.TestCase):
    def test_lean_mirrors(self):
        source = ["import SigabaNeoStd.Lattices.Estimator.PrimalBdd",
                  "open SigabaNeo.Lattices.Estimator"]
        expected = []
        for n in (512, 768, 1024):
            e = f"(ND.cbd {3 if n == 512 else 2})"
            for attack in ("PrimalBdd.cost", "PrimalHybrid.costBdd", "PrimalHybrid.costMitm"):
                source.append(f"#eval ({attack} (LWEParams.mk' {n} 3329 {e} {e} (some {n}))).get!")
            expected.extend(costs(n))
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Check.lean"
            path.write_text("\n".join(source) + "\n")
            result = subprocess.run(["lake", "env", "lean", str(path)], cwd=REPO,
                                    capture_output=True, text=True, timeout=240)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual([int(line) for line in result.stdout.splitlines()], expected)

    def test_fast_profile(self):
        # `profile` skips the blocks above the cut-off and sums the underflowed tail in one step;
        # it must equal the block-by-block definition (`profile_slow`, `NumPrimal.profile`).
        import random
        from lwemodel import num_primal
        rng = random.Random(7)
        for _ in range(500):
            k = rng.randrange(0, 6000)
            step = rng.randrange(1, fx.ONE // 8)
            first = rng.randrange(-70 * fx.ONE, 120 * fx.ONE)
            mitm = rng.random() < 0.5
            self.assertEqual(num_primal.profile(k, first, step, mitm),
                             num_primal.profile_slow(k, first, step, mitm))

    def test_gaussian_guess_bounds_after_normalization(self):
        # For exactly n samples normalization swaps the Gaussian error into the secret.
        error = nd.gauss(fx.of_rat(32, 10))
        p = LWE(256, 1023, nd.uniform_mod(1023), error, 256)
        self.assertIsNone(primal_bdd(p))
        self.assertIsNone(cost_bdd(p))
        self.assertAlmostEqual(cost_mitm(p) / fx.ONE, 841.8262122574771, delta=0.1)

    @unittest.skipUnless(os.getenv("LWE_ESTIMATOR_SAGE"), "set LWE_ESTIMATOR_SAGE to sage")
    def test_sage_kyber(self):
        # Set PYTHONPATH to the pinned lattice-estimator checkout for this subprocess.
        script = """from estimator import LWE, schemes
from estimator.simulator import GSA
p = schemes.Kyber512
for c in [LWE.primal_bdd(p, red_shape_model=GSA),
          LWE.primal_hybrid(p, red_shape_model=GSA, mitm=False, babai=False),
          LWE.primal_hybrid(p, red_shape_model=GSA, mitm=True, babai=True)]:
    print(float(c['rop'].log(2)))
"""
        result = subprocess.run([os.environ["LWE_ESTIMATOR_SAGE"], "-python", "-c", script],
                                capture_output=True, text=True, check=True, timeout=600)
        for ours, ref in zip(costs(512), map(float, result.stdout.splitlines()), strict=True):
            self.assertAlmostEqual(ours / fx.ONE, ref, delta=0.1)
