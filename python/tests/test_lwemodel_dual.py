"""Check the two computable cost models against Lean and, optionally, pinned Sage."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from common import REPO
from lwemodel import dual, dual_hybrid, fx, nd
from lwemodel.params import LWE


class DualModels(unittest.TestCase):
    def test_lean_mirrors(self):
        source = ["import SigabaNeoStd.Lattices.Estimator.Dual",
                  "import SigabaNeoStd.Lattices.Estimator.DualHybrid",
                  "open SigabaNeo.Lattices.Estimator"]
        expected = []
        for n, eta in [(512, 3), (768, 2), (1024, 2)]:
            p = LWE(n, 3329, nd.cbd(eta), nd.cbd(eta), n)
            source.append(f"def p{n} := LWEParams.mk' {n} 3329 "
                          f"⟨.cbd {eta}, none⟩ ⟨.cbd {eta}, none⟩ (some {n})")
            for name, model in [('Dual', dual), ('DualHybrid', dual_hybrid)]:
                source.append(f"#eval ({name}.cost p{n}).getD (-1)")
                expected.append(model.cost(p))
        # This finite-sample point exercises cancellation in Sage's majority amplification.
        gaussian = nd.gauss(fx.of_rat(16, 5))
        p = LWE(256, 1023, gaussian, gaussian, 512)
        source += ["def g : ND := ⟨.gauss (Fx.ofRat 16 5), none⟩",
                   "def gp := LWEParams.mk' 256 1023 g g (some 512)",
                   "#eval (Dual.cost gp).getD (-1)", "#eval (DualHybrid.cost gp).getD (-1)"]
        expected += [dual.cost(p), dual_hybrid.cost(p)]
        with tempfile.TemporaryDirectory() as scratch:
            path = Path(scratch) / 'Check.lean'
            path.write_text('\n'.join(source))
            result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=REPO,
                                    check=True, capture_output=True, text=True, timeout=180)
        self.assertEqual([int(v) for v in result.stdout.splitlines()], expected)

    @unittest.skipUnless(os.getenv('SAGE_ESTIMATOR'), 'requires pinned estimator on Sage PYTHONPATH')
    def test_sage(self):
        from estimator import schemes
        from estimator.lwe_dual import dual as reference, matzov
        from sage.all import log
        for n, eta in [(512, 3), (768, 2), (1024, 2)]:
            p = LWE(n, 3329, nd.cbd(eta), nd.cbd(eta), n)
            instance = getattr(schemes, f'Kyber{n}').normalize()
            for model, attack in [(dual, reference), (dual_hybrid, matzov)]:
                with self.subTest(n=n, model=model.__name__):
                    self.assertAlmostEqual(model.cost(p)/fx.ONE, float(log(attack(instance)['rop'], 2)),
                                           delta=0.1)
