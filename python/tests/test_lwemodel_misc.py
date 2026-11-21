"""Exact Lean/Python costs and optional pinned Sage comparisons for four LWE models."""
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

from common import REPO
from lwemodel import arora_gb, bkw, fx, guess, nd
from lwemodel.params import LWE


MODELS = (("Bkw.cost", bkw.cost), ("AroraGB.cost", arora_gb.cost),
          ("Guess.exhaustiveCost", guess.exhaustive_cost), ("Guess.mitmCost", guess.mitm_cost))


def points():
    for n, eta in [(512, 3), (768, 2), (1024, 2)]:
        yield (LWE(n, 3329, nd.cbd(eta), nd.cbd(eta), n),
               f"LWEParams.mk' {n} 3329 (ND.cbd {eta}) (ND.cbd {eta}) (some {n})")
    yield (LWE(64, 1023, nd.uniform(-1,1), nd.uniform(-1,1)),
           "LWEParams.mk' 64 1023 (ND.uniform (-1) 1) (ND.uniform (-1) 1) none")
    yield (LWE(256, 1023, nd.uniform(-1,1), nd.gauss(fx.of_rat(12,10))),
           "LWEParams.mk' 256 1023 (ND.uniform (-1) 1) (ND.gauss (Fx.ofRat 12 10)) none")


class MiscModels(unittest.TestCase):
    def test_exact_mirrors(self):
        source = [f"import SigabaNeo.Lib.Lattices.Estimator.{mod}" for mod in ("Bkw","Guess","AroraGB")]
        source.append("open SigabaNeo.Lattices.Estimator")
        expected = []
        for p, expr in points():
            for name, model in MODELS:
                source.append(f"#eval ({name} ({expr})).getD (-1)")
                v = model(p)
                expected.append(-1 if v is None else v)
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "Misc.lean"
            path.write_text("\n".join(source))
            out = subprocess.run(["lake","env","lean",str(path)], cwd=REPO, check=True,
                                 capture_output=True, text=True, timeout=180)
        self.assertEqual([int(v) for v in out.stdout.splitlines()], expected)

    @unittest.skipUnless(os.getenv("SAGE_ESTIMATOR"), "requires estimator on Sage PYTHONPATH")
    def test_sage(self):
        from estimator import schemes, LWE as SageLWE, ND
        from estimator.errors import InsufficientSamplesError
        from estimator.lwe_guess import guess_composition, exhaustive_search, mitm
        from sage.all import oo, log
        refs = [schemes.Kyber512, schemes.Kyber768, schemes.Kyber1024,
                SageLWE.Parameters(64,1023,ND.Uniform(-1,1),ND.Uniform(-1,1),oo),
                SageLWE.Parameters(256,1023,ND.Uniform(-1,1),ND.DiscreteGaussian(1.2),oo)]
        attacks = [SageLWE.coded_bkw,guess_composition(SageLWE.arora_gb),exhaustive_search,mitm]
        for (p,_), ref in zip(points(),refs):
            for (name,model),attack in zip(MODELS,attacks):
                with self.subTest(n=p.n,attack=name):
                    try:
                        bits = log(attack(ref)["rop"],2)
                    except InsufficientSamplesError:
                        bits = oo
                    ours = model(p)
                    if bits == oo:
                        self.assertIsNone(ours)
                    else:
                        self.assertAlmostEqual(ours/fx.ONE, float(bits), delta=0.1)
