"""`ModuleLWE.H` at the Kyber parameter sets meets the security levels of the Kyber specification.

Kyber (Round 3 specification, Table 4) claims classical Core-SVP hardness 118, 182 and 256 bits for
Kyber512, Kyber768 and Kyber1024 (the module-LWE part, without the rounding of the ciphertext).
`H` is the floor of the cheapest attack of the lattice estimator in its default cost model
(docs/LWE_ESTIMATOR.md); the estimator itself reports 139.7, 196.4 and 262.3 (dual_hybrid).
NIST categories 1/3/5 compare against AES key search (≈ 143/207/272 bits of gates); those are
recorded, not asserted, since the estimator's model does not reach them for Kyber512/768/1024
(a known, public gap that NIST's evaluation attributes to the cost of memory access).
"""

from __future__ import annotations

import subprocess
import tempfile
import unittest
from pathlib import Path

from common import REPO

KYBER = {  # name: (rank, eta1 (secret), eta (error), spec Core-SVP bits, NIST category gates)
    "kyber512": (2, 3, 3, 118, 143),
    "kyber768": (3, 2, 2, 182, 207),
    "kyber1024": (4, 2, 2, 256, 272),
}


class Kyber(unittest.TestCase):

    def test_spec_levels(self):
        lines = ["import SigabaNeoStd.Lattices.ModuleLWE", "open SigabaNeo.Lattices"]
        for name, (k, es, ee, _, _) in KYBER.items():
            lines.append(f"#eval ModuleLWE.H {{ N := 256, rank := {k}, m := {k}, q := 3329, "
                         f"error := .cbd {ee}, secret := .cbd {es} }}")
        with tempfile.TemporaryDirectory() as d:
            f = Path(d) / "K.lean"
            f.write_text("\n".join(lines) + "\n")
            r = subprocess.run(["lake", "env", "lean", str(f)], cwd=REPO, capture_output=True,
                               text=True, timeout=1800)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        bits = [int(x) for x in r.stdout.split()]
        self.assertEqual(bits, [139, 196, 262])
        for h, (name, (_, _, _, spec, _)) in zip(bits, KYBER.items()):
            self.assertGreaterEqual(h, spec, name)


if __name__ == "__main__":
    unittest.main()
