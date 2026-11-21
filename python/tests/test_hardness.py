"""The conservative bound (`SigabaNeo.Lattices.Hardness.securityBits`) agrees with its Python
mirror (`python/lwe_hardness.py`), and `decide +kernel` evaluates it."""

from __future__ import annotations

import subprocess
import tempfile
import unittest
from fractions import Fraction
from pathlib import Path

from common import REPO

import lwe_hardness as L

# (N, rank, m, q, s, secret)
POINTS = [
    (256, 2, 2, 3329, Fraction(307, 100), ("gauss", Fraction(307, 100))),
    (256, 3, 3, 3329, Fraction(5, 2), ("gauss", Fraction(5, 2))),
    (1, 512, 1024, 3329, Fraction(2), ("gauss", Fraction(2))),
    (1, 512, 1024, 3329, Fraction(1), ("gauss", Fraction(1))),
    (1, 1024, 2048, 2 ** 32 - 1, Fraction(8), ("uniform", None)),
    (1, 256, 512, 1023, Fraction(3), ("bounded", 1)),
    (1, 640, 2 ** 64, 2 ** 15, Fraction(7), ("uniform", None)),
    (1024, 1, 1, 12289, Fraction(8), ("gauss", Fraction(8))),
    (2048, 1, 2, 2 ** 54, Fraction(8), ("bounded", 1)),
    (3, 1, 1, 97, Fraction(3), ("uniform", None)),           # not a power of two: 0
    (1, 64, 64, 2 ** 64 - 59, Fraction(1, 2), ("gauss", Fraction(1, 2))),
    (1, 256, 256, 1023, Fraction(1), ("bounded", 1)),        # errors smaller than the secret
]


def lean_q(r: Fraction) -> str:
    return f"({r.numerator} / {r.denominator} : ℚ)"


def lean_secret(sec) -> str:
    kind, arg = sec
    if kind == "uniform":
        return ".uniform"
    if kind == "gauss":
        return f"(.gauss {lean_q(arg)})"
    return f"(.bounded {arg})"


def py_secret(sec) -> L.Secret:
    return L.Secret(sec[0], sec[1])


class Hardness(unittest.TestCase):

    def run_lean(self, text: str) -> str:
        with tempfile.TemporaryDirectory() as d:
            f = Path(d) / "T.lean"
            f.write_text(text)
            r = subprocess.run(["lake", "env", "lean", str(f)], cwd=REPO, capture_output=True,
                               text=True, timeout=900)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        return r.stdout

    def test_mirror(self):
        lines = ["import SigabaNeo.Lib.Lattices.Hardness", "open SigabaNeo.Lattices"]
        for N, rank, m, q, s, sec in POINTS:
            lines.append(f"#eval Hardness.securityBits {N} {rank} {m} {q} "
                         f"{lean_secret(('gauss', s))} {lean_secret(sec)}")
        out = self.run_lean("\n".join(lines) + "\n").split()
        expected = [L.H(N, rank, m, q, L.Secret("gauss", s), py_secret(sec))
                    for N, rank, m, q, s, sec in POINTS]
        self.assertEqual([int(x) for x in out], expected)

    def test_decide(self):
        h = L.H(1, 256, 512, 1023, L.Secret("gauss", Fraction(3)), L.Secret("bounded", 1))
        self.run_lean("\n".join([
            "import SigabaNeo.Lib.Lattices.Hardness",
            "open SigabaNeo.Lattices",
            f"example : {h} ≤ Hardness.securityBits 1 256 512 1023 (.gauss 3) (.bounded 1) :=",
            "  by decide +kernel",
            ""]))
        self.assertGreater(h, 0)


if __name__ == "__main__":
    unittest.main()
