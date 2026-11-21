"""Noise distributions of the lattice estimator (estimator/nd.py), the subset used here; mirror of
SigabaNeo/Lib/Lattices/Estimator/ND.lean. Numbers are fixed point (fx)."""

from __future__ import annotations

import math
from dataclasses import dataclass, replace

from . import fx


@dataclass(frozen=True)
class ND:
    """kind: "gauss" (arg: stddev, fixed point), "cbd" (arg: eta), "uniform" (arg: (a, b));
    n: number of coefficients (None: unspecified)."""
    kind: str
    arg: object
    n: int | None = None

    # ---- derived quantities (estimator fields)
    @property
    def stddev(self) -> int:
        if self.kind == "gauss":
            return self.arg
        if self.kind == "cbd":
            return fx.sqrt(fx.of_rat(self.arg, 2))
        a, b = self.arg
        m = b - a + 1
        return fx.sqrt(fx.of_rat(m * m - 1, 12))

    @property
    def mean(self) -> int:
        if self.kind == "uniform":
            a, b = self.arg
            return fx.of_rat(a + b, 2)
        return 0

    @property
    def bounds(self):
        """(lo, hi) integers, or None if unbounded."""
        if self.kind == "gauss":
            # the estimator's resize keeps the default constructor's infinite bounds
            return None
        if self.kind == "cbd":
            return (-self.arg, self.arg)
        return self.arg

    @property
    def density(self) -> int:
        if self.kind == "gauss":
            return max(0, fx.ONE - fx.div(fx.ONE, fx.mul(fx.SQRT2PI, self.arg)))
        if self.kind == "cbd":
            e = self.arg
            return fx.ONE - fx.of_rat(math.comb(2 * e, e), 4 ** e)
        a, b = self.arg
        m = b - a + 1
        return fx.ONE - fx.of_rat(1, m) if a <= 0 <= b else fx.ONE

    @property
    def is_bounded(self) -> bool:
        return self.bounds is not None

    @property
    def is_sparse(self) -> bool:
        return self.density < fx.ONE // 2

    @property
    def is_gaussian_like(self) -> bool:
        return self.kind in ("gauss", "cbd")

    def resize(self, n: int) -> "ND":
        return replace(self, n=n)

    def hamming_weight(self) -> int:
        # round(len * density)
        return (2 * self.n * self.density + fx.ONE) >> (fx.P + 1)


def gauss(stddev: int, n=None) -> ND:
    return ND("gauss", stddev, n)


def cbd(eta: int, n=None) -> ND:
    return ND("cbd", eta, n)


def uniform(a: int, b: int, n=None) -> ND:
    return ND("uniform", (a, b), n)


def uniform_mod(q: int, n=None) -> ND:
    a = -(q // 2)
    return ND("uniform", (a, a + q - 1), n)
