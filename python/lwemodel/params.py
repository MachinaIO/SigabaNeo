"""LWE parameters of the lattice estimator (estimator/lwe_parameters.py); mirror of
SigabaNeo/Lib/Lattices/Estimator/Params.lean."""

from __future__ import annotations

from dataclasses import dataclass

from .nd import ND


@dataclass(frozen=True)
class LWE:
    n: int
    q: int
    Xs: ND
    Xe: ND
    m: int | None = None   # None: unlimited samples

    def __post_init__(self):
        object.__setattr__(self, "Xs", self.Xs.resize(self.n))
        if self.m is not None:
            object.__setattr__(self, "Xe", self.Xe.resize(self.m))

    def m_ge(self, k: int) -> bool:
        return self.m is None or self.m >= k

    def normalize(self) -> "LWE":
        """The normal form (estimator `LWEParameters.normalize`)."""
        if self.Xe.stddev < self.Xs.stddev and self.m_ge(2 * self.n):
            m = None if self.m is None else self.m - self.n
            return LWE(self.n, self.q, self.Xe, self.Xe, m)
        if self.Xe.stddev < self.Xs.stddev and self.m == self.n:
            return LWE(self.n, self.q, self.Xe, self.Xs, self.n)
        return self
