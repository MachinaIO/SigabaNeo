"""Primal uSVP attack, GSA shape model (estimator `primal_usvp`, `PrimalUSVP.cost_gsa`); mirror of
SigabaNeo/Lib/Lattices/Estimator/Usvp.lean. The estimator's local search over β is replaced by an
exhaustive scan of the same range, so the result is at most the estimator's."""

from . import fx
from .params import LWE
from .reduction import log2_delta, matzov_bits

MAX_BETA = 1754


def log2_xi(p: LWE) -> int:
    if p.Xs.stddev < p.Xe.stddev:
        return fx.log2(p.Xe.stddev) - fx.log2(p.Xs.stddev)
    return 0


def solve_for_d(p: LWE, m, beta: int, x: int, log2tau: int, l2xi: int, l2q: int):
    """Smallest d ∈ [n, m] satisfying the uSVP condition (a d² + b d + c ≥ 0), or None."""
    se2 = fx.mul(p.Xe.stddev, p.Xe.stddev)
    C = fx.log2(se2 * (beta - 1) + fx.mul(fx.exp2(log2tau), fx.exp2(log2tau))) // 2
    a = -x
    b = x * (2 * beta - 1) + l2q - C
    c = log2tau + p.n * l2xi - (p.n + 1) * l2q
    n = p.n
    if fx.mul(a, fx.of_int(n * n)) + b * n + c >= 0:
        return n
    disc = fx.mul(b, b) - 4 * fx.mul(a, c)
    if disc < 0:
        return None
    d1 = fx.div(-b + fx.sqrt(disc), 2 * a)
    # a < 0: the solution is ceil(d1) if n <= d1
    if fx.of_int(n) <= d1:
        dd = fx.ceil(d1)
        return dd if m is None else min(m, dd)
    return None


def cost_gsa(beta: int, p: LWE, m):
    x = log2_delta(beta)
    l2xi = log2_xi(p)
    log2tau = fx.log2(p.Xe.stddev)
    l2q = fx.log2(fx.of_int(p.q))
    d = solve_for_d(p, m, beta, x, log2tau, l2xi, l2q)
    if d is None:
        return None
    if d < beta:
        d = beta
    if d == beta and (m is None or d < m):
        d += 1
    se2 = fx.mul(p.Xe.stddev, p.Xe.stddev)
    lhs = fx.log2(se2 * (beta - 1) + fx.mul(p.Xe.stddev, p.Xe.stddev)) // 2
    rhs = x * (2 * beta - d - 1) + (log2tau + l2xi * p.n + l2q * (d - p.n - 1)) // d
    if lhs > rhs:
        return None
    return matzov_bits(beta, d)


def primal_usvp(params: LWE):
    p = params.normalize()
    if p.Xs.stddev <= p.Xe.stddev:
        m = None if p.m is None else p.m + p.n
    else:
        m = p.m
    max_beta = MAX_BETA if m is None else max(min(MAX_BETA, m), 45)
    best = None
    for beta in range(40, max_beta):
        best = fx.cost_min(best, cost_gsa(beta, p, m))
    return best
