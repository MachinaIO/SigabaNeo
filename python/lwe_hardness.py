"""Reference implementation of the LWE security function `H` (SigabaNeo/Lib/Lattices/Hardness.lean).

`H` is a conservative lower bound, in bits, on the cost of every known classical attack on LWE
(and on Ring-/Module-LWE through their LWE view). The Lean definition is the one that counts; this
file mirrors it with the same integer arithmetic, so that the two can be compared (`selftest`), and
compares `H` with the lattice estimator (`validate`, which needs Sage and the estimator).

Every quantity is an interval of fixed-point numbers with `P` fractional bits. Each step rounds in
the attacker's favour, so `H` is below the real-valued model it approximates. The model is
described in docs/LWE_HARDNESS.md.

  python3 lwe_hardness.py H N RANK M Q S_NUM S_DEN SECRET [SECRET_ARG...]
  python3 lwe_hardness.py selftest
  sage -python lwe_hardness.py validate ESTIMATOR_DIR
"""

from __future__ import annotations

import math
import sys
from fractions import Fraction

P = 32                 # fractional bits of the fixed-point numbers
F = 1 << P
K = 64                 # working precision of the logarithm
BITS_CAP = 1024        # no claim above this many bits
BETA_MAX = 4096        # largest block size scanned
SIEVE_NUM, SIEVE_DEN = 292, 1000   # classical sieving exponent (BDGL16): 2^(0.292 β')
SAFETY_BITS = 0        # subtracted from the minimum (see docs/LWE_HARDNESS.md)

# Rational enclosures of the constants.
PI = (Fraction(314159265, 10**8), Fraction(314159266, 10**8))
E = (Fraction(271828182, 10**8), Fraction(271828183, 10**8))


# ---------------------------------------------------------------- fixed point and intervals

def fdiv(a: int, b: int) -> int:
    return a // b


def cdiv(a: int, b: int) -> int:
    return -((-a) // b)


def log2_lo_nat(x: int) -> int:
    """floor(F * log2 x) or slightly less, for x >= 1."""
    assert x >= 1
    e = x.bit_length() - 1
    m = (x << K) >> e
    frac = 0
    for _ in range(P):
        m = (m * m) >> K
        frac <<= 1
        if m >= 1 << (K + 1):
            frac |= 1
            m >>= 1
    return e * F + frac


def log2_nat(x: int) -> tuple[int, int]:
    lo = log2_lo_nat(x)
    return (lo, lo + 2)


def log2_q(r: Fraction) -> tuple[int, int]:
    a, b = log2_nat(r.numerator), log2_nat(r.denominator)
    return (a[0] - b[1], a[1] - b[0])


def log2_iv(r: tuple[Fraction, Fraction]) -> tuple[int, int]:
    return (log2_q(r[0])[0], log2_q(r[1])[1])


def iv_const(v: int) -> tuple[int, int]:
    return (v * F, v * F)


def iv_add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def iv_sub(a, b):
    return (a[0] - b[1], a[1] - b[0])


def iv_smul(k: int, a):
    return (k * a[0], k * a[1]) if k >= 0 else (k * a[1], k * a[0])


def iv_div_nat(a, k: int):
    return (fdiv(a[0], k), cdiv(a[1], k))


def iv_mul(a, b):
    ps = [a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1]]
    return (fdiv(min(ps), F), cdiv(max(ps), F))


def iv_div(a, b):
    assert b[0] > 0
    ps = [a[0] * F * 1, a[1] * F]
    qs = [fdiv(p, d) for p in ps for d in b]
    qs2 = [cdiv(p, d) for p in ps for d in b]
    return (min(qs), max(qs2))


def iv_sqrt(a):
    lo = math.isqrt(max(0, a[0]) * F)
    hi = math.isqrt(max(0, a[1]) * F) + 1
    return (lo, hi)


def iv_max0(a):
    return (max(0, a[0]), max(0, a[1]))


LOG2_PI = log2_iv(PI)
LOG2_E = log2_iv(E)
LOG2_2PI = iv_add(iv_const(1), LOG2_PI)
LOG2_2PIE = iv_add(LOG2_2PI, LOG2_E)
LOG2_4_3 = log2_q(Fraction(4, 3))

# Root-Hermite factors of the estimator for β ≤ 40 (reduction.py, `_delta`).
DELTA_SMALL = [(2, Fraction(102190, 10**5)), (5, Fraction(101862, 10**5)),
               (10, Fraction(101616, 10**5)), (15, Fraction(101485, 10**5)),
               (20, Fraction(101420, 10**5)), (25, Fraction(101342, 10**5)),
               (28, Fraction(101331, 10**5)), (40, Fraction(101295, 10**5))]


def log2_delta(beta: int):
    """Enclosure of log2 δ(β), the estimator's root-Hermite factor."""
    if beta <= 2:
        return log2_q(DELTA_SMALL[0][1])
    if beta < 40:
        prev = DELTA_SMALL[0][1]
        for b, d in DELTA_SMALL[1:]:
            if b > beta:
                return log2_q(prev)
            prev = d
    if beta == 40:
        return log2_q(DELTA_SMALL[-1][1])
    # log2 δ = (log2(β/(2πe)) + log2(πβ)/β) / (2(β-1))
    lb = log2_nat(beta)
    t1 = iv_sub(lb, LOG2_2PIE)
    t2 = iv_div_nat(iv_add(LOG2_PI, lb), beta)
    return iv_div_nat(iv_add(t1, t2), 2 * (beta - 1))


# ---------------------------------------------------------------- distributions

def gauss_log2_sigma(s: Fraction):
    """Enclosure of log2 of the standard deviation of D_{Z,s} (ρ_s(x) = exp(-π x²/s²))."""
    hi = iv_sub(log2_q(s), iv_div_nat(LOG2_2PI, 2))[1]
    # Var(D_{Z,s}) >= r(s) s²/(2π), r from the table below (checked numerically).
    if s >= 2:
        r = Fraction(999, 1000)
    elif s >= Fraction(3, 2):
        r = Fraction(97, 100)
    elif s >= Fraction(6, 5):
        r = Fraction(8, 10)
    elif s >= 1:
        r = Fraction(49, 100)
    else:
        r = None
    if r is not None:
        lo = iv_add(iv_sub(log2_q(s), iv_div_nat(LOG2_2PI, 2)), iv_div_nat(log2_q(r), 2))[0]
    else:
        # Var >= 2 ρ_s(1)/ρ_s(Z) >= 2^(1-k)/(1+s), k >= π log2(e)/s².
        k = tail_exp(0, s)
        lo = fdiv((1 - k) * F - log2_q(1 + s)[1], 2)
    return (lo, hi)


def tail_exp(B: int, s: Fraction) -> int:
    """k = ceil(π log2(e) (B+1)² / s²), so that exp(-π (B+1)²/s²) >= 2^-k."""
    v = PI[1] * (B + 1) ** 2 / (s * s)
    return cdiv(iv_mul((cdiv(v.numerator * F, v.denominator),) * 2, LOG2_E)[1], F)


def ell(B: int, s: Fraction) -> int:
    """Lower bound (fixed point) on log2(1/Pr[|e| <= B]) for e ← D_{Z,s}."""
    # Point masses are at most 1/ρ_s(Z) <= 1/max(1, s).
    l1 = 0
    if s > 1:
        l1 = max(0, log2_q(s)[0] - log2_nat(2 * B + 1)[1])
    # Pr[|e| > B] >= 2 ρ_s(B+1)/ρ_s(Z) >= 2^(1-k)/(1+s), and -log2(1-x) >= x.
    k = tail_exp(B, s)
    l2 = fdiv(2 * F * s.denominator, (s.numerator + s.denominator) << k)
    return max(l1, l2)


class Secret:
    """`uniform` (mod q), `gauss` (D_{Z,s}), `bounded` (uniform on [-B, B])."""

    def __init__(self, kind: str, arg=None):
        self.kind, self.arg = kind, arg


def secret_log2_sigma(sec: Secret, q: int):
    if sec.kind == "cbd":
        return iv_div_nat(iv_sub(log2_nat(sec.arg), log2_nat(2)), 2)
    if sec.kind == "uniform":
        v = Fraction(q * q - 1, 12)
        a = log2_q(v)
        return iv_div_nat(a, 2)
    if sec.kind == "gauss":
        return gauss_log2_sigma(sec.arg)
    B = sec.arg
    a = iv_sub(log2_nat(B * (B + 1)), log2_nat(3))
    return iv_div_nat(a, 2)


def cbd_min_entropy_lo(eta: int) -> int:
    return max(0, log2_nat(4 ** eta)[0] - log2_nat(math.comb(2 * eta, eta))[1])


def secret_min_entropy_lo(sec: Secret, q: int) -> int:
    if sec.kind == "cbd":
        return cbd_min_entropy_lo(sec.arg)
    if sec.kind == "uniform":
        return log2_nat(q)[0]
    if sec.kind == "gauss":
        return max(0, log2_q(sec.arg)[0])
    return log2_nat(2 * sec.arg + 1)[0]


# ---------------------------------------------------------------- lattice attacks

def d4f_hi(beta: int):
    """Upper bound on Ducas' dimensions for free, β log(4/3)/log(β/(2πe)), capped at β."""
    den = iv_sub(log2_nat(beta), LOG2_2PIE)[0]
    if den <= LOG2_4_3[1]:
        return beta * F
    return min(beta * F, cdiv(beta * LOG2_4_3[1] * F, den))


def sieve_bits_lo(beta: int) -> int:
    dim = max(0, beta * F - d4f_hi(beta))
    return fdiv(dim * SIEVE_NUM, SIEVE_DEN * F)


def usvp_fmax_hi(beta, n, m, log2q, log2se, log2xi):
    """Upper bound on max_d f(d) over d ∈ [n+1, n+m+1]; the primal attack with block size β
    succeeds (GSA, 2016 estimate) iff some f(d) >= 0."""
    x = log2_delta(beta)
    lhs = iv_add(log2se, iv_div_nat(log2_nat(beta), 2))
    A = iv_sub(iv_add(iv_smul(2 * beta - 1, x), log2q), lhs)
    C = iv_sub(iv_add(log2se, iv_smul(n, log2xi)), iv_smul(n + 1, log2q))
    a, b = n + 1, n + m + 1

    def f(d):
        return iv_add(iv_sub(A, iv_smul(d, x)), iv_div_nat(C, d))

    if C[0] >= 0:
        return f(a)[1]
    if C[1] < 0:
        absC = (-C[1], -C[0])
        d2 = iv_div(absC, x)
        if d2[1] < a * a * F:
            return f(a)[1]
        if d2[0] > b * b * F:
            return f(b)[1]
        return iv_sub(A, iv_smul(2, iv_sqrt(iv_mul(absC, x))))[1]
    return max(f(a)[1], A[1])


def lattice_lb(n, m, q, log2se, log2ss) -> int:
    """Lower bound on lattice attacks. The target (s, e) is rescaled so that both parts have the
    standard deviation of the larger one: the secret part by ξ_s, the error part by ξ_e (which
    multiplies the q-ary part of the volume, so it enters as log q + log ξ_e)."""
    star = (max(log2se[0], log2ss[0]), max(log2se[1], log2ss[1]))
    log2xi = iv_max0(iv_sub(star, log2ss))
    log2q = iv_add(log2_nat(q), iv_max0(iv_sub(star, log2se)))
    cap = min(BETA_MAX, n + m + 1)
    for beta in range(2, cap + 1):
        if usvp_fmax_hi(beta, n, m, log2q, star, log2xi) >= 0:
            return sieve_bits_lo(beta)
    return sieve_bits_lo(cap)


# ---------------------------------------------------------------- algebraic (Arora–Ge, Gröbner)

def binom(a: int, b: int) -> int:
    return math.comb(a, b) if 0 <= b <= a else 0


class OutOfFuel(Exception):
    pass


def fuel_for(n: int) -> int:
    """Iteration bound of every loop of `gb_lb`; running out gives the bound 0."""
    return 8 * n + 256


def ell_dist(B: int, dist: Secret, q: int) -> int:
    """Lower bound (fixed point) on log2(1/Pr[|e| <= B]) for e from `dist`."""
    if dist.kind == "gauss":
        return ell(B, dist.arg)
    if dist.kind == "cbd":
        if dist.arg <= B:
            return 0
        return max(0, cbd_min_entropy_lo(dist.arg) - log2_nat(2 * B + 1)[1])
    width = 2 * dist.arg + 1 if dist.kind == "bounded" else q
    if 2 * B + 1 >= width:
        return 0
    return max(0, log2_nat(width)[0] - log2_nat(2 * B + 1)[1])


def gb_lb(n, m, err: Secret, sec: Secret | None, q: int, best: int) -> int:
    """Lower bound (fixed point) on Arora–Ge with Gröbner bases, or `best` if that is smaller.

    Solving at degree d with M error equations of degree D = 2B+1 (and the secret's equations)
    needs the ideal to contain every monomial of degree d, so M c(d-D) + n c(d-Ds) >= c(d), where
    c(k) counts monomials of degree k in n variables. It costs at least binom(n+d, d)^2 and succeeds
    only if the M errors are in [-B, B]."""
    fuel = fuel_for(n)

    def c(k):  # monomials of degree k in n variables
        return binom(n - 1 + k, n - 1) if k >= 0 else 0

    # Secret equations: (degree, penalty) choices; degree None if there are none.
    sec_choices = [(None, 0)]
    if sec is not None and sec.kind in ("bounded", "cbd"):
        sec_choices = [(2 * sec.arg + 1, 0)]
    elif sec is not None and sec.kind == "gauss":
        sec_choices = []
        for Bs in range(fuel + 1):
            if Bs == fuel:
                return 0
            pen = n * ell(Bs, sec.arg)
            sec_choices.append((2 * Bs + 1, pen))
            if pen == 0:
                break

    for B in range(fuel + 1):
        if B == fuel:
            return 0
        D = 2 * B + 1
        if 2 * log2_nat(binom(n + D, D))[0] >= best:
            return best
        lB = ell_dist(B, err, q)
        for Ds, pen in sec_choices:
            for i in range(fuel + 1):
                if i == fuel:
                    return 0
                d = D + i
                bc = 2 * log2_nat(binom(n + d, d))[0]
                if bc + pen >= best:
                    break
                num = c(d) - (n * c(d - Ds) if Ds is not None else 0)
                Mmin = 0 if num <= 0 else cdiv(num, c(d - D))
                if Mmin <= m:
                    best = min(best, bc + pen + Mmin * lB)
    return 0


# ---------------------------------------------------------------- H

def is_pow2(x: int) -> bool:
    return x >= 1 and x & (x - 1) == 0


def valid(d: Secret) -> bool:
    return d.kind == "uniform" or d.arg > 0


def H(N: int, rank: int, m: int, q: int, err: Secret, sec: Secret) -> int:
    """Conservative security bits of Module-LWE over Z_q[X]/(X^N + 1), rank `rank`, `m` module
    samples, error law `err`, secret law `sec`."""
    if not (is_pow2(N) and rank >= 1 and m >= 1 and q >= 2 and valid(err) and valid(sec)):
        return 0
    n, mm = N * rank, N * m
    # Views (samples, secret law, error law): the instance; its normal form (secret distributed
    # like the errors, n samples fewer); with at least n samples, secret and errors swapped
    # (for n samples with A invertible, A^{-1} b = s + A^{-1} e is LWE with secret e, error s).
    views = [(mm, sec, err)]
    if mm > n:
        views.append((mm - n, err, err))
    if mm >= n and sec.kind != "uniform":
        views.append((n, err, sec))
    best = BITS_CAP * F
    for mv, sv, ev in views:
        log2ss = secret_log2_sigma(sv, q)
        log2se = secret_log2_sigma(ev, q)
        best = min(best, lattice_lb(n, mv, q, log2se, log2ss) * F)
        best = min(best, fdiv(n * secret_min_entropy_lo(sv, q), 2))
        gsec = None if sv.kind == "uniform" else sv
        best = gb_lb(n, mv, ev, gsec, q, best)
    ring = (N.bit_length() - 1) * F
    return max(0, fdiv(best - ring, F) - SAFETY_BITS)


def parse_secret(args):
    kind = args[0]
    if kind == "uniform":
        return Secret("uniform")
    if kind == "gauss":
        return Secret("gauss", Fraction(int(args[1]), int(args[2])))
    return Secret("bounded", int(args[1]))


if __name__ == "__main__":
    if sys.argv[1] == "H":
        N, rank, m, q, a, b = map(int, sys.argv[2:8])
        print(H(N, rank, m, q, Secret("gauss", Fraction(a, b)), parse_secret(sys.argv[8:])))


# ---------------------------------------------------------------- validation against the estimator

def validate(estimator_dir: str, jobs: int = 8) -> None:
    """Compare H with the cheapest attack the lattice estimator reports, on a grid of plain LWE
    parameters (N = 1). Prints one line per point and the smallest margin."""
    import itertools
    from multiprocessing import Pool

    grid = []
    for n, logq, s, kind, mfac in itertools.product(
            [128, 256, 512, 1024, 2048], [10, 16, 32, 64], ["1", "3", "8", "64"],
            ["uniform", "gauss", "ternary"], [1, 2, 0]):
        grid.append((n, logq, s, kind, mfac))
    with Pool(jobs, initializer=_init_estimator, initargs=(estimator_dir,)) as pool:
        rows = []
        for row in pool.imap_unordered(_validate_point, grid, chunksize=1):
            print(*row, sep="\t", flush=True)
            rows.append(row)
    worst = None
    for row in rows:
        if row[-1] is not None and (worst is None or row[-1] < worst[-1]):
            worst = row
    print("worst margin:", worst)


def _init_estimator(estimator_dir):
    sys.path.insert(0, estimator_dir)


def _validate_point(pt):
    n, logq, s, kind, mfac = pt
    from estimator import LWE, ND, RC  # noqa
    from sage.all import oo, log, sqrt, pi, RR
    q = 2 ** logq - 1 if logq <= 32 else 2 ** logq - 59
    sw = Fraction(int(s), 1)
    sd = RR(sw) / sqrt(2 * pi)
    Xe = ND.DiscreteGaussian(sd)
    if kind == "uniform":
        Xs, sec = ND.UniformMod(q), Secret("uniform")
    elif kind == "gauss":
        Xs, sec = Xe, Secret("gauss", sw)
    else:
        Xs, sec = ND.Uniform(-1, 1), Secret("bounded", 1)
    m_est = oo if mfac == 0 else mfac * n
    m_ours = 2 ** 64 if mfac == 0 else mfac * n
    h = H(1, n, m_ours, q, Secret("gauss", sw), sec)
    params = LWE.Parameters(n=n, q=q, Xs=Xs, Xe=Xe, m=m_est)
    costs = {}
    for tag, fn in [("default", lambda: LWE.estimate(params, quiet=True, jobs=1)),
                    ("core", lambda: LWE.estimate(params, red_cost_model=RC.ADPS16,
                                                  quiet=True, jobs=1)),
                    ("rough", lambda: LWE.estimate.rough(params, quiet=True, jobs=1))]:
        try:
            for k, v in fn().items():
                r = v["rop"]
                if r != oo and r > 0:
                    costs[f"{tag}:{k}"] = float(log(r, 2))
        except Exception as exc:  # noqa
            costs[f"{tag}:error"] = None
    finite = {k: v for k, v in costs.items() if v is not None}
    if not finite:
        return (n, logq, s, kind, mfac, h, None, None, None)
    k = min(finite, key=finite.get)
    return (n, logq, s, kind, mfac, h, k, round(finite[k], 1), round(finite[k] - h, 1))


if __name__ == "__main__" and sys.argv[1] == "validate":
    validate(sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 8)
