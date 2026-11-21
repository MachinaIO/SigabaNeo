"""Fixed-point arithmetic shared by the attack models (mirror of
SigabaNeo/Lib/Lattices/Estimator/Fx.lean; every function returns the same integer).

A number x is the integer round-down of x * 2^P. All divisions round down (floor)."""

P = 48
ONE = 1 << P
K = 2 * P  # working precision of log2

LN2 = 195103586505167
LOG2E = 406082553034799
PI = 884279719003555
E = 765128314358509
SQRT2PI = 705553135224032


def of_int(k: int) -> int:
    return k << P


def of_rat(a: int, b: int) -> int:
    return (a << P) // b


def mul(a: int, b: int) -> int:
    return (a * b) >> P


def div(a: int, b: int) -> int:
    return (a << P) // b


def floor(a: int) -> int:
    return a >> P


def ceil(a: int) -> int:
    return -((-a) >> P)


def log2_nat(v: int) -> int:
    """log2 of a positive integer, as a fixed-point number (rounded down)."""
    e = v.bit_length() - 1
    m = (v << K) >> e
    frac = 0
    for _ in range(P):
        m = (m * m) >> K
        frac <<= 1
        if m >= 1 << (K + 1):
            frac |= 1
            m >>= 1
    return (e << P) + frac


def log2(x: int) -> int:
    """log2 of a positive fixed-point number."""
    return log2_nat(x) - (P << P)


def ln(x: int) -> int:
    return mul(log2(x), LN2)


def exp2(y: int) -> int:
    """2^y for a fixed-point y."""
    k = y >> P
    f = y - (k << P)
    t = mul(f, LN2)
    s, term = ONE, ONE
    for i in range(1, 64):
        term = mul(term, t) // i
        if term == 0:
            break
        s += term
    return s << k if k >= 0 else s >> (-k)


def exp(x: int) -> int:
    return exp2(mul(x, LOG2E))


def sqrt(x: int) -> int:
    import math
    return math.isqrt(max(0, x) << P)


def pow_(x: int, y: int) -> int:
    """x^y for x > 0."""
    return exp2(mul(y, log2(x)))


def log2_add(a: int, b: int) -> int:
    """log2(2^a + 2^b)."""
    hi, lo = max(a, b), min(a, b)
    return hi + log2(ONE + exp2(lo - hi))


# Costs are log2 values (fixed point) or None (infinite).
def cost_min(a, b):
    if a is None:
        return b
    if b is None:
        return a
    return min(a, b)


def cost_add(a, b):
    if a is None or b is None:
        return None
    return log2_add(a, b)
