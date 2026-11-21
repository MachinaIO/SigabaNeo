"""Numerics for estimator.lwe_guess, gb and lwe_bkw (fixed-point mirror)."""
from . import fx as F


def width(x):
    if x.kind == "gauss":
        return 8 * F.mul(F.SQRT2PI, x.stddev) + 3 * F.ONE
    a, b = x.bounds
    return F.of_int(b - a + 1)


def tail(x):
    return F.ONE - 2 * F.exp(-4 * F.PI) if x.kind == "gauss" else F.ONE


def repeat_bits(logp):
    if logp >= F.log2(F.of_rat(99, 100)):
        return 0
    if logp < -40 * F.ONE:
        return F.log2(F.ln(100 * F.ONE)) - logp
    return F.log2_nat(F.ceil(F.div(-F.ln(100 * F.ONE), F.ln(F.ONE - F.exp2(logp)))))


def local(start, stop, evaluate, smaller):
    """Precision-one local_minimum, including its exclusive upper bound."""
    lo, hi = start, stop - 1
    x, direction, best, seen = hi, -1, None, set()
    while start <= x < stop and x not in seen:
        seen.add(x)
        y = evaluate(x)
        if len(seen) == 1 or smaller(y, best):
            best = y
            if abs(direction) == 2:
                x, direction = x - 1, -1
            elif direction == -1:
                hi, x, direction = x, (lo + x + 1) // 2, -2
            else:
                lo, x, direction = x, (x + hi) // 2, 2
        elif direction == -1:
            x, direction = x + 2, 1
        elif direction == 1:
            break
        elif direction == -2:
            lo, x = x, (x + hi + 1) // 2
        else:
            hi, x = x, (lo + x) // 2
    return best
