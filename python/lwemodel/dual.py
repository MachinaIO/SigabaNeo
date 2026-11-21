"""Micciancio-Regev dual reduction, Gaussian distinguisher and GJ21 sampling.
Scan every integer block size in the estimator's interval.
"""
from . import fx
from .num_dual import delta, rho_bits, short_bits, logn


def cost(p):
    p = p.normalize()
    if p.Xs.is_sparse or min(p.Xs.stddev, p.Xe.stddev, p.n, p.q) <= 0:
        return None
    xs = fx.log2(p.Xs.stddev)
    c = xs + logn(p.q) - fx.log2(p.Xe.stddev)
    best = None
    for b in range(40, max(48, min(1754, p.m if p.m is not None else 1754))):
        h = delta(b)
        m = max(1, fx.ceil(fx.sqrt(fx.div(p.n*c, h))) - p.n)
        if p.m is not None:
            m = min(m, p.m)
        d = p.n+m
        sigma = rho_bits(b, 2*b) + xs + d*h - m*c//d
        if sigma > 4*fx.ONE - fx.log2(fx.SQRT2PI):
            continue
        # -log2(advantage^2), with advantage = exp(-2 pi^2 sigma^2).
        a = fx.mul(fx.mul(4*fx.mul(fx.PI, fx.PI), fx.LOG2E), fx.exp2(2*sigma))
        if a > 2150*fx.ONE:
            continue
        numerator = 2*fx.ln(fx.of_int(50))
        if a < -2*fx.log2(fx.of_rat(99,100)):
            count = 0
        elif a < 24*fx.ONE:
            count = logn(fx.ceil(fx.div(numerator, -fx.ln(fx.ONE-fx.exp2(-a)))))
        else:
            # Sage subtracts advantage squared from one in a variable-
            # precision RealField. Round to the ulp immediately below one.
            prec = min(2048, max(53, 2*fx.ceil(a//2)))
            units = fx.floor(fx.exp2(fx.of_int(prec)-a) + fx.ONE//2)
            if units == 0:
                continue
            count = fx.log2(numerator) + fx.of_int(prec) - logn(units)
        red = short_bits(b,d,count)
        if red is not None:
            best = fx.cost_min(best,fx.log2_add(red,count))
    return best
