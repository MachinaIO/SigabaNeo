"""Classical exhaustive_search and analytical mitm from estimator.lwe_guess."""
from math import comb
from . import fx as F
from .num_misc import width, tail, repeat_bits


def exhaustive_cost(params):
    p = params.normalize()
    prob = F.sqrt(F.of_rat(99, 100))
    if p.Xs.kind == "gauss":
        if p.n * F.log2(tail(p.Xs)) < F.log2(prob):
            return None
        size = p.n * F.log2(width(p.Xs))
    else:
        size = F.log2_nat(F.ceil(prob * F.floor(width(p.Xs)) ** p.n))
    s = F.mul(F.PI, p.Xe.stddev) // p.q
    exponent = 4 * F.mul(s, s)
    if exponent > 10000 * F.LN2:
        return None  # estimator Cost.sanity_check caps rop at 2^10000
    m = 8 * F.mul(F.exp(exponent), F.mul(size, F.LN2) - F.ln(-F.ln(prob)))
    bits = F.ONE + size + F.log2(m)
    return bits if p.m_ge(F.ceil(m)) and bits <= 10000 * F.ONE else None


def mitm_cost(params):
    p = params.normalize()
    err, sec = width(p.Xe), width(p.Xs)
    if err >= p.q * F.ONE:
        return None
    den = 2 * F.ONE - err // p.q
    k = F.floor(F.div(F.of_int(p.n), den) + F.ONE // 2)
    prob = p.n * F.log2(tail(p.Xs))
    if p.Xs.is_sparse:
        h = p.Xs.hamming_weight()
        if not h:
            return None
        j = h*k//p.n
        prob += F.log2_nat(comb(k,j)*comb(p.n-k,h-j)) - F.log2_nat(comb(p.n,h))
        T = F.div(h*(F.log2_nat(p.n)-F.log2_nat(h)+F.log2(sec-F.ONE)+F.LOG2E), den)
        T -= F.log2_nat(h)//2 + F.div(h*h*F.LOG2E, 2*p.n*F.mul(den,den))
    else:
        T = k * F.log2(sec)
    m = max(1, F.floor(T + F.log2(T) + F.ONE//2)) if T > 0 else 1
    return F.of_int(m) + repeat_bits(prob + m*F.log2(tail(p.Xe))) if p.m_ge(m) else None


exhaustive_search = exhaustive_cost
mitm = mitm_cost
