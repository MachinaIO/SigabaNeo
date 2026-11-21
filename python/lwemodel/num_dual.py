"""GJ21.short_vectors with the MATZOV classical sieve fit and progressive BKZ."""
from functools import lru_cache
from . import fx, reduction as r

delta = lru_cache(4096)(r.log2_delta)
free = lru_cache(4096)(r.d4f)
logn = lru_cache(8192)(fx.log2_nat)
SLOPE = fx.of_rat(2075, 10000)


def sieve_dim(b, d):
    s = b - fx.floor(free(b))
    if b < d:
        s = min(d, s + fx.floor(fx.div(logn(d-b) + r.LOG2_C, r.NN_A)))
    return s


def rho_bits(b, d):
    s = sieve_dim(b, d)
    return fx.log2(fx.of_rat(4, 3)) // 2 + (s-1)*(delta(s)-delta(b))


def short_bits(b, d, log_n):
    if log_n == 0:
        return r.matzov_bits(b, d)
    s = sieve_dim(b, d)
    batch = fx.floor(fx.exp2(SLOPE*s))
    if log_n > logn(batch) + 1000*fx.ONE:
        return None
    runs = max(1, (fx.ceil(fx.exp2(log_n)) + batch-1)//batch)
    sieve = r.LOG2_C + r.NN_A*s + r.NN_B
    return logn(runs) + fx.log2_add(r.matzov_bits(b, d), sieve)
