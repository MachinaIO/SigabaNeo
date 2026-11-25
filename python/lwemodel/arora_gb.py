"""Hilbert-series semi-regularity model and multiplicative guessing from gb.py/lwe_guess.py."""
from dataclasses import replace
from math import comb
from . import fx as F
from .num_misc import local, repeat_bits


def gb(n, d, m, secret):
    # Logarithmic derivative of (1-z^d)^m (1-z^s)^n / (1-z)^n.
    # Each residue accumulator sums the earlier coefficients in that class.
    terms = [(1, n), (d, -m*d)]
    if secret:
        terms.append((secret, -n*secret))
    sums = [[0]*min(step, 2*n) for step, _ in terms]
    a = 1
    for k in range(1, 2*n):
        v = 0
        for (step, mult), row in zip(terms, sums):
            row[(k-1) % step] += a
            v += mult * row[k % step] if k >= step else 0
        a = v // k
        if a < 0:
            return 2 * F.log2_nat(comb(n+k,k))
    return None


def gaussian_samples(c):
    neglog = F.log2(F.mul(c, F.SQRT2PI)) - F.ONE + F.mul(F.mul(c,c), F.LOG2E)//2
    if neglog >= 257*F.ONE:
        return 2**31
    if neglog > 25*F.ONE:
        return F.floor(F.mul(-F.ln(F.of_rat(99,100)), F.exp2(neglog)))
    return F.floor(F.div(F.ln(F.of_rat(99,100)), F.ln(F.ONE-F.exp2(-neglog))))


def single(p):
    p = p.normalize()
    s = 0
    if p.Xs.stddev <= p.Xe.stddev:
        s = (2*F.ceil(3*p.Xs.stddev)+1 if p.Xs.kind == 'gauss'
             else p.Xs.bounds[1]-p.Xs.bounds[0]+1)
    best = None
    if p.Xe.kind != 'gauss':
        d = p.Xe.bounds[1]-p.Xe.bounds[0]+1
        if d < 2*p.n or s:
            m = p.m if p.m is not None and p.n >= 2 and d >= p.m.bit_length() else p.n**min(d,2*p.n)
            best = gb(p.n,d,min(m,p.m) if p.m is not None else m,s)
    if p.Xe.is_gaussian_like and p.Xe.stddev:
        g, stuck = None, 0
        for t in range(F.ceil(p.Xe.stddev),p.n):
            m = gaussian_samples(F.div(F.of_int(t),p.Xe.stddev))
            if not p.m_ge(m):
                break
            if 2*t+1 >= 2*p.n or m <= p.n and not s:
                continue
            v = gb(p.n,2*t+1,m,s)
            if v is None:
                continue
            if g is None or v < g:
                g, stuck = v, 0
            else:
                stuck += 1
                if stuck == 5:
                    break
        best = F.cost_min(best,g)
    return best


def cost(params):
    p = params.normalize()
    if p.Xs.kind == "gauss" and not p.Xs.is_sparse:
        # The dense wrapper has an empty guessing interval for infinite base.
        return None
    baseline = single(p) if not p.Xs.is_sparse else None
    if baseline is None and not p.Xs.is_sparse:
        return None
    base = 2 if p.Xs.kind == "gauss" else p.Xs.bounds[1]-p.Xs.bounds[0]+1
    logbase = F.log2_nat(base)
    if not logbase:
        return single(p)
    h = p.Xs.hamming_weight()

    def candidate(z):
        v = single(replace(p,n=p.n-z))
        if v is None:
            raise ArithmeticError
        penalty = z*logbase
        if p.Xs.is_sparse:
            penalty, space, hits = 0, 0, 0
            # Only zero-weight guesses have finite space for unbounded Gaussians.
            count = min(z,h,1) if p.Xs.kind == "gauss" else min(z,h)
            for j in range(count):
                space += comb(z,j)*(base-1)**j
                hits += comb(h,j)*comb(p.n-h,z-j)
                if not hits:
                    if p.Xs.kind == "gauss":
                        raise ArithmeticError
                    continue
                cur = F.log2_nat(space)+repeat_bits(F.log2_nat(hits)-F.log2_nat(comb(p.n,z)))
                if penalty and cur >= penalty:
                    break
                penalty = cur
        return v + penalty
    stop = p.n-40 if p.Xs.is_sparse else min(p.n,baseline//logbase)
    try:
        return local(0,stop,candidate,lambda a,b:a<=b)
    except ArithmeticError:
        return None


arora_gb = cost
