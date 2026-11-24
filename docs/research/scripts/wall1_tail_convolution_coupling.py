"""Finite and interval checks of a joint tail/convolution bound, not BKZ drift."""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import ceil
from numbers import Rational
from mpmath import iv

iv.dps = 60

def interval(x):
    x = F(x)
    return iv.mpf(x.numerator) / x.denominator

def fourier_cap(q, p):
    if p in (0, 1):
        return iv.mpf(0)
    return iv.sin(iv.pi * interval(p)) / (q * iv.sin(iv.pi / q))

def triple_interval(q, beta, p, r):
    values = (beta, p, r)
    bounds = []
    for i in range(3):
        others = [values[j] for j in range(3) if j != i]
        variance = others[0]*(1-others[0])*others[1]*(1-others[1])
        for cap in (fourier_cap(q, values[i]), interval(values[i]), interval(1-values[i])):
            bounds.append(interval(beta*p*r) + cap*iv.sqrt(interval(variance)))
    return bounds

@lru_cache(None)
def certified_bound(q, beta, p, r):
    upper = min(beta*p, beta*r, p*r)
    for bound in triple_interval(q, beta, p, r):
        # Floating point proposes a rational cap; interval comparison certifies it.
        cap = F(ceil(float(bound.b)*10**12)+1, 10**12)
        assert bound.b < interval(cap).a
        upper = min(upper, cap)
    return upper

def partition_certificate(q, profiles, tail_caps, delta):
    """Certified linear-cap bound given valid radial caps for ordered bins.

    All bins must have valid two-height witnesses. tail_caps[l-1] bounds
    the incoming miss set at cutoff c_l, not just the winner-tail event.
    Require c_l>=1 or another proved tail-set inclusion. The caller must
    establish these hypotheses on its actual state. Inputs must be rational.
    """
    if any(not isinstance(x,Rational) for x in [delta,*tail_caps,*[x for pair in profiles for x in pair]]):
        raise TypeError('Use certified rational density caps and delta, not floats.')
    profiles = [tuple(map(F,pair)) for pair in profiles]
    tail_caps = list(map(F,tail_caps))
    delta = F(delta)
    assert profiles and len(tail_caps) == len(profiles)-1 and delta > 0
    assert all(0 <= x <= 1 for pair in profiles for x in pair)
    assert all(0 <= x <= 1 for x in tail_caps)
    best = [F(0)]
    paths = [()]
    for k, (p, r) in enumerate(profiles, start=1):
        candidates = [(p*r, ((0,k),))]
        for l in range(1,k):
            cost = certified_bound(q, tail_caps[l-1], p, r)
            candidates.append((best[l]+cost, paths[l]+((l,k),)))
        value, path = min(candidates)
        best.append(value)
        paths.append(path)
    return min(F(1), best[-1]/delta), paths[-1]

def partition_checks():
    try:
        partition_certificate(3,[(0.1,F(1))],[],F(1))
    except TypeError:
        pass
    else:
        raise AssertionError('Uncertified float input was accepted.')
    # All four ordered radial sets and all suffix events in F_3.
    n = 3
    checked = 0
    for levels in product(range(5), repeat=n):
        sets = [{v for v in range(n) if levels[v] >= t} for t in (4,3,2,1)]
        profiles = [(F(len(sets[2*j]),n), F(len(sets[2*j+1]),n)) for j in range(2)]
        hs = [[F(sum((v+u)%n in sets[2*j+1] for v in sets[2*j]),n)
               for u in range(n)] for j in range(2)]
        for mask in range(1 << n):
            suffix = {u for u in range(n) if mask >> u & 1}
            bound, _ = partition_certificate(n, profiles, [F(len(suffix),n)], F(7,25))
            actual = sum((min(F(1), hs[int(u in suffix)][u]/F(7,25)) for u in range(n)),F(0))/n
            assert actual <= bound
            checked += 1
    p = F(2,7)
    bound, path = partition_certificate(7, [(F(0),F(0)),(p,p)], [p], p)
    assert path == ((0,1),(1,2))
    assert bound < p  # Earlier shared-prefix relaxation has exact optimum p.
    print('Exact two-bin partition checks:', checked)
    print('Two-bin rational certificate:', bound, 'partition:', path)
    print('Earlier shared-prefix optimum:', p)
    checked = 0
    for levels in product(range(7), repeat=n):
        sets = [{v for v in range(n) if levels[v] >= t} for t in (6,5,4,3,2,1)]
        profiles = [(F(len(sets[2*j]),n), F(len(sets[2*j+1]),n)) for j in range(3)]
        hs = [[F(sum((v+u)%n in sets[2*j+1] for v in sets[2*j]),n)
               for u in range(n)] for j in range(3)]
        for bins in product(range(3), repeat=n):
            tails = [F(sum(j>=l for j in bins),n) for l in (1,2)]
            bound, _ = partition_certificate(n, profiles, tails, F(7,25))
            actual = sum((min(F(1),hs[bins[u]][u]/F(7,25)) for u in range(n)),F(0))/n
            assert actual <= bound
            checked += 1
    print('Exact three-bin partition checks:', checked)

def main():
    count = 0
    upper_cap_count = 0
    for q in (3, 5):
        subsets = list(product((0, 1), repeat=q))
        for a in subsets:
            p = F(sum(a), q)
            for b in subsets:
                r = F(sum(b), q)
                overlap = [sum(a[v]*b[(v+u)%q] for v in range(q)) for u in range(q)]
                for d in subsets:
                    beta = F(sum(d), q)
                    actual = F(sum(d[u]*overlap[u] for u in range(q)), q*q)
                    assert actual <= certified_bound(q, beta, p, r)
                    count += 1
                    if q == 3:
                        for db, ap, br in product(range(sum(d),q+1), range(sum(a),q+1), range(sum(b),q+1)):
                            assert actual <= certified_bound(q, F(db,q), F(ap,q), F(br,q))
                            upper_cap_count += 1
    p = F(932, 3329)
    joint = triple_interval(3329, p, p, p)[0]
    assert joint.b < interval(F('0.0715')).a
    assert interval(p*p).a > interval(F('0.0783')).b
    a = {1, 6}
    assert sum(v in a and (v+u)%7 in a for u in a for v in range(7)) == 0
    assert certified_bound(7, F(2,7), F(2,7), F(2,7)) < F(4,49)
    print('Exact finite subset triple checks:', count)
    print('Exact one-sided density-cap checks:', upper_cap_count)
    print('q=3329, density932/3329 joint scalar cap:', joint)
    print('Joint cap <.0715; separate prefix budget >.0783.')
    print('No production selected-history profile or drift bound is asserted.')
    partition_checks()

if __name__ == '__main__':
    main()
