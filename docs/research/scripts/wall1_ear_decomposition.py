"""General ear witnesses and a deliberately overlap-blind Gaussian envelope.

This covers every connected affine support, but need not meet the exit budget.
"""
import contextlib
from fractions import Fraction as F
from itertools import product
from math import comb, factorial
from pathlib import Path
import io
import runpy
from mpmath import iv
from wall1_centered_affine_cancellation import rank
from wall1_factorial_cumulants import difference_weights


def ear_checks():
    checked = steps = 0
    for q, dim in ((3, 2), (2, 3)):
        points = list(product(range(q), repeat=dim))
        ranks = {s: rank([(1, *p) for i, p in enumerate(points) if s >> i & 1], q)
                 for s in range(1 << len(points))}
        circuits = [s for s, r in ranks.items() if s.bit_count() == r+1
                    and all(ranks[s ^ (1 << i)] == r
                            for i in range(len(points)) if s >> i & 1)]
        for support, r in ranks.items():
            if support.bit_count() < 3:
                continue
            sub = (support-1) & support
            while sub and ranks[sub]+ranks[support ^ sub] != r:
                sub = (sub-1) & support
            if sub:
                continue
            contained = [c for c in circuits if c & support == c]
            for first in contained:
                union, ears = first, 1
                while union != support:
                    options = [c for c in contained if c & union and c & ~union]
                    assert options
                    # Cardinality minimal implies inclusion minimal outside union.
                    chosen = min(options, key=lambda c: ((c & ~union).bit_count(), c))
                    outside = chosen & ~union
                    t = outside.bit_count()
                    assert ranks[union | chosen]-ranks[union] == t-1
                    assert (chosen & union).bit_count() <= ranks[union]
                    # The new positions form a circuit in the contraction.
                    assert all(ranks[union | (outside ^ (1 << i))] == ranks[union]+t-1
                               for i in range(len(points)) if outside >> i & 1)
                    union |= chosen
                    ears += 1
                    steps += 1
                assert ears == support.bit_count()-r
                checked += 1
    print(f'Passed {checked} complete ear decompositions and {steps} rank-increment checks.')


def holder_checks():
    # Positive rational functions: no theta approximation in this regression.
    q = 5
    f = [F(1, 1+min(x, q-x)) for x in range(q)]
    checked = 0
    for first, second, third in ((2, 1, 1), (3, 2, 1), (2, 2, 2)):
        bound = F(1)
        for t in (first, second, third):
            bound *= sum((v**t for v in f), F(0))/q
        for scale in product(range(1, q), repeat=3):
            actual = F(0)
            for u, v, w in product(range(q), repeat=3):
                value = F(1)
                for j in range(first):
                    value *= f[(scale[0]*u+(j+1)*v+j*w) % q]
                for j in range(second):
                    value *= f[(scale[1]*v+(j+1)*w) % q]
                for j in range(third):
                    value *= f[(scale[2]*w+j) % q]
                actual += value/q**3
            assert actual <= bound
            checked += 1
    print(f'Passed {checked} exact triangular Holder checks.')


def envelope(h, r, c, q, n, m, radius):
    """Sum all labelled ears with starting girth c, dropping overlap geometry."""
    I = iv.mpf
    ell = h-r
    beta = I(r*n)/(2*h*radius**2)
    a = iv.pi**2/beta
    alpha = a/q**2
    delta = 2*iv.exp(-a/4)/(1-iv.exp(-2*a))
    def theta(x):
        def geometric(y):
            return 1+2*iv.exp(-y)/(1-iv.exp(-3*y))
        return geometric(x) if x > iv.pi else iv.sqrt(iv.pi/x)*geometric(iv.pi**2/x)
    # Fourier factor T_beta is taken out globally, once for each column.
    moments = {t: (theta(t*alpha)+sum(
        (comb(t, j)*delta**j*(theta((t-j)*alpha) if j < t else q)
        for j in range(1, t+1)), I(0)))/q for t in range(1, h+1)}
    # Coefficient/position counts are not raised to the ambient dimension.
    state = {c: I(comb(h, c)*q**(c-2))*moments[c]**n}
    for ears in range(1, ell):
        nxt = {}
        for size, weight in state.items():
            for t in range(1, h-size-(ell-ears-1)+1):
                count = sum(comb(size, overlap)*q**(t+overlap-2)
                            for overlap in range(max(1, c-t), size-ears+1))
                if count:
                    nxt[size+t] = nxt.get(size+t, I(0))+weight*comb(h-size, t)*count*moments[t]**n
        state = nxt
    return (state.get(h, I(0))*iv.exp(h*beta*radius**2)
            *(iv.pi/beta)**(I(h*n)/2)/q**(m*r))


def actual_parameters():
    with contextlib.redirect_stdout(io.StringIO()):
        s = runpy.run_path(str(Path(__file__).with_name('wall1_draw14_frontier.py')))
    h = 14
    total = iv.mpf(0)
    for r in range(2, h):
        value = sum((envelope(h, r, c, s['q'], s['N'], s['m'], s['radius'])
                     for c in range(3, r+2)), iv.mpf(0))
        total += value
        print('rank', r, 'log10 activity:', iv.log10(value), flush=True)
    weight = sum((iv.mpf(abs(v.numerator))/v.denominator*s['mu']**d
                  for d, v in enumerate(difference_weights(12)[h])), iv.mpf(0))
    charge = s['normalizer']*weight*total/factorial(h)
    print('Overlap-blind size-14 transfer envelope:', iv.log10(charge), flush=True)
    print('This is an upper-bound diagnostic, not a lower bound on the actual error.')


if __name__ == '__main__':
    ear_checks()
    holder_checks()
    actual_parameters()
