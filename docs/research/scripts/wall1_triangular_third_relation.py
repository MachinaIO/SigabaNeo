"""Third circuits crossing a triangular anchor and bounds for >=3 new points."""
import contextlib
from collections import Counter
from itertools import combinations, product
from math import comb
from pathlib import Path
import io
import runpy
from mpmath import iv
from wall1_centered_affine_cancellation import rank
from wall1_short_relation_shapes import equal_pair_sum_ball_bound, equal_pair_sum_alias_bound
from wall1_factorial_cumulants import difference_weights
from wall1_linear_remainder import remainder_weights, transfer


def new_group_bound(radius_sq, n, t, q):
    beta = iv.mpf((t-1)*n)/(2*t*radius_sq)
    def theta(x):
        geometric = lambda a: 1+2*iv.exp(-a)/(1-iv.exp(-3*a))
        return geometric(x) if x > iv.pi else iv.sqrt(iv.pi/x)*geometric(iv.pi**2/x)
    kernel = iv.mpf(1)
    for j in range(1, t):
        kernel *= theta(beta*(j+1)/j)
    return iv.exp(t*beta*radius_sq)*(kernel*theta(beta*q*q/t))**n


def finite_checks():
    q = 5
    points = [(1, 0, 0, 0), (4, 0, 0, 0), (0, 1, 0, 0),
              (0, 4, 0, 0), (0, 0, 1, 0), (0, 0, 4, 0),
              (0, 0, 0, 1), (1, 0, 0, 1), (0, 1, 0, 1),
              (0, 0, 1, 2), (1, 1, 0, 1), (1, 0, 1, 2)]
    rows = [(1, *p) for p in points]
    ranks = {s: rank([row for i, row in enumerate(rows) if s >> i & 1], q)
             for s in range(1 << len(rows))}
    anchor = (1 << 6)-1
    anchor_basis = sum(1 << i for i in (0, 1, 2, 4))
    assert ranks[anchor] == ranks[anchor_basis] == 4
    checked = 0
    for tail in range(1 << 6):
        support = anchor | (tail << 6)
        r = ranks[support]
        if r <= 4:
            continue
        sub = (support-1) & support
        while sub and ranks[sub]+ranks[support ^ sub] != r:
            sub = (sub-1) & support
        if sub:
            continue
        outside = [i for i in range(6, 12) if support >> i & 1]
        for extension in combinations(outside, r-4):
            basis = anchor_basis | sum(1 << i for i in extension)
            if ranks[basis] != r:
                continue
            found = False
            for e in outside:
                if basis >> e & 1:
                    continue
                circuit = (1 << e) | sum(1 << b for b in range(12)
                    if basis >> b & 1 and ranks[(basis ^ (1 << b)) | (1 << e)] == r)
                if not circuit & anchor_basis or not circuit & (basis ^ anchor_basis):
                    continue
                t = (circuit & ~anchor).bit_count()
                assert 2 <= t <= r-3
                assert ranks[anchor | circuit] == t+3
                found = True
            assert found
            checked += 1
    print(f'Passed {checked} crossing fundamental-circuit checks.')
    iv.dps = 80
    counts = 0
    for radius in (1, 2):
        ball = [x for x in product(range(-radius, radius+1), repeat=2)
                if sum(a*a for a in x) <= radius**2]
        for q in (3, 5):
            for t in (2, 3, 4):
                bound = new_group_bound(iv.mpf(radius**2), 2, t, q)
                for rest in product(range(1, q), repeat=t-1):
                    dist = Counter({(0, 0): 1})
                    for a in (1, *rest):
                        nxt = Counter()
                        for v, count in dist.items():
                            for x in ball:
                                nxt[tuple((b+a*c) % q for b, c in zip(v, x))] += count
                        dist = nxt
                    assert max(dist.values()) <= bound
                    counts += 1
    print(f'Passed {counts} exact modular new-group counts, including arbitrary targets.')


def actual_parameters():
    with contextlib.redirect_stdout(io.StringIO()):
        s = runpy.run_path(str(Path(__file__).with_name('wall1_draw14_frontier.py')))
        from wall1_general_two_relations import draw14_bounds
        _, full, strata = draw14_bounds()
        _, _, free_strata = draw14_bounds(exclude_triangular_anchors=True)
    I, mu, q, n, m, radius = [s[k] for k in ('I', 'mu', 'q', 'N', 'm', 'radius')]
    anchor = (equal_pair_sum_ball_bound(radius**2, n, 3)
              +equal_pair_sum_alias_bound(radius**2, n, 3, q))/q**(4*m)
    weights = [sum((I(abs(v.numerator))/v.denominator*mu**d
                    for d, v in enumerate(poly)), I(0)) for poly in difference_weights(12)]
    baseline = {h: full[h] if h <= 13 else s['base'][h] for h in range(3, 25)}
    linear = s['normalizer']*remainder_weights(weights, baseline, 14)[14]
    h = 14
    large_total = I(0)
    rank_nine_two = I(0)
    for r in range(5, 10):
        large = I(0)
        for t in range(2, r-2):
            extra = r-t-3
            group = new_group_bound(radius**2, n, t, q)/q**(m*(t-1))
            value = I(0)
            for a in range(max(1, 4-t), 5):
                choices = comb(h, 6)*75*comb(h-6, t)*comb(4, a)*comb(h-6-t, extra)
                value += (choices*q**(t+a-2)*anchor*group*mu**extra
                          *q**((r-1)*(h-r-3))/(extra+1))
            print('rank', r, 'new points', t, 'log10 weighted envelope',
                  iv.log10(linear*value), flush=True)
            if t >= 3:
                large += value
            elif r == 9:
                rank_nine_two = value
        large_total += large
    assert linear*large_total < I('1.566e-25')
    assert linear*rank_nine_two < I('1.484e-24')
    print('All >=3-new-point witness families, weighted:', linear*large_total, flush=True)
    prior_admitted = sum((free_strata[h, r, c] if c == 4 and 5 <= r <= 9 else value
                          for (size, r, c), value in strata.items() if size == h and r >= 3), I(0))
    baseline[14] += prior_admitted+large_total+rank_nine_two
    known = s['normalizer']*transfer(weights, baseline)
    assert known < I('5.395e-13')
    print('Known transfer including new witness families and all rank-nine triangles:', known)
    print('OPEN: rank-5..8 triangles with only two-new-point crossing witnesses, larger components, histories.')
    return s, baseline, linear


if __name__ == '__main__':
    finite_checks()
    actual_parameters()
