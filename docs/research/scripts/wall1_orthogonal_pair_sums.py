"""Exact regressions for the orthogonal six-point ball count and aliases."""
from collections import Counter
from fractions import Fraction as F
from itertools import product
from mpmath import iv
from wall1_short_relation_shapes import orthogonal_pair_ball_bound, orthogonal_pair_alias_bound


def finite_checks():
    iv.dps = 80
    checked = 0
    for n, radius in ((2, 1), (2, 2), (2, 3), (4, 1), (4, 2)):
        points = [x for x in product(range(-radius, radius+1), repeat=n)
                  if sum(t*t for t in x) <= radius**2]
        pairs = Counter(tuple(a+b for a, b in zip(x, y)) for x in points for y in points)
        exact = sum(pairs[tuple(a+b for a, b in zip(x, y))]
                    *pairs[tuple(a-b for a, b in zip(x, y))] for x in points for y in points)
        assert exact <= orthogonal_pair_ball_bound(iv.mpf(radius**2), n)
        for q in (3, 5, 7, 17):
            modular = Counter()
            for x, count in pairs.items():
                modular[tuple(a % q for a in x)] += count
            total = sum(modular[tuple((a+b) % q for a, b in zip(x, y))]
                        *modular[tuple((a-b) % q for a, b in zip(x, y))]
                        for x in points for y in points)
            assert 0 <= total-exact <= orthogonal_pair_alias_bound(iv.mpf(radius**2), n, q).b
            checked += 1
    rows = ((1, 1, -1, -1, 0, 0), (1, -1, 0, 0, 1, -1))
    # Free coordinates are x1,x2,x3,x5. The solved coordinates x4,x6 are integral.
    basis = ((0, 0, 1, -1, 0, 0), (0, 0, 0, 0, 1, 1),
             (1, 0, 0, 1, 0, 1), (0, 1, 0, 1, 0, -1))
    orthogonal = []
    for v in basis:
        assert all(sum(a*b for a, b in zip(v, row)) == 0 for row in rows)
        w = list(map(F, v))
        for u in orthogonal:
            coefficient = sum(a*b for a, b in zip(w, u))/sum(a*a for a in u)
            w = [a-coefficient*b for a, b in zip(w, u)]
        assert sum(a*a for a in w) == 2
        orthogonal.append(w)
    assert sum(a*b for a, b in zip(*rows)) == 0
    assert all(sum(a*a for a in row) == 4 for row in rows)
    print(f'Passed {checked} exact real/modular counts and four rational Gram--Schmidt checks.')


if __name__ == '__main__':
    finite_checks()
