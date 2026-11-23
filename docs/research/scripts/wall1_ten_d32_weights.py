"""Exact rational Gram checks for ten-position determinant-32 planes."""
from fractions import Fraction as F
from math import prod
from wall1_short_relation_shapes import balanced_rows
from wall1_rare_second_line import norm_rows


def checks():
    rows = [v for v in norm_rows(10, 8) if all(v[4:])]
    checked = 0
    for a in balanced_rows((0, 1, 2, 3), 10):
        for b in rows:
            if sum(x*y for x, y in zip(a, b)) != 0:
                continue
            shared = [i for i in range(4) if b[i]]
            assert len(shared) == 2 and all(abs(x) <= 1 for x in b)
            weights = [F(1)]*4 + [F(9, 8)]*6
            for i in shared:
                weights[i] = F(5, 8)
            assert sum(weights) == 10
            def inner(x, y):
                return sum(F(u*v)/w for u, v, w in zip(x, y, weights))
            first = inner(a, a)
            second = inner(b, b)-inner(a, b)**2/first
            assert inner(a, b) == 0
            assert (first, second) == (F(26, 5), F(128, 15))
            assert prod(weights)*first*second > 32
            # An exclusive old coordinate and a new coordinate give a unit minor.
            assert any(a[i] and not b[i] for i in range(4))
            checked += 1
    assert checked == 300
    print(f'Passed {checked} exact weighted Gram and unit-minor checks.')
    print('Weighted determinant product:', prod(weights)*first*second)


if __name__ == '__main__':
    checks()
