"""First-moment anchor probability and a check against naive conditioning/deletion."""
import contextlib
from fractions import Fraction as F
from itertools import combinations, product
from math import factorial
from pathlib import Path
import io
import runpy
from wall1_short_relation_shapes import equal_pair_sum_ball_bound, equal_pair_sum_alias_bound


def conditioning_checks():
    points = list(product(range(2), repeat=2))
    outcomes = [tuple((b+a*x+c*y) % 2 == 0 for x, y in points)
                for b, a, c in product(range(2), repeat=3)]
    # All proper subsets are independent in this affine four-circuit.
    for size in range(4):
        for indices in combinations(range(4), size):
            assert F(sum(all(row[i] for i in indices) for row in outcomes), 8) == F(1, 2)**size
    good = [row for row in outcomes if not all(row)]
    assert len(good) == 7
    assert F(sum(row[0] for row in good), len(good)) == F(3, 7)
    assert F(sum(row[0] and row[1] for row in good), len(good)) == F(1, 7)
    moments = [sum((F(factorial(sum(row)), factorial(sum(row)-j))
                    if sum(row) >= j else F(0) for row in outcomes), F(0))/8
               for j in range(5)]
    void = F(sum(not any(row) for row in outcomes), 8)
    assert sum(((-1)**j*moments[j]/factorial(j) for j in range(5)), F(0)) == void == F(1, 8)
    deleted = moments[:]
    deleted[4] = 0
    naive = sum(((-1)**j*deleted[j]/factorial(j) for j in range(5)), F(0))
    assert naive == 0 < void
    # Event-level conditioning is harmless in TV, but does not preserve moments.
    good_indices = [i for i, row in enumerate(outcomes) if not all(row)]
    for mask in range(1 << len(outcomes)):
        unconditional = F(mask.bit_count(), 8)
        conditional = F(sum(mask >> i & 1 for i in good_indices), 7)
        assert abs(unconditional-conditional) <= F(1, 8)
    print('Passed exact affine-square independence/deletion checks and 256 event-TV checks.')


def actual_parameters():
    with contextlib.redirect_stdout(io.StringIO()):
        s = runpy.run_path(str(Path(__file__).with_name('wall1_draw14_frontier.py')))
    radius_sq, n, q, m = s['radius']**2, s['N'], s['q'], s['m']
    main = equal_pair_sum_ball_bound(radius_sq, n, 3)
    aliases = equal_pair_sum_alias_bound(radius_sq, n, 3, q)
    # Five affine-compatible signed pair patterns. Counting ordered witnesses
    # without a symmetry divisor is an upper bound for the existence event.
    probability = 5*(main+aliases)/q**(4*m)
    assert probability < s['I']('3e-87')
    print('Fresh affine-graph eligible triangular-anchor probability <=', probability)
    print('OPEN: a valid conditional/robust void bound; cannot simply delete cumulant terms.')


if __name__ == '__main__':
    conditioning_checks()
    actual_parameters()
