"""Bound all exactly cubic retained grids at freezes 21..406.

Uses the existing certified Hermite cap 56.2142 and its unconditional
determinant recurrence. Rank thresholds are outward-interval certified;
each probability comparison is an exact integer inequality. This is not
a bound on noncubic selected states or on their void probabilities.
"""
from math import ceil, comb

from wall1_hermite_budget import log_floors, iv


def main():
    floors = log_floors()
    rows = []
    for f in range(21, 407):
        exponent_floor = floors[f] / iv.ln(3329)
        # A float proposes an integer only; both endpoints are verified below.
        d = ceil(float(exponent_floor.a))
        assert exponent_floor > d-1 and exponent_floor < d
        k = 400-d
        assert 0 <= k < min(f, 400)
        exponent = (400-k)*(f-k)
        numerator = 2*comb(505+f, f)
        assert numerator * 10**1155 < 3329**exponent
        rows.append((f, d, k, exponent))
    assert len(rows) == 386 and 386 < 1000
    print('All 386 interval rank thresholds and exact probability comparisons passed.')
    print('Each coordinate-rank exceptional probability < 1e-1155.')
    print('Union over freezes 21..406 < 386e-1155 < 1e-1152.')
    for row in rows:
        if row[0] in (21, 52, 375, 395, 404, 406):
            print('freeze, minimum quotient rank, coordinate-rank ceiling, q exponent:', row)
    print('Scope: exactly cubic projected grids, not all failure states.')


if __name__ == '__main__':
    main()
