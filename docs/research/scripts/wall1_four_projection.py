"""Exact old-coordinate projection and parity checks for balanced four rows."""
from fractions import Fraction as F
from itertools import product
from collections import Counter


def finite_checks():
    checked = 0
    C = (1, 1, -1, -1)
    for z in product(range(-4, 5), repeat=4):
        projection = sum(x*x for x in z)-F(sum(z)**2, 4)
        multiplicities = Counter(z)
        if len(multiplicities) > 1:
            assert projection >= F(3, 4)
        if 0 < projection < 2:
            # Range >=2 already forces variance >=2, so these are all
            # integer translates of a binary pattern.
            assert max(z)-min(z) == 1
            odd = sum(c*x for c,x in zip(C,z)) % 2
            if not odd:
                assert sorted(multiplicities.values()) == [2, 2]
                assert 1 not in multiplicities.values()
        if 1 in multiplicities.values() and sum(c*x for c,x in zip(C,z)) % 2 == 0:
            assert projection >= 2
        checked += 1
    print(f'Passed {checked} exact four-coordinate projection/parity checks.')


if __name__ == '__main__':
    finite_checks()
