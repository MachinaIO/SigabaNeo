"""Arithmetic certificate for the marked-Gram reachability obstruction.

The general determinant lemma is proved in wall1_gram_multheight.md.
This script certifies its numerical contradiction, not the lemma itself.
"""
from math import factorial
from mpmath import iv


def main():
    # V_506 = pi^253 / 253!, and pi > 3.
    assert 3**253 * 549**506 > factorial(253) * 102**400
    iv.dps = 80
    volume = iv.pi**253 / factorial(253)
    ceiling = (iv.mpf(102)**400 / volume)**(iv.mpf(1) / 506)
    assert ceiling.b < iv.mpf('212.241').a
    print('Exact determinant contradiction passed for g >= 549.')
    print('Scale ceiling from unit-generated K and marked Gram bound:', ceiling)


if __name__ == '__main__':
    main()
