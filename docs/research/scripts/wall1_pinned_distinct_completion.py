"""Exact pinned distinct-completion counting; no production bound claim."""
from fractions import Fraction
from itertools import combinations, permutations
from math import prod


def completions(cardinality, used, order):
    assert min(cardinality, used, order) >= 0
    if cardinality < used + order:
        return 0
    return prod(range(cardinality-used-order+1, cardinality-used+1))


def checks():
    checked = 0
    for cardinality in range(8):
        universe = set(range(cardinality))
        for used in range(cardinality+1):
            for forbidden in combinations(universe, used):
                available = universe.difference(forbidden)
                for order in range(5):
                    actual = sum(1 for _ in permutations(available, order))
                    assert actual == completions(cardinality, used, order)
                    for cap in range(cardinality, 10):
                        assert actual <= completions(cap, used, order)
                    checked += 1
    for cap in (24, 100, 10**30):
        for used in range(1, 24):
            for order in range(25-used):
                ratio = Fraction(completions(cap, used, order), cap**order)
                loss = Fraction(order*used+order*(order-1)//2, cap)
                assert 1-loss <= ratio <= 1
                checked += 1
    assert -1665 % 3329 == 1664 % 3329
    assert max(1665**2, 1664**2) < 2933**2
    print(f'PASS: {checked} exact distinct-completion and relative-factor checks.')


if __name__ == '__main__':
    checks()
