"""Exact coefficient counts for two norm-four directions on seven positions."""
from collections import Counter
from itertools import product
from mpmath import iv
from wall1_short_relation_shapes import (
    balanced_rows, line_words, shared_four_gaussian_bound, shared_four_ball_bound)


def normalized(word, q):
    pivot = next(x for x in word if x % q)
    return tuple(x*pow(pivot, -1, q) % q for x in word)


def finite_checks():
    checked = 0
    first_support = frozenset(range(4))
    for q in (5, 7, 17):
        codes = {}
        for first in balanced_rows(tuple(first_support), 7):
            for shared in first_support:
                for second in balanced_rows((shared, 4, 5, 6), 7):
                    lines = tuple(sorted(normalized(w, q) for w in line_words(first, second, q)))
                    assert len(set(lines)) == q+1
                    assert lines not in codes
                    codes[lines] = shared
                    fours = [w for w in lines if sum(bool(x) for x in w) == 4]
                    assert len(fours) == 2
                    checked += 1
        assert len(codes) == 36
        for overlap in (1, 2, 3):
            target = frozenset((*range(overlap), 4, 5, 6))
            matching = 0
            for lines in codes:
                supports = [frozenset(i for i, x in enumerate(w) if x) for w in lines]
                if target in supports:
                    assert supports.count(target) == 1
                    assert not any(s < target for s in supports)
                    matching += 1
            assert matching == (0 if overlap == 2 else 9)
            checked += 1
    print(f'Passed {checked} seven-position code and prescribed-circuit counts (9,0,9).')


def weighted_count_checks():
    iv.dps = 80
    checked = 0
    for n, radius in ((2, 1), (2, 2), (2, 3), (4, 1), (4, 2)):
        points = [x for x in product(range(-radius, radius+1), repeat=n)
                  if sum(t*t for t in x) <= radius**2]
        pairs = Counter(tuple(a+b for a, b in zip(x, y)) for x in points for y in points)
        triples = Counter()
        for pair, count in pairs.items():
            for x in points:
                triples[tuple(a+b for a, b in zip(pair, x))] += count
        real = sum(triples[x]**2 for x in points)
        assert real <= shared_four_ball_bound(iv.mpf(radius**2), n)
        for q in (3, 5, 7, 17):
            modular = Counter()
            for x, count in triples.items():
                modular[tuple(a % q for a in x)] += count
            exact = sum(modular[tuple(a % q for a in x)]**2 for x in points)
            assert exact <= shared_four_gaussian_bound(iv.mpf(radius**2), n, q)
            assert 0 <= exact-real <= shared_four_gaussian_bound(
                iv.mpf(radius**2), n, q, aliases_only=True).b
            checked += 1
    print(f'Passed {checked} exact seven-point modular counts against the weighted bound.')


if __name__ == '__main__':
    finite_checks()
    weighted_count_checks()
