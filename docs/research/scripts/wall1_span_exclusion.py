"""Exhaustive rank-three coefficient checks, including forced/repeated events."""
from collections import Counter
from itertools import combinations
from span_exclusion import grouped_subsets


def extend(space, vector):
    return frozenset(space | {v ^ vector for v in space})


def span(vectors, base=frozenset({0})):
    for v in vectors:
        base = extend(base, v)
    return base


spaces = {span(subset) for size in range(8) for subset in combinations(range(1, 8), size)}
assert len(spaces) == 16
cases = 0
for base in spaces:
    for mask in range(128):
        events = [v for v in range(1, 8) if mask & (1 << (v-1))]
        for forbidden in (None, 7):
            def admissible(state):
                return forbidden is None or forbidden not in state

            layers = grouped_subsets(base, events, extend, admissible)
            for degree, layer in enumerate(layers):
                expected = Counter(span(subset, base) for subset in combinations(events, degree)
                                   if admissible(span(subset, base)))
                assert layer == expected
            for cap in (0, 1, 2):
                assert grouped_subsets(base, events, extend, admissible, cap) == layers[:cap+1]
            cases += 1

for events in ([0], [1, 1], [0, 1, 1, 2], []):
    layers = grouped_subsets(frozenset({0}), events, extend)
    for degree, layer in enumerate(layers):
        assert layer == Counter(span(subset) for subset in combinations(events, degree))
    cases += 1
print(f'Passed {cases} rank-three grouping, pruning, truncation and repeated-event cases.')
