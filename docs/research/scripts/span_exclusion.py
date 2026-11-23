"""Group subset sums by generated span while retaining Bonferroni degree.

`extend(state, event)` returns the span after adding an event. `admissible`
must reject only states whose every extension has zero contribution.
States and events may be any hashable objects; arithmetic is exact integer.
"""
from collections import Counter


def grouped_subsets(base, events, extend, admissible=lambda state: True, max_order=None):
    events = tuple(events)
    if max_order is None:
        max_order = len(events)
    if max_order < 0:
        raise ValueError('max_order must be nonnegative')
    cap = min(max_order, len(events))
    layers = [Counter() for _ in range(cap+1)]
    if admissible(base):
        layers[0][base] = 1
    for processed, event in enumerate(events):
        # Descending degree prevents reusing this event in the same subset.
        for degree in range(min(processed, cap-1), -1, -1):
            for state, count in tuple(layers[degree].items()):
                enlarged = extend(state, event)
                if admissible(enlarged):
                    layers[degree+1][enlarged] += count
    return layers
