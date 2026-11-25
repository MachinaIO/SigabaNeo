"""Exact enumeration of the unit-line histories in wall1_profile.md."""
from fractions import Fraction
from itertools import product


def enumerate_history(q, n, queries, pivot, event, first_tie=False):
    mass = hit = Fraction(0)
    for row in product(range(q), repeat=n):
        if not row[pivot]:
            continue
        weight = Fraction(1, q**n)
        for indices, chosen in queries:
            axes = [i for i in indices if row[i] == 0]
            if chosen not in axes or (first_tie and chosen != axes[0]):
                break
            if not first_tie:
                weight /= len(axes)
        else:
            mass += weight
            if all(row[i] for i in event):
                hit += weight
    return mass, hit / mass if mass else None


if __name__ == "__main__":
    for q in (2, 3):
        for n in range(3, 7):
            for first_tie in (False, True):
                for j in (0, 2):
                    queries = [(range(3), j), (range(3), 0), (range(2), 0)]
                    print("revisit", q, n, first_tie, j,
                          enumerate_history(q, n, queries, 1, [2], first_tie))
                if n >= 5:
                    for j in (1, 3):
                        survivors = [i for i in (1, 2, 3) if i != j]
                        queries = [(range(3), 0), (range(1, 4), j)]
                        print("forward", q, n, first_tie, j,
                              enumerate_history(q, n, queries, survivors[0],
                                                [survivors[1], 4], first_tie))
