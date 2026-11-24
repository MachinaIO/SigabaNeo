"""Exact shared-fresh-mark factorial moments, with a partial full-event gate.

The gate A != 0 is not a complete shortest-winner or chronological-history
event. All hits use the SAME fresh column U. This finite check establishes
neither a production moment estimate nor a selected-history probability.
"""
from fractions import Fraction
from itertools import combinations, product
from math import factorial

from fixed_quotient_graph_space import FixedQuotientGraphSpace


Q = 3
CANDIDATES = ((1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 0))
HEIGHTS = (1, 2)
FULL_BAD = (0, 0, 1, 0)
U_ZERO = (0, 0, 0, 1)


def falling(z, k):
    return factorial(z) // factorial(z - k) if z >= k else 0


def main():
    model = FixedQuotientGraphSpace(Q, 2, 2, 0)

    def joint(hits):
        # Exclude U=0 and then A=0; both masses remain unconditional.
        return (model.joint_probability((), hits)
                - model.joint_probability((), hits + (U_ZERO,))
                - model.joint_probability((FULL_BAD,), hits)
                + model.joint_probability((FULL_BAD,), hits + (U_ZERO,)))

    rank_moments = []
    assignment_checks = 0
    for k in range(len(CANDIDATES) + 1):
        total = Fraction(0)
        for ids in combinations(range(len(CANDIDATES)), k):
            for heights in product(HEIGHTS, repeat=k):
                hits = tuple(CANDIDATES[i] + (j,) for i, j in zip(ids, heights))
                mass = joint(hits)
                assert mass >= 0
                total += mass
                assignment_checks += 1
        # On U != 0, each candidate has at most one successful height.
        # Therefore distinct candidate subsets, times k!, give (Z)_k.
        rank_moments.append(factorial(k) * total)

    vectors = tuple(product(range(Q), repeat=2))
    totals = [0] * (len(CANDIDATES) + 1)
    histogram = [0] * (len(CANDIDATES) + 1)
    direct_joint = 0
    for a, u in product(vectors, repeat=2):
        if not any(a) or not any(u):
            continue
        labels = tuple(tuple((z[i] - a[i] * z[2]) % Q for i in range(2))
                       for z in CANDIDATES)
        line = {tuple(j * x % Q for x in u) for j in HEIGHTS}
        z = sum(label in line for label in labels)
        histogram[z] += 1
        for k in range(len(totals)):
            totals[k] += falling(z, k)
        direct_joint += labels[0] in line and labels[1] in line
    direct_moments = tuple(Fraction(x, Q**4) for x in totals)
    assert tuple(rank_moments) == direct_moments
    assert sum(histogram) == 64

    # The two constant axis labels cannot lie on one common scalar line.
    # Independent U per hit instead gives (8/9)*(2/9)^2 = 32/729.
    independent_joint = Fraction(8, 9) * Fraction(2, 9)**2
    shared_joint = sum((joint((CANDIDATES[0] + (j,), CANDIDATES[1] + (l,)))
                        for j, l in product(HEIGHTS, repeat=2)), Fraction(0))
    assert shared_joint == Fraction(direct_joint, Q**4) == 0
    assert independent_joint == Fraction(32, 729) != shared_joint
    print('Exact unconditional M_0,...,M_4:', direct_moments)
    print('Gated Z histogram (out of 81):', tuple(histogram))
    print('Shared versus independent axis-pair joint:', shared_joint, independent_joint)
    print('PASS:', assignment_checks, 'rank assignments; 81 direct (A,U) designs')


if __name__ == '__main__':
    main()
