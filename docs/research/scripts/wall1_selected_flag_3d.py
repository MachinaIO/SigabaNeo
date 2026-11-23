"""Complete three-dimensional first-selection tests with residual randomness.

Exact finite examples only: no extrapolation to width 506 or later draws.
"""
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import floor, isqrt
from span_exclusion import grouped_subsets
from conditional_graph_space import ConditionalGraphSpace
from void_square_polynomial import falling, kernel_value, mixed_square_expectation
from optimal_void_square import optimal_square, weighted_gram
from joint_tail_square import evaluate as joint_evaluate, joint_gram, optimal_one_sided_square


def dot(left, right):
    return sum(a*b for a, b in zip(left, right))


cases = biased_cases = 0
mixed_checks = mixed_improvements = 0
optimal_improvements = 0
joint_improvements = 0
bias_witness = None
for q in (3, 5):
    zero = (0, 0, 0)

    def label(matrix, point):
        return (point[0]-dot(matrix, point[1:])) % q

    matrices = list(product(range(q), repeat=2))
    signed = sorted((dot(v, v), v) for v in product(range(-1, 2), repeat=3)
                    if v != zero and v < tuple(-a for a in v))
    # All integer vectors of squared norm <=3 are in this cube. Finding a member
    # for every design certifies that each direct winner is globally shortest.
    winners = {a: next(key for key in signed if label(a, key[1]) == 0) for a in matrices}
    assert len(winners) == q*q
    radii = (F(1, 4), F(3, 4), F(1), F(2))
    sums = {radius: [F(0), F(0), F(0), F(0), F(0), F(0)] for radius in radii}
    for key in signed:
        length_sq, winner = key
        if not any(winner[1:]):
            continue
        model = ConditionalGraphSpace(q, 1, 2, [winner])
        base = ()
        extend = lru_cache(None)(model.extend)
        conditional = [a for a in matrices if label(a, winner) == 0]
        assert len(conditional) == q  # One independent input remains unread.
        forbidden = set()
        for earlier in signed:
            if earlier >= key:
                break
            v = tuple(a % q for a in earlier[1])
            inverse = pow(next(a for a in v if a), -1, q)
            forbidden.add(tuple(a*inverse % q for a in v))
        forbidden = sorted(forbidden)
        layers = grouped_subsets(base, [model.reduce(v) for v in forbidden],
                                 extend, model.graphic)

        @lru_cache(None)
        def probability(space):
            # The integral winner is primitive in the ambient lattice: E=F.
            # Thus saturation imposes nothing beyond containment in this fixture.
            return model.joint_probability(space)

        for radius_sq in radii:
            bound = radius_sq+F(length_sq, 4)
            limit = isqrt(bound.numerator//bound.denominator)
            points = [z for z in product(range(-limit, limit+1), repeat=3)
                      if -F(1, 2) <= F(dot(z, winner), length_sq) < F(1, 2)
                      and dot(z, z)-F(dot(z, winner)**2, length_sq) <= radius_sq]
            weights = Counter(model.reduce(tuple((x-y) % q for x, y in zip(z, zz)))
                              for z in points for zz in points)

            @lru_cache(None)
            def moments(space):
                return (probability(space),
                        sum(w*probability(extend(space, v)) for v, w in weights.items()),
                        sum(w*ww*probability(extend(extend(space, v), vv))
                            for v, w in weights.items() for vv, ww in weights.items()))

            rows = [[sum(count*moments(space)[i] for space, count in layer.items())
                     for i in range(3)] for layer in layers]
            selected = [sum((-1)**j*row[i] for j, row in enumerate(rows)) for i in range(3)]
            actual = [F(0), F(0), F(0)]
            observed_joint = []
            tail = void_exit = 0
            threshold = F(25*len(points)**2, 18*q)
            for a in conditional:
                labels = Counter(label(a, z) for z in points)
                collisions = sum(w*w for w in labels.values())
                assert collisions % 2 == len(points) % 2
                chosen = all(label(a, z) != 0 for z in forbidden)
                observed_joint.append((sum(label(a, z) == 0 for z in forbidden), collisions))
                assert chosen == (winners[a] == key)
                if chosen:
                    actual[0] += 1
                    actual[1] += collisions
                    actual[2] += collisions**2
                    tail += collisions > threshold
                    void_exit += F(q-len(labels), q) > F(7, 25)
            assert selected == [v/q for v in actual]
            assert void_exit <= tail
            mass, first, second = selected
            upper = mass
            if mass:
                mean = first/mass
                variance = second/mass-mean*mean
                assert variance >= 0
                if 0 < mass < 1 and mean != moments(base)[1]:
                    biased_cases += 1
                    if bias_witness is None:
                        bias_witness = (q, winner, radius_sq, mass, moments(base)[1], mean)
                if threshold > mean:
                    upper = mass*variance/(variance+(threshold-mean)**2)
                elif variance == 0 and threshold == mean:
                    upper = F(0)  # Strict-tail event is empty.
            assert F(tail, q) <= upper <= mass
            parity_upper = upper
            tail_start = floor(threshold)+1
            tail_start += (len(points)-tail_start) % 2
            if mass:
                centers = set(range(floor(first/mass)-3, floor(first/mass)+4))
                centers.add(tail_start-3)
                for c in centers:
                    if c % 2 == len(points) % 2 or c > tail_start-3:
                        continue
                    numerator = second-2*c*first+(c*c-1)*mass
                    assert numerator >= 0
                    candidate = numerator/((tail_start-c)**2-1)
                    assert F(tail, q) <= candidate
                    parity_upper = min(parity_upper, candidate)
                    for cutoff in range(0, len(forbidden)+2, 2):
                        truncated = sum((-1)**j*(row[2]-2*c*row[1]+(c*c-1)*row[0])
                                        for j, row in enumerate(rows) if j <= cutoff)
                        assert truncated >= numerator
                        assert F(tail, q) <= truncated/((tail_start-c)**2-1)
            center = F(len(points)**2, q)
            true_square = second-2*center*first+center*center*mass
            for cutoff in range(0, len(forbidden)+2, 2):
                square_upper = sum((-1)**j*(row[2]-2*center*row[1]+center**2*row[0])
                                   for j, row in enumerate(rows) if j <= cutoff)
                assert square_upper >= true_square >= 0
                assert F(tail, q) <= square_upper/(threshold-center)**2
            mu = rows[1][0] if len(rows) > 1 else F(0)
            joint_upper = parity_upper
            assert mu == F(sum(z for z, j in observed_joint), q)
            for degree in (1, 2, 3):
                mixed = mixed_square_expectation(rows, mu, degree, center,
                                                 event_count=len(forbidden))
                direct_mixed = sum((j-center)**2*kernel_value(z, mu, degree)**2
                                   for z, j in observed_joint)/q
                assert mixed == direct_mixed >= true_square >= 0
                assert F(tail, q) <= mixed/(threshold-center)**2
                bonferroni = sum((-1)**h*(row[2]-2*center*row[1]+center**2*row[0])
                                  for h, row in enumerate(rows) if h <= 2*degree)
                mixed_improvements += mixed < bonferroni
                mixed_checks += 1
                gram = weighted_gram([row[2]-2*center*row[1]+center**2*row[0]
                                      for row in rows], degree, event_count=len(forbidden))
                coefficients, optimum = optimal_square(gram)
                direct_optimum = sum((j-center)**2
                                     * sum(c*falling(z, h) for h, c in enumerate(coefficients))**2
                                     for z, j in observed_joint)/q
                assert optimum == direct_optimum >= true_square
                assert optimum <= mixed
                assert F(tail, q) <= optimum/(threshold-center)**2
                optimal_improvements += optimum < mixed
                matrix = joint_gram(rows, degree, tail_start, event_count=len(forbidden))
                joint_coefficients, joint_value = optimal_one_sided_square(matrix)
                direct_joint = sum(joint_evaluate(joint_coefficients, z, j, tail_start)**2
                                   for z, j in observed_joint)/q
                assert joint_value == direct_joint
                assert F(tail, q) <= joint_value
                # The product certificate is feasible in the enlarged polynomial class.
                assert joint_value <= optimum/(tail_start-center)**2
                joint_improvements += joint_value < optimum/(tail_start-center)**2
                joint_upper = min(joint_upper, joint_value)
            sums[radius_sq][0] += mass/q
            sums[radius_sq][1] += F(void_exit, q*q)
            sums[radius_sq][2] += F(tail, q*q)
            sums[radius_sq][3] += upper/q
            sums[radius_sq][4] += parity_upper/q
            sums[radius_sq][5] += joint_upper/q
            cases += 1
    for radius, (mass, void, tail, upper, parity, joint) in sums.items():
        assert mass == 1 and void <= tail <= joint <= parity <= upper <= 1
        print(f'q={q}, R^2={radius}: total mass={mass}, void exit={void}, '
              f'certificate failure={tail}, variance upper={upper}, parity upper={parity}, '
              f'combined joint upper={joint}')
assert biased_cases > 0
print('First bias witness (q, winner, R^2, selection mass given containment, '
      'containment mean, selected mean):', bias_witness)
print(f'Passed {cases} three-dimensional flag/radius cases; '
      f'{biased_cases} cases have a collision-mean change after selection.')
print(f'Passed {mixed_checks} mixed square identities and tail bounds; '
      f'{mixed_improvements} improve on the same-degree Bonferroni numerator.')
print(f'Weighted-optimal squares passed all {mixed_checks} cases; '
      f'{optimal_improvements} strictly improve on the same-degree Charlier square.')
print(f'Joint squares passed all {mixed_checks} cases; '
      f'{joint_improvements} strictly improve on the optimized product at the same integer threshold.')
