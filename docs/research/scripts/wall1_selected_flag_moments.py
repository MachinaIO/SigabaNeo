"""Exact planar shortest-selection, rank-formula and weighted Bonferroni checks."""
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, product
from math import gcd, isqrt
from span_exclusion import grouped_subsets

cases = 0
subset_terms = moment_states = 0
for q in (3, 5):
    zero = (0, 0)

    def span(vectors):
        result = {zero}
        for v in vectors:
            result = {((x+a*v[0]) % q, (y+a*v[1]) % q)
                      for x, y in result for a in range(q)}
        return frozenset(result)

    def dim(space):
        return {1: 0, q: 1, q*q: 2}[len(space)]

    def input_rank(space):
        return int(any(y for x, y in space))

    @lru_cache(None)
    def extend(space, vector):
        return span(tuple(space)+(vector,))

    def sat(large, contained):
        r, t, s = dim(large), dim(contained), input_rank(large)
        if input_rank(contained) != t or r-t > 1:
            return F(0)
        answer = F(1)
        for j in range(s-t):
            answer *= 1-F(q**(r-s+j), q)
        return answer

    signed = sorted((x*x+y*y, x, y)
                    for x in range(-q, q+1) for y in range(-q, q+1)
                    if (x < 0 or x == 0 and y < 0) and x*x+y*y <= q*q)
    winners = {a: next(key for key in signed if (key[1]-a*key[2]) % q == 0)
               for a in range(q)}
    for key in signed:
        length_sq, x, y = key
        index = gcd(x, y)
        if index not in (1, q):
            continue  # q Lambda subset Gamma is necessary.
        large = span([(x//index, y//index)])
        contained = span([(x, y)])
        t = dim(contained)
        if input_rank(contained) != t:
            continue
        conditional = [a for a in range(q) if (x-a*y) % q == 0]
        assert F(len(conditional), q) == F(1, q**t)

        def joint(vectors):
            augmented = span(list(contained)+list(vectors))
            u = dim(augmented)
            if input_rank(augmented) != u or large & augmented != contained:
                return F(0)
            return F(1, q**(u-t))*sat(span(list(large)+list(augmented)), augmented)

        # Merge identical modular membership events, retaining forced zero residues.
        forbidden = set()
        for competitor in signed:
            if competitor >= key:
                break
            v = tuple(a % q for a in competitor[1:])
            if any(v):
                inv = pow(next(a for a in v if a), -1, q)
                v = tuple(a*inv % q for a in v)
            forbidden.add(v)
        forbidden = sorted(forbidden)

        def admissible(space):
            return input_rank(space) == dim(space) and large & space == contained

        layers = grouped_subsets(contained, forbidden, extend, admissible)
        # Independent subset enumeration verifies the grouped coefficients exactly.
        for degree, layer in enumerate(layers):
            brute = Counter()
            for subset in combinations(forbidden, degree):
                state = span(tuple(contained)+subset)
                if admissible(state):
                    brute[state] += 1
            assert layer == brute
        assert grouped_subsets(contained, forbidden, extend, admissible, 2) == layers[:3]
        for radius_sq in (F(1, 4), F(1), F(4)):
            bound = radius_sq+F(length_sq, 4)
            limit = isqrt(bound.numerator//bound.denominator)
            points = [(z, w) for z, w in product(range(-limit, limit+1), repeat=2)
                      if -F(1, 2) <= F(z*x+w*y, length_sq) < F(1, 2)
                      and F((y*z-x*w)**2, length_sq) <= radius_sq]
            weights = Counter(((z-zz) % q, (w-ww) % q)
                              for z, w in points for zz, ww in points)
            # Cache joint probabilities by the actual span of imposed equations.
            @lru_cache(None)
            def probability(imposed):
                return joint(imposed)

            @lru_cache(None)
            def moments(state):
                return (probability(state),
                        sum(w*probability(extend(state, v)) for v, w in weights.items()),
                        sum(w*ww*probability(extend(extend(state, v), vv))
                            for v, w in weights.items() for vv, ww in weights.items()))

            by_order = []
            for layer in layers:
                by_order.append([sum(count*moments(state)[k] for state, count in layer.items())
                                 for k in range(3)])
            subset_terms += 2**len(forbidden)
            moment_states += moments.cache_info().currsize
            exact = [sum((-1)**j*row[k] for j, row in enumerate(by_order))
                     for k in range(3)]
            direct = [F(0), F(0), F(0)]
            tail_count = 0
            center = F(len(points)**2, q)
            threshold = F(25, 18)*center
            for a in conditional:
                labels = Counter((z-a*w) % q for z, w in points)
                collisions = sum(v*v for v in labels.values())
                kernel = frozenset((a*b % q, b) for b in range(q))
                selected = large & kernel == contained and all(
                    (v[0]-a*v[1]) % q != 0 for v in forbidden)
                assert selected == (winners[a] == key)
                if selected:
                    direct[0] += 1
                    direct[1] += collisions
                    direct[2] += collisions**2
                    tail_count += collisions > threshold
            direct = [value/len(conditional) for value in direct]
            assert exact == direct
            true_square = direct[2]-2*center*direct[1]+center**2*direct[0]
            for cutoff in range(0, len(forbidden)+2, 2):
                upper = sum((-1)**j*(row[2]-2*center*row[1]+center**2*row[0])
                            for j, row in enumerate(by_order) if j <= cutoff)
                assert upper >= true_square >= 0
                assert F(tail_count, len(conditional)) <= upper/(threshold-center)**2
            cases += 1
print(f'Passed {cases} selected-flag/radius cases, exact moments and weighted tail bounds.')
print(f'{subset_terms} subset moment evaluations replaced by {moment_states} span evaluations.')
