"""Exhaustive finite checks of saturation and joint collision probabilities."""
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from conditional_graph_space import ConditionalGraphSpace, row_basis

flags_checked = joint_checks = 0
for q, m, d in ((2, 1, 2), (3, 1, 2), (2, 2, 2)):
    n = m+d
    vectors = list(product(range(q), repeat=n))
    zero = (0,)*n
    origin = frozenset([zero])

    def dim(space):
        size, rank = len(space), 0
        while size > 1:
            assert size % q == 0
            size //= q
            rank += 1
        return rank

    @lru_cache(None)
    def extend(space, v):
        return frozenset(tuple((x+a*y) % q for x, y in zip(w, v))
                         for w in space for a in range(q))

    @lru_cache(None)
    def join(left, right):
        result = left
        for v in sorted(right):
            if v not in result:
                result = extend(result, v)
        return result

    spaces = {origin}
    pending = [origin]
    while pending:
        old = pending.pop()
        for v in vectors:
            new = extend(old, v)
            if new not in spaces:
                spaces.add(new)
                pending.append(new)

    def input_rank(space):
        return dim(frozenset(v[m:] for v in space))

    @lru_cache(None)
    def sat_prob(large, contained):
        assert contained <= large
        rank = dim(contained)
        if input_rank(contained) != rank:
            return F(0)
        r, s = dim(large), input_rank(large)
        a = r-s
        if r-rank > m:
            return F(0)
        answer = F(1)
        for j in range(s-rank):
            answer *= 1-F(q**(a+j), q**m)
        return answer

    kernels = []
    for entries in product(range(q), repeat=m*d):
        kernel = frozenset(v for v in vectors if all(
            (v[row]-sum(entries[row*d+col]*v[m+col] for col in range(d))) % q == 0
            for row in range(m)))
        kernels.append(kernel)

    # Ordered pair differences of a fixed small candidate set, with multiplicities.
    points = [zero, vectors[1], vectors[-1]]
    differences = Counter(tuple((a-b) % q for a, b in zip(z, zz))
                          for z in points for zz in points)
    for large in sorted(spaces, key=lambda s: (len(s), sorted(s))):
        for contained in sorted(spaces, key=lambda s: (len(s), sorted(s))):
            if not contained <= large or input_rank(contained) != dim(contained):
                continue
            conditional = [k for k in kernels if contained <= k]
            saturated = [k for k in conditional if k & large == contained]
            t = dim(contained)
            model = ConditionalGraphSpace(q, m, d, contained)
            residual_saturation = row_basis((model.reduce(v) for v in large), q)
            assert len(residual_saturation) == dim(large)-t
            assert model.joint_probability((), residual_saturation) == sat_prob(large, contained)
            assert F(len(conditional), len(kernels)) == F(1, q**(m*t))
            assert F(len(saturated), len(conditional)) == sat_prob(large, contained)

            def joint(extra):
                augmented = contained
                for v in extra:
                    augmented = extend(augmented, v)
                u = dim(augmented)
                if input_rank(augmented) != u or augmented & large != contained:
                    answer = F(0)
                else:
                    answer = F(1, q**(m*(u-t))) * sat_prob(join(large, augmented), augmented)
                residual = row_basis((model.reduce(v) for v in extra), q)
                assert model.joint_probability(residual, residual_saturation) == answer
                return answer

            predicted_first = sum(w*joint((v,)) for v, w in differences.items())
            predicted_second = sum(w*ww*joint((v, vv))
                                   for v, w in differences.items()
                                   for vv, ww in differences.items())
            collision_counts = [sum(w for v, w in differences.items() if v in k)
                                for k in saturated]
            assert predicted_first == F(sum(collision_counts), len(conditional))
            assert predicted_second == F(sum(j*j for j in collision_counts), len(conditional))
            flags_checked += 1
            joint_checks += len(differences)+len(differences)**2
print(f'Passed {flags_checked} nested-space cases and {joint_checks} joint-moment terms.')
