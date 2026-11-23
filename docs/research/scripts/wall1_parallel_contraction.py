"""Parallel-class contraction after excluding large crossing circuits."""
import contextlib
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from math import comb
import io
from wall1_short_relation_shapes import equal_pair_sum_ball_bound, equal_pair_sum_alias_bound
from wall1_factorial_cumulants import difference_weights
from wall1_linear_remainder import transfer


def associated_stirling(n, k):
    table = {(0, 0): 1}
    for size in range(1, n+1):
        for blocks in range(1, k+1):
            table[size, blocks] = (blocks*table.get((size-1, blocks), 0)
                                  +(size-1)*table.get((size-2, blocks-1), 0))
    return table.get((n, k), 0)


def parallel_completion_count(outside, quotient_rank, anchor_rank, q):
    """No-large-crossing completion cover, with fixed class representatives."""
    return sum(comb(outside, loops)*associated_stirling(outside-loops, quotient_rank)
               *q**(anchor_rank*(outside-loops-quotient_rank)+(anchor_rank-1)*loops)
               for loops in range(outside-2*quotient_rank+1))


def marked_parallel_completion_count(outside, other_classes, anchor_rank, q):
    """One already represented class may receive any number of extra points."""
    return sum(comb(outside,j)*q**(anchor_rank*j)
               *parallel_completion_count(outside-j,other_classes,anchor_rank,q)
               for j in range(outside+1))


def single_class_pair_completion_count(outside, anchor_rank, q):
    """Pair-marked rank-one quotient cover, divided by its exact multiplicity."""
    assert outside>=0 and anchor_rank>=1 and q>=2
    return sum((F(comb(outside,j)*q**(anchor_rank*j+(anchor_rank-1)*(outside-j)),
                  comb(j+2,2)) for j in range(outside+1)),F(0))


def weighted_partition_checks():
    checked = 0
    for anchor_rank in (4,5):
        for q in (3,7):
            values = {(0,0): 1}
            for n in range(19):
                for k in range(10):
                    if n:
                        # Insert a loop, insert into an existing class, or
                        # pair the new label with a singleton to form a class.
                        values[n,k] = ((q**(anchor_rank-1)+k*q**anchor_rank)
                                       *values.get((n-1,k),0)
                                       +(n-1)*q**anchor_rank*values.get((n-2,k-1),0))
                    assert values.get((n,k),0) == parallel_completion_count(n,k,anchor_rank,q)
                    checked += 1
    print(f'Passed {checked} exact weighted-partition recurrence checks.')
    checked = 0
    for d in (4,5):
        q = 3
        values = {(0,0): 1}
        for n in range(17):
            for k in range(9):
                if n:
                    values[n,k] = ((q**(d-1)+(k+1)*q**d)*values.get((n-1,k),0)
                                   +(n-1)*q**d*values.get((n-2,k-1),0))
                assert values.get((n,k),0) == marked_parallel_completion_count(n,k,d,q)
                checked += 1
    print(f'Passed {checked} exact marked-class recurrence checks.')


def partition_checks():
    partitions = [()]
    checked = 0
    for n in range(9):
        counts = Counter(len(p) for p in partitions if all(len(block) >= 2 for block in p))
        for k in range(9):
            assert counts[k] == associated_stirling(n, k)
            checked += 1
        nxt = []
        for p in partitions:
            nxt.append((*p, (n,)))
            for i in range(len(p)):
                nxt.append(tuple((*block, n) if j == i else block for j, block in enumerate(p)))
        partitions = nxt
    print(f'Passed {checked} associated-partition counts against exact set partitions.')


def pivot_checks():
    cases = pivots = parallel = 0
    for q, r in ((3, 4), (2, 5)):
        x = {0, 1}
        y = set(range(2, r))
        vectors = [v for v in product(range(q), repeat=r) if any(v)]
        for first, second in combinations(vectors, 2):
            extras = [(1, 1)+((0,)*(r-2)), first, second]
            supports = [{i for i, a in enumerate(v) if a} for v in extras]
            reached = {0}
            while True:
                enlarged = reached | set().union(*(s for s in supports if s & reached))
                if enlarged == reached:
                    break
                reached = enlarged
            if len(reached) != r:
                continue
            cases += 1
            if any(s & x and len(s & y) >= 2 for s in supports):
                continue  # A large crossing witness already exists in this basis.
            pure = [i for i, s in enumerate(supports) if not s & x and len(s & y) >= 2]
            if not pure:
                assert all(len(s & y) <= 1 for s in supports)
                parallel += 1
                continue
            found = False
            for i, s in enumerate(supports):
                if not s & x or len(s & y) != 1:
                    continue
                b = next(iter(s & y))
                for j in pure:
                    if b not in supports[j]:
                        continue
                    e, f = extras[i], extras[j]
                    scale = f[b]*pow(e[b], -1, q) % q
                    coordinates = [(a-scale*c) % q for a, c in zip(f, e)]
                    coordinates[b] = scale
                    assert any(coordinates[a] for a in x)
                    assert sum(bool(coordinates[a]) for a in y) >= 2
                    # Reconstruct the old vector in the single-pivot basis.
                    recovered = [(coordinates[a] if a != b else 0)+scale*e[a] for a in range(r)]
                    assert tuple(a % q for a in recovered) == f
                    found = True
                    pivots += 1
            assert found
    assert cases and pivots and parallel
    print(f'Passed {cases} connected fundamental graphs, {pivots} pivot witnesses, {parallel} parallel cases.')


def actual_parameters():
    from wall1_triangular_third_relation import actual_parameters as prior
    with contextlib.redirect_stdout(io.StringIO()):
        s, baseline, linear = prior()
    I, iv, mu, q, n, m, radius = [s[k] for k in ('I', 'iv', 'mu', 'q', 'N', 'm', 'radius')]
    anchor = (equal_pair_sum_ball_bound(radius**2, n, 3)
              +equal_pair_sum_alias_bound(radius**2, n, 3, q))/q**(4*m)
    admitted = I(0)
    for k in range(1, 5):
        completions = parallel_completion_count(8,k,4,q)
        activity = comb(14, 6)*75*anchor*mu**k*completions
        print('rank', k+4, 'parallel-class weighted envelope:', linear*activity, flush=True)
        if k >= 2:
            admitted += activity
    assert linear*admitted < I('3.219e-17')
    baseline[14] += admitted
    weights = [sum((I(abs(v.numerator))/v.denominator*mu**d
                    for d, v in enumerate(poly)), I(0)) for poly in difference_weights(12)]
    known = s['normalizer']*transfer(weights, baseline)
    assert known < I('5.396e-13')
    assert F(5396, 10**16)+F(24692, 10**16) == F(30088, 10**16)
    assert F(9131+5396+24692, 10**16) < F(3922, 10**15)
    print('Known transfer including ranks six through eight:', known)
    print('OPEN at size 14: rank-five triangular configurations; larger sizes and histories also open.')
    return s, baseline, linear


if __name__ == '__main__':
    partition_checks()
    weighted_partition_checks()
    pivot_checks()
    actual_parameters()
