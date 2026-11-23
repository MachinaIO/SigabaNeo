"""Exact conditional collision moments; not a width-506 probability estimate."""
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import product


def apply(matrix, vector, q):
    return tuple(sum(a*b for a, b in zip(row, vector)) % q for row in matrix)


cases = maps_checked = 0
for q, m, d in ((2, 1, 2), (3, 1, 2), (3, 2, 2), (2, 2, 3)):
    # Integer points are distinct even when some have the same residues.
    fixtures = [list(product((0, 1), repeat=m+d)),
                [tuple((j*(h+1)+j//3) % 5-2 for h in range(m+d))
                 for j in range(12)]]
    for points in fixtures:
        points = sorted(set(points))
        for t in range(d+1):
            fixed = [tuple((row+col+1) % q for col in range(t)) for row in range(m)]
            forced = 0
            weights = defaultdict(Counter)
            for z in points:
                for zz in points:
                    dx = tuple(a-b for a, b in zip(z[:m], zz[:m]))
                    dy = tuple(a-b for a, b in zip(z[m:], zz[m:]))
                    image = apply(fixed, dy[:t], q)
                    u = tuple((a-b) % q for a, b in zip(dx, image))
                    v = tuple(a % q for a in dy[t:])
                    if not any(v):
                        forced += not any(u)
                    else:
                        inverse = pow(next(a for a in v if a), -1, q)
                        ell = tuple(a*inverse % q for a in v)
                        output = tuple(a*inverse % q for a in u)
                        weights[ell][output] += 1
            p = F(1, q**m)
            mean = forced + p*sum(sum(row.values()) for row in weights.values())
            variance = sum(p*sum(w*w for w in row.values())
                           - p*p*sum(row.values())**2 for row in weights.values())
            observed = []
            for entries in product(range(q), repeat=m*(d-t)):
                residual = [entries[row*(d-t):(row+1)*(d-t)] for row in range(m)]
                matrix = [fixed[row]+tuple(residual[row]) for row in range(m)]
                labels = Counter()
                for z in points:
                    ay = apply(matrix, z[m:], q)
                    labels[tuple((a-b) % q for a, b in zip(z[:m], ay))] += 1
                collisions = sum(count*count for count in labels.values())
                predicted = forced + sum(row[apply(residual, ell, q)]
                                         for ell, row in weights.items())
                assert collisions == predicted
                observed.append(collisions)
            assert len(observed) == q**(m*(d-t))
            assert F(sum(observed), len(observed)) == mean
            assert sum((F(value)-mean)**2 for value in observed)/len(observed) == variance
            for gap in (F(1, 2), F(1), F(3), F(10)):
                actual = F(sum(value > mean+gap for value in observed), len(observed))
                assert actual <= variance/(variance+gap*gap)
            if t == d:
                assert not weights and variance == 0 and observed == [forced]
            cases += 1
            maps_checked += len(observed)
print(f'Passed {cases} conditional fixtures and {maps_checked} residual-map enumerations.')
