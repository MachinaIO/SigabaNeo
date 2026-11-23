"""Exact rational checks of whole-flag occupancy, including lost raw labels."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
from math import floor, isqrt


def dot(x, y):
    return sum(a*b for a, b in zip(x, y))


def sub(x, y, scale=1):
    return tuple(a-scale*b for a, b in zip(x, y))


def check(q, slopes, basis):
    n = len(slopes)+1
    orthogonal = []
    for w in basis:
        v = tuple(map(F, w))
        for u in orthogonal:
            v = sub(v, u, dot(v, u)/dot(u, u))
        assert dot(v, v) > 0
        orthogonal.append(v)
    squares = [dot(v, v) for v in orthogonal]

    def project(z):
        p = tuple(map(F, z))
        for v, s2 in zip(orthogonal, squares):
            p = sub(p, v, dot(z, v)/s2)
        return p

    def label(z):
        return (z[0]-dot(slopes, z[1:])) % q

    def reduce(z):
        for w, v, s2 in reversed(list(zip(basis, orthogonal, squares))):
            z = sub(z, w, floor(dot(z, v)/s2+F(1, 2)))
        return z

    def inside(z):
        return all(-F(1, 2) <= dot(z, v)/s2 < F(1, 2)
                   for v, s2 in zip(orthogonal, squares))

    assert all(label(w) == 0 for w in basis)
    for z in product(range(-2, 3), repeat=n):
        reduced = reduce(z)
        assert inside(reduced) and project(reduced) == project(z)
        assert label(reduced) == label(z)
        for w in basis:
            assert reduce(sub(z, w)) == reduced

    cases = 0
    losses = set()
    for radius_sq in (F(0), F(1, 4), F(1), F(4)):
        norm_bound = radius_sq + sum(squares)/4
        limit = isqrt(norm_bound.numerator//norm_bound.denominator)
        points = [z for z in product(range(-limit, limit+1), repeat=n)
                  if inside(z) and dot(project(z), project(z)) <= radius_sq]
        assert all(dot(z, z) <= norm_bound for z in points)
        kernel = {label(z) for z in points if not any(project(z))}
        assert kernel and all((a-b) % q in kernel for a in kernel for b in kernel)
        k = len(kernel)
        losses.add(k)
        counts = [0]*q
        lifts = defaultdict(list)
        projected_classes = defaultdict(set)
        for z in points:
            c, p = label(z), project(z)
            counts[c] += 1
            lifts[p].append(c)
            projected_classes[min((c-a) % q for a in kernel)].add(p)
        class_names = {min((c-a) % q for a in kernel) for c in range(q)}
        for labels in lifts.values():
            assert len(labels) == k and len(set(labels)) == k
            assert set(labels) == {(labels[0]+a) % q for a in kernel}
        next_counts = {c: len(projected_classes[c]) for c in class_names}
        assert all(counts[c] == next_counts[min((c-a) % q for a in kernel)]
                   for c in range(q))
        total, collisions = sum(counts), sum(v*v for v in counts)
        next_total = sum(next_counts.values())
        next_collisions = sum(v*v for v in next_counts.values())
        assert total == k*next_total and collisions == k*next_collisions
        assert collisions == sum(label(sub(z, w)) == 0 for z in points for w in points)
        assert F(total*total, q*collisions) == F(
            next_total*next_total, len(class_names)*next_collisions)
        void = F(counts.count(0), q)
        assert void == F(list(next_counts.values()).count(0), len(class_names))
        assert void <= 1-F(total*total, q*collisions)
        cases += 1
    return cases, losses


total_cases, all_losses = 0, set()
for q in (3, 5):
    for a in (0, 1, 2):
        fixtures = [
            ((a,), [(q, 0)]),
            ((a,), [(a, 1)]),
            ((a,), [(q+a, 1)]),
            ((a, 1), [(q, 0, 0), (a, 1, 0)]),
            ((a, 1), [(q+1, 0, 1), (a+1, 1, 1)]),
            ((a, 1), [(a, 1, 0), (1, 0, 1)]),
        ]
        for slopes, basis in fixtures:
            count, losses = check(q, slopes, basis)
            total_cases += count
            all_losses.update(losses)
assert all_losses == {1, 3, 5}
print(f'Passed {total_cases} exact flag/radius cases; kernel sizes {sorted(all_losses)}.')
