"""Reproduce the rational edge walk for WatsonGramVertices.lean using pplpy.

The ten coordinates are twice the off-diagonal Gram entries. At a vertex the
tight inequalities define its tangent cone. Each extreme ray reaches the next
vertex at the first tight constraint along that ray. The polytope is bounded
by the pair tests, and its vertex-edge graph is connected. Signed permutations
preserve the input constraints. PPL computes the local cones over the rationals.

Run with a Python interpreter containing pplpy. No files are written. The
final comparison checks the representatives against the Lean table up to orbit.
"""

from collections import Counter, deque
from fractions import Fraction
from itertools import combinations, permutations, product
from math import lcm, prod
from pathlib import Path
import re

import ppl


PAIRS = list(combinations(range(5), 2))
VARIABLES = [ppl.Variable(i) for i in range(len(PAIRS))]


def coefficient_tests():
    vectors = list(product((-1, 0, 1), repeat=5))
    for j in range(5):
        for signs in product((-1, 1), repeat=5):
            vectors.append(tuple(a * (2 if i == j else 1) for i, a in enumerate(signs)))
    return [
        (sum(a * a for a in z) - 1, tuple(z[i] * z[j] for i, j in PAIRS))
        for z in vectors
        if next((a for a in z if a), 0) > 0
        if sum(a * a for a in z) > 1
    ]


def signed_permutations():
    maps = []
    for perm in permutations(range(5)):
        indices = [PAIRS.index(tuple(sorted((perm[i], perm[j])))) for i, j in PAIRS]
        for tail in product((-1, 1), repeat=4):
            signs = (1,) + tail
            maps.append(tuple((index, signs[i] * signs[j]) for index, (i, j) in zip(indices, PAIRS)))
    return maps


def dot(x, y):
    return sum(a * b for a, b in zip(x, y, strict=True))


def neighbors(vertex, rows):
    denominator = lcm(*(x.denominator for x in vertex))
    numerator = [int(x * denominator) for x in vertex]
    slacks = [c * denominator + dot(row, numerator) for c, row in rows]
    assert min(slacks) == 0
    cone = ppl.C_Polyhedron(10, "universe")
    for (_, row), slack in zip(rows, slacks, strict=True):
        if slack == 0:
            cone.add_constraint(dot(row, VARIABLES) >= 0)
    for generator in cone.minimized_generators():
        if generator.is_point():
            assert all(generator.coefficient(var) == 0 for var in VARIABLES)
            continue
        assert generator.is_ray()
        ray = [int(generator.coefficient(var)) for var in VARIABLES]
        step = min(
            Fraction(slack, -slope)
            for slack, (_, row) in zip(slacks, rows, strict=True)
            if (slope := dot(row, ray)) < 0
        )
        assert step > 0
        yield tuple((u + step * r) / denominator for u, r in zip(numerator, ray, strict=True))


def gram_determinant(vertex):
    matrix = [[Fraction(i == j) for j in range(5)] for i in range(5)]
    for x, (i, j) in zip(vertex, PAIRS, strict=True):
        matrix[i][j] = matrix[j][i] = Fraction(x, 2)
    for i in range(5):
        assert matrix[i][i] > 0
        for j in range(i + 1, 5):
            ratio = matrix[j][i] / matrix[i][i]
            for k in range(i + 1, 5):
                matrix[j][k] -= ratio * matrix[i][k]
    return prod(matrix[i][i] for i in range(5))


def lean_representatives():
    source = Path(__file__).with_name("WatsonGramVertices.lean").read_text()
    table = source.split("def vertexEdges", 1)[1].split("/--", 1)[0]
    return [
        tuple(Fraction(int(x), 2) for x in row.split(","))
        for row in re.findall(r"!\[([-0-9,]+)\]", table)
    ]


def main():
    rows = coefficient_tests()
    maps = signed_permutations()

    def orbit(v):
        return {tuple(sign * v[index] for index, sign in action) for action in maps}

    # The all-one off-diagonal coordinates give the A5 Gram matrix. Its ten
    # lower bounds on the pair differences are independently tight.
    first = (1,) * 10
    pending = deque([first])
    seen = orbit(first)
    counts = Counter()
    orbit_counts = Counter()
    table = set(lean_representatives())
    while pending:
        v = pending.popleft()
        images = orbit(v)
        match = images & table
        assert len(match) == 1, (v, match)
        table -= match
        determinant = gram_determinant(v)
        counts[determinant] += len(images)
        orbit_counts[determinant] += 1
        for w in neighbors(v, rows):
            if w not in seen:
                pending.append(w)
                seen.update(orbit(w))
    assert not table
    assert len(seen) == sum(counts.values())
    print(f"{len(rows)} inequalities, {len(seen)} vertices, {sum(orbit_counts.values())} orbits")
    for det in sorted(counts):
        print(f"det = {det}: {counts[det]} vertices in {orbit_counts[det]} orbits")


if __name__ == "__main__":
    main()
