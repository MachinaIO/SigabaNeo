"""Walk the perfect-form cones in rank six using exact arithmetic (pplpy and cypari2).

Matrices are primitive integral representatives. Compare determinants only after
dividing by the minimum to the power n. PPL lists the rays of the cone cut out by
all shortest vectors. PARI computes short vectors and integral isometries. The
group action on rays uses integral congruence and never identifies opposite rays.
This program is an independent computation, not a Lean coverage proof.
"""

import argparse
from collections import deque
from fractions import Fraction
from functools import reduce
from itertools import combinations_with_replacement
from math import gcd

import numpy as np
import ppl
from cypari2 import Pari


pari = Pari()


def matrix(rows):
    n = len(rows)
    return pari.matrix(n, n, [int(x) for row in rows for x in row])


def primitive(form):
    divisor = reduce(gcd, (int(x) for col in form for x in col))
    return form / divisor


def pd(form):
    return int(form.qfsign()[0]) == form.nrows()


def form_value(form, z):
    return int(z.Vec() * form * z)


def neighbor(form, minimum, direction):
    """Find the first new contact on a ray; every vector crossing is short at trial."""
    low, high = Fraction(0), None
    step = Fraction(1)
    while True:
        test = step.denominator * form + step.numerator * direction
        if pd(test):
            vectors = pari.qfminim(test, step.denominator * minimum)[2]
            crossings = []
            for z in vectors:
                slope = form_value(direction, z)
                if slope < 0:
                    crossings.append(Fraction(form_value(form, z) - minimum, -slope))
            if crossings:
                first = min(crossings)
                assert 0 < first <= step
                end = first.denominator * form + first.numerator * direction
                change = pari.qflllgram(end)
                return primitive(change.mattranspose() * end * change)
            low = step
        else:
            high = step
        step = 2 * step if high is None else (low + high) / 2


def ray_orbits(form, short):
    n = form.nrows()
    pairs = list(combinations_with_replacement(range(n), 2))
    variables = [ppl.Variable(i) for i in range(len(pairs))]
    constraints = ppl.Constraint_System()
    for z in short:
        row = [int(z[i]) * int(z[j]) * (1 if i == j else 2) for i, j in pairs]
        constraints.insert(sum(a * v for a, v in zip(row, variables)) >= 0)
    cone = ppl.C_Polyhedron(constraints)
    rays = set()
    for generator in cone.minimized_generators():
        if generator.is_point():
            continue
        assert generator.is_ray()
        rays.add(tuple(int(generator.coefficient(v)) for v in variables))
    count = len(rays)
    actions = [np.array(a.python(), dtype=object) for a in pari.qfauto(form)[1]]
    rows, cols = zip(*pairs)
    representatives = []
    while rays:
        ray = min(rays)
        rays.remove(ray)
        representatives.append(ray)
        pending = [ray]
        while pending:
            r = pending.pop()
            m = np.empty((n, n), dtype=object)
            m[rows, cols] = m[cols, rows] = r
            for a in actions:
                image = tuple((a.T @ m @ a)[rows, cols])
                if image in rays:
                    rays.remove(image)
                    pending.append(image)
    def unpack(ray):
        a = [[0]*n for _ in range(n)]
        for (i, j), v in zip(pairs, ray):
            a[i][j] = a[j][i] = v
        return matrix(a)
    return count, list(map(unpack, representatives))


def walk(n):
    first = matrix([[1 + int(i == j) for j in range(n)] for i in range(n)])
    forms, pending = [first], deque([0])
    while pending:
        k = pending.popleft()
        form = forms[k]
        _, minimum, short = pari.qfminim(form)
        minimum = int(minimum)
        det = Fraction(int(form.matdet()), minimum**n)
        print(f"form {k}: det/min^{n}={det}, contacts={short.ncols()}", flush=True)
        count, directions = ray_orbits(form, short)
        neighbors = []
        for r in directions:
            end = neighbor(form, minimum, r)
            j = next((i for i, other in enumerate(forms)
                      if other.matdet() == end.matdet() and pari.qfisom(other, end) != 0), None)
            if j is None:
                j = len(forms)
                forms.append(end)
                pending.append(j)
            neighbors.append(j)
        print(f"  rays={count}, ray orbits={len(directions)}, neighbors={neighbors}", flush=True)
        print(f"  Gram={form.python()}", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("rank", type=int, choices=(3, 4, 5, 6, 7), default=6, nargs="?")
    walk(parser.parse_args().rank)
