"""Generate the oriented rank-seven pivots in the basis of WatsonSevenRepresentatives.

Run with Sage's Python (pplpy, cypari2, numpy, scipy, Sage graphs), with Sage's
bin on PATH. Pass the Lean Wall1 directory. Only WatsonSevenPivots*.lean are
generated. At E7, use facets of smaller links and reverse a pivot at its dual.
The published orbit and facet totals are stopping checks, not a Lean proof.
See D.-O. Jaquet-Chiffelle, J. Théor. Nombres Bordeaux 4 (1992), 273–377.
"""
import argparse
from fractions import Fraction
from heapq import heappop, heappush
from itertools import combinations_with_replacement
from math import gcd, lcm
from pathlib import Path
import re

import numpy as np
import ppl
from scipy.optimize import linprog
from sage.all import Graph

from watson_perfect_neighbors import matrix, pari, pd, ray_orbits, first_contact_step


PAIRS = list(combinations_with_replacement(range(7), 2))
E7 = 12
DUAL = 25
NS = 'SigabaNeo.Wall1.Watson.HigherGram.Seven'


def read_forms(folder):
    source = (folder / 'WatsonSevenRepresentatives.lean').read_text()
    forms = []
    for index, rows in re.findall(r'^private def gram(\d+) : Q := !!\[(.*)\]$', source, re.M):
        assert int(index) == len(forms)
        a = [[Fraction(x) for x in row.split(',')] for row in rows.split(';')]
        m = lcm(*(x.denominator for row in a for x in row))
        f = matrix([[m*x for x in row] for row in a])
        assert int(f.qfminim()[1]) == m
        forms.append((m, f))
    assert len(forms) == 33
    return forms


def endpoint(forms, k, ray):
    m, form = forms[k]
    t = first_contact_step(form, m, ray)
    a = (t.denominator*form + t.numerator*ray) / (m*t.denominator)
    for j, (minimum, target) in enumerate(forms):
        g = minimum*a
        if g.denominator() != 1 or g.matdet() != target.matdet():
            continue
        u = pari.qfisom(g, target)
        if u != 0:
            assert u.mattranspose()*target*u == g and abs(u.matdet()) == 1
            return j, t/m, u
    raise ValueError(f'no matching endpoint at form {k}')


def unpack(v):
    a = [[0]*7 for _ in range(7)]
    for (i, j), x in zip(PAIRS, v, strict=True):
        a[i][j] = a[j][i] = int(x)
    return matrix(a)


def packed(a):
    return np.array([int(a[i, j]) for i, j in PAIRS], dtype=np.int64)


def reverse_dual(forms):
    _, f = forms[DUAL]
    _, rays = ray_orbits(f, f.qfminim()[2])
    assert len(rays) == 1
    j, _, change = endpoint(forms, DUAL, rays[0])
    assert j == E7
    v = change**-1
    a = -v.mattranspose()*rays[0]*v
    return packed(a) // gcd(*map(int, packed(a)))


def link_rays(normals, r):
    """Quotient by r, enumerate link directions, and lift to the adjacent facet."""
    y = normals @ r
    cut = int(np.flatnonzero(r)[0])
    variables = [ppl.Variable(i) for i in range(27)]
    cs = ppl.Constraint_System()
    for row in normals[y == 0]:
        cs.insert(sum(int(a)*x for a, x in zip(np.delete(row, cut), variables) if a) >= 0)
    for g in ppl.C_Polyhedron(cs).minimized_generators():
        if g.is_ray():
            v = np.insert([int(g.coefficient(x)) for x in variables], cut, 0)
            w = normals @ v
            j = min(np.flatnonzero(y > 0), key=lambda i: Fraction(int(w[i]), int(y[i])))
            yield y[j]*v - w[j]*r


def e7_rays(forms):
    _, f = forms[E7]
    z = np.array(f.qfminim()[2].python(), dtype=np.int64).T
    normals = np.array([[(1 if i == j else 2)*u[i]*u[j] for i,j in PAIRS] for u in z])
    assert normals.shape == (63, 28)
    dots = z @ np.array(f.python()) @ z.T
    graph = Graph((range(63), [(i,j) for i in range(63) for j in range(i) if dots[i,j]]),
                  format='vertices_and_edges')
    order = int(f.qfauto()[0])
    assert order == 2903040
    rays, known, pending = [], set(), []
    orbit_sizes = []

    def record(r):
        r = r // gcd(*map(int, r))
        y = normals @ r
        assert min(y) == 0 < max(y)
        tight = np.flatnonzero(y == 0).tolist()
        coloring = [tight, np.flatnonzero(y != 0).tolist()]
        key = (len(tight), graph.canonical_label(partition=coloring).graph6_string())
        if key in known:
            return
        rows = normals[tight]
        assert pari.matrix(len(tight), 28, list(map(int, rows.flat))).matrank() == 27
        ray = unpack(r)
        # Every common automorphism preserves this positive definite sum. Check
        # the converse on a generating set before using its order.
        c = 1
        while True:
            joint = c*f + ray
            if pd(joint):
                stabilizer, generators = joint.qfauto()
                if all(u.mattranspose()*f*u == f for u in generators):
                    break
            c *= 2
        stabilizer = int(stabilizer)
        assert order % stabilizer == 0
        orbit_sizes.append(order // stabilizer)
        known.add(key)
        heappush(pending, (len(tight), len(rays)))
        rays.append(ray)

    # LP only proposes some starting faces. Recover each ray as an exact
    # one-dimensional integer kernel and check all its contact evaluations.
    rng = np.random.default_rng(17)
    for _ in range(200):
        solution = linprog(rng.normal(size=28), A_ub=-normals, b_ub=np.zeros(63),
                           A_eq=[normals.sum(axis=0)], b_eq=[1], bounds=(None,None))
        assert solution.success
        rows = normals[np.abs(normals @ solution.x) < 1e-8]
        basis = pari.matrix(len(rows), 28, list(map(int, rows.flat))).matkerint()
        assert basis.ncols() == 1
        r = np.array(basis.python(), dtype=np.int64)[:,0]
        record(r if min(normals @ r) == 0 else -r)
    # Reserve the orbit of size 28 for the reverse pivot from the dual.
    while sum(orbit_sizes) < 79900912 - 28:
        _, i = heappop(pending)
        for r in link_rays(normals, packed(rays[i])):
            record(r)
    record(reverse_dual(forms))
    assert len(rays) == 157 and sum(orbit_sizes) == 79900912
    return rays


def literal(a):
    return '!![' + '; '.join(','.join(map(str,row)) for row in a.python()) + ']'


def pivot(forms, k, r):
    dst, step, u = endpoint(forms, k, r)
    return f"""  {{ dst := {dst}, step := {step}
    direction := {literal(r)}
    change := {literal(u)}
    unit := by
      apply isUnit_iff_exists_inv.mpr
      exact ⟨{literal(u**-1)}, matrix_eq_of_entries _ _ (by decide +kernel)⟩
    positive := by decide +kernel
    endpoint := matrix_eq_of_entries _ _ (by decide +kernel) }}"""


def emit(folder, tables):
    # Splitting at 48 records bounds both peak kernel memory and per-file time.
    chunks, parts = [], [[] for _ in tables]
    chunk, count = [], 0
    for k, rows in enumerate(tables):
        while rows:
            take = min(48-count, len(rows))
            part = f'form{k}part{len(parts[k])}'
            parts[k].append(part)
            chunk.append(f'\ndef {part} : List (Pivot {k}) := [\n' + ',\n'.join(rows[:take]) + ']\n')
            rows = rows[take:]
            count += take
            if count == 48:
                chunks.append(chunk)
                chunk, count = [], 0
    if chunk:
        chunks.append(chunk)
    imports = []
    for i, declarations in enumerate(chunks):
        name = f'WatsonSevenPivots{i}'
        imports.append(f'import SigabaNeo.Lib.Lattices.Research.Wall1.{name}\n')
        header = f"""import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenPivot

/-! Exact rank-seven Voronoi pivot identities generated by `watson_seven_pivots.py`. -/

namespace {NS}.PivotData
open Matrix
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
"""
        (folder / (name+'.lean')).write_text(header + ''.join(declarations) + f'\nend {NS}.PivotData\n')
    cases = ''.join(f"  | ⟨{k},_⟩ => {' ++ '.join(names)}\n" for k, names in enumerate(parts))
    (folder / 'WatsonSevenPivots.lean').write_text(''.join(imports) + f"""
namespace {NS}
open PivotData

/-- Oriented pivots grouped by their source representative. -/
def pivots : (k : Fin 33) → List (Pivot k)
{cases}  | ⟨n+33,h⟩ => by omega

end {NS}
""")


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('folder', type=Path)
    args = parser.parse_args()
    forms = read_forms(args.folder)
    tables = []
    for k, (_, f) in enumerate(forms):
        rays = e7_rays(forms) if k == E7 else ray_orbits(f, f.qfminim()[2])[1]
        tables.append([pivot(forms, k, ray) for ray in rays])
        print(f'{k}: {len(rays)} oriented pivots', flush=True)
    assert sum(map(len, tables)) == 657
    emit(args.folder, tables)
