"""Generate and verify Boolean support certificates for the seven rank-six cones.

For a feasible displacement D, y_i = z_i^t D z_i at each contact is nonnegative.
A nonzero ray whose positive support is contained in supp(y) can be subtracted
until another y_i vanishes. Thus it suffices to exclude nonempty, realizable
supports containing no listed ray. Choose the largest binary support in its
automorphism orbit. The CNF expresses the necessary conditions on this support.

Four types of clauses encode nonemptiness, exact dependencies of the contact
normals, certified ray images, and improvements in the binary support under an
integral automorphism. The final UNSAT certificate is LRAT. LP calls propose row
dependencies; every such dependency is checked with integer arithmetic.

Requires cypari2, pplpy, numpy, scipy, pycosat and CaDiCaL. Set WATSON_PYCOSAT to
an extension built for the same Python version if it is installed in another env.
"""

import argparse
from collections import deque
from fractions import Fraction
from functools import reduce
from itertools import combinations, combinations_with_replacement
from math import gcd, lcm
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile

import numpy as np
import ppl
from scipy.optimize import linprog

from watson_perfect_neighbors import pari
from watson_six_marked_frames import lean_forms, sign_normalized


def sat_solver():
    if path := os.getenv("WATSON_PYCOSAT"):
        spec = importlib.util.spec_from_file_location("pycosat", path)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        return module.solve
    import pycosat
    return pycosat.solve


def integral_row(v):
    q = [Fraction(float(x)).limit_denominator(100000) for x in v]
    scale = lcm(*(x.denominator for x in q))
    a = [int(scale*x) for x in q]
    g = reduce(gcd, a)
    return [x//g for x in a]


def group_paths(generators):
    m = len(generators[0])
    identity = tuple(range(m))
    seen = {identity: 0}
    elements = [identity]
    parents = [None]
    for idx, p in enumerate(elements):
        for j, g in enumerate(generators):
            h = tuple(p[i] for i in g)
            if h not in seen:
                seen[h] = len(elements)
                elements.append(h)
                parents.append((idx, j))
    def word(idx):
        w = []
        while idx:
            idx, j = parents[idx]
            w.append(j)
        return w[::-1]
    return np.asarray(elements, dtype=np.int32), word


def cone(k):
    minimum, entries = lean_forms()[k]
    form = pari.matrix(6, 6, entries)
    _, check_min, zmat = form.qfminim()
    assert check_min == minimum
    z = [tuple(map(int, v)) for v in zmat]
    positions = {sign_normalized(v): i for i, v in enumerate(z)}
    generators = form.qfauto()[1]
    permutations = [tuple(positions[sign_normalized(g*v)] for v in zmat) for g in generators]
    for g in generators:
        assert g.mattranspose()*form*g == form and abs(int(g.matdet())) == 1
    autos, word = group_paths(permutations)
    pairs = list(combinations_with_replacement(range(6), 2))
    normals = np.array([[v[i]*v[j]*(1 if i == j else 2) for i, j in pairs] for v in z],
                       dtype=np.int64)
    variables = [ppl.Variable(i) for i in range(21)]
    cs = ppl.Constraint_System()
    for v in normals:
        cs.insert(sum(int(a)*x for a,x in zip(v, variables, strict=True)) >= 0)
    rays = sorted(tuple(int(g.coefficient(x)) for x in variables)
                  for g in ppl.C_Polyhedron(cs).minimized_generators() if g.is_ray())
    supports = np.array(rays, dtype=np.int64) @ normals.T > 0
    assert np.linalg.matrix_rank(normals) == 21
    bits = 1 << np.arange(len(z))
    masks = supports @ bits
    images = {}
    seeds = []
    for r,s in zip(rays, supports, strict=True):
        if int(s @ bits) in images:
            continue
        orbit = s[autos] @ bits
        ids, first = np.unique(orbit, return_index=True)
        for mask, g in zip(ids, first, strict=True):
            images[int(mask)] = (len(seeds), word(int(g)))
        seeds.append(r)
    assert set(map(int,masks)) == set(images)
    # The first independent contact rows give an exact left inverse.
    m = len(z)
    N = pari.matrix(m, 21, list(map(int,normals.ravel())))
    ids = [int(i)-1 for i in N.matindexrank()[0]]
    basis = pari.matrix(21,21,[int(normals[i,j]) for i in ids for j in range(21)])
    inv = basis**-1
    scale = int(inv.denominator())
    tomography = (scale*inv).python()
    return (dict(contacts=z, generators=[g.python() for g in generators],
                 permutations=permutations, raySeeds=seeds, basis=ids,
                 inverse=tomography, scale=scale),
            normals, autos, word, supports, masks, images)


def certify(k, cadical, directory):
    data, normals, autos, word, supports, masks, images = cone(k)
    m = len(normals)
    bits = 1 << np.arange(m)
    clauses = [list(range(1,m+1))]
    reasons = [['nonzero']]
    deps = []
    dep_seen = set()
    def dependency(a):
        if tuple(a) in dep_seen:
            return
        dep_seen.update((tuple(a),tuple(-x for x in a)))
        assert np.all(np.array(a, dtype=object) @ normals == 0)
        positive = [i for i,c in enumerate(a) if c>0]
        negative = [i for i,c in enumerate(a) if c<0]
        assert positive and negative
        index = len(deps)
        deps.append(list(map(int,a)))
        for lhs,rhs in ((positive,negative),(negative,positive)):
            for i in lhs:
                clauses.append([-i-1]+[j+1 for j in rhs])
                reasons.append(['relation',index,i])
    sums = {}
    for indices in combinations(range(m),4):
        v = tuple(normals[list(indices)].sum(axis=0))
        if v in sums:
            a = np.zeros(m,dtype=int)
            a[list(indices)] += 1
            a[list(sums[v])] -= 1
            dependency(a)
        else:
            sums[v] = indices

    solve = sat_solver()
    while True:
        solution = solve(clauses, vars=m)
        if solution == 'UNSAT':
            break
        sel = np.array(solution[:m])>0
        orbit = sel[autos] @ bits
        gi = int(orbit.argmax())
        if orbit[gi] > (sel @ bits):
            g = autos[gi]
            delta = bits[np.argsort(g)]-bits
            lower = int(delta.clip(max=0).sum())
            choices = [i for i in range(m) if delta[i] and sel[i] == (delta[i]>0)]
            clause = []
            for i in sorted(choices,key=lambda i: -abs(delta[i])):
                lower += abs(int(delta[i]))
                clause.append(-i-1 if sel[i] else i+1)
                if lower>0:
                    break
            assert lower>0
            clauses.append(clause)
            reasons.append(['symmetry',word(gi)])
            continue
        contained = np.flatnonzero(~np.any(supports & ~sel,axis=1))
        if len(contained):
            j = int(contained[np.argmin(supports[contained].sum(axis=1))])
            clauses.append([-int(i)-1 for i in np.flatnonzero(supports[j])])
            seed,w = images[int(masks[j])]
            reasons.append(['ray',seed,w])
            continue
        # A Farkas relation positive somewhere on the allowed support.
        both = np.hstack((normals.T,-normals.T))
        bounds = [(0,None)]*m + [(0,0) if b else (0,None) for b in sel]
        cost = np.tile(np.where(sel,1.0,1.001),2)
        ans = linprog(cost, A_eq=np.vstack((both,np.r_[sel.astype(float),np.zeros(m)])),
                      b_eq=np.r_[np.zeros(21),1],bounds=bounds,method='highs')
        assert ans.success
        a = integral_row(ans.x[:m]-ans.x[m:])
        assert all(c>=0 for c,b in zip(a,sel) if b) and any(c>0 and b for c,b in zip(a,sel))
        old = len(clauses)
        dependency(a)
        assert old<len(clauses)

    with tempfile.TemporaryDirectory() as tmp:
        cnf = Path(tmp)/'input.cnf'
        lrat = Path(tmp)/'proof.lrat'
        cnf.write_text(f'p cnf {m} {len(clauses)}\n'+''.join(
            ' '.join(map(str,c))+' 0\n' for c in clauses))
        run = subprocess.run([cadical,'-q','--plain','--no-binary','--lrat',cnf,lrat],
                             capture_output=True, text=True)
        if run.returncode != 20:
            raise RuntimeError(f'CaDiCaL returned {run.returncode}: {run.stdout} {run.stderr}')
        proof = lrat.read_text()
    data.update(relations=deps, clauses=clauses, reasons=reasons)
    directory.mkdir(parents=True,exist_ok=True)
    (directory/f'support{k}.json').write_text(json.dumps(data,separators=(',',':')))
    (directory/f'support{k}.lrat').write_text(proof)
    print(f'form {k}: {len(clauses)} clauses, {len(deps)} exact relations, '
          f'{len(proof.splitlines())} LRAT lines', flush=True)


if __name__ == '__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('output',type=Path)
    p.add_argument('--cadical',default='cadical')
    p.add_argument('--form',type=int,choices=range(7),action='append')
    args=p.parse_args()
    for k in args.form if args.form is not None else range(7):
        certify(k,args.cadical,args.output)
