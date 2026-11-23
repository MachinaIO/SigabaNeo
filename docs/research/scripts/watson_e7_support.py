"""Generate the E7 contact clauses and their LRAT refutation.

Run in the same Sage environment as watson_seven_pivots.py. Supply the Wall1
Lean directory, a scratch directory and an LRAT-capable CaDiCaL. The C++17
helper indexes the 79,900,912 ray supports. For emitting Lean modules, run
watson_e7_certificate.py and then watson_e7_geometry.py on the scratch data.
"""
import argparse
import ctypes as C
import importlib.util
from itertools import combinations
import json
import os
from pathlib import Path
import subprocess
import tempfile

import numpy as np
from scipy.optimize import linprog

from watson_seven_pivots import E7, PAIRS, e7_rays, packed, pari, read_forms
from watson_six_support import integral_row


def routine(library, name, result, *args):
    fn = getattr(library, name)
    fn.restype, fn.argtypes = result, args
    return fn


def sign_normalized(v):
    return tuple(v if v[np.flatnonzero(v)[0]] > 0 else -v)


class Orbits:
    def __init__(self, library, perms, axes):
        lib = C.CDLL(str(library))
        ptr, integer, mask = C.c_void_p, C.c_int, C.c_uint64
        init = routine(lib, 'makegroup', integer, integer, ptr, ptr)
        assert init(len(perms), perms.ctypes.data, axes.ctypes.data) == 1451520
        self.add = routine(lib, 'addbank', integer, integer, mask)
        self.improvement = routine(lib, 'maximize', integer, mask)
        self.contained = routine(lib, 'contained', mask, mask, ptr, ptr)
        self.getword = routine(lib, 'getword', integer, integer, ptr, integer)
        self.getperm = routine(lib, 'permutation', None, integer, ptr)

    def word(self, element):
        output = np.empty(64, dtype=np.int32)
        length = self.getword(element, output.ctypes.data, len(output))
        assert length >= 0
        return output[:length].tolist()

    def action(self, element):
        output = np.empty(63, dtype=np.int32)
        self.getperm(element, output.ctypes.data)
        return output


class SupportSearch:
    def __init__(self, normals):
        path = os.getenv('WATSON_PYCOSAT') or importlib.util.find_spec('pycosat').origin
        lib = C.CDLL(path)
        ptr, integer = C.c_void_p, C.c_int
        self.solver = routine(lib, 'picosat_init', ptr)()
        self.literal = routine(lib, 'picosat_add', integer, ptr, integer)
        self.solve = routine(lib, 'picosat_sat', integer, ptr, integer)
        self.deref = routine(lib, 'picosat_deref', integer, ptr, integer)
        self.reset = routine(lib, 'picosat_reset', None, ptr)
        self.clauses, self.reasons, self.relations = [], [], []
        self.seen = set()
        self.normals = normals

    def clause(self, literals, why):
        clause = list(map(int, literals))
        for x in clause:
            self.literal(self.solver, x)
        self.literal(self.solver, 0)
        self.clauses.append(clause)
        self.reasons.append(why)

    def relation(self, row):
        if tuple(row) in self.seen:
            return
        assert np.all(row @ self.normals == 0)
        self.seen.update((tuple(row), tuple(-row)))
        index = len(self.relations)
        self.relations.append(row.tolist())
        for signed in (row, -row):
            tail = [int(j)+1 for j in np.flatnonzero(signed < 0)]
            for j in np.flatnonzero(signed > 0):
                self.clause([-j-1]+tail, ['relation', index, int(j)])

    def initial(self, masks):
        self.clause(range(1,64), ['nonzero'])
        sums = {}
        for support in combinations(range(63),4):
            key = self.normals[list(support)].sum(axis=0).astype(np.int16).tobytes()
            if key in sums:
                row = np.zeros(63, dtype=int)
                row[list(support)] += 1
                row[list(sums[key])] -= 1
                self.relation(row)
            else:
                sums[key] = support
        for j, mask in enumerate(masks):
            self.clause([-i-1 for i in range(63) if mask >> i & 1], ['ray',j,[]])

    def refute(self, orbits, bits):
        both = np.hstack((self.normals.T, -self.normals.T))
        seed, element = C.c_int(), C.c_int()
        while (status := self.solve(self.solver,-1)) == 10:
            active = np.array([self.deref(self.solver,i+1) > 0 for i in range(63)])
            mask = int(active @ bits)
            move = orbits.improvement(mask)
            if move:
                gain = bits[np.argsort(orbits.action(move))] - bits
                floor = int(gain.clip(max=0).sum())
                choices = (i for i,v in enumerate(gain) if v and active[i] == (v>0))
                clause = []
                for i in sorted(choices, key=lambda j: -abs(int(gain[j]))):
                    floor += abs(int(gain[i]))
                    clause.append(-i-1 if active[i] else i+1)
                    if floor > 0:
                        break
                assert floor > 0
                self.clause(clause, ['symmetry',orbits.word(move)])
                continue
            ray = orbits.contained(mask,C.byref(seed),C.byref(element))
            if ray:
                self.clause([-i-1 for i in range(63) if ray >> i & 1],
                            ['ray',seed.value,orbits.word(element.value)])
                continue
            # Separate the alleged support from the cone of contact values.
            result = linprog(np.tile(np.where(active,1.0,1.001),2),
                A_eq=np.vstack((both, np.r_[active.astype(float),np.zeros(63)])),
                b_eq=np.r_[np.zeros(28),1],
                bounds=[(0,None)]*63 + [(0,0) if x else (0,None) for x in active])
            assert result.success
            self.relation(np.array(integral_row(result.x[:63]-result.x[63:])))
        self.reset(self.solver)
        assert status == 20


def generate(folder, scratch, cadical):
    forms = read_forms(folder)
    form = forms[E7][1]
    z = np.array(form.qfminim()[2].python(), dtype=np.int64).T
    index = {sign_normalized(v):i for i,v in enumerate(z)}
    generators = form.qfauto()[1]
    perms = np.ascontiguousarray([[index[sign_normalized(v)] for v in z @ np.array(g.python()).T]
                                  for g in generators], dtype=np.uint8)
    axes = np.array([index[tuple(e)] for e in np.eye(7,dtype=int)], dtype=np.int32)
    normals = np.array([[(1 if i==j else 2)*v[i]*v[j] for i,j in PAIRS] for v in z])
    seeds = [packed(r).tolist() for r in e7_rays(forms)]
    bits = 1 << np.arange(63)
    masks = [int((normals @ r > 0) @ bits) for r in seeds]
    with tempfile.TemporaryDirectory() as temporary:
        library = Path(temporary)/'orbits.so'
        subprocess.run([os.getenv('CXX','c++'), '-std=c++17', '-O3', '-shared', '-fPIC',
                        Path(__file__).with_name('watson_e7_orbits.cpp'), '-o', library], check=True)
        orbits = Orbits(library, perms, axes)
        total = sum(orbits.add(i,masks[i]) for i in sorted(range(len(masks)),
                                                           key=lambda i: masks[i].bit_count()))
        assert total == 79900912
        search = SupportSearch(normals)
        search.initial(masks)
        search.refute(orbits,bits)
    matrix = pari.matrix(63,28,list(map(int,normals.flat)))
    basis = [int(i)-1 for i in matrix.matindexrank()[0]]
    inverse = pari.matrix(28,28,list(map(int,normals[basis].flat)))**-1
    scale = int(inverse.denominator())
    data = dict(contacts=z.tolist(), generators=[g.python() for g in generators],
                permutations=perms.tolist(), raySeeds=seeds, basis=basis,
                inverse=(scale*inverse).python(), scale=scale, relations=search.relations,
                clauses=search.clauses, reasons=search.reasons)
    scratch.mkdir(parents=True,exist_ok=True)
    (scratch/'support12.json').write_text(json.dumps(data,separators=(',',':')))
    cnf = scratch/'support12.cnf'
    cnf.write_text(f'p cnf 63 {len(search.clauses)}\n' +
                   ''.join(' '.join(map(str,c))+' 0\n' for c in search.clauses))
    result = subprocess.run([cadical,'-q','--plain','--no-binary','--lrat',cnf,scratch/'support12.lrat'])
    if result.returncode != 20:
        raise RuntimeError(f'CaDiCaL returned {result.returncode}, expected UNSAT (20)')


if __name__=='__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('folder',type=Path)
    parser.add_argument('scratch',type=Path)
    parser.add_argument('--cadical',default='cadical')
    args = parser.parse_args()
    generate(args.folder,args.scratch,args.cadical)
