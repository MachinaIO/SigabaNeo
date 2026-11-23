"""Count rank-six shortest frames up to signed permutation and lattice automorphisms.

Read the seven rational representatives from WatsonSixRepresentatives.lean. For each
one, PARI supplies the shortest vector lines and generators of the automorphism group.
Enumerate unordered six-element sets of distinct lines, keeping one per orbit.
The absolute integral determinant of a frame is its index. Requires cypari2.
"""

from collections import Counter
from fractions import Fraction
from itertools import combinations
from math import lcm
from pathlib import Path
import re

from cypari2 import Pari


def lean_forms():
    root = Path(__file__).resolve().parents[3]
    source = (root / "SigabaNeo/Lib/Lattices/Research/Wall1/WatsonSixRepresentatives.lean").read_text()
    table = source.split("def forms :", 1)[1].split("private def upper :", 1)[0]
    forms = []
    for row in re.findall(r"!!\[([^\]]+)\]", table):
        entries = [Fraction(x) for x in re.split(r"[,;]", row)]
        assert len(entries) == 36
        scale = lcm(*(x.denominator for x in entries))
        forms.append((scale, [int(scale * x) for x in entries]))
    assert len(forms) == 7
    return forms


def sign_normalized(z):
    v = tuple(int(x) for x in z)
    return v if next(x for x in v if x) > 0 else tuple(-x for x in v)


def byte_actions(form, short):
    positions = {sign_normalized(z): i for i, z in enumerate(short)}
    actions = []
    for g in form.qfauto()[1]:
        perm = [positions[sign_normalized(g * z)] for z in short]
        assert sorted(perm) == list(range(len(perm)))
        # Five byte lookups implement the permutation of a 36-bit subset mask.
        tables = []
        for offset in range(0, 40, 8):
            table = [0]*256
            for x in range(1, 256):
                bit = x & -x
                i = offset + bit.bit_length() - 1
                table[x] = table[x-bit] | (1 << perm[i] if i < len(perm) else 0)
            tables.append(table)
        actions.append(tables)
    return actions


def frame_indices(form, short):
    actions = byte_actions(form, short)
    seen = set()
    counts = Counter()
    for frame in combinations(range(short.ncols()), 6):
        mask = sum(1 << i for i in frame)
        if mask in seen:
            continue
        seen.add(mask)
        pending = [mask]
        while pending:
            s = pending.pop()
            u, v, w, x, y = s & 255, (s >> 8) & 255, (s >> 16) & 255, (s >> 24) & 255, s >> 32
            for a, b, c, d, e in actions:
                t = a[u] | b[v] | c[w] | d[x] | e[y]
                if t not in seen:
                    seen.add(t)
                    pending.append(t)
        U = pari.matrix(6, 6, [short[i, j] for i in range(6) for j in frame])
        index = abs(int(U.matdet()))
        if index:
            counts[index] += 1
    return counts


if __name__ == "__main__":
    pari = Pari()
    total = Counter()
    for k, (minimum, entries) in enumerate(lean_forms()):
        form = pari.matrix(6, 6, entries)
        _, actual, short = form.qfminim()
        assert actual == minimum
        counts = frame_indices(form, short)
        total.update(counts)
        print(f"form {k}, frame orbits by index {dict(sorted(counts.items()))}", flush=True)
    print(f"total {dict(sorted(total.items()))}", flush=True)
