"""Exact finite checks for the adaptive linear-transcript bridge.

No simulation, external dependencies, or claim about width-506 probabilities.
"""
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import product, combinations


def dot(a, b, q):
    return sum(x*y for x, y in zip(a, b)) % q


def transcript(a, q):
    rows = [(1, 0, 0)]
    answers = [a[0]]
    if answers[0] != 0:
        rows.append((0, 1, answers[0]))
        answers.append(dot(a, rows[-1], q))
        if answers[1] != 0:
            rows.append((0, 0, 1))
            answers.append(a[2])
    return tuple(rows), tuple(answers)


def rank(rows, q):
    rows = [list(r) for r in rows]
    r = 0
    for c in range(3):
        pivot = next((j for j in range(r, len(rows)) if rows[j][c]), None)
        if pivot is None:
            continue
        rows[r], rows[pivot] = rows[pivot], rows[r]
        inv = pow(rows[r][c], -1, q)
        rows[r] = [(v*inv) % q for v in rows[r]]
        for j in range(len(rows)):
            if j != r:
                mul = rows[j][c]
                rows[j] = [(x-mul*y) % q for x, y in zip(rows[j], rows[r])]
        r += 1
    return r


def run():
    transcript_checks = fresh_checks = event_checks = 0
    for q in (3, 5, 7):
        matrices = list(product(range(q), repeat=3))
        groups = defaultdict(list)
        for a in matrices:
            groups[transcript(a, q)].append(a)
        for (rows, answers), members in groups.items():
            expected = [a for a in matrices
                        if all(dot(a, y, q) == x for y, x in zip(rows, answers))]
            assert members == expected
            r = rank(rows, q)
            assert len(members) == q**(3-r)
            # Every newly queried direction outside the old span is uniform.
            for y in product(range(q), repeat=3):
                if rank(rows+(y,), q) == r+1:
                    counts = Counter(dot(a, y, q) for a in members)
                    assert counts == {x: len(members)//q for x in range(q)}
                    fresh_checks += 1
            transcript_checks += 1

        # In L_(a,b)={(x,y,z): x=a*y+b*z mod q}, the signed unit
        # winner (0,0,-1) is selected iff b=0 and a!=0. Every other
        # nonzero integer vector has squared norm >=1, so this is a
        # global shortest-vector statement, with ambient lexicographic ties.
        contain = list(range(q))  # a, after fixing b=0
        selected = [a for a in contain if a != 0]
        s = F(q-1, q)
        tv = sum(abs(F(int(a != 0), q-1)-F(1, q)) for a in contain)/2
        assert tv == 1-s
        assert max(F(int(a != 0), q-1)/F(1, q) for a in contain) == 1/s
        for n in range(q+1):
            for event in combinations(contain, n):
                p = F(n, q)
                actual = F(sum(a != 0 for a in event), q-1)
                assert max(F(0), (p+s-1)/s) <= actual <= min(F(1), p/s)
                event_checks += 1
        # A genuinely untouched coordinate c remains uniform even after selection.
        counts = Counter(c for a, b, c in matrices if b == 0 and a != 0)
        assert counts == {c: q-1 for c in range(q)}
        # An invertible transformation for each input is not necessarily a
        # bijection of the entire sample space when chosen from that input.
        images = Counter((a*(pow(a, -1, q) if a else 1)) % q for a in range(q))
        assert images == {0: 1, 1: q-1}
        print(f'q={q}: selected mass={s}, TV={tv}, max density={1/s}, '
              f'data-dependent transform mass at 1={F(q-1,q)}')
    print(f'PASS: {transcript_checks} adaptive transcripts; '
          f'{fresh_checks} fresh-direction laws; {event_checks} event bounds')


if __name__ == '__main__':
    run()
