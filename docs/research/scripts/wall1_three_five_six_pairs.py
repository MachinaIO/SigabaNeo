"""Exact H=5 two-six charts: C=012, S=0134; integer arithmetic only.

Run from any working directory. No external packages required. The accompanying
note proves completeness independently of the finite checks.
"""
from collections import Counter, defaultdict
from itertools import combinations
from wall1_rare_second_line import norm_rows


def support(row, q=None):
    return tuple(i for i, x in enumerate(row) if (x % q if q else x))


def chart(a, b, q):
    p = next(i for i in (3, 4) if a[i] or b[i])
    first = tuple(b[p]*a[i] - a[p]*b[i] for i in range(5))
    if support(first, q) != (0, 1, 2):
        return None
    second = tuple(b[2]*a[i] - a[2]*b[i] for i in range(5))
    if support(second, q) != (0, 1, 3, 4):
        return None
    f = tuple(x * pow(first[0] % q, -1, q) % q for x in first)
    v = tuple((second[i] - second[0]*f[i]) *
              pow(second[3] % q, -1, q) % q for i in range(5))
    return f, v


def main():
    rows = list(norm_rows(5, 6, minimum_support=3))
    fours = list(norm_rows(5, 4, minimum_support=1))
    assert len(rows) == 30
    assert len(fours) == 15
    full_pairs = [(a,b) for a,b in combinations(rows, 2)
                  if all(x or y for x,y in zip(a,b))]
    determinants = Counter(36-sum(x*y for x,y in zip(a,b))**2
                           for a,b in full_pairs)
    print('norm-six lines:', len(rows), 'full-support pairs:', len(full_pairs),
          'determinants:', dict(sorted(determinants.items())))
    for q in (7, 17, 3329):
        codes = defaultdict(set)
        excluded = set()
        for a,b in full_pairs:
            dot = sum(x*y for x,y in zip(a,b))
            d = 36-dot*dot
            key = chart(a,b,q)
            if key is None:
                continue
            if abs(dot) == 4:
                difference = tuple(x-(1 if dot>0 else -1)*y
                                   for x,y in zip(a,b))
                assert sum(x*x for x in difference) == 4
                excluded.add(key)
                continue
            assert abs(dot) in (1,2)
            # A unit minor proves saturation in the rational two-plane.
            assert any(abs(a[i]*b[j]-a[j]*b[i]) == 1
                       for i,j in combinations(range(5),2))
            # Projective column classes 2,2,1 prove girth exactly three.
            classes = Counter()
            for x,y in zip(a,b):
                classes[(1,y*pow(x%q,-1,q)%q) if x else (0,1)] += 1
            assert sorted(classes.values()) == [1,2,2]
            f,v = key
            # Exhaustively exclude every balanced norm-four integer line
            # even in the modular preimage (stronger than real-plane check).
            for w in fours:
                u = w[0] % q
                z = (w[3]-u*f[3]) % q
                assert any((w[i]-u*f[i]-z*v[i]) % q for i in range(5))
            codes[d].add(key)
        actual = {d:len(s) for d,s in sorted(codes.items())}
        assert actual == {32:4, 35:4}, (q,actual)
        assert len(excluded) == 1
        assert len(set.union(*codes.values())) == 8
        assert not excluded.intersection(set.union(*codes.values()))
        print(f'q={q}: no-four charts={actual}; excluded norm-four charts=1; '
              'GS squared lengths=(6,16/3) or (6,35/6)')


if __name__ == '__main__':
    main()
