"""Exact norm-six/eight line counts and prescribed-support uniqueness."""
from math import comb, isqrt
from collections import Counter
from itertools import combinations
from wall1_short_relation_shapes import balanced_rows


def norm_rows(size, norm, minimum_support=4):
    def visit(prefix, left, remaining):
        if left == 0:
            if remaining == 0 and sum(prefix) == 0:
                support = [x for x in prefix if x]
                if len(support) >= minimum_support and support[0] > 0:
                    yield tuple(prefix)
            return
        for x in range(-isqrt(remaining), isqrt(remaining)+1):
            yield from visit((*prefix,x), left-1, remaining-x*x)
    yield from visit((), size, norm)


def finite_checks():
    total = 0
    for size in range(4, 11):
        three_allowed = list(norm_rows(size,6,minimum_support=3))
        assert len(three_allowed) == 10*comb(size,6)+3*comb(size,3)
        for norm in (6, 8):
            rows = list(norm_rows(size,norm))
            expected = 10*comb(size,6) if norm == 6 else 35*comb(size,8)+20*comb(size,5)
            assert len(rows) == expected, (size,norm,len(rows),expected)
            total += len(rows)
    checked = 0
    q = 7
    first = (1,1,-1,-1,0,0,0,0)
    for norm in (6,8):
        for row in norm_rows(8,norm):
            if not all(row[4:]):
                continue
            supports = Counter()
            for scalar in range(q):
                word = tuple((v+scalar*c)%q for v,c in zip(row,first))
                old = tuple(i for i in range(4) if word[i])
                if 1 <= len(old) <= 3:
                    supports[old] += 1
            assert all(count == 1 for count in supports.values())
            checked += 1
    print(f'Passed {total} exact short-line enumerations and {checked} support-uniqueness checks.')
    checked = 0
    fours = [row for support in combinations(range(6),4) for row in balanced_rows(support,6)]
    longer = list(norm_rows(6,6,minimum_support=3))+list(norm_rows(6,8,minimum_support=3))
    q = 7
    for first in fours:
        for second in longer:
            if not all(a or b for a,b in zip(first,second)):
                continue
            words = [second]+[tuple((a+t*b)%q for a,b in zip(first,second)) for t in range(q)]
            supports = Counter(tuple(i for i,x in enumerate(word) if x%q) for word in words)
            assert all(count == 1 for support,count in supports.items() if len(support)<6)
            checked += 1
    print(f'Passed {checked} arbitrary short-line-pair proper-support uniqueness checks.')


if __name__ == '__main__':
    finite_checks()
