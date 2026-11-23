"""Exact two-norm-six planes on nine positions with a prescribed six-circuit."""
from collections import defaultdict
from itertools import combinations
from wall1_rare_second_line import norm_rows

COUNTS={3:((27,28),(35,72)),4:((35,96),),5:((35,240),)}


def exact_counts():
    firsts=[row+(0,0,0) for row in norm_rows(6,6)]
    for q in (7,17,3329):
        codes=defaultdict(set)
        for a in firsts:
            for b in norm_rows(9,6):
                if not all(b[6:]):continue
                dot=sum(x*y for x,y in zip(a,b))
                gram=36-dot*dot
                assert gram in (27,35)
                minors={(i,j):a[i]*b[j]-a[j]*b[i] for i,j in combinations(range(9),2)}
                assert 1 in map(abs,minors.values())
                # Girth six: every complementary four columns have rank two.
                assert all(any(minors[i,j] for i,j in combinations(comp,2))
                           for comp in combinations(range(9),4))
                inverse=pow(b[6]%q,-1,q)
                key=(a,tuple((x-b[0]*y)*inverse%q for x,y in zip(b,a)))
                for scalar in {(-b[i]*pow(a[i]%q,-1,q))%q for i in range(6)}:
                    support=tuple(i for i in range(6) if (b[i]+scalar*a[i])%q)
                    for overlap in (3,4,5):
                        if support==tuple(range(overlap)):
                            codes[overlap,gram].add(key)
        expected={(a,d):n for a,entries in COUNTS.items() for d,n in entries}
        assert {k:len(v) for k,v in codes.items()}==expected
        print(f'q={q}: exact norm-six pair strata, primitive minors and girth-six tests passed.')


if __name__=='__main__':
    exact_counts()
