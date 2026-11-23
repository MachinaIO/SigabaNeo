"""Two norm-six lines with a prescribed three-circuit and five new positions."""
from collections import defaultdict
from itertools import combinations
from wall1_rare_second_line import norm_rows

COUNTS={1:((32,10),(35,20)),2:((32,10),(35,20))}


def exact_counts():
    firsts=[a+(0,)*5 for a in norm_rows(3,6,minimum_support=3)]
    seconds=[b for b in norm_rows(8,6,minimum_support=3) if all(b[3:])]
    for q in (7,17,3329):
        codes=defaultdict(set)
        for a in firsts:
            for b in seconds:
                assert sum(bool(x) for x in b[:3])==1 and all(abs(x)<=1 for x in b)
                dot=sum(x*y for x,y in zip(a,b))
                gram=36-dot*dot
                assert gram in (32,35)
                assert any(abs(a[i]*b[j]-a[j]*b[i])==1 for i,j in combinations(range(8),2))
                f=tuple(x*pow(a[0]%q,-1,q)%q for x in a)
                key=(f,tuple((b[i]-b[0]*f[i])*pow(b[3]%q,-1,q)%q for i in range(8)))
                for scalar in {(-b[i]*pow(a[i]%q,-1,q))%q for i in range(3)}:
                    support=tuple(i for i in range(3) if (b[i]+scalar*a[i])%q)
                    for overlap in (1,2):
                        if support==tuple(range(overlap)):
                            codes[overlap,gram].add(key)
        assert {k:len(v) for k,v in codes.items()}=={
            (a,d):n for a,entries in COUNTS.items() for d,n in entries}
        print(f'q={q}: each prescribed overlap has10 determinant32 and20 determinant35 planes.')


if __name__=='__main__':
    exact_counts()
