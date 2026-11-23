"""One-norm-four rare planes on five positions with a prescribed three-circuit."""
from collections import defaultdict
from functools import reduce
from itertools import combinations
from math import gcd
from wall1_short_relation_shapes import balanced_rows
from wall1_rare_second_line import norm_rows


def exact_counts():
    fours=[a for support in combinations(range(5),4) for a in balanced_rows(support,5)]
    for q in (7,17,3329):
        families={}
        for norm in (6,8):
            codes=defaultdict(set)
            for a in fours:
                for b in norm_rows(5,norm,minimum_support=3):
                    minors={(i,j):a[i]*b[j]-a[j]*b[i] for i,j in combinations(range(5),2)}
                    if not reduce(gcd,minors.values()) or minors[3,4]:continue
                    p=next((i for i in (3,4) if a[i] or b[i]),None)
                    if p is None:continue
                    first=tuple((b[p]*a[i]-a[p]*b[i])%q for i in range(5))
                    if any(not first[i] for i in range(3)):continue
                    i,j=next(k for k,v in minors.items() if v)
                    inverse=pow(minors[i,j]%q,-1,q)
                    def member(w):
                        u=(w[i]*b[j]-w[j]*b[i])*inverse%q
                        v=(a[i]*w[j]-a[j]*w[i])*inverse%q
                        return all((u*x+v*y-z)%q==0 for x,y,z in zip(a,b,w))
                    if sum(member(w) for w in fours)>1:continue
                    for overlap in (1,2):
                        k=overlap
                        second=tuple((b[k]*a[i]-a[k]*b[i])%q for i in range(5))
                        if tuple(i for i,x in enumerate(second) if x)!=tuple(range(overlap))+(3,4):continue
                        assert 1 in map(abs,minors.values())
                        f=tuple(x*pow(first[0],-1,q)%q for x in first)
                        v=tuple((second[i]-second[0]*f[i])*pow(second[3],-1,q)%q for i in range(5))
                        dot=sum(x*y for x,y in zip(a,b))
                        codes[overlap,4*norm-dot*dot].add((f,v))
            expected=({(1,20):1,(2,20):1,(2,23):6,(2,24):6} if norm==6 else
                      {(2,23):6,(2,31):12})
            assert {k:len(v) for k,v in codes.items()}==expected
            families[norm]=codes
        assert families[6][2,23]==families[8][2,23]
        print(f'q={q}: exact five-position one-four Gram strata and duplicate removal passed.')


if __name__=='__main__':
    exact_counts()
