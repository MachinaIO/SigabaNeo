"""Six-position prescribed four-circuit rare planes, with full girth filtering."""
from itertools import combinations
from collections import defaultdict
from math import gcd
from functools import reduce
from wall1_short_relation_shapes import balanced_rows
from wall1_rare_second_line import norm_rows


def exact_counts():
    for q in (7,17,3329):
        fours=[a for C in combinations(range(6),4) for a in balanced_rows(C,6)]
        for norm in (6,8):
         out=defaultdict(set)
         for a in fours:
          for b in norm_rows(6,norm):
           minors={(i,j):a[i]*b[j]-a[j]*b[i] for i,j in combinations(range(6),2)};g=reduce(gcd,minors.values())
           assert max(map(abs,minors.values()))<7
           if not g or minors[4,5]:continue
           if not all(any(minors[i,j] for i,j in combinations(comp,2)) for comp in combinations(range(6),3)):continue
           p=next((i for i in (4,5) if a[i] or b[i]),None)
           if p is None:continue
           first=tuple((b[p]*a[i]-a[p]*b[i])%q for i in range(6))
           if any(not first[i] for i in range(4)):continue
           i,j=next(k for k,v in minors.items() if v);inv=pow(minors[i,j]%q,-1,q)
           def member(w):
            u=(w[i]*b[j]-w[j]*b[i])*inv%q;v=(a[i]*w[j]-a[j]*w[i])*inv%q
            return all((u*x+v*y-z)%q==0 for x,y,z in zip(a,b,w))
           if sum(member(w) for w in fours)>1:continue
           for overlap in (2,3):
            k=overlap;second=tuple((b[k]*a[i]-a[k]*b[i])%q for i in range(6))
            if tuple(i for i,x in enumerate(second) if x)!=tuple(range(overlap))+(4,5):continue
            f=tuple(x*pow(first[0],-1,q)%q for x in first)
            v=tuple((second[i]-second[0]*f[i])*pow(second[4],-1,q)%q for i in range(6))
            dot=sum(x*y for x,y in zip(a,b));D=4*norm-dot*dot
            assert g==1 and 1 in map(abs,minors.values())
            out[overlap,D].add((f,v))
         expected=({(2,24):12} if norm==6 else {(3,28):36,(3,31):72,(3,32):24,(2,31):24,(2,32):8})
         assert {k:len(v) for k,v in out.items()}==expected
         print(f'q={q}, norm={norm}: girth-four exact Gram strata verified.')


if __name__=='__main__':
    exact_counts()
