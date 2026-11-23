"""Exact rare short planes with a prescribed three-circuit on six positions."""
from collections import defaultdict
from functools import reduce
from itertools import combinations
from math import gcd
from wall1_short_relation_shapes import balanced_rows
from wall1_rare_second_line import norm_rows


def exact_counts():
    for q in (7,17,3329):
        families={}
        for norm in (6,8):
            codes=defaultdict(set)
            for support in combinations(range(6),4):
                for a in balanced_rows(support,6):
                    for b in norm_rows(6,norm,minimum_support=3):
                        minors=[a[i]*b[j]-a[j]*b[i] for i,j in combinations(range(6),2)]
                        g=reduce(gcd,minors)
                        if not g or any(a[i]*b[j]-a[j]*b[i] for i,j in combinations(range(3,6),2)):
                            continue
                        p=next((i for i in range(3,6) if a[i] or b[i]),None)
                        if p is None:
                            continue
                        first=tuple((b[p]*a[i]-a[p]*b[i])%q for i in range(6))
                        if any(not first[i] for i in range(3)):
                            continue
                        for overlap in (1,2):
                            k=overlap
                            second=tuple((b[k]*a[i]-a[k]*b[i])%q for i in range(6))
                            target=tuple(range(overlap))+tuple(range(3,6))
                            if tuple(i for i,x in enumerate(second) if x)!=target:
                                continue
                            assert 1 in map(abs,minors) and g==1
                            inverse=pow(first[0],-1,q)
                            f=tuple(x*inverse%q for x in first)
                            inverse=pow(second[3],-1,q)
                            v=tuple((second[i]-second[0]*f[i])*inverse%q for i in range(6))
                            dot=sum(x*y for x,y in zip(a,b))
                            codes[overlap,4*norm-dot*dot].add((f,v))
            expected=({(1,20):3,(1,23):6,(2,20):3,(2,23):6} if norm==6 else
                      {(1,23):6,(2,23):6})
            assert {k:len(v) for k,v in codes.items()}==expected
            families[norm]=codes
        for overlap in (1,2):
            assert families[6][overlap,23]==families[8][overlap,23]
            triple_lines={tuple(x*pow(row[0]%q,-1,q)%q for x in row)
                          for row in norm_rows(6,6,minimum_support=3)
                          if all(row[i] for i in range(3)) and not any(row[3:])}
            assert all(first in triple_lines for first,_ in families[6][overlap,20])
        print(f'q={q}: each prescribed overlap has 3 determinant-20 and 6 determinant-23 planes; no extra norm-eight plane.')


if __name__=='__main__':
    exact_counts()
