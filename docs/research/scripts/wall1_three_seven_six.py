"""Norm-six plane counts with a three-circuit on seven positions."""
from wall1_rare_second_line import norm_rows
from collections import defaultdict
rows=[v for v in norm_rows(7,6) if all(v[3:])]
for q in (7,17,3329):
 codes=defaultdict(set)
 for short in norm_rows(3,6,minimum_support=3):
  a=short+(0,)*4
  pivot=next(i for i,x in enumerate(a) if abs(x)==1)
  for v in rows:
   dot=sum(x*y for x,y in zip(a,v));d=36-dot*dot
   inv=pow(v[3]%q,-1,q)
   factor=v[pivot]*pow(a[pivot]%q,-1,q)%q
   key=(a,tuple((x-factor*y)*inv%q for x,y in zip(v,a)))
   for scalar in {(-v[i]*pow(a[i]%q,-1,q))%q for i in range(3)}:
    support=tuple(i for i in range(3) if (v[i]+scalar*a[i])%q)
    for overlap in (1,2):
     if support==tuple(range(overlap)):codes[overlap,d].add(key)
 actual={k:len(v) for k,v in sorted(codes.items())}
 assert actual=={(1,32):4,(2,27):18,(2,32):4,(2,35):24,(2,36):18}
 print(q,actual)
