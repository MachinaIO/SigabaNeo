"""Ten-position planes with a norm-six three-circuit and norm-eight extension."""
from wall1_rare_second_line import norm_rows
from collections import defaultdict
rows=[v for v in norm_rows(10,8) if all(v[3:])]
for q in (7,17,3329):
 codes=defaultdict(set)
 for short in norm_rows(3,6,minimum_support=3):
  a=short+(0,)*7
  pivot=next(i for i,x in enumerate(a) if x==1 or x==-1)
  for v in rows:
   inv=pow(v[3]%q,-1,q)
   factor=v[pivot]*pow(a[pivot]%q,-1,q)%q
   key=(a,tuple((x-factor*y)*inv%q for x,y in zip(v,a)))
   d=48-sum(x*y for x,y in zip(a,v))**2
   for scalar in {(-v[i]*pow(a[i]%q,-1,q))%q for i in range(3)}:
    support=tuple(i for i in range(3) if (v[i]+scalar*a[i])%q)
    for overlap in (1,2):
     if support==tuple(range(overlap)):codes[overlap,d].add(key)
 actual={k:len(v) for k,v in sorted(codes.items())}
 assert actual=={(1,44):35,(1,47):70,(2,44):35,(2,47):70}
 print(q,actual)
