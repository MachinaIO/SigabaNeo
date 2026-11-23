"""Norm-ten pairs with a four-circuit on eleven positions."""
from wall1_rare_second_line import norm_rows
from collections import defaultdict
rows=[v for v in norm_rows(11,10) if all(v[4:])]
for q in (7,17,3329):
 codes=defaultdict(set)
 for short in norm_rows(4,10):
  a=short+(0,)*7
  pivot=next(i for i,x in enumerate(a) if abs(x)==1)
  for v in rows:
   dot=sum(x*y for x,y in zip(a,v))
   d=100-dot*dot
   inv=pow(v[4]%q,-1,q)
   factor=v[pivot]*pow(a[pivot]%q,-1,q)%q
   key=(a,tuple((x-factor*y)*inv%q for x,y in zip(v,a)))
   for scalar in {(-v[i]*pow(a[i]%q,-1,q))%q for i in range(4)}:
    support=tuple(i for i in range(4) if (v[i]+scalar*a[i])%q)
    for overlap in (1,2,3):
     if support==tuple(range(overlap)):codes[overlap,d].add(key)
 actual={k:len(v) for k,v in sorted(codes.items())}
 assert actual=={(2,75):70,(2,84):140,(2,91):140,(2,100):140,
                 (3,75):210,(3,84):420,(3,91):420,(3,96):1344,(3,99):1344,(3,100):420}
 print(q,actual)
