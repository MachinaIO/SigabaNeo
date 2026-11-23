"""Norm-six/eight planes with a six-circuit on twelve coordinates."""
from wall1_rare_second_line import norm_rows
from collections import defaultdict
rows=[v for v in norm_rows(12,8,minimum_support=6) if all(v[6:])]
for q in (7,17,3329):
 codes=defaultdict(set)
 for short in norm_rows(6,6,minimum_support=6):
  a=short+(0,)*6
  for v in rows:
   dot=sum(x*y for x,y in zip(a,v));d=48-dot*dot
   inv=pow(v[6]%q,-1,q)
   factor=v[0]*pow(a[0]%q,-1,q)%q
   key=(a,tuple((x-factor*y)*inv%q for x,y in zip(v,a)))
   for scalar in {(-v[i]*pow(a[i]%q,-1,q))%q for i in range(6)}:
    support=tuple(i for i in range(6) if (v[i]+scalar*a[i])%q)
    for overlap in range(1,6):
     if support==tuple(range(overlap)):codes[overlap,d].add(key)
 actual={k:len(v) for k,v in sorted(codes.items())}
 assert actual=={(2,44):180,(2,48):170,(4,44):180,(5,48):850}
 print(q,actual)
