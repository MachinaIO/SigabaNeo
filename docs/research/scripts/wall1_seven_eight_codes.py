"""Exact norm-four/eight code counts on seven coordinates."""
from wall1_short_relation_shapes import balanced_rows
from wall1_rare_second_line import norm_rows
from collections import defaultdict
rows=[v for v in norm_rows(7,8) if all(v[4:])]
for q in (7,17,3329):
 codes=defaultdict(set)
 for first in balanced_rows((0,1,2,3),7):
  for second in rows:
   dot=sum(x*y for x,y in zip(first,second))
   det=32-dot*dot
   inv=pow(second[4]%q,-1,q)
   key=(first,tuple((x-second[0]*y)*inv%q for x,y in zip(second,first)))
   for scalar in {(-second[i]*pow(first[i]%q,-1,q))%q for i in range(4)}:
    support=tuple(i for i in range(4) if (second[i]+scalar*first[i])%q)
    for a in (1,2,3):
     if support==tuple(range(a)):codes[a,det].add(key)
 actual={k:len(v) for k,v in sorted(codes.items())}
 assert actual=={(2,23):14,(2,28):18,(2,31):10,(2,32):18,
                 (3,23):42,(3,31):30,(3,32):54}
 # D23 witnesses reduce to norm six, already covered by the six-row stratum.
 for a in balanced_rows((0,1,2,3),7):
  for v in rows:
   dot=sum(x*y for x,y in zip(a,v))
   if 32-dot*dot==23:
    sign=1 if dot>0 else -1
    assert sum((x-sign*y)**2 for x,y in zip(v,a))==6
 print(q,actual)
