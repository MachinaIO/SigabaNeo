"""Norm-four/ten witnesses on ten positions, including coefficient-two rows."""
from wall1_short_relation_shapes import balanced_rows
from wall1_rare_second_line import norm_rows
from collections import defaultdict
rows=[v for v in norm_rows(10,10) if all(v[4:])]
for q in (7,17,3329):
 codes=defaultdict(set)
 for first in balanced_rows((0,1,2,3),10):
  for second in rows:
   dot=sum(x*y for x,y in zip(first,second))
   det=40-dot*dot
   inv=pow(second[4]%q,-1,q)
   key=(first,tuple((x-second[0]*y)*inv%q for x,y in zip(second,first)))
   for scalar in {(-second[i]*pow(first[i]%q,-1,q))%q for i in range(4)}:
    support=tuple(i for i in range(4) if (second[i]+scalar*first[i])%q)
    for a in (1,2,3):
     if support==tuple(range(a)):codes[a,det].add(key)
 actual={k:len(v) for k,v in sorted(codes.items())}
 assert actual=={(1,36):45,(1,39):270,(2,40):46,(3,36):45,(3,39):270}
 print(q,actual)
