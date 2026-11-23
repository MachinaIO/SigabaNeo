"""Norm-four/ten planes on twelve coordinates with prescribed overlaps."""
from itertools import combinations
from collections import defaultdict
from wall1_short_relation_shapes import balanced_rows
for q in (7,17,3329):
 codes=defaultdict(set)
 for first in balanced_rows((0,1,2,3),12):
  for old in combinations(range(4),2):
   support=old+tuple(range(4,12))
   for plus in combinations(support[1:],4):
    positive={support[0],*plus}
    second=tuple(1 if i in positive else -1 if i in support else 0 for i in range(12))
    assert sum(second)==0
    dot=sum(x*y for x,y in zip(first,second))
    determinant=40-dot*dot
    inverse=pow(second[4]%q,-1,q)
    key=(first,tuple((x-second[0]*y)*inverse%q for x,y in zip(second,first)))
    for scalar in {(-second[i]*pow(first[i]%q,-1,q))%q for i in range(4)}:
     old_support=tuple(i for i in range(4) if (second[i]+scalar*first[i])%q)
     for a in (1,2,3):
      if old_support==tuple(range(a)): codes[a,determinant].add(key)
 actual={k:len(v) for k,v in codes.items()}
 assert actual=={(2,36):196,(2,40):182,(3,40):546}
 print(q,actual)
