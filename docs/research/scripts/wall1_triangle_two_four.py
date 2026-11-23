"""Gram determinants of triangular norm-four extensions on two new positions."""
from wall1_short_relation_shapes import balanced_rows
from itertools import combinations
from collections import Counter
from wall1_shared_dependent_codes import determinant
UPPER_COUNTS={32:6,36:24,44:18,48:6}
patterns=[]
four_pair_checks=0
for a in balanced_rows((0,1,2,3),8):
 for b in balanced_rows((2,3,4,5),8):
  dot=sum(x*y for x,y in zip(a,b))
  if abs(dot)!=2:continue
  assert any(abs(a[i]*b[j]-a[j]*b[i])==1 for i,j in combinations(range(6),2))
  counts=Counter()
  for old in combinations(range(6),2):
   for v in balanced_rows(old+(6,7),8):
    x=sum(i*j for i,j in zip(a,v));y=sum(i*j for i,j in zip(b,v))
    gram=48-4*x*x+2*dot*x*y-4*y*y
    counts[gram]+=1
    if gram==32:
     columns=Counter()
     for col in zip(a,b,v):
      sign=next(z for z in col if z)
      columns[tuple(sign*z for z in col)]+=1
     assert len(columns)==4 and set(columns.values())=={2}
     # The four projective directions form a unimodular circuit. Their
     # unique dependence has coefficients +/-1, giving four equal pair sums.
     assert all(abs(determinant(*triple))==1 for triple in combinations(columns,3))
     four_pair_checks+=1
  assert sum(counts.values())==45
  patterns.append(counts)
assert len(patterns)==5
assert four_pair_checks==27
assert {d:max(c[d] for c in patterns) for d in UPPER_COUNTS}==UPPER_COUNTS
if __name__=='__main__':
 print('Passed225 affine witnesses across five patterns:',UPPER_COUNTS)
 print('Passed27 determinant32 four-pair structural checks.')
