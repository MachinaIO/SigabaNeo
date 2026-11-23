"""All-integer projection certificate for the nine-position determinant44 anchor."""
from itertools import combinations,product
from fractions import Fraction as F
from collections import Counter
from wall1_short_relation_shapes import balanced_rows
a=(1,1,-1,-1,0,0,0,0,0)
b=(0,0,1,1,-1,-1,0,0,0)
c=(1,0,0,0,0,0,1,-1,-1)
gram=[[sum(x*y for x,y in zip(u,v)) for v in (a,b,c)] for u in (a,b,c)]
adj=[[16,8,-4],[8,15,-2],[-4,-2,12]]
assert [[sum(gram[i][k]*adj[k][j] for k in range(3)) for j in range(3)]
        for i in range(3)]==[[44 if i==j else 0 for j in range(3)] for i in range(3)]
assert (F(4)+F(3)+F(11,3))/4==F(8,3)
def energy(v):
 x,y,z=[sum(i*j for i,j in zip(row,v)) for row in (a,b,c)]
 return 44*sum(i*i for i in v)-16*x*x-16*x*y+8*x*z-15*y*y+4*y*z-12*z*z
counts=0;best=999;witness=None
for norm in range(4):
 for support in combinations(range(9),norm):
  for signs in product((-1,1),repeat=norm):
   v=[0]*9
   for i,s in zip(support,signs):v[i]=s
   e=energy(v);assert e>=0
   counts+=1
   if 0<e<best:best=e;witness=v
assert counts==835 and best==24
assert F(8,3)+F(best,44)<4
def projective_columns(rows):
 result=Counter()
 for col in zip(*rows):
  sign=next(x for x in col if x)
  result[tuple(sign*x for x in col)]+=1
 return result
target=projective_columns((a,b,c))
patterns=0
for old_a in balanced_rows((0,1,2,3),9):
 for old_b in balanced_rows((2,3,4,5),9):
  dot=sum(x*y for x,y in zip(old_a,old_b))
  if abs(dot)!=2:continue
  third=tuple(x-(1 if dot>0 else -1)*y for x,y in zip(old_a,old_b))
  lines=(old_a,old_b,third)
  for j in range(6):
   first=next(x for x in lines if x[j])
   second=next(x for x in lines if not x[j])
   if sum(x*y for x,y in zip(first,second))>0:second=tuple(-x for x in second)
   for extension in balanced_rows((j,6,7,8),9):
    if sum(x*y for x,y in zip(first,extension))<0:extension=tuple(-x for x in extension)
    assert projective_columns((first,second,extension))==target
    patterns+=1
assert patterns==90
print('Passed835 integer projection checks and90 signed-permutation certificates.')
print('Projected squared minimum6/11; rounding squared radius8/3; cutoff106/33<4.')
