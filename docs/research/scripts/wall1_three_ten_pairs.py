from wall1_rare_second_line import norm_rows
from itertools import product
from collections import defaultdict
rows={n:[v for v in norm_rows(10,n) if all(v[3:]) and any(v[:3])] for n in (8,10)}
checked=0
for n,m in ((8,8),(8,10),(10,10)):
 by_new=defaultdict(list)
 for b in rows[m]:
  sign=b[3];assert abs(sign)==1
  by_new[tuple(sign*x for x in b[3:])].append(tuple(sign*x for x in b))
 for a in rows[n]:
  sign=a[3];assert abs(sign)==1
  a=tuple(sign*x for x in a)
  for b in by_new[a[3:]]:
   if a==b:continue
   if not all(b[i]-a[i] for i in range(3)):continue
   dot=sum(x*y for x,y in zip(a,b))
   assert 2*abs(dot)>n,(a,b,n,m,dot)
   checked+=1
print('Excluded all three reduced-pair classes;',checked,'eligible proportional pairs checked.')
