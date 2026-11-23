"""Reduced short-pair certificates with a three-circuit on seven positions."""
from wall1_rare_second_line import norm_rows
from collections import Counter
for n,m in ((8,8),(8,10),(10,10)):
 counts=Counter()
 firsts=[v for v in norm_rows(7,n,minimum_support=3) if all(v[3:])]
 for a in firsts:
  for b in norm_rows(7,m,minimum_support=3):
   if any(b[i]*a[3]!=b[3]*a[i] for i in range(3,7)):continue
   if not all(b[i]*a[3]-b[3]*a[i] for i in range(3)):continue
   dot=sum(x*y for x,y in zip(a,b))
   if 2*abs(dot)>n:continue
   counts[n*m-dot*dot]+=1
 assert dict(counts)=={(8,8):{},(8,10):{76:24},(10,10):{91:48,96:18}}[n,m]
 print(n,m,dict(counts))
