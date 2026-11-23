"""Weighted Gram certificate for eight-position determinant28 planes."""
from fractions import Fraction as F
from math import prod
from wall1_short_relation_shapes import balanced_rows
from wall1_rare_second_line import norm_rows

def checks():
    rows=[v for v in norm_rows(8,8) if all(v[4:])]
    count=0
    for a in balanced_rows((0,1,2,3),8):
        for original in rows:
            dot=sum(x*y for x,y in zip(a,original))
            if 32-dot*dot!=28:continue
            v=original
            if sum(bool(x) for x in v[:4])==4:
                sign=1 if dot>0 else -1
                v=tuple(x-sign*y for x,y in zip(v,a))
            old=[i for i in range(4) if v[i]]
            assert len(old)==1 and abs(v[old[0]])==2
            assert all(abs(x)==1 for x in v[4:])
            weights=[F(7,8)]*4+[F(21,16)]*4
            weights[old[0]]=F(1,8)
            assert sum(weights)==8
            def inner(x,y):return sum(F(u*z)/w for u,z,w in zip(x,y,weights))
            first=inner(a,a)
            second=inner(v,v)-inner(a,v)**2/first
            assert (first,second)==(F(80,7),F(1328,105))
            assert prod(weights)*first*second>28
            count+=1
    assert count==96
    print('Passed',count,'exact D28 basis-change and weighted Gram checks.')
    print('Weighted determinant product:',prod(weights)*first*second)

if __name__=='__main__':checks()
