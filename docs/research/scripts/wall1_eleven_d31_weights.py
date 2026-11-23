"""Exact rational weights for eleven-position norm-four/eight planes."""
from fractions import Fraction as F
from math import prod
from wall1_short_relation_shapes import balanced_rows
from wall1_rare_second_line import norm_rows

def checks():
    rows=[v for v in norm_rows(11,8) if all(v[4:])]
    checked=0
    for a in balanced_rows((0,1,2,3),11):
        for b in rows:
            old=[i for i in range(4) if b[i]]
            assert len(old)==1 and all(abs(x)<=1 for x in b)
            weights=[F(11,12)]*4+[F(77,72)]*7
            weights[old[0]]=F(55,72)
            assert sum(weights)==11
            def inner(x,y):return sum(F(u*v)/w for u,v,w in zip(x,y,weights))
            first=inner(a,a)
            second=inner(b,b)-inner(a,b)**2/first
            assert (first,second)==(F(252,55),F(576,77))
            assert prod(weights)*first*second>31
            checked+=1
    assert checked==420
    print('Passed420 exact weighted Gram checks; squared heights252/55 and576/77.')
    print('Weighted determinant product:',prod(weights)*first*second)

if __name__=='__main__':checks()
