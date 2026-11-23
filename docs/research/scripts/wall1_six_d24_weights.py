"""Exact weighted Gram check for six-position four/six determinant24 planes."""
from fractions import Fraction as F
from wall1_short_relation_shapes import balanced_rows
from wall1_rare_second_line import norm_rows
from math import prod


def checks():
    count=0
    weights=[F(5,6)]*4+[F(4,3)]*2
    assert sum(weights)==6
    for a in balanced_rows((0,1,2,3),6):
        for b in norm_rows(6,6,minimum_support=6):
            if sum(x*y for x,y in zip(a,b))!=0:continue
            def inner(x,y):return sum(F(u*v)/w for u,v,w in zip(x,y,weights))
            first=inner(a,a)
            off=inner(a,b)
            second=inner(b,b)-off**2/first
            assert (first,off,second)==(F(24,5),0,F(63,10))
            assert prod(weights)*first*second==F(700,27)>24
            count+=1
    assert count==12
    print('Passed12 exact six-position weighted Gram checks.')


if __name__=='__main__':checks()
