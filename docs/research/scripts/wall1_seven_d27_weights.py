"""Exact weights for three-circuit determinant27 planes on seven positions."""
from fractions import Fraction as F
from math import prod
from wall1_rare_second_line import norm_rows


def checks():
    checked=0
    rows=[v for v in norm_rows(7,6) if all(v[3:])]
    for short in norm_rows(3,6,minimum_support=3):
        a=short+(0,)*4
        for b in rows:
            if abs(sum(x*y for x,y in zip(a,b)))!=3:continue
            weights=[F(1,8) if abs(x)==2 else F(23,16) for x in short]+[F(1)]*4
            assert sum(weights)==7
            assert all(abs(x)<=1 for x in b)
            def inner(x,y):return sum(F(u*v)/w for u,v,w in zip(x,y,weights))
            first=inner(a,a)
            second=inner(b,b)-inner(a,b)**2/first
            assert (first,second)==(F(768,23),F(100,23))
            assert prod(weights)*first*second==F(75,2)>27
            # Unit old coefficient and new unit entry certify saturation.
            assert any(abs(x)==1 for x in a[:3])
            checked+=1
    assert checked==36
    print('Passed36 exact weighted Gram checks; weighted determinant product75/2.')


if __name__=='__main__':checks()
