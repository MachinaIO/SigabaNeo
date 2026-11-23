"""Exact sign-sensitive weights for nine-position determinant31 planes."""
from fractions import Fraction as F
from math import prod
from wall1_short_relation_shapes import balanced_rows
from wall1_rare_second_line import norm_rows


def checks():
    rows=[v for v in norm_rows(9,8) if all(v[4:])]
    checked=0
    for a in balanced_rows((0,1,2,3),9):
        for b in rows:
            dot=sum(x*y for x,y in zip(a,b))
            if abs(dot)!=1:continue
            assert all(abs(x)<=1 for x in b) and sum(bool(x) for x in b[:4])==3
            b=tuple(dot*x for x in b)
            weights=[F(5,6) if x*y==1 else F(5,12) if x*y==-1 else F(13,12)
                     for x,y in zip(a[:4],b[:4])]+[F(7,6)]*5
            assert sum(weights)==9
            def inner(x,y):return sum(F(u*v)/w for u,v,w in zip(x,y,weights))
            assert inner(a,b)==0
            assert inner(a,a)==F(372,65) and inner(b,b)==F(318,35)
            assert prod(weights)*inner(a,a)*inner(b,b)==F(19724215,559872)>31
            assert any(a[i] and not b[i] for i in range(4))
            checked+=1
    assert checked==300
    print('Passed weighted Gram checks:',checked,'weighted determinant product19724215/559872.')


if __name__=='__main__':checks()
