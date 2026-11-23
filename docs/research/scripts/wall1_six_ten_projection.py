"""Projection certificate and affine types for two-six determinant32 anchors."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations,product
from wall1_rare_second_line import norm_rows

REPRESENTATIVES=(
 ((1,1,1,-1,-1,-1,0,0,0,0),(1,1,0,0,0,0,1,-1,-1,-1)),
 ((1,1,1,-1,-1,-1,0,0,0,0),(1,0,0,-1,0,0,1,1,-1,-1)))


def checks():
    a=(1,)*6+(0,)*4
    b=(1,1,0,0,0,0,1,1,1,1)
    def energy(v):
        x=sum(i*j for i,j in zip(a,v));y=sum(i*j for i,j in zip(b,v))
        return 32*sum(z*z for z in v)-6*x*x+4*x*y-6*y*y
    checked=0;best=32
    for norm in range(4):
        for support in combinations(range(10),norm):
            for signs in product((-1,1),repeat=norm):
                v=[0]*10
                for i,sign in zip(support,signs):v[i]=sign
                value=energy(v);assert value>=0
                if value:best=min(best,value)
                checked+=1
    assert checked==1161 and best==24
    assert energy((1,)+(0,)*9)==24
    assert (F(6)+F(16,3))/4==F(17,6)
    assert F(17,6)+F(3,4)==F(43,12)<4
    types=[Counter(zip(*rows)) for rows in REPRESENTATIVES]
    checked_pairs=0
    outside=[v for v in norm_rows(10,6,minimum_support=6) if all(v[6:])]
    for old in norm_rows(6,6,minimum_support=6):
        first=old+(0,)*4
        for second in outside:
            dot=sum(x*y for x,y in zip(first,second))
            if abs(dot)!=2:continue
            if dot<0:second=tuple(-x for x in second)
            columns=Counter(zip(first,second))
            negated=Counter((-x,-y) for x,y in zip(first,second))
            assert columns in types or negated in types
            checked_pairs+=1
    assert checked_pairs==780
    assert 32*24**4<3329**2
    print('Passed1161 projection checks; minimum3/4, rounding radius17/6.')
    print('Passed780 balance-preserving two-type anchor checks.')


if __name__=='__main__':checks()
