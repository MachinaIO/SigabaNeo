"""Counts and weighted Gram identities for six-circuit ten-position planes."""
from fractions import Fraction as F
from itertools import combinations
from math import comb,prod
from wall1_rare_second_line import norm_rows


def checks():
    six=list(norm_rows(10,6,minimum_support=6))
    eight=list(norm_rows(10,8,minimum_support=6))
    assert len(six)==2100==10*comb(10,6)
    assert len(eight)==1575==35*comb(10,8)
    checked=0
    for short in norm_rows(6,6,minimum_support=6):
        a=short+(0,)*4
        for b in six:
            if not all(b[6:]):continue
            if abs(sum(x*y for x,y in zip(a,b)))!=2:continue
            weights=[F(11,12) if x and y else F(49,48) for x,y in zip(a,b)]
            assert sum(weights)==10
            def inner(x,y):return sum(F(u*v)/w for u,v,w in zip(x,y,weights))
            first=inner(a,a)
            second=inner(b,b)-inner(a,b)**2/first
            assert first==F(3288,539)
            assert second==F(35712,6713)
            assert prod(weights)*first*second>32
            assert any(abs(a[i]*b[j]-a[j]*b[i])==1 for i,j in combinations(range(10),2))
            checked+=1
    assert checked==780
    print('Line counts:',len(six),len(eight),'pair-witness cover:',len(six)*len(eight))
    print('Weighted determinant32 checks:',checked,'product:',prod(weights)*first*second)


if __name__=='__main__':checks()
