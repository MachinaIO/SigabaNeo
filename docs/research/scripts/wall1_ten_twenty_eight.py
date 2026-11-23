"""Geometry and witness checks for the ten-position determinant28 anchor."""
from fractions import Fraction as F
from itertools import combinations, product
from math import comb


def finite_checks():
    from wall1_short_relation_shapes import balanced_rows
    from wall1_rare_second_line import norm_rows
    a=(1,)*4+(0,)*6
    b=(1,1,0,0)+(1,)*6
    checked=0
    for v in product((-1,0,1),repeat=10):
        groups=(range(2),range(2,4),range(4,10))
        sums=[sum(v[i] for i in G) for G in groups]
        within=sum(F((v[i]-v[j])**2,len(G)) for G in groups for i,j in combinations(G,2))
        explicit=within+F((3*sums[0]-3*sums[1]-sums[2])**2,42)
        x,y=sum(z*w for z,w in zip(a,v)),sum(z*w for z,w in zip(b,v))
        D=F(sum(z*z for z in v))-F(8*x*x-4*x*y+4*y*y,28)
        assert D==explicit and (D==0 or D>=F(1,2))
        checked+=1
    count=0
    for first in balanced_rows((0,1,2,3),10):
        for second in norm_rows(10,8):
            if not all(second[4:]):continue
            if abs(sum(x*y for x,y in zip(first,second)))!=2:continue
            assert any(abs(first[i]*second[j]-first[j]*second[i])==1
                       for i,j in combinations(range(10),2))
            count+=1
    assert count==330 and comb(10,4)*count==69300
    assert F(4*8*8,4*28)==F(16,7) and 28*25**4<3329**2
    print(f'Passed{checked} projection checks and330 primitive witnesses per first support.')


if __name__=='__main__':
    finite_checks()
