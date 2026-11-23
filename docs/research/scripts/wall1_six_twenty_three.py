"""Six-position girth-three determinant23 anchor geometry and witnesses."""
from fractions import Fraction as F
from itertools import combinations, product
from wall1_short_relation_shapes import balanced_rows
from wall1_rare_second_line import norm_rows


def finite_checks():
    a,b=(1,1,1,1,0,0),(1,0,0,0,2,1)
    checked=0
    for v in product((-1,0,1),repeat=6):
        norm=sum(z*z for z in v)
        if norm>2:continue
        x,y=sum(z*w for z,w in zip(a,v)),sum(z*w for z,w in zip(b,v))
        D=F(norm)-F(6*x*x-2*x*y+4*y*y,23)
        assert D==0 or D>=F(7,23)
        checked+=1
    assert checked==73 and F(7+48,23)<3
    count=0
    for support in combinations(range(6),4):
        for a in balanced_rows(support,6):
            for b in norm_rows(6,6,minimum_support=3):
                if not all(x or y for x,y in zip(a,b)):continue
                if abs(sum(x*y for x,y in zip(a,b)))!=1:continue
                assert sum(bool(x) for x in b)==3
                assert any(abs(a[i]*b[j]-a[j]*b[i])==1 for i,j in combinations(range(6),2))
                count+=1
    assert count==360 and 23*26**4<3329**2
    assert F(4*6*8,4*23)==F(48,23)
    print('Passed73 bounded projection representatives and360 primitive affine witnesses.')


if __name__=='__main__':
    finite_checks()
