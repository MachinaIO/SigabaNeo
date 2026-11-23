"""Five-position two-norm-four determinant15 geometry."""
from fractions import Fraction as F
from itertools import combinations, product
from wall1_short_relation_shapes import balanced_rows


def finite_checks():
    a,b=(1,1,1,1,0),(1,1,-1,0,1)
    checked=0
    for v in product((-1,0,1),repeat=5):
        norm=sum(x*x for x in v)
        if norm>1:continue
        x,y=sum(z*w for z,w in zip(a,v)),sum(z*w for z,w in zip(b,v))
        D=F(norm)-F(4*x*x-2*x*y+4*y*y,15)
        assert D==0 or D>=F(1,3)
        checked+=1
    assert checked==11 and F(1,3)+F(8,5)<2
    rows=[row for C in combinations(range(5),4) for row in balanced_rows(C,5)]
    count=0
    for a,b in combinations(rows,2):
        if not all(x or y for x,y in zip(a,b)):continue
        dot=sum(x*y for x,y in zip(a,b))
        assert abs(dot) in (1,3)
        if abs(dot)==3:
            sign=1 if dot>0 else -1
            assert sum(bool(x-sign*y) for x,y in zip(a,b))==2
            continue
        assert any(abs(a[i]*b[j]-a[j]*b[i])==1 for i,j in combinations(range(5),2))
        count+=1
    assert count==60 and 15*29**4<3329**2
    assert F(4*4*6,4*15)==F(8,5)
    print('Passed11 bounded representatives and60 primitive determinant15 witness pairs.')


if __name__=='__main__':
    finite_checks()
