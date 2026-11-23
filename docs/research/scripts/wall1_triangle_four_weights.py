"""Exact weighted Gram certificate for all triangular norm-four extensions."""
from fractions import Fraction as F
from wall1_short_relation_shapes import balanced_rows
from itertools import combinations


def checks():
    checked=0
    for a in balanced_rows((0,1,2,3),9):
        for b in balanced_rows((2,3,4,5),9):
            dot=sum(x*y for x,y in zip(a,b))
            if abs(dot)!=2:continue
            third=tuple(x-(1 if dot>0 else -1)*y for x,y in zip(a,b))
            lines=(a,b,third)
            for j in range(6):
                first=next(x for x in lines if x[j])
                second=next(x for x in lines if not x[j])
                weights=[F(1)]*6+[F(9,8)]*3
                weights[j]=F(5,8)
                assert sum(weights)==9
                for v in balanced_rows((j,6,7,8),9):
                    def inner(x,y):return sum(F(u*z)/w for u,z,w in zip(x,y,weights))
                    d1=inner(first,first)
                    off=inner(first,second)
                    d2=inner(second,second)-off**2/d1
                    x,y=inner(v,first),inner(v,second)
                    d3=inner(v,v)-x*x/d1-(y-x*off/d1)**2/d2
                    assert (d1,d2,d3)==(F(23,5),F(72,23),F(32,9))
                    assert y==0
                    checked+=1
    assert checked==90
    assert F(5,8)*F(9,8)**3*F(23,5)*F(72,23)*F(32,9)==F(729,16)>44
    print('Passed90 exact weighted Gram checks; determinant product729/16 versus44.')


if __name__=='__main__':checks()
