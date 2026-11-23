"""Exact checks for excluding an additional norm-four direction."""
from fractions import Fraction as F
from itertools import product
from math import comb, floor
from wall1_rare_second_line import norm_rows


def finite_checks():
    checked=0
    for a,b,cover in (
        ((1,1,-1,-1,0,0),(0,0,-1,-1,1,1),F(4,3)),
        ((1,-1,1,-1,0,0),(0,0,1,-1,-1,1),F(4,3)),
        ((1,1,-1,-1,0,0),(1,-1,0,0,1,-1),F(2)),
        ((1,1,-1,-1,0,0,0),(1,0,0,0,1,-1,-1),F(8,5)),
        ((1,1,-1,-1,0,0,0,0),(1,1,0,0,1,-1,-1,-1),F(9,5)),
        ((1,1,-1,-1,0,0,0,0,0),(1,0,0,0,1,1,-1,-1,-1),F(48,23))):
        dot=sum(x*y for x,y in zip(a,b))
        size=len(a)
        norm_b=sum(z*z for z in b)
        determinant=4*norm_b-dot*dot
        for v in product((-1,0,1),repeat=size+2):
            if sum(v):
                continue
            x=sum(z*c for z,c in zip(v,a))
            y=sum(z*c for z,c in zip(v,b))
            u,w=F(norm_b*x-dot*y,determinant),F(4*y-dot*x,determinant)
            height=F(sum(z*z for z in v))-u*x-w*y
            candidates=[tuple(z-ru*c-rw*d for z,c,d in zip(v,a+(0,0),b+(0,0)))
                        for ru in (floor(u),floor(u)+1) for rw in (floor(w),floor(w)+1)]
            reduced=min(candidates,key=lambda row:sum(z*z for z in row))
            norm=sum(z*z for z in reduced)
            assert sum(reduced)==0 and norm%2==0
            assert norm<=height+cover
            if 0<height<6-cover:
                assert norm in (2,4)
            checked+=1
        for t in range(1,5):
            rare=[v for v in norm_rows(size+t,4) if all(v[size:])]
            assert len(rare)==3*comb(size,4-t)
    print(f'Passed {checked} exact plane-rounding checks and twenty-four rare-line counts.')


if __name__=='__main__':
    finite_checks()
