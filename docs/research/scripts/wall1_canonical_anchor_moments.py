"""Exact completion-square identities for certified canonical anchor charts."""
from fractions import Fraction as F
from itertools import product

CHARTS={12:((1,1,-1,0),(1,1,0,-1)),
        16:((1,1,-1,0),(1,-1,0,1)),
        15:((1,1,-1,0,0),(1,0,0,1,-1))}


def checks():
    checked=0
    for determinant,cols in CHARTS.items():
        r=len(cols[0]);cross=sum(a*b for a,b in zip(*cols))
        assert all(sum(v)==1 and sum(x*x for x in v)==3 for v in cols)
        assert 16-cross*cross==determinant
        H=((4,cross),(cross,4))
        inverse=((F(4,determinant),F(-cross,determinant)),
                 (F(-cross,determinant),F(4,determinant)))
        spectral=4+abs(cross)
        assert spectral=={12:6,16:4,15:5}[determinant]
        for v in product((-1,0,1),repeat=r):
            u=tuple(sum(a*x for a,x in zip(col,v)) for col in cols)
            shift=tuple(sum(inverse[i][j]*u[j] for j in range(2)) for i in range(2))
            residual=sum(x*x for x in v)-sum(u[i]*shift[i] for i in range(2))
            assert residual>=F(sum(x*x for x in v),spectral)
            for b in product((-1,0,1),repeat=2):
                direct=sum((v[i]+sum(cols[j][i]*b[j] for j in range(2)))**2
                           for i in range(r))+sum(x*x for x in b)
                w=tuple(F(b[i])+shift[i] for i in range(2))
                square=sum(w[i]*H[i][j]*w[j] for i in range(2) for j in range(2))
                assert direct==residual+square
                checked+=1
    print('Passed exact canonical completion-square identities:',checked)


if __name__=='__main__':checks()

# At a large weight the raw wrapped moment exceeds one. This regression
# distinguishes the raw spectral majorant from a normalized free factor.
if __name__=='__main__':
    from mpmath import iv
    from wall1_anchored_dual_completion import raw_moment, free_moment
    iv.dps=40
    beta=iv.mpf(100)
    assert raw_moment(3,beta,2).a>1
    assert free_moment(3,beta,2)==1
    print('Passed raw versus normalized moment regression.')
