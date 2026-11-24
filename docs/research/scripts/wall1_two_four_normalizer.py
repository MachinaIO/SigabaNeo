"""Exact canonical unit-minor charts for the nine two-four codes."""
from fractions import Fraction as F
from collections import Counter
from itertools import product
from wall1_short_relation_shapes import balanced_rows


def checks():
    basis=(0,1,2,4);counts=Counter()
    for u in balanced_rows((0,1,2,3),6):
        for v in balanced_rows((0,1,4,5),6):
            assert u[5]==v[3]==0 and abs(u[3]*v[5])==1
            cols=[tuple(-F(row[i],row[p]) for i in basis)
                  for row,p in ((u,3),(v,5))]
            assert all(sum(col)==1 for col in cols)
            a=sum(x*x for x in cols[0]);b=sum(x*x for x in cols[1])
            cross=sum(x*y for x,y in zip(*cols))
            determinant=(1+a)*(1+b)-cross*cross
            assert a==b==3 and cross in (-2,0,2)
            assert determinant==16-sum(x*y for x,y in zip(u,v))**2
            counts[determinant]+=1
    assert counts=={F(12):5,F(16):4}
    print('Passed nine canonical unit-minor charts; determinants 12:5, 16:4.')


def convolution_checks():
    tested=0
    charts=(((1,1,-1,0),(1,1,0,-1)),((1,1,-1,0),(1,-1,0,1)))
    for q in (3,5):
        f=[F(1,1+min(x,q-x)**2) for x in range(q)]
        conv=[F(1)]+[F(0)]*(q-1)
        for _ in range(6):
            conv=[sum((conv[y]*f[(x-y)%q] for y in range(q)),F(0)) for x in range(q)]
        for columns in charts:
            hyper=[F(0)]*q
            for x in product(range(q),repeat=4):
                value=F(0)
                for b0,b1 in product(range(q),repeat=2):
                    term=f[b0]*f[b1]
                    for j in range(4):
                        term*=f[(x[j]+columns[0][j]*b0+columns[1][j]*b1)%q]
                    value+=term
                hyper[sum(x)%q]+=value
            assert hyper==conv
            tested+=1
    print('Passed exact anchor hyperplane/convolution identities:',tested)


def completion_checks():
    from mpmath import iv
    from wall1_anchored_dual_completion import completion_details
    iv.dps=60;I=iv.mpf;q=3329
    R2=I('1.21')*iv.exp(2*(386*iv.log(q)-iv.log(iv.pi**253/iv.factorial(253)))/506)-2
    s={'iv':iv,'q':q,'N':518,'radius':iv.sqrt(R2)}
    tested=0
    for r,h in ((4,6),(4,8),(9,24)):
        for free in (None,I(518)/(2*R2)):
            kwargs=dict(anchor_size=6,free_beta=free,coordinate_count=518)
            generic=completion_details(s,r,h,**kwargs)
            tri=completion_details(s,r,h,anchor_gram_det=12,**kwargs)
            square=completion_details(s,r,h,anchor_gram_det=16,**kwargs)
            # Spectral moments use different eigenvalues, so the two certified
            # families no longer have an ordering determined by determinant.
            assert 0<tri[0] and tri[0].b<=generic[0].b
            assert 0<square[0] and square[0].b<=generic[0].b
            if h>r+2:
                assert completion_details(s,r,h,anchor_gram_det=12,**kwargs) is tri
            tested+=1
    try:
        completion_details(s,4,8,anchor_size=5,anchor_gram_det=12)
    except AssertionError:pass
    else:raise AssertionError('Unsupported anchor accepted')
    print('Passed determinant-specific completion/cache cases:',tested)


if __name__=='__main__':
    checks()
    convolution_checks()
    completion_checks()
