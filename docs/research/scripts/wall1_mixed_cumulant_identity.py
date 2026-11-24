"""Exact mixed-cumulant identity for the negative weighted selection term."""
from fractions import Fraction as F
from math import factorial
from itertools import product
from wall1_affine_square_certificate import coefficients, falling


def mixed_series(law, degree):
    """Return [t^j] E[Q(1+t)^N]/E[(1+t)^N], without independence."""
    assert sum(p for _,_,p in law)==1
    A=[sum(p*falling(n,j) for q,n,p in law)/factorial(j) for j in range(degree+1)]
    B=[sum(p*q*falling(n,j) for q,n,p in law)/factorial(j) for j in range(degree+1)]
    out=[]
    for j in range(degree+1):
        out.append(B[j]-sum((A[i]*out[j-i] for i in range(1,j+1)),F(0)))
    return out


def main():
    laws=[[(0,0,F(1,2)),(1,1,F(1,2))],
          [(0,1,F(1,2)),(1,0,F(1,2))],
          [(0,0,F(1,3)),(2,1,F(1,6)),(4,5,F(1,2))],
          [(q,n,F(1,12)) for q in range(3) for n in range(4)]]
    checked=0
    for law in laws:
        mu=sum(p*n for q,n,p in law)
        for t in (1,2,3,6,12):
            _,f,_=coefficients(mu,t)
            c=mixed_series(law,2*t)
            def delta_value(n,j):
                return sum((f[k]*falling(k,j)*falling(n,k-j)
                            for k in range(j,len(f))),F(0))
            exact=sum(p*q*delta_value(n,0) for q,n,p in law)
            rhs=sum((c[j]*sum(p*delta_value(n,j) for q,n,p in law)
                     for j in range(len(f))),F(0))
            assert exact==rhs
            bound=c[0]*sum(p*delta_value(n,0) for q,n,p in law)
            for j in range(1,len(f)):
                major=sum((p*sum((abs(f[k])*falling(k,j)*falling(n,k-j)
                                 for k in range(j,len(f))),F(0))
                           for q,n,p in law),F(0))
                assert major>=sum(p*abs(delta_value(n,j)) for q,n,p in law)
                bound-=abs(c[j])*major
            assert bound<=exact
            checked+=1
    assert mixed_series(laws[0],1)[1]>0
    assert mixed_series(laws[1],1)[1]<0
    assert all(c==0 for c in mixed_series(laws[-1],24)[1:])
    print(f'Passed {checked} exact joint-law identities and signed-term lower bounds, through degree24.')
    print('Mixed coefficients can have either sign; independent-law mixed terms vanish.')
    affine_shift_checks()


def affine_shift_checks():
    checked=0
    for q in (2,3,5):
        matrices=list(product(range(q),repeat=2))
        for candidates in (((0,0,0),(0,1,0)),
                           ((0,0,0),(1,1,0),(0,0,1),(1,1,1))):
            for requirement in (lambda a:True, lambda a:a[1]==0,
                                lambda a:(a[0]+a[1])%q==1):
                selected=[a for a in matrices if requirement(a)]
                for target in range(q):
                    law=[]
                    collision=[]
                    for a in selected:
                        Q=int(a[0]==target)
                        counts=[sum((x-a[0]*y-a[1]*z)%q==v for x,y,z in candidates)
                                for v in range(q)]
                        assert F(sum(counts),q)==F(len(candidates),q)
                        J=sum(n*n for n in counts)
                        collision.append((Q,J))
                        law.extend((Q,n,F(1,len(selected)*q)) for n in counts)
                    cs=mixed_series(law,4)
                    assert cs[1]==0
                    eq=F(sum(Q for Q,J in collision),len(selected))
                    ej=F(sum(J for Q,J in collision),len(selected))
                    eqj=F(sum(Q*J for Q,J in collision),len(selected))
                    assert 2*cs[2]==(eqj-eq*ej)/q
                    if q==3 and len(candidates)==2 and len(selected)==9:
                        assert 2*cs[2]==(F(4,27) if target==0 else F(-2,27))
                    checked+=1
    print(f'Passed {checked} exact auxiliary-shift cancellation and collision-covariance checks.')


if __name__=='__main__':
    main()
