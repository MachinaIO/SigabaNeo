"""Nonorthogonal, redundant-label checks for the multheight majorizer.

Use M=Z^2, K=q^-1 Z^2 and T=q^-1[[1,1,0],[0,1,0]].
T^T T <= 3/q^2 I because the difference quadratic form is
(x-y)^2+x^2+3z^2. Labels Fq^3 surject onto K/M with fibers q.
Representatives T*center(label) need not be nearest representatives.
Branch choices below depend on the physical mark, never its redundant label.
They need not be shortest: contractivity applies to every nonzero branch w.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import product


def dot(x,y):
    return sum((a*b for a,b in zip(x,y)),F(0))


def center(x,q):
    return (x+q//2)%q-q//2


def representative(a,q):
    x,y,_=(center(v,q) for v in a)
    return (F(x+y,q),F(y,q))


def physical(a,q):
    return ((a[0]+a[1])%q,a[1]%q)


def main():
    q=3;base=F(3,2);heights=(-1,0,1);radius_sq=F(1,3);k=2
    labels=tuple(product(range(q),repeat=3))
    fibers=Counter(physical(a,q) for a in labels)
    assert len(fibers)==q*q and set(fibers.values())=={q}
    # A diagonal-only bound fails, even on centered labels.
    x=(1,1,0)
    assert dot(representative(x,q),representative(x,q))==F(5,q*q)
    assert F(5,q*q)>F(2,q*q)*sum(v*v for v in x)
    checked=0;strict_non_nearest=0;miss_moment=F(0);majorant_moment=F(0)
    for u in labels:
        U=physical(u,q)
        # Both branches are legal graph-lattice vectors: e1 in M or (U/q,1).
        horizontal=bool(U[0]%2)
        w=(F(1),F(0),F(0)) if horizontal else (
            F(center(U[0],q),q),F(center(U[1],q),q),F(1))
        quotient=Counter((physical(v,q)[1],) if horizontal else physical(v,q)
                         for v in labels)
        assert len(set(quotient.values()))==1
        misses=0;majorants=F(0)
        for v in labels:
            rv=representative(v,q);ru=representative(u,q)
            nearest=tuple(F(center(t,q),q) for t in physical(v,q))
            strict_non_nearest+=dot(rv,rv)>dot(nearest,nearest)
            all_missed=True;exponent=0
            for j in heights:
                a=tuple((v[i]+j*u[i])%q for i in range(3))
                ra=representative(a,q)
                difference=tuple(ra[i]-rv[i]-j*ru[i] for i in range(2))
                assert all(z.denominator==1 for z in difference)
                coordinates=tuple(center(z,q) for z in a)
                xx,yy,zz=coordinates
                gap=F(3,q*q)*sum(z*z for z in coordinates)-dot(ra,ra)
                assert gap==F((xx-yy)**2+xx*xx+3*zz*zz,q*q)>=0
                lift=(*ra,F(j))
                norm=dot(lift,lift)
                projected=norm-dot(lift,w)**2/dot(w,w)
                surrogate=j*j+F(3,q*q)*sum(z*z for z in coordinates)
                assert 0<=projected<=norm<=surrogate
                all_missed &= projected>radius_sq
                exponent+=3*(j*j-radius_sq)+sum(z*z for z in coordinates)
                checked+=1
            assert exponent.denominator==1
            majorant=base**int(exponent)
            assert int(all_missed)<=majorant
            misses+=all_missed;majorants+=majorant
        miss_moment+=F(misses,len(labels))**k
        majorant_moment+=(majorants/len(labels))**k
    miss_moment/=len(labels);majorant_moment/=len(labels)
    kernels=[sum((base**sum(center(v+j*u,q)**2 for j in heights)
                  for v in range(q)),F(0))/q for u in range(q)]
    prefactor=base**int(3*(sum(j*j for j in heights)-len(heights)*radius_sq))
    factored=prefactor**k*(sum((x**k for x in kernels),F(0))/q)**3
    assert miss_moment<=majorant_moment==factored
    assert strict_non_nearest>0
    print('Passed',checked,'exact nonorthogonal Gram, lift and branch projection checks.')
    print('Surjective labels and branch quotient fibers checked; diagonal-only bound refuted.')
    print('Shared-label moment factorization holds despite nonnearest representatives.')


if __name__=='__main__':
    main()
