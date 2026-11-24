"""Exact anisotropic anchored-pivot checks, with nontrivial anchor convolution."""
from fractions import Fraction as F
from itertools import product
from wall1_dual_rank_pivot_bound import rank


def main():
    q=3;r=3;k=n=2
    old=(F(2),F(1,2),F(1,2));free=(F(3,2),F(3,4),F(3,4))
    fs=(old,old,free);mu=(F(1),F(1,16),F(1,16))
    # Two affine extra-anchor columns, with zero free-coordinate row.
    A=((1,2),(0,-1),(0,0))
    psi={}
    for x in product(range(q),repeat=r):
        value=F(0)
        for b in product(range(q),repeat=2):
            weight=mu[b[0]]*mu[b[1]]
            for j in range(r):weight*=fs[j][(x[j]+sum(A[j][a]*b[a] for a in range(2)))%q]
            value+=weight
        psi[x]=value
    zero=psi[(0,)*r]
    assert all(x<=zero for x in psi.values())
    hyper=[sum(v for x,v in psi.items() if sum(x)%q==c) for c in range(q)]
    assert max(hyper)==hyper[0]
    eta_exact=hyper[0]/(q**(r-1)*zero)
    ratios=[sum(f)/(q*max(f)) for f in fs]
    candidates=[]
    for drop in range(r):
        val=sum(mu)**2
        for j in range(r):
            if j!=drop:val*=ratios[j]
        candidates.append(val)
    eta=min([F(1)]+candidates)
    assert eta_exact<=eta<1
    matrices=0
    for es in product(range(q),repeat=k*n):
        B=(es[:n],es[n:]);t=rank(B,q);total=F(0)
        for coeff in product(range(q),repeat=(r-1)*k):
            V=[coeff[:k],coeff[k:]]
            V.append(tuple((1-V[0][a]-V[1][a])%q for a in range(k)))
            weight=F(1)
            for i in range(n):
                y=tuple(sum(V[j][a]*B[a][i] for a in range(k))%q for j in range(r))
                weight*=psi[y]
            total+=weight
        mean=total/q**((r-1)*k)
        assert mean<=zero**n*eta_exact**t<=zero**n*eta**t
        matrices+=1
    print('Passed',matrices,'exact anisotropic anchored shared-coefficient sums.')
    print('Exact eta',eta_exact,'uniform eta bound',eta,'drop candidates',candidates)

if __name__=='__main__':main()
