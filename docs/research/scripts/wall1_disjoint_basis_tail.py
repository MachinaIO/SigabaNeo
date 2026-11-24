"""Greedy deletion bound for disjoint full bases; auxiliary iid law only."""
from fractions import Fraction as F
from itertools import combinations, product
from math import comb
from mpmath import iv
from wall1_centered_affine_cancellation import rank
from wall1_anchored_dual_completion import theta, GAMMA_GRID


def checks():
    checked=0
    for k,n,L in ((1,6,2),(2,4,2),(2,5,2)):
        s=(L-1)*k
        for zero in (F(1,2),F(3,4)):
            failure=F(0)
            for entries in product(range(2),repeat=k*n):
                columns=[tuple(entries[j*k+i] for i in range(k)) for j in range(n)]
                bases=[set(J) for J in combinations(range(n),k)
                       if rank([columns[j] for j in J],2)==k]
                packed=any(not (a & b) for a in bases for b in bases)
                if not packed:
                    assert any(rank([columns[j] for j in range(n) if j not in S],2)<k
                               for S in combinations(range(n),s))
                    zeros=entries.count(0)
                    failure+=zero**zeros*(1-zero)**(k*n-zeros)
                checked+=1
            bound=min(F(1),comb(n,s)*(2**k-1)*max(zero,1-zero)**(n-s))
            atom=max(zero,1-zero)
            sequential=sum((F(comb(n,j))*(1-atom)**j*atom**(n-j)
                            for j in range(L*k)),F(0))
            assert failure<=bound and failure<=sequential
            states=[F(1)]+[F(0)]*(L*k)
            for _ in range(n):
                new=[F(0)]*len(states)
                new[-1]=states[-1]
                for j in range(L*k):
                    reject=atom**(k-j%k)
                    new[j]+=states[j]*reject
                    new[j+1]+=states[j]*(1-reject)
                states=new
            geometric_failure=sum(states[:-1],F(0))
            z=(1+1/atom)/2
            chernoff=z**(-(n-L*k+1))
            for c in range(1,k+1):
                chernoff*=((1-atom**c)/(1-z*atom**c))**L
            assert failure<=geometric_failure<=chernoff
    print('Passed exact deletion-witness and weighted failure checks:',checked)


def diagnostic():
    iv.dps=65;q=3329;n=118;k=14
    for L in (2,3):
        s=(L-1)*k
        for gamma in GAMMA_GRID:
            tau=iv.pi**2/(q*q*iv.mpf(gamma))
            atom=theta(q*q*tau)/theta(tau)
            raw=iv.mpf(comb(n,s))*((q**k-1)//(q-1))*atom**(n-s)
            sequential=sum((iv.mpf(comb(n,j))*(1-atom)**j*atom**(n-j)
                            for j in range(L*k)),iv.mpf(0))
            print('L,gamma,deletion_log10,sequential_log10',L,gamma,
                  iv.log10(raw),iv.log10(sequential))


if __name__=='__main__':
    checks()
    diagnostic()
