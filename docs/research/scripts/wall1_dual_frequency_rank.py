"""Exact finite rank checks and interval discrete-Gaussian residue bounds."""
from fractions import Fraction as F
from math import comb
from itertools import product
from mpmath import iv


def rank(rows,q):
    a=[list(row) for row in rows];i=0
    for j in range(len(a[0])):
        p=next((s for s in range(i,len(a)) if a[s][j]%q),None)
        if p is None: continue
        a[i],a[p]=a[p],a[i];inv=pow(a[i][j],-1,q)
        a[i]=[v*inv%q for v in a[i]]
        for s in range(len(a)):
            if s!=i:
                c=a[s][j];a[s]=[(x-c*y)%q for x,y in zip(a[s],a[i])]
        i+=1
        if i==len(a): break
    return i


def gauss_binomial(k,t,q):
    a=b=1
    for j in range(t): a*=q**(k-j)-1;b*=q**(t-j)-1
    assert a%b==0
    return a//b


def main():
    checks=0
    for q in (2,3):
        for k,n in ((2,2),(2,3),(3,2)):
            # Nonuniform laws: no uniform-mod-q assumption in the bound.
            laws=[tuple(F(1,q) for _ in range(q)),tuple(F(j+1,q*(q+1)//2) for j in range(q))]
            for law in laws:
                masses=[F(0)]*(k+1)
                for flat in product(range(q),repeat=k*n):
                    rows=[flat[i*n:(i+1)*n] for i in range(k)]
                    weight=F(1)
                    for v in flat: weight*=law[v]
                    masses[rank(rows,q)]+=weight
                assert sum(masses)==1
                for t in range(k):
                    assert sum(masses[:t+1])<=gauss_binomial(k,t,q)*max(law)**(n*(k-t))
                    if t<=n:
                        assert sum(masses[:t+1])<=comb(k,t)*max(law)**((n-t)*(k-t))
                    checks+=1
    iv.dps=60; I=iv.mpf;q=3329;k=6;n=118
    def theta_bounds(t):
        # j=101 onward: successive term ratio at most exp(-203t).
        low=1+2*sum(iv.exp(-t*j*j) for j in range(1,101))
        high=low+2*iv.exp(-t*101**2)/(1-iv.exp(-203*t))
        return low,high
    for primal_gamma in ('1e-7','6.85e-6'):
        tau=iv.pi**2/(q*q*I(primal_gamma))
        denlo,denhi=theta_bounds(tau);numlo,numhi=theta_bounds(tau*q*q)
        M=numhi/denlo; Mlow=numlo/denhi
        deficient=gauss_binomial(k,k-1,q)*M**n
        tilted=sum((I(q)**(10*(k-t))-1)*gauss_binomial(k,t,q)*M**(n*(k-t)) for t in range(k))
        zero_lower=1-(1-Mlow**n)**k
        print('primal gamma / dual tau:',primal_gamma,tau)
        print('maximum residue atom upper:',M)
        print('rank < 6 upper (cap at one):',deficient)
        print('rank < 6 lower from a zero row:',zero_lower)
        print('E[q^(10*(6-rank))]-1 upper:',tilted)
        if primal_gamma=='1e-7': assert zero_lower>I('.999999998')
        else: assert deficient<I('3e-64') and tilted<I('5e-29')
    print('Passed exact finite weighted-rank checks:',checks)

if __name__=='__main__':main()
