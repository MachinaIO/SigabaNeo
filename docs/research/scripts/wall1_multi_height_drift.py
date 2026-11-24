"""Exact tests for a multi-height fresh-column void-power bound."""
from fractions import Fraction as F
from itertools import product
from mpmath import iv


def checks():
    checked=0
    for q in (3,5,7):
        # Each point belongs to neither hit set, zero-layer only, or both.
        for labels in product(range(3),repeat=q):
            hits0={v for v,x in enumerate(labels) if x>=1}
            hits1={v for v,x in enumerate(labels) if x==2}
            hitsets={-1:hits1,0:hits0,1:hits1}
            a={j:F(len(A),q) for j,A in hitsets.items()}
            p0=1-a[0]
            overlap=[F(sum(all((v+j*u)%q not in A for j,A in hitsets.items())
                            for v in range(q)),q) for u in range(q)]
            assert all(x<=p0 for x in overlap)
            if any(x==1 for x in a.values()):
                assert all(x==0 for x in overlap)
                continue
            odds=sum((x/(1-x) for x in a.values()),F(0))
            bound=1/(1+odds)
            assert sum(overlap)/q<=bound
            # Verify exact first and second moments of the optimized hit sum.
            ys=[sum((F((v+j*u)%q in A)/(1-a[j]) for j,A in hitsets.items()),F(0))
                for u,v in product(range(q),repeat=2)]
            assert sum(ys)/q**2==odds
            assert sum(y*y for y in ys)/q**2==odds*odds+odds
            for k in (1,2,4,24):
                assert sum(x**k for x in overlap)/q<=p0**(k-1)*bound
            checked+=1
    print('Passed',checked,'exact nested-profile multi-height power checks.')


def corridor():
    iv.dps=65;I=iv.mpf
    # Sufficient profile hypotheses, not measured or established at histories.
    P=I('.18');pstar=I('.208');T=20;L=2*T+1;k=24
    ratio=(pstar/P)**k/(pstar+L*(1-pstar))
    assert ratio<I(1)
    print('Conditional multiplier under p(sqrt(B²-400))<=.208 and P=.18:',ratio)
    print('These are unproved profile hypotheses; no global failure bound follows.')

if __name__=='__main__':checks();corridor()
