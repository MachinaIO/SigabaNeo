"""Exact two-layer conditional power drift; finite checks, not BKZ evidence."""
from fractions import Fraction as F
from itertools import product
from math import gcd

POWERS=(1,2,4,12,24)

def subset_checks():
    cases=0
    for h in range(2,8):
        for state in product(range(3),repeat=h):
            a={i for i,s in enumerate(state) if s==2}
            c={i for i,s in enumerate(state) if s>=1}
            p,r=F(len(a),h),F(len(c),h)
            overlaps=[F(sum(v in a and (v+u)%h in c for v in range(h)),h)
                      for u in range(h)]
            assert sum(overlaps)/h==p*r
            assert all(x<=p for x in overlaps)
            for k in POWERS:
                assert sum(x**k for x in overlaps)/h<=p**k*r
            cases+=1
    return cases

def residue(v,q):
    return min(v%q,(-v)%q)

def graph_checks():
    cases=0
    for q in (3,5,7,11):
        for b2 in (1,2,4,9):
            old2=[residue(v,q)**2 for v in range(q)]
            a={v for v in range(q) if old2[v]>b2}
            c={v for v in range(q) if old2[v]>b2-1}
            outgoing=[]
            for u in range(q):
                # (q,0) is available, so the shortest squared norm is <=q^2.
                candidates=[(x*x+j*j,x,j) for x in range(-q,q+1)
                            for j in range(-q,q+1)
                            if (x or j) and (x-u*j)%q==0]
                s2,x,j=min(candidates)
                assert gcd((x-u*j)//q,j)==1
                # Projected W has spacing q/s; Q(v,0) has coordinate -j*v/s.
                misses={v for v in range(q) if F(residue(j*v,q)**2,s2)>b2}
                overlap={v for v in a if (v+u)%q in c}
                assert misses<=overlap
                outgoing.append(F(len(misses),q))
                cases+=1
            p,r=F(len(a),q),F(len(c),q)
            for k in POWERS:
                assert sum(x**k for x in outgoing)/q<=p**k*r
    return cases

if __name__=='__main__':
    print(f'{subset_checks()} exact nested-subset configurations passed.')
    print(f'{graph_checks()} actual shortest-winner branches passed.')
    print(f'Five powers checked: {POWERS}.')
    print(f'Conditional k=24, r<=0.28 tolerance: {(1/.28)**(1/24):.10f}.')
