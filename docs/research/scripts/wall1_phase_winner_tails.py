"""Exact phase bounds for actual shortest-winner upper tails.

Finite rational examples only; no production probability estimate.
For a kernel of order q, q equally spaced parallel phases imply that
an open winning arc longer than k spacings excludes at least k aliases.
Thus e_j<c^2-k^2*s^2/(4*q^2), gcd(j,q)=1, excludes k aliases from
{actual shortest norm >= c}. Strict inequalities match the >= tail.
Combine this bound with the height-one bound by minimum, never product.
"""
from fractions import Fraction as F
from itertools import product
from math import gcd
from wall1_horizontal_selected_convolution import (
    winner, rectangular_winner, centered, rootfloor,
)


def phase_bound(q,s2,d2,u,c2):
    excluded=0
    for j in range(1,rootfloor(c2)+1):
        if j*j>=c2 or gcd(j,q)!=1:
            continue
        e=d2*centered(j*u,q)**2+j*j
        for k in range(1,q+1):
            if e<c2-F(k*k,4*q*q)*s2:
                excluded=max(excluded,k)
    return F(q-excluded,q)


def skew_incoming(q,a):
    """Complete nearest representatives for the old skew lattice modulo qK.

    Centered coefficients have norm <=(16/25)*a^2*q^2. The Gram floor
    (18/25)*a^2 implies every nearest has x^2+y^2<q^2 (indeed <=8q^2/9).
    Thus [-q,q]^2 includes all improving/tied candidates.
    """
    nearest={}
    for x,y in product(range(-q,q+1),repeat=2):
        value=a*a*(F(x*x+y*y)+F(14,25)*x*y)
        mark=(x%q,y%q)
        if mark not in nearest or value<nearest[mark]:
            nearest[mark]=value
    assert len(nearest)==q*q
    return nearest


def main():
    fixtures=[]
    for q,a in product((3,5,7),(F(1,4),F(1,2),F(1))):
        fixtures.append(('skew',q,a,None))
    for q,a,t in product((7,11),(F(1,4),F(1,2)),(F(1),F(2))):
        fixtures.append(('rectangle',q,a,t))
    cases=fiber_checks=branches=phase_better=height_better=0
    examples=[]
    multheight_gain=projected_gain=raw_worse=0
    radial_checks=0
    radial_examples=[]
    for kind,q,a,t in fixtures:
        s2=(q*a)**2
        if kind=='skew':
            d2=(a*F(24,25))**2
            norms=[[winner(q,a,u1,u2)[0] for u1 in range(q)] for u2 in range(q)]
            old=skew_incoming(q,a)
        else:
            d2=t*t
            norms=[[rectangular_winner(q,a,t,u1,u2)[0]
                    for u1 in range(q)] for u2 in range(q)]
            old={(u1,u2):a*a*centered(u1,q)**2+t*t*centered(u2,q)**2
                 for u1,u2 in product(range(q),repeat=2)}
        branches+=q*q
        assert all(norms[u2][u1]<=old[u1,u2]+1
                   for u1,u2 in product(range(q),repeat=2))
        cutoffs=sorted(c for c in {F(1),F(2),F(4),s2/4,s2/2,3*s2/4,s2}
                       if 0<c<=s2)
        previous=None
        for c2 in cutoffs:
            cases+=1
            bounds=[]
            actuals=[]
            for u2 in range(q):
                actual=F(sum(v>=c2 for v in norms[u2]),q)
                bound=phase_bound(q,s2,d2,u2,c2)
                assert actual<=bound
                actuals.append(actual)
                bounds.append(bound)
                fiber_checks+=1
            actual=sum(actuals,F(0))/q
            # Exact shared-mark orbit formula, using independently computed
            # old nearest distances rather than enumerated graph winners.
            for u1,u2 in product(range(q),repeat=2):
                orbit_tail=all(old[(j*u1)%q,(j*u2)%q]+j*j>=c2
                               for j in range(1,rootfloor(c2)+1) if j*j<c2)
                assert orbit_tail==(norms[u2][u1]>=c2)
            phase=sum(bounds,F(0))/q
            height=F(sum(v+1>=c2 for v in old.values()),q*q)
            projected=[d2*centered(v,q)**2 for v in range(q)]
            raw=list(old.values())
            def radial_exclusions(values,j):
                return sum((F(sum(value<c2-j*j-F(k*k,4*q*q)*s2
                                  for value in values),len(values))
                            for k in range(1,q+1)),F(0))
            m1_average=radial_exclusions(projected,1)
            projected_one=1-m1_average/q
            raw_phase=1-radial_exclusions(raw,1)/q
            assert actual<=phase<=projected_one<=raw_phase
            assert height<=raw_phase
            for j in range(1,rootfloor(c2)+1):
                if j*j>=c2 or gcd(j,q)!=1:
                    continue
                # For fixed j the true strict threshold indicators are nested
                # in k, so their sum equals the maximum qualifying k.
                direct=[]
                for u in range(q):
                    e=d2*centered(j*u,q)**2+j*j
                    direct.append(max([0]+[k for k in range(1,q+1)
                                          if e<c2-F(k*k,4*q*q)*s2]))
                mean=F(sum(direct),q)
                assert mean==radial_exclusions(projected,j)<=m1_average
                radial_checks+=1
            multheight_gain+=phase<projected_one
            projected_gain+=projected_one<height
            raw_worse+=raw_phase>height
            if phase<projected_one or projected_one<height:
                radial_examples.append((kind,q,str(a),str(t),str(c2),str(actual),
                                        str(phase),str(projected_one),str(height),str(raw_phase)))
            combined=min(phase,height)
            assert actual<=combined<=phase and combined<=height
            # All four unconditional tails/bounds must be nonincreasing.
            current=(actual,phase,height,combined)
            if previous is not None:
                assert all(now<=before for now,before in zip(current,previous))
            previous=current
            phase_better+=phase<height
            height_better+=height<phase
            if phase<height:
                examples.append((kind,q,str(a),str(t),str(c2),
                                 str(actual),str(phase),str(height)))
    print('Lattice configurations:',len(fixtures),'actual winner branches:',branches)
    print('Cutoff cases:',cases,'conditional fiber checks:',fiber_checks)
    print('Exact shared-mark orbit formula matches every branch at every cutoff.')
    print('Phase strictly improves height-one tail:',phase_better)
    print('Height-one strictly improves phase tail:',height_better)
    print('Examples (kind,q,a,T,c2,actual,phase,height):',examples[:12])
    print('Fixed-height radial equalities checked:',radial_checks)
    print('Multiheight phase gain over projected height-one:',multheight_gain)
    print('Projected marginal gain over old height-one:',projected_gain)
    print('Raw radial phase bound strictly worse than old height-one:',raw_worse)
    print('Radial examples (kind,q,a,T,c2,actual,phase,projected1,old1,rawphase):',radial_examples[:12])
    print('All exact >= tail, radial relaxation, minimum-combination, and monotonicity checks passed.')


if __name__=='__main__':
    main()
