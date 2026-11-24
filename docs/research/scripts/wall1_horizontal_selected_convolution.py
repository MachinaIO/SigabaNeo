"""Exact selected-horizontal convolution checks on rational planar lattices.

Toy radii and fixed finite examples only: no production-history claim.
An additional diagonal family uses K=diag(a,T) Z^2, q=7,11, and
a<T. Its winner search uses |x|<=q, |y|<=floor(qa/T), |j|<=floor(qa).
K has basis a(1,0), a(7/25,24/25); M=qK. The fixed lexicographic old
shortest vector is w0=(-q,0), length s=q*a. The Gram eigenvalue floor
is (18/25)*a^2. Every graph winner has norm<=s, hence
x^2+y^2<=25*q^2/18 and |j|<=floor(s); |x|,|y|<=2q is complete.
Only congruent x,y are enumerated. Ties use (norm^2,x,y,j).

After forcing projection off w0, transverse spacing is d=a*24/25.
Projected marked graph distances at squared radius b2 need only heights
|j|<=floor(sqrt(b2)); the nearest horizontal lift at each height is the
centered residue. This counts every projected hit, not only J={0,1}.
The exact full-fiber selection probability rho records which aliases
actually select w0; it is not assumed independent of the projected mark.
"""
from fractions import Fraction as F
from math import isqrt, gcd


def rootfloor(x):
    return isqrt(x.numerator//x.denominator)


def centered(x,q):
    return (x+q//2)%q-q//2


def winner(q,a,u1,u2):
    s2=(q*a)**2
    best=(s2,-q,0,0)
    for j in range(-rootfloor(s2),rootfloor(s2)+1):
        startx=-2*q+(j*u1+2*q)%q
        starty=-2*q+(j*u2+2*q)%q
        for x in range(startx,2*q+1,q):
            for y in range(starty,2*q+1,q):
                if not (x or y or j):
                    continue
                norm=a*a*(F(x*x+y*y)+F(14,25)*x*y)+j*j
                key=(norm,x,y,j)
                if key<best:
                    best=key
    return best


def potential(p,delta):
    return min(F(1),p/delta)


def phase_survival(q,s2,d2,u):
    """At least k excluded aliases from a strict open winning arc.

    For gcd(j,q)=1 the q parallel phases are equally spaced modulo the
    horizontal winner length. The displayed strict inequality makes the
    open winning arc longer than k phase spacings. Such an arc contains
    at least k phases, including for k=q where all aliases are excluded.
    """
    excluded=0
    for j in range(1,rootfloor(s2)+1):
        if j*j>=s2 or gcd(j,q)!=1:
            continue
        energy=d2*centered(j*u,q)**2+j*j
        for k in range(1,q+1):
            if energy<s2*(1-F(k*k,4*q*q)):
                excluded=max(excluded,k)
    return F(q-excluded,q)


def rectangular_winner(q,a,transverse,u1,u2):
    """Complete box from each nonnegative diagonal summand <= (qa)^2."""
    s2=(q*a)**2
    ymax=rootfloor(s2/(transverse*transverse))
    best=(s2,-q,0,0)
    for j in range(-rootfloor(s2),rootfloor(s2)+1):
        for x in range(-q+(j*u1+q)%q,q+1,q):
            for y in range(-ymax+(j*u2+ymax)%q,ymax+1,q):
                if not (x or y or j):
                    continue
                best=min(best,(a*a*x*x+transverse*transverse*y*y+j*j,x,y,j))
    return best


def rectangular_checks():
    delta=F(7,25)
    branches=selected=radius_cases=positive_branches=0
    strict_weighted=strict_support=strict_phase=0
    phase_examples=[]
    examples=[]
    for q in (7,11):
        for a in (F(1,4),F(1,2)):
            for transverse in (F(1),F(2)):
                s2=(q*a)**2
                d2=transverse*transverse
                event=[[rectangular_winner(q,a,transverse,u1,u2)[1:]==(-q,0,0)
                        for u1 in range(q)] for u2 in range(q)]
                branches+=q*q
                selected+=sum(map(sum,event))
                rho=[F(sum(row),q) for row in event]
                probability=sum(rho,F(0))/q
                allowed=[]
                phases=[]
                for u2 in range(q):
                    forbidden=any(d2*centered(j*u2,q)**2+j*j<F(3,4)*s2
                                  for j in range(1,rootfloor(F(3,4)*s2)+1))
                    if forbidden:
                        assert not any(event[u2])
                    allowed.append(not forbidden)
                    phase=phase_survival(q,s2,d2,u2)
                    assert rho[u2]<=phase<=int(not forbidden)
                    phases.append(phase)
                for b2 in sorted({F(4),d2*(q//2-1)**2}):
                    radius_cases+=1
                    miss0=[d2*centered(v,q)**2>b2 for v in range(q)]
                    miss1=[d2*centered(v,q)**2>b2-1 for v in range(q)]
                    p0,p1=F(sum(miss0),q),F(sum(miss1),q)
                    convolution=[]
                    actual=[]
                    for u2 in range(q):
                        c=F(sum(miss0[v] and miss1[(v+u2)%q]
                                for v in range(q)),q)
                        convolution.append(c)
                        p=F(sum(not any(d2*centered(v+j*u2,q)**2+j*j<=b2
                                        for j in range(-rootfloor(b2),rootfloor(b2)+1))
                                for v in range(q)),q)
                        actual.append(p)
                        assert p<=c<=p0
                        if p>0:
                            positive_branches+=sum(event[u2])
                    assert sum(convolution,F(0))/q==p0*p1
                    lhs=sum((r*potential(p,delta) for r,p in zip(rho,actual)),F(0))/q
                    weighted=sum((r*potential(c,delta) for r,c in zip(rho,convolution)),F(0))/q
                    coarse=min(probability,p0*p1/delta,probability*potential(p0,delta))
                    assert lhs<=weighted<=coarse
                    unrestricted=sum((potential(c,delta) for c in convolution),F(0))/q
                    support_cap=sum((ok*potential(c,delta)
                                     for ok,c in zip(allowed,convolution)),F(0))/q
                    phase_cap=sum((phase*potential(c,delta)
                                   for phase,c in zip(phases,convolution)),F(0))/q
                    assert weighted<=phase_cap<=support_cap<=unrestricted
                    if phase_cap<support_cap:
                        strict_phase+=1
                        phase_examples.append((q,str(a),str(transverse),str(b2),
                                               str(weighted),str(phase_cap),str(support_cap)))
                    strict_weighted+=weighted<coarse
                    strict_support+=support_cap<unrestricted
                    if weighted<coarse or support_cap<unrestricted:
                        examples.append((q,str(a),str(transverse),str(b2),str(probability),
                                         str(lhs),str(weighted),str(coarse),
                                         str(support_cap),str(unrestricted)))
    assert positive_branches>0 and strict_weighted>0 and strict_support>0
    print('Rectangular winner branches:',branches,'selected horizontal:',selected,
          'radius cases:',radius_cases)
    print('Rectangular selected branch/radius pairs with positive actual void:',positive_branches)
    print('Rectangular strict weighted/coarse improvements:',strict_weighted,
          'strict support/unrestricted improvements:',strict_support)
    print('Rectangular examples (q,a,T,b2,PrE,actual,weighted,coarse,support,unrestricted):',examples[:10])
    print('Rectangular strict phase/binary improvements:',strict_phase,
          'examples (q,a,T,b2,weighted,phase,binary):',phase_examples[:8])


def main():
    delta=F(7,25)
    configurations=branches=radius_cases=selected_branches=0
    support_exclusions=support_nontrivial=0
    strict_weighted=actual_strict=0
    examples=[]
    strict_phase=0
    phase_examples=[]
    for q in (3,5,7):
        for a in (F(1,4),F(1,2),F(1)):
            configurations+=1
            s2=(q*a)**2
            d2=(a*F(24,25))**2
            # Each row is one quotient fiber u2, with q aliases u1.
            event=[[winner(q,a,u1,u2)[1:]==(-q,0,0)
                    for u1 in range(q)] for u2 in range(q)]
            branches+=q*q
            selected_branches+=sum(map(sum,event))
            rho=[F(sum(row),q) for row in event]
            probability=sum(rho,F(0))/q
            allowed=[]
            phases=[]
            for u2 in range(q):
                # A short projected graph vector can be lifted and rounded
                # along w0; parallel norm^2<=s2/4. A strict projected
                # norm^2<3*s2/4 would produce a strictly shorter graph vector.
                support_hit=any(d2*centered(j*u2,q)**2+j*j<F(3,4)*s2
                                for j in range(1,rootfloor(F(3,4)*s2)+1))
                if support_hit:
                    assert not any(event[u2])
                    support_exclusions+=q
                    support_nontrivial+=1
                phase=phase_survival(q,s2,d2,u2)
                assert rho[u2]<=phase<=int(not support_hit)
                allowed.append(not support_hit)
                phases.append(phase)
            for b2 in sorted({F(1),F(2),s2+F(1,4)}):
                if b2<1:
                    continue
                radius_cases+=1
                miss0=[d2*centered(v,q)**2>b2 for v in range(q)]
                miss1=[d2*centered(v,q)**2>b2-1 for v in range(q)]
                p0=F(sum(miss0),q)
                p1=F(sum(miss1),q)
                convolution=[]
                actual=[]
                for u2 in range(q):
                    c=F(sum(miss0[v] and miss1[(v+u2)%q]
                            for v in range(q)),q)
                    convolution.append(c)
                    missed=0
                    for v in range(q):
                        hit=any(d2*centered(v+j*u2,q)**2+j*j<=b2
                                for j in range(-rootfloor(b2),rootfloor(b2)+1))
                        missed+=not hit
                    p=F(missed,q)
                    actual.append(p)
                    assert p<=c<=p0
                assert sum(convolution,F(0))/q==p0*p1
                lhs=sum((r*potential(p,delta) for r,p in zip(rho,actual)),F(0))/q
                weighted=sum((r*potential(c,delta) for r,c in zip(rho,convolution)),F(0))/q
                coarse=min(probability,p0*p1/delta,
                           probability*potential(p0,delta))
                assert lhs<=weighted<=coarse
                phase_cap=sum((phase*potential(c,delta)
                               for phase,c in zip(phases,convolution)),F(0))/q
                support_cap=sum((ok*potential(c,delta)
                                 for ok,c in zip(allowed,convolution)),F(0))/q
                assert weighted<=phase_cap<=support_cap
                if phase_cap<support_cap:
                    strict_phase+=1
                    phase_examples.append((q,str(a),str(b2),str(weighted),str(phase_cap),str(support_cap)))
                if weighted<coarse:
                    strict_weighted+=1
                    examples.append((q,str(a),str(b2),str(probability),
                                     str(lhs),str(weighted),str(coarse)))
                actual_strict+=lhs<weighted
    print('Lattice configurations:',configurations,'actual winner branches:',branches,
          'selected horizontal branches:',selected_branches)
    print('Radius cases:',radius_cases)
    print('Strict support criterion excludes quotient fibers:',support_nontrivial,
          'full aliases:',support_exclusions)
    print('Selection-weighted clipped convolution strictly improves coarse bound:',strict_weighted)
    print('Actual projected void strictly improves two-height witness bound:',actual_strict)
    print('Strict examples (q,a,b2,PrE,actual,weighted,coarse):',examples[:8])
    print('Planar strict phase/binary improvements:',strict_phase,
          'examples (q,a,b2,weighted,phase,binary):',phase_examples[:8])
    rectangular_checks()
    print('All exact winner, convolution, capped-selection, and support checks passed.')


if __name__=='__main__':
    main()
