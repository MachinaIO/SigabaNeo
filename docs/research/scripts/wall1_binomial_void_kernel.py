"""Exact binomial orthogonal-polynomial void certificates and transfer identity.

The large-L values are reference binomial benchmarks only. Their geometry
and their applicability to actual selected incidence are not established.
"""
from fractions import Fraction as F
from math import comb, factorial


def choose(n,k):
    """Polynomial binomial coefficient, valid also for negative integer n."""
    if k<0:
        return F(0)
    result=F(1)
    for i in range(k):
        result*=F(n-i,i+1)
    return result


def falling(z,j):
    result=1
    for k in range(j):
        result*=z-k
    return result


def denominator(L,p,t):
    odds=p/(1-p)
    term=F(1)
    total=term
    for j in range(1,t+1):
        term*=F(L-j+1,j)*odds
        total+=term
    return total


def kernel(L,p,t,z):
    odds=p/(1-p)
    numerator=F(0)
    for j in range(t+1):
        kraw=sum((choose(z,a)*choose(L-z,j-a)*(-1/odds)**a
                  for a in range(j+1)),F(0))
        numerator+=odds**j*kraw
    return numerator/denominator(L,p,t)


def coefficients(L,p,t):
    values=[kernel(L,p,t,z)**2 for z in range(2*t+1)]
    result=[]
    for j in range(2*t+1):
        result.append(values[0]/factorial(j))
        values=[b-a for a,b in zip(values,values[1:])]
    return tuple(result)


def polynomial(coeff,z):
    return sum((c*falling(z,j) for j,c in enumerate(coeff)),F(0))


def main():
    kernel_cases=point_checks=transfer_checks=0
    for L in range(2,11):
        for p in (F(1,5),F(1,2),F(4,5)):
            binomial=[F(comb(L,z))*p**z*(1-p)**(L-z) for z in range(L+1)]
            for t in range(min(4,L)+1):
                D=denominator(L,p,t)
                coeff=coefficients(L,p,t)
                assert kernel(L,p,t,0)==1
                assert coeff[0]==1
                for z in range(max(L,2*t)+3):
                    assert polynomial(coeff,z)==kernel(L,p,t,z)**2
                    point_checks+=1
                expectation=sum((weight*polynomial(coeff,z)
                                 for z,weight in enumerate(binomial)),F(0))
                moment_expectation=sum((c*falling(L,j)*p**j
                                        for j,c in enumerate(coeff)),F(0))
                assert expectation==moment_expectation==1/D
                assert binomial[0]<=1/D
                kernel_cases+=1
                # Arbitrary rational laws as well as the reference law,
                # combined with deterministic threshold selection events.
                raw=[F(1+(z*z+2*z)%7) for z in range(L+1)]
                arbitrary=[v/sum(raw) for v in raw]
                for law in (binomial,arbitrary):
                    for cutoff in sorted({-1,0,L//2,L}):
                        selected=[weight if z<=cutoff else F(0)
                                  for z,weight in enumerate(law)]
                        mass=sum(selected,F(0))
                        moments=[sum((weight*falling(z,j)
                                      for z,weight in enumerate(selected)),F(0))
                                 for j in range(2*t+1)]
                        lhs=sum((weight*polynomial(coeff,z)
                                 for z,weight in enumerate(selected)),F(0))
                        expansion=sum((c*moment for c,moment in zip(coeff,moments)),F(0))
                        transfer=mass/D+sum((coeff[j]*(moments[j]-mass*falling(L,j)*p**j)
                                             for j in range(1,2*t+1)),F(0))
                        assert lhs==expansion==transfer
                        assert selected[0]<=lhs
                        transfer_checks+=1
    print('Small exact kernel cases:',kernel_cases,'polynomial point checks:',point_checks)
    print('Selected factorial-moment transfer checks:',transfer_checks)
    K=3329**2-1
    L=58*K
    target=F(1951,10**15)  # 1.951e-12, strict target
    print('Reference L=',L,'K=',K,'strict target=',target)
    for J in (1,2,4,8,16):
        p=F(J,K)
        first=next((t for t in range(25) if 1/denominator(L,p,t)<target),None)
        if first is None:
            print('J',J,'no degree t<=24; upper at24 display',float(1/denominator(L,p,24)))
        else:
            cap=1/denominator(L,p,first)
            assert cap<target
            if first:
                assert 1/denominator(L,p,first-1)>=target
            coeff=coefficients(L,p,first)
            sensitivity=sum((abs(coeff[j])*falling(L,j)*p**j
                             for j in range(1,2*first+1)),F(0))
            relative_tolerance=(target-cap)/sensitivity
            assert relative_tolerance>0
            assert cap+relative_tolerance*sensitivity==target
            print('J',J,'minimum t',first,'squared polynomial degree',2*first,
                  'reference bound display',float(cap),
                  'common relative moment tolerance display',float(relative_tolerance))
    # A geometric volume surrogate, not a lattice point-count estimate.
    # If all heights use one radius, granting J heights shrinks that radius.
    c2=F(61,2)**2
    for J in range(2,31):
        volume_gain_squared=J*J*((c2-J*J)/(c2-1))**505
        assert volume_gain_squared<1
    print('Common-radius volume surrogate at c=30.5,d=505: all J=2..30 lose versus J=1.')
    print('All exact polynomial, binomial optimal-kernel normalization, and transfer checks passed.')
    print('Large-case results are binomial references, not geometric production estimates.')


if __name__=='__main__':
    main()
