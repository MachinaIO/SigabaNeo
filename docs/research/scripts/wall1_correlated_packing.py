"""Exact dependent-column regressions for conditional-atom base packing."""
from fractions import Fraction as F
from math import factorial
from wall1_matroid_packing import packing_bound


def parity_failure(n,rho):
    """Two independent binary rows, each tilted by its whole-row parity.

    Row probability is 2^-n*(1+rho*(-1)^parity). Columns are dependent.
    Conditional scalar atom maximum is (1+rho)/2, even fixing all others.
    """
    total=bad=F(0)
    for a in range(n+1):
        for b in range(n-a+1):
            for c in range(n-a-b+1):
                z=n-a-b-c
                multiplicity=factorial(n)//(factorial(a)*factorial(b)*factorial(c)*factorial(z))
                mass=F(multiplicity,4**n)*(1+rho*(-1)**(a+c))*(1+rho*(-1)**(b+c))
                total+=mass
                nonzero=a+b+c
                # Two disjoint bases in F2^2 need four nonzero columns and
                # at least two outside every nonzero one-dimensional flat.
                if nonzero<4 or nonzero-max(a,b,c)<2:
                    bad+=mass
    assert total==1
    return bad


def main():
    checked=0
    for rho in (F(1,5),F(1,2)):
        atom=(1+rho)/2
        for n in (4,6,8,12,20):
            exact=parity_failure(n,rho)
            bound=packing_bound(n,2,2,atom)
            assert exact<=bound
            if n==20 and rho==F(1,5):
                assert bound<1
                print('Nontrivial exact correlated-law check:',exact,'<=',bound)
            checked+=1
    print(f'Passed {checked} exact correlated-column packing checks.')
    print('These are parity-law tests, not production Gaussian or selected-history estimates.')


if __name__=='__main__':
    main()
