"""Sharp integer second-moment void bound and exact finite certificates."""
from fractions import Fraction as F
from itertools import product


def integer_void_upper(mass_upper, mean_lower, factorial_upper):
    if mean_lower<=0:
        return mass_upper,1
    r=factorial_upper/mean_lower
    k=max(1,-(-r.numerator//r.denominator))
    return mass_upper-2*mean_lower/(k+1)+factorial_upper/(k*(k+1)),k


def main():
    checks=0
    for counts in product(range(3),repeat=6):
        if not sum(counts):
            continue
        denominator=sum(counts)+1  # non-unit mass also checked
        m0=F(sum(counts),denominator)
        m1=F(sum(i*n for i,n in enumerate(counts)),denominator)
        m2=F(sum(i*(i-1)*n for i,n in enumerate(counts)),denominator)
        bound,k=integer_void_upper(m0,m1,m2)
        assert F(counts[0],denominator)<=bound<=m0
        for j in range(1,8):
            assert bound<=m0-2*m1/(j+1)+m2/(j*(j+1))
            for z in range(9):
                assert F((z-j)*(z-j-1),j*(j+1))>=int(z==0)
        if m1:
            pk=(k*m1-m2)/k
            pk1=(m2-(k-1)*m1)/(k+1)
            assert min(bound,pk,pk1)>=0
            assert bound+pk+pk1==m0
            assert k*pk+(k+1)*pk1==m1
            assert k*(k-1)*pk+k*(k+1)*pk1==m2
            cs=m0-m1*m1/(m1+m2)
            r=m2/m1
            gain=m1*(k-r)*(r-k+1)/(k*(k+1)*(r+1))
            assert cs-bound==gain>=0
            nu=m1/m0
            if nu>1:
                assert gain<=m0/(4*nu*(nu-1))
        checks+=1
    fixture,k=integer_void_upper(F(72,125),F(54,125),F(76,625))
    assert k==1 and fixture==F(128,625)
    nu=10**16
    max_gain=F(1,4*nu*(nu-1))
    assert max_gain<F('2.500000000000001e-33')
    print('Exact distribution/optimality checks:',checks)
    print('Fixture exact void:',fixture,'k:',k)
    print('Maximum integer correction for mean >=1e16, mass <=1:',float(max_gain))
    print('Production selected collision bound remains unproved.')


if __name__=='__main__':
    main()
