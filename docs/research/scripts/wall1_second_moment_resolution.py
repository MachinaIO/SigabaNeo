"""Resolution diagnostic for the selected scalar-collision moment certificate.

Independent nonzero labels are a comparison model, NOT the selected BKZ law.
All assertions use exact rational arithmetic. No production failure bound.
"""
from fractions import Fraction as F
from itertools import product


def moments(q, h, length):
    k=h-1
    return (F(length), length+F(length*(length-1),k),
            length+F((q-1)*length*(length-1),k))


def miss_certificate(q,h,length,r=F(0)):
    k=h-1
    n,j,c=moments(q,h,length)
    d=r*(q-1)*j+(1-r)*c
    return F(k,h)*(1-F(q-1,k)*n*n/d)


def main():
    checks=0
    for q,dim in ((3,1),(3,2),(5,1)):
        labels=[v for v in product(range(q),repeat=dim) if any(v)]
        h=q**dim
        for length in range(1,5):
            sj=sc=uncovered=0
            for sample in product(labels,repeat=length):
                sj+=sum(x==y for x,y in product(sample,repeat=2))
                sc+=sum(y==tuple(t*a%q for a in x)
                        for x,y,t in product(sample,sample,range(1,q)))
                covered={tuple(t*a%q for a in x) for x in sample for t in range(1,q)}
                uncovered+=len(labels)-len(covered)
            count=len(labels)**length
            n,j,c=moments(q,h,length)
            assert (F(sj,count),F(sc,count))==(j,c)
            actual=F(uncovered,count*h)
            assert actual==F(h-1,h)*(1-F(q-1,h-1))**length
            for r in (F(0),F(1,4),F(1)):
                bound=miss_certificate(q,h,length,r)
                assert actual<=bound
                a=1+r*(q-2)
                assert bound==F(h-1,h)*(1-F(length)/(length-1+F((h-1)*a,q-1)))
                checks+=1
    q=3329
    k=q**388-1  # a large quotient fixture, not an asserted history distribution
    for mu in (58,119):
        bound=miss_certificate(q,k+1,mu*k)
        assert F(2,10**6)<bound<F(6,10**6)
        # Finite-K exact lower and upper enclosure around the limiting formula.
        limit=F(1,1+(q-1)*mu)
        assert 0<limit-bound<F(2,k)
        print('mu=',mu,'best r=0 moment miss bound in (2e-6,6e-6); limit=',limit)
    epsilon=F(1951,10**15)
    # Exact solve at finite K, including the zero-mark prefactor.
    a=F(1,q-1)-F(1,k)
    required_mu=a*(F(k,k+1)/epsilon-1)
    assert required_mu>150_000_000
    print('For comparison miss <=1.951e-12, this certificate requires mu >150000000.')
    print('Exact finite-model moment and miss checks:',checks)
    print('This diagnoses the second-moment certificate, not the true BKZ law or failure.')


if __name__=='__main__':
    main()
