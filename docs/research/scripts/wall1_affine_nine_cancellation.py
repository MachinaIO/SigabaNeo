"""Tilted square removes the unsuppressed nine-input term; ten-input term remains."""
from fractions import Fraction as F
from itertools import product
from math import comb, factorial
from pathlib import Path
import runpy
from wall1_affine_square_certificate import central_square, coefficients, partial_exp, falling
from wall1_affine_circuit_components import correction_bound
from wall1_affine_rank_extensions import activity


def finite_checks():
    central=central_square(5,F(1,16))
    assert central[10,0]==F(1,14400)
    assert central[9,0]==-45*central[10,0]
    assert all(b==0 for a,b in central if a>=9)
    checks=0
    for mu in (F(1,3),F(2),F(7,2),F(715)):
        a,f,_=coefficients(mu,5,F(1,16))
        D=partial_exp(mu,5)
        assert a[0]==D+mu**4/16
        assert sum(c*mu**h for h,c in enumerate(f))==D+F(7,32)*mu**4
        for x in range(13):
            H=sum(c*falling(x,j) for j,c in enumerate(a))
            assert H*H==sum(c*(x-mu)**j*mu**b for (j,b),c in central.items())
            assert int(x==0)<=H*H/a[0]**2
            checks+=1
    ys=list(product(range(3),repeat=2))
    laws=[tuple((a+b*y[0]+c*y[1]) % 3 for y in ys) for a,b,c in product(range(3),repeat=3)]
    for config in range(32):
        fibers=[{i % 3,(i+1) % 3} if config >> (i % 5) & 1 else {i % 3} for i in range(9)]
        rho=[F(len(b),3) for b in fibers]
        values=[tuple(F(int(v in b))-p for v,b,p in zip(law,fibers,rho)) for law in laws]
        W9=sum(prod(v) for v in values)/len(values)
        mixed=[sum(prod(v[:i])*v[i]**2*prod(v[i+1:]) for v in values)/len(values)
               for i in range(9)]
        W8=[sum(prod(v[:i])*prod(v[i+1:]) for v in values)/len(values) for i in range(9)]
        lhs=-45*W9+5*sum(mixed)
        rhs=-10*sum(rho)*W9+5*sum(rho[i]*(1-rho[i])*W8[i] for i in range(9))
        assert lhs==rhs
        checks+=1
    print(f'Passed {checks} exact tilted-square and nine-input cancellation checks.')


def prod(values):
    out=F(1)
    for v in values:
        out*=v
    return out


if __name__ == '__main__':
    finite_checks()
    s=runpy.run_path(str(Path(__file__).with_name('wall1_affine_nullity_one.py')))
    I,mu,R,q=s['I'],s['mu'],s['R'],s['q']
    rho_max=2*s['s']['volume'][400]*(R**2+I(100))**200 / q**400
    tilt=I(1)/16
    a,f,majorant=coefficients(mu,5,tilt)
    reference=(partial_exp(mu,5)+I(7)/32*mu**4)*factorial(5)**2/(I('.280')*mu**10)
    independent_error=(rho_max*factorial(5)**2/(I('.280')*mu**10)
                       *sum(majorant[h]*comb(h,2)*mu**(h-1) for h in range(2,11)))
    eps=s['epsilon']
    def activities(cap):
        return {h:eps[h]+((2**h-1-h-comb(h,2))*q**(h-3)*eps[3] if h>=4 else I(0))
                +(sum((activity(h,r,q,mu,eps) for r in range(3,h-1)),I(0)) if h<=cap else I(0))
                for h in range(3,11)}
    central=central_square(5,F(1,16))
    small=I(0)
    for j in range(3,11):
        coefficient=sum((I(abs(c.numerator))/c.denominator*mu**b
                         for (degree,b),c in central.items() if degree==j),I(0))
        small+=coefficient*correction_bound(mu,activities(8),j)
    small*=factorial(5)**2/(I('.280')*mu**10)
    B8=correction_bound(mu,activities(8),8)
    B9=correction_bound(mu,activities(9),9)
    nine=(90*rho_max*B9+45*mu*B8)/(I('.280')*mu**10)
    assert reference < I('2.390e-12')
    assert independent_error < I('2.597e-293')
    assert small < I('4.950e-22')
    assert nine < I('3.210e-22')
    assert reference+independent_error+small+nine < I('2.391e-12')
    print('Reference < 2.390e-12; independent Bernoulli error < 2.597e-293')
    print('Small components < 4.950e-22; all nine-input supports < 3.210e-22')
    print('UNBOUNDED: connected ten-input component of rank >=3, nullity >=2; later histories.')
