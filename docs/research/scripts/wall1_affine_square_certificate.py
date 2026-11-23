"""Degree-ten square certificate; dependent-design remainder is not bounded here."""
from fractions import Fraction as F
from itertools import product
from math import comb, factorial
from pathlib import Path
import runpy
from wall1_affine_circuit_components import correction_bound
from wall1_affine_rank_extensions import activity


def central_square(t, tilt=F(0)):
    """Exact coefficients of K_t(mu+z;mu)^2, keyed by (z degree, mu degree)."""
    def mul(a,b):
        out={}
        for (i,j),v in a.items():
            for (k,l),w in b.items():
                out[i+k,j+l]=out.get((i+k,j+l),F(0))+v*w
        return {key:v for key,v in out.items() if v}
    K={}
    falling_poly={(0,0):F(1)}
    for j in range(t+1):
        for r in range(t-j+1):
            scale=F((-1)**j,factorial(j)*factorial(r))
            for (a,b),v in falling_poly.items():
                K[a,b+r]=K.get((a,b+r),F(0))+scale*v
        if j<t:
            r=t-1-j
            scale=tilt*comb(t-1,j)*(-1)**r
            for (a,b),v in falling_poly.items():
                K[a,b+r]=K.get((a,b+r),F(0))+scale*v
        falling_poly=mul(falling_poly,{(1,0):F(1),(0,1):F(1),(0,0):F(-j)})
    result=mul(K,K)
    assert all(a+b<=2*t for a,b in result)
    return result


def partial_exp(mu,t):
    return sum((mu**j/factorial(j) for j in range(t+1)),mu*0)


def falling(x,j):
    v=1
    for i in range(j):
        v*=x-i
    return v


def coefficients(mu,t,tilt=F(0)):
    a=[(-1)**j*partial_exp(mu,t-j)/factorial(j) for j in range(t+1)]
    if tilt != 0:
        for j in range(t):
            a[j]+=tilt*comb(t-1,j)*(-mu)**(t-1-j)
    f=[mu*0 for _ in range(2*t+1)]
    majorant=[mu*0 for _ in range(2*t+1)]
    for i in range(t+1):
        for j in range(t+1):
            for ell in range(min(i,j)+1):
                mult=comb(i,ell)*comb(j,ell)*factorial(ell)
                f[i+j-ell]+=a[i]*a[j]*mult
                majorant[i+j-ell]+=abs(a[i]*a[j])*mult
    return a,f,majorant


def finite_checks():
    checks=0
    for t in range(1,6):
        central=central_square(t)
        for mu in (F(1,3),F(2),F(7,2)):
            a,f,majorant=coefficients(mu,t)
            D=partial_exp(mu,t)
            assert sum(c*mu**h for h,c in enumerate(f))==D
            assert a[0]==D
            for x in range(2*t+3):
                K=sum(c*falling(x,j) for j,c in enumerate(a))
                assert K*K==sum(c*falling(x,j) for j,c in enumerate(f))
                assert K*K==sum(c*(x-mu)**j*mu**b for (j,b),c in central.items())
                assert int(x==0) <= K*K/(D*D)
                checks+=1
    for rho in ((F(1,3),F(2,5)),(F(1,2),)*5,
                (F(1),F(1,7),F(3,4)),(F(1,100),)*6):
        mu=sum(rho)
        a,f,majorant=coefficients(mu,5)
        D=partial_exp(mu,5)
        expectation=F(0)
        factorial_moments=[F(0)]*11
        for bits in product(range(2),repeat=len(rho)):
            weight=F(1)
            for p,b in zip(rho,bits):
                weight*=p if b else 1-p
            x=sum(bits)
            K=sum(c*falling(x,j) for j,c in enumerate(a))
            expectation+=weight*K*K
            for h in range(11):
                factorial_moments[h]+=weight*falling(x,h)
        for h in range(2,11):
            assert 0 <= mu**h-factorial_moments[h] <= comb(h,2)*mu**(h-1)*max(rho)
        error=sum(majorant[h]*comb(h,2)*mu**(h-1)*max(rho) for h in range(2,11))
        assert abs(expectation-D) <= error
        checks+=1
    print(f'Passed {checks} exact square, Poisson-reference and Bernoulli-error checks.')


if __name__ == '__main__':
    finite_checks()
    s=runpy.run_path(str(Path(__file__).with_name('wall1_affine_nullity_one.py')))
    I,mu,R,iv=s['I'],s['mu'],s['R'],s['iv']
    # Any output fiber is inside this m-dimensional integer ball.
    rho_max=2*s['s']['volume'][400]*(R**2+I(400)/4)**200 / 3329**400
    a,f,majorant=coefficients(mu,5)
    baseline=1/(I('.280')*partial_exp(mu,5))
    error=(rho_max*factorial(5)**2/mu**10/I('.280')
           *sum(majorant[h]*comb(h,2)*mu**(h-1) for h in range(2,11)))
    assert baseline < I('2.274e-12') and error < I('2.575e-293')
    print('Poisson reference / rho < 2.274e-12')
    print('Independent Bernoulli correction / rho < 2.575e-293')
    central=central_square(5)
    eps=s['epsilon'];q=3329
    for cap in (8,9):
        activities={h:eps[h]+((2**h-1-h-comb(h,2))*q**(h-3)*eps[3] if h>=4 else I(0))
                    + (sum((activity(h,r,q,mu,eps) for r in range(3,h-1)),I(0))
                       if h<=cap else I(0)) for h in range(3,11)}
        transferred=I(0)
        for j in range(3,11):
            coeff=sum((I(abs(c.numerator))/c.denominator*mu**b
                       for (a,b),c in central.items() if a==j),I(0))
            transferred+=coeff*correction_bound(mu,activities,j)
        transferred*=factorial(5)**2/(I('.280')*mu**10)
        if cap == 8:
            assert transferred < I('4.859e-22')
            print('Dependent correction through component size 8 < 4.859e-22')
        else:
            assert transferred > I('8.68e-11')
            print('Size-nine transferred majorant > 8.68e-11: insufficient.')
    print('UNBOUNDED: expectation difference under the actual dependent affine law.')
