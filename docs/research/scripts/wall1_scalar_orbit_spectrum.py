"""Certified sign-quotient scalar spectra and exhaustive small-group checks.

Uses outward interval trigonometry at 40 decimal digits, then exact dyadic
endpoint arithmetic. This is a finite operator calculation, not a production
probability estimate or a selected-history distribution assertion.
"""
from fractions import Fraction as F
from time import perf_counter
import mpmath as mp

mp.iv.dps=40
SCALE=10**8


def exact_endpoint(t):
    sign,man,exponent,_=t
    result=F((-1 if sign else 1)*man)
    return result*2**exponent if exponent>=0 else result/F(2**(-exponent))


def quotient_logs(q,g):
    n=(q-1)//2
    representatives=[]
    x=1
    for _ in range(n):
        representatives.append(min(x,q-x))
        x=x*g%q
    assert len(set(representatives))==n
    assert set(representatives)==set(range(1,n+1))
    assert min(x,q-x)==1
    return {v:i for i,v in enumerate(representatives)}


def spectral_caps(q,g,js):
    logs=quotient_logs(q,g)
    n=(q-1)//2
    roots=[(mp.iv.cos(2*mp.iv.pi*t/n),mp.iv.sin(2*mp.iv.pi*t/n))
           for t in range(n)]
    result={}
    for size in js:
        exponents=[logs[min(j,q-j)] for j in range(1,size+1)]
        scores=[]
        lowers=[]
        for k in range(1,n):
            real=mp.iv.mpf(0)
            imag=mp.iv.mpf(0)
            for e in exponents:
                c,s=roots[k*e%n]
                real+=c
                imag+=s
            # Interval exponentiation squares correctly even across zero.
            score=(real**2+imag**2)/(size*size)
            lower,upper=map(exact_endpoint,score._mpi_)
            assert lower<=upper
            scores.append(upper)
            lowers.append(lower)
        maximum_upper=max(scores)
        numerator=(maximum_upper.numerator*SCALE+maximum_upper.denominator-1)//maximum_upper.denominator
        interval_cap=F(numerator,SCALE)
        # Every interval upper endpoint is checked exactly against the cap.
        assert all(upper<=interval_cap for upper in scores)
        best=max(range(len(lowers)),key=lowers.__getitem__)
        lower_cap=F((lowers[best]*SCALE).__floor__(),SCALE)
        assert lower_cap<=lowers[best]
        # Triangle inequality independently proves rho^2<=1. This handles
        # exact unit eigenvalues whose outward numerical intervals cross 1.
        rigorous_cap=min(F(1),interval_cap)
        assert lower_cap<=rigorous_cap
        result[size]=(rigorous_cap,interval_cap,lower_cap,best+1)
    return logs,result


def small_checks():
    count=0
    mixed_count=0
    for q in (7,11,13):
        n=(q-1)//2
        for g in range(2,q):
            try:
                quotient_logs(q,g)
                break
            except AssertionError:
                pass
        logs,caps=spectral_caps(q,g,range(1,min(3,n)+1))
        for size,(rho2,_,_,_) in caps.items():
            shifts=[logs[j] for j in range(1,size+1)]
            fixtures=[]
            for mask in range(1<<n):
                values=[F(sum(bool(mask&(1<<((x+e)%n))) for e in shifts),size)
                        for x in range(n)]
                density=F(mask.bit_count(),n)
                mean=sum(values,F(0))/n
                moment=sum((x*x for x in values),F(0))/n
                union=F(sum(x>0 for x in values),n)
                assert mean==density
                assert moment-density*density<=rho2*density*(1-density)
                if density:
                    assert union>=density*density/moment
                    assert union>=density/(density+rho2*(1-density))
                else:
                    assert union==moment==0
                fixtures.append((density,union))
                count+=1
            # H=F_q^2 has q+1 projective lines. Place arbitrary symmetric
            # sets on two lines, leaving all remaining lines empty.
            for a,ba in fixtures:
                for b,bb in fixtures:
                    mu=(a+b)/(q+1)
                    nu=(a*a+b*b)/(q+1)
                    covered=(ba+bb)/(q+1)
                    assert mu*mu<=nu<=mu
                    if mu:
                        bound=mu*mu/(rho2*mu+(1-rho2)*nu)
                        assert mu<=bound<=covered
                        if nu==mu:
                            assert bound==mu
                    mixed_count+=1
    return count,mixed_count


def main():
    start=perf_counter()
    logs,caps=spectral_caps(3329,3,(2,3,8,16,24,32,64))
    assert len(logs)==1664
    print('q=3329 sign quotient: 1664 distinct classes; generator 3 verified.')
    for size,(cap,raw,lower,k) in caps.items():
        print('J',size,'rho² lower',lower,'upper',cap,
              'raw interval cap',raw,'max-lower frequency',k)
    single,mixed=small_checks()
    print('Exact small-group subset checks:',single)
    print('Exact projective-line second-moment checks:',mixed)
    print('Elapsed seconds:',round(perf_counter()-start,3))
    print('All endpoint, spectral variance, and exact union/second-moment checks passed.')


if __name__=='__main__':
    main()
