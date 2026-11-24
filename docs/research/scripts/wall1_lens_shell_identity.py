"""Exact one-dimensional lattice audits of the lens/shell decomposition."""
from fractions import Fraction as F
from collections import Counter
from math import comb
from mpmath import iv


def main():
    checks=positive_error=negative_error=0
    for s in (1,2,3,7):
        for q in (3,5,7,11):
            for numerator in (3,4,5,6,7):
                rho=F(q*numerator,8*s)
                # K=(1/s)Z, M=(q/s)Z, rho<lambda_1(M).
                A0=(s*rho).__floor__()
                if not A0:
                    continue
                candidates=tuple(j for j in range(-A0,A0+1) if j)
                counts=Counter(j%q for j in candidates)
                assert 0 not in counts
                A=len(candidates)
                B=sum(n*n for n in counts.values())
                differences=range(-(2*s*rho).__floor__(),(2*s*rho).__floor__()+1)
                lens_sum=F(0)
                error=F(0)
                for j in differences:
                    if not j or j%q:
                        continue
                    lens=max(F(0),2*rho-abs(F(j,s)))
                    w=sum(x+j in candidates for x in candidates)
                    lens_sum+=lens
                    error+=w-s*lens
                D=F(q,s)
                ball=2*rho
                J=lens_sum-ball**2/D
                a=s*ball
                assert B==A+a*a/q+s*J+error
                nu=F(A,q-1)
                delta=F(A,a)-1
                R=F((q-1)*B,A*A)-1
                decomposed=1/nu+F(q-1,q)/(1+delta)**2-1+F(q-1,A*A)*(s*J+error)
                assert R==decomposed>=0
                positive_error+=error>0
                negative_error+=error<0
                checks+=1
    assert positive_error and negative_error
    iv.dps=80
    for d in (1,3,505):
        I=iv.mpf
        logvd=I(d)/2*iv.ln(iv.pi)-iv.loggamma(I(d)/2+1)
        logvm=I(d-1)/2*iv.ln(iv.pi)-iv.loggamma(I(d+1)/2)
        ratio=iv.exp(logvm-logvd+d*iv.ln(2)+2*iv.loggamma(I(d+1)/2)-iv.loggamma(d+1))
        assert ratio.a>I('0.999999999999999999999999999999999999999999999999999999999999999999')
        assert ratio.b<I('1.000000000000000000000000000000000000000000000000000000000000000001')
    print('Exact lattice decomposition checks:',checks)
    print('Positive/negative aggregate lens errors:',positive_error,negative_error)
    print('Continuum convolution normalization checked at dimensions1,3,505.')
    p=F(251,1000)
    gate_weight=sum((F(comb(505,j))*p**j*(1-p)**(505-j)
                     for j in range(253,506)),F(0))
    assert gate_weight<F('1.704e-33')
    print('Upper kernel weight below the old-minimum cutoff:',float(gate_weight))
    print('Production radial and discrete lens errors remain unbounded.')


if __name__=='__main__':
    main()
