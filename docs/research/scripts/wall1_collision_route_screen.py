"""Interval lens-relaxation screen and exact independent-mask counting."""
from fractions import Fraction as F
from itertools import product
from mpmath import iv


def main():
    iv.dps=70
    I=iv.mpf
    d=505
    b=I(d)/2
    inflation=iv.exp(d*iv.ln(2)+2*iv.loggamma(b+1)-iv.loggamma(2*b+1))
    r2=I('1.21')*I('31.9457')**2
    cutoff=r2/(4*(r2-2))
    assert cutoff.b<I('.251').a
    mean=b/(2*b+1)
    variance=b*(b+1)/((2*b+1)**2*(2*b+2))
    retained=1-variance/(variance+(mean-I('.251'))**2)
    factor=inflation*retained
    assert factor.a>I('27.95').b
    print('Enclosing-ball convolution inflation:',inflation)
    print('Old-minimum-gated inflation lower bound:',factor)
    print('Associated continuum benchmark void certificate lower bound:',1-1/factor)
    checks=0
    for q in (2,3,5):
        for k in range(1,5):
            masks=[h for h in product(range(q),repeat=k) if any(h)]
            for t in range(k):
                # V=span(e_1,...,e_t), witness e_(t+1); basis invariance
                # makes this representative of all V and v outside V.
                detected=sum(not any(h[:t]) and h[t]!=0 for h in masks)
                probability=F(q**(k-t-1)*(q-1),q**k-1)
                assert F(detected,len(masks))==probability
                checks+=1
    logcost=120*iv.ln(3329)/iv.ln(10)
    assert logcost.a>422
    print('Independent-mask finite counts:',checks)
    print('Conservative q^120 cost log10:',logcost)
    print('No actual collision energy or failure probability is inferred.')


if __name__=='__main__':
    main()
