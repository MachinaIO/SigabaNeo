"""Rigorous finite-sum multheight bound for the fixed 400-marked rectangle.

All q^2 exponentials are upper-bounded by fixed-point integer Taylor sums.
Only the final geometric prefactor and logarithms use outward intervals.
"""
from fractions import Fraction as F
from math import factorial
import numpy as np
from mpmath import iv


def main():
    q=3329;m=400;half=16;J=2*half+1;degree=16;scale=2**24
    denominator=10*q*q  # theta=1/10
    xmax=F(J,40)
    remainder=xmax**(degree+1)/(factorial(degree+1)*(1-xmax))
    assert 0<xmax<1 and scale*remainder<1
    # Prove every int64 intermediate remains representable, including sums.
    smax=J*(q//2)**2
    assert scale*smax+denominator*degree <2**63
    assert q*(degree+2)*scale <2**63
    u=np.arange(q,dtype=np.int64)[:,None]
    v=np.arange(q,dtype=np.int64)[None,:]
    S=np.zeros((q,q),dtype=np.int64)
    for j in range(-half,half+1):
        residues=(v+j*u+q//2)%q-q//2
        S+=residues*residues
    assert int(S.max())<=smax
    term=np.full_like(S,scale);total=term.copy()
    for d in range(1,degree+1):
        divisor=denominator*d
        term=(term*S+divisor-1)//divisor
        assert int(term.max())<=scale
        total+=term
    total+=1  # strictly bounds the analytic Taylor remainder
    rows=total.sum(axis=1,dtype=np.int64)
    numerator=sum(int(x)**24 for x in rows)
    divisor=q*(q*scale)**24
    # K(u) <= row[u]/(q*scale); average K(u)^24 is exact-rational upper.
    iv.dps=80;I=iv.mpf
    mu=F(q*q-1,12*q*q)
    variance=sum((F(j*j,q*q)-mu)**2 for j in range(-q//2+1,q//2+1))/q
    cv=lambda x:I(x.numerator)/x.denominator
    R2=I(605)**2-1
    ell2=R2/(m*cv(mu)+I('1.3')*iv.sqrt(m*cv(variance)))
    V=iv.pi**253/iv.factorial(253)
    c=iv.exp((iv.log(V)+506*iv.log(550)-I(m)/2*iv.log(ell2))/105)
    B2=I(605)**2*c**(-I(2)/506)-1
    assert c>1 and B2>0
    sum_j2=half*(half+1)*(2*half+1)//3
    logmoment=I(24)/10*(sum_j2-J*B2)/ell2+m*(iv.log(I(numerator))-iv.log(I(divisor)))
    normalized=iv.exp(logmoment-24*iv.log(I('.280')))
    assert normalized.b<I('1e-25').a
    # Reuse the certified iid Berry--Esseen input from the radial-profile note.
    # Shevtsova arXiv:1111.6554v1, Corollary1: constant0.4748.
    third=sum(abs(F(j*j,q*q)-mu)**3 for j in range(-q//2+1,q//2+1))/q
    be=I('.4748')*cv(third)/(cv(variance)**I('1.5')*iv.sqrt(m))
    z=I('1.3');integral=I(0)
    for d in range(40):
        integral+=(-1)**d*z**(2*d+1)/(I(2)**d*iv.factorial(d)*(2*d+1))
    nextterm=z**81/(I(2)**40*iv.factorial(40)*81)
    normal_lo=I('.5')-(integral+nextterm)/iv.sqrt(2*iv.pi)
    normal_hi=I('.5')-integral/iv.sqrt(2*iv.pi)
    incoming_lo=normal_lo-be;incoming_hi=normal_hi+be
    assert incoming_lo.a>I('.06').b and incoming_hi.b<I('.14').a
    incoming_potential_lower=(incoming_lo/I('.280'))**24
    assert normalized.b<incoming_potential_lower.a
    print('Incoming void lower/upper bounds:',incoming_lo,incoming_hi)
    print('Incoming capped potential lower bound:',incoming_potential_lower)
    print('Strict expected capped contraction certified for this rectangle.')
    print('Exact finite table:',q*q,'pairs; heights',-half,half,'theta 1/10')
    print('Taylor remainder scaled upper:',remainder*scale)
    print('ell squared:',ell2)
    print('actual winner cap c:',c)
    print('outgoing radius squared lower parameter:',B2)
    print('Raw outgoing 24th moment upper:',iv.exp(logmoment))
    print('Capped outgoing potential upper:',normalized)
    print('Certified <1e-25 for this fixed rectangle; no general history-law claim.')

if __name__=='__main__':main()
