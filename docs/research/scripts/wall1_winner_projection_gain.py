"""Actual shortest winners and projected void in a rank-one-marked rectangular subclass."""
from fractions import Fraction as F
from math import isqrt
from mpmath import iv

def main():
    iv.dps=60;I=iv.mpf;q=3329;ell=1475;g=I(550);L=I('1.10')*g
    V=iv.pi**253/iv.factorial(253)
    c=iv.exp((iv.log(V)+506*iv.log(g)-iv.log(ell))/504)
    # Every j beyond this window is too long after the maximum below is checked.
    J=60;winners=[]
    for u in range(q):
        best=None
        for j in range(1,J+1):
            r=(j*u)%q;r=min(r,q-r)
            numerator=ell*ell*r*r+q*q*j*j
            if best is None or numerator<best[0]:best=(numerator,j,r)
        winners.append(best)
    maximum=max(v[0] for v in winners)
    assert maximum<q*q*J*J and I(maximum)/q**2<c*c and maximum<q*q*ell*ell
    # This certifies all unsearched heights, unmarked coordinates, and horizontal rows.
    S=iv.sqrt(I(maximum))/q
    assert L*L*(1-I(1)/506)*S**(-I(2)/506)>1
    oldR=iv.sqrt(L*L-1)
    def floor_cert(x):
        a=int(x.a);b=int(x.b);assert a==b;return a
    oldhit=floor_cert(q*oldR/ell);p=F(max(0,q-1-2*oldhit),q)
    actual=[];positive=[]
    for u,(num,j,r) in enumerate(winners):
        assert 1<=j<q
        s=iv.sqrt(I(num))/q
        B=iv.sqrt(L*L*s**(-I(2)/506)-1)
        hit=floor_cert(q*B*s/ell)
        miss=F(max(0,q-1-2*hit),q)
        actual.append(miss)
        if miss:positive.append((u,j,r,miss))
        assert miss<=p
    moment=sum(x**24 for x in actual)/q
    ratio=moment/p**24
    assert [x[0] for x in positive]==[0,1,q-1]
    assert ratio<F(1,3300)
    print('rank505 g550 ell1475 unmarkedside',c)
    print('old radius',oldR,'old void',p,float(p))
    print('maximum winner length',iv.sqrt(I(maximum))/q,'exhaustive height cutoff',J)
    print('positive outgoing branches',positive)
    print('exact E p_out^24 / p_old^24',ratio)
    print('ratio decimal',float(ratio))
    print('all branches p_out<=p_old; all but three full coverage; exact winner and actual radius certified')
if __name__=='__main__':main()
