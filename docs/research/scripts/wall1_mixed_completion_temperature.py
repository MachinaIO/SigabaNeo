"""Certified input-only Gaussian pivot completion bound; no production changes."""
from fractions import Fraction as F
from mpmath import iv

def evaluate(R2,label):
    I=iv.mpf;q=3329;d=10;k=6;R=iv.sqrt(R2)
    def value(t):
        weights=[iv.exp(-t*I(j*j)/q**2) for j in range(1,q//2+1)]
        Z=1+2*sum(weights,I(0))
        E=2*sum((I(j*j)/q**2*w for j,w in enumerate(weights,1)),I(0))/Z
        return t*R2/q**2+d*iv.log(Z),R2/q**2-d*E
    lo=I(0);hi=I(2)
    assert value(lo)[1]<0<value(hi)[1]
    for _ in range(42):
        mid=(lo+hi)/2;derivative=value(mid)[1]
        if derivative<0:lo=mid
        else:
            assert derivative>0
            hi=mid
    f0,g0=value(I(0));fl,gl=value(lo);fh,gh=value(hi)
    assert g0<0 and gl<0<gh
    mid=(lo+hi)/2;fm,gm=value(mid)
    lower=fl+gl*(hi-lo)
    optimal=I([lower.a,fm.b])
    original=I(k*d)*iv.log(q)
    gaussian=I(k)*optimal
    volume=iv.pi**5/iv.factorial(5)
    existing=min(I(q**d),volume*(R+iv.sqrt(d)/2)**d,key=lambda x:x.b)
    assert gaussian>k*iv.log(existing)
    print('CASE',label,'radius',R)
    print('d10 k6 inputdim118 outputdim400; beta_anchor unchanged; new-point count exponent60')
    print('beta_new minimizer bracket',I([lo.a,hi.b])/q**2)
    print('log10 q^60',original/iv.log(10))
    print('log10 optimal complete Gaussian factor',gaussian/iv.log(10))
    print('log10 ratio to beta_new=0',(gaussian-original)/iv.log(10))
    print('log10 volume completion factor at same R',k*iv.log10(existing))
    print('log10 Gaussian / volume',gaussian/iv.log(10)-k*iv.log10(existing))
    assert R2<I(d*(q*q-1))/12
    print('Initial derivative negative; convex global minimum bracket certified.')
def main():
    iv.dps=65;I=iv.mpf;q=3329
    assert F(2933**2)<F(10*(q*q-1),12)
    evaluate(I(2933**2),'exact2933')
    # Same expression as wall1_draw14_frontier.py; no evaluator import.
    volume506=iv.pi**253/iv.factorial(253)
    actualR2=I('1.21')*iv.exp(2*(I(386)*iv.log(q)-iv.log(volume506))/506)-2
    evaluate(actualR2,'production')

if __name__=='__main__':main()
