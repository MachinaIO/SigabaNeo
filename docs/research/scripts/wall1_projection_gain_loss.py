"""Exact finite hit-set gain/loss and clipped potential increment checks."""
from fractions import Fraction as F


def phi(p,delta,k):return min(F(1),(p/delta)**k)

def bound(p,loss,gain,delta,k):
    d=max(F(0),loss-gain)
    return min(1-phi(p,delta,k),F(k,1)/delta*d*min(F(1),(p+d)/delta)**(k-1))


def main():
    checks=0
    for h in range(1,8):
        full=set(range(h))
        sets=[{j for j in range(h) if mask>>j&1} for mask in range(1<<h)]
        for a in sets:
            p=F(h-len(a),h)
            for b in sets:
                loss=F(len(a-b),h);gain=F(len(b-a),h)
                witness=F(h-len(b),h)
                assert witness==p+loss-gain
                for delta,k in ((F(7,25),24),(F(2,3),2),(F(1),1)):
                    if p>=delta:continue
                    incr=phi(witness,delta,k)-phi(p,delta,k)
                    assert max(F(0),incr)<=bound(p,loss,gain,delta,k)
                    # Every actual hit superset of the witness improves the bound.
                    actual=b|{0}
                    assert phi(F(h-len(actual),h),delta,k)-phi(p,delta,k)<=bound(p,loss,gain,delta,k)
                    checks+=1
    # Exact toy exhibiting cancellation across the shared random transition.
    delta=F(7,25);p=delta/2;k=24
    # A complete-hit branch and a threshold-hit branch; rational weights
    # chosen so that the signed expected potential increment is zero.
    weight=F(1,2**k)
    increments=(phi(delta,delta,k)-phi(p,delta,k),-phi(p,delta,k))
    signed=weight*increments[0]+(1-weight)*increments[1]
    positive=weight*max(F(0),increments[0])+(1-weight)*max(F(0),increments[1])
    assert signed==0 and positive>0
    # Quotient example: fiber size2, quotient hits {0,2}; pullback fraction exact.
    raw=range(6);mapping=lambda x:x%3;hits={0,2}
    pulled={v for v in raw if mapping(v) in hits}
    assert F(len(pulled),6)==F(len(hits),3)
    assert all(sum(mapping(v)==c for v in raw)==2 for c in range(3))
    print('Passed exhaustive gain/loss increment checks:',checks)
    print('Signed cancellation and quotient-fiber fixtures passed.')

if __name__=='__main__':main()
