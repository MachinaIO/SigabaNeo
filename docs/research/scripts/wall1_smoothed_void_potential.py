"""Exact abstract overlap obstruction and interval cap accounting, not a lattice counterexample."""
from fractions import Fraction as F
from mpmath import iv

def checks():
    h,k=3329,24
    c=F(h-1,h)
    moment=F(1,h)*c**k+F(h-1,h)*F(h-2,h)**k
    ratio=moment/c**k
    assert ratio==F(1,h)+F(h-1,h)*F(h-2,h-1)**k
    # Rational contraction near the documented draw129 cap ratio.
    a=F(987,1000)
    for d in (1,24,505):
        amplification=ratio/a**d
        assert amplification>1
        # A step at transformed radius 2, test radius 560. Both cutoffs exceed it.
        initial=c**k*F(2,560)**d
        outgoing=moment*F(2,560*a)**d
        assert outgoing/initial==amplification
        print('degree',d,'exact amplification >1',float(amplification),flush=True)
    iv.dps=60;I=iv.mpf
    r=I(ratio.numerator)/ratio.denominator
    critical=iv.log(1/r)/iv.log(I(1000)/987)
    print('critical degree for this overlap family',critical)
    delta=I('.18');budget=I('1e-12')
    for d in (1,24,505):
        needed=budget*delta**24*(I('32.42764')/I('583.27530'))**d
        print('degree',d,'sufficient initial E Phi log10',iv.log10(needed))
        print('degree',d,'277 q-cap penalty log10',I(277*d)/506*iv.log10(3329))
    print('Passed exact finite-overlap amplification identities; no actual lattice realization asserted.')

if __name__=='__main__':checks()
