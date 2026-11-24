"""Odd-dimensional direct relation counts; no draw15 probability certificate."""
from collections import Counter
from itertools import product
from math import factorial,isqrt
from mpmath import iv
from wall1_short_relation_shapes import (
    half_factorial,equal_pair_sum_ball_bound,orthogonal_pair_ball_bound,
    shared_four_ball_bound)


def main():
    iv.dps=80
    I=iv.mpf
    checked=0
    for n in (1,2,3):
        for radius_sq in (1,2,4):
            extent=isqrt(radius_sq)
            points=[x for x in product(range(-extent,extent+1),repeat=n)
                    if sum(t*t for t in x)<=radius_sq]
            pair=Counter(tuple(x+y for x,y in zip(a,b)) for a in points for b in points)
            for k in (2,3,4):
                actual=sum(v**k for v in pair.values())
                assert I(actual).b < equal_pair_sum_ball_bound(I(radius_sq),n,k).a
                checked+=1
            orth=sum(pair[tuple(x+y for x,y in zip(a,b))]*pair[tuple(x-y for x,y in zip(a,b))]
                     for a in points for b in points)
            assert I(orth).b < orthogonal_pair_ball_bound(I(radius_sq),n).a
            shared=sum(sum(pair[tuple(x-y for x,y in zip(a,b))] for b in points)**2 for a in points)
            assert I(shared).b < shared_four_ball_bound(I(radius_sq),n).a
            checked+=2
    # Even-dimensional gamma coefficients agree with the previous factorial formula.
    for n in (2,4,518):
        for k in (2,3,4):
            R=I(1000000)
            exponent=(k+1)*n//2
            old=(I(2)**(k+1+n)*iv.pi**exponent*factorial(k*n//2)
                 /factorial(n//2)**k/factorial(exponent)*(R+I(5)*n/16)**exponent)
            new=equal_pair_sum_ball_bound(R,n,k)
            assert abs(new-old).b < old.a*I('1e-65')
    for n in range(1,20):
        assert abs(half_factorial(n+2)-(I(n)/2+1)*half_factorial(n)).b<I('1e-60')
    # Production odd dimension is evaluated at its actual conservative raw radius.
    volume506=iv.pi**253/factorial(253)
    radius_sq=I('1.21')*iv.exp(2*(385*iv.ln(3329)-iv.ln(volume506))/506)-2
    for name,value in (
        ('three equal pairs',equal_pair_sum_ball_bound(radius_sq,519,3)),
        ('orthogonal pair',orthogonal_pair_ball_bound(radius_sq,519)),
        ('shared four',shared_four_ball_bound(radius_sq,519))):
        assert value.a>0
        print('N519',name,'count upper log10:',iv.log10(value))
    print('Exact finite relation-count checks:',checked)
    print('Even-dimensional factorial regression and half-gamma recurrence passed.')
    print('No complete incidence cover or actual draw15 void bound is asserted.')


if __name__=='__main__':
    main()
