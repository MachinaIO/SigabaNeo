"""Certify why the orthogonal determinant-matched H=F3^2 fixture loses its winner."""
from fractions import Fraction as F
from math import factorial
from mpmath import iv


def checks():
    # pi<22/7 makes these rational sufficient conditions exact.
    pi_upper = F(22, 7)
    for a, denominator in ((F(1), 9), (F(2), 36)):
        g2 = (2*a*a+F(1001, 1000))/F(121, 100)
        assert (pi_upper*g2)**253 < denominator*factorial(253)
    # On the only interval where the former diagonal winner can beat
    # horizontal 3a and vertical 3, a^2>=1/7 ensures c'(a)>0.
    assert F(1008, 7)-F(1001, 500) > 0
    iv.dps = 70
    I = iv.mpf
    volume = iv.pi**253/iv.factorial(253)
    for a in (I(1), I(2)):
        g2 = (2*a*a+I('1.001'))/I('1.21')
        c = iv.exp((iv.log(volume)+253*iv.log(g2)-iv.log(9*a*a))/503)
        assert c.b < 1
        print('a,c:', a, c)
    print('Passed exact rational c(1)<1, c(2)<1 and monotonicity certificates.')


if __name__ == '__main__':
    checks()
