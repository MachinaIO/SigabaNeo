"""Extend the existing Part 215/217 minorant; no selected variance claim."""
from fractions import Fraction
from mpmath import iv
from wall1_hermite_budget import log_floors


def main():
    iv.dps = 80
    I = iv.mpf
    b = I(505)/2
    logv = 253*iv.ln(iv.pi)-iv.loggamma(254)
    floors = log_floors()
    gmin = iv.exp((floors[-1]-logv)/506)
    gmax = iv.exp((floors[0]-logv)/506)
    beta = (b+2)/(I('1.21')*gmin**2-2)
    oldbeta = (b+2)/(iv.sqrt(2)*1352/iv.sqrt(3)-1)
    assert beta.b < oldbeta.a
    for lo, hi in ((0,1),(1,2),(2,4)):
        v = iv.pi**2/(beta*(1+hi**2))
        error = (1+lo**2)**(-I(505)/4)*((1+2*iv.exp(-v)/(1-iv.exp(-3*v)))**505-1)
        assert (I(5)/4*error).b < I('1e-5').a
        print('Fourier band',lo,hi,'error:',error)
    def gamma_density(x):
        return iv.exp((b-1)*iv.ln(b+x)-(b+x)-iv.loggamma(b))
    # Mode at x=-1; the minimum on [-1,1] is an endpoint.
    assert gamma_density(-1).b < I('.027').a
    assert gamma_density(-1).a > I('.024').b
    assert gamma_density(1).a > I('.024').b
    m0 = 2*I('.024')*I(3)/4*(I(5)/6)**4-I('.027')/4-I('1e-5')
    assert m0.a > I('.01060').b
    # log derivative of g^-506 (1.21g²-2)^(505/2):
    # -1 + 1010/(1.21g²-2). Negative throughout this interval.
    assert (I('1.21')*gmin**2-2).a > 1010
    lower = I('.01060')*iv.exp(b-2+b*iv.ln(iv.pi*(I('1.21')*gmax**2-2)/(b+2))-logv-506*iv.ln(gmax))
    assert lower.a > 10**16
    print('g interval endpoints:',gmin,gmax)
    print('Uniform nonzero cell count / h lower bound:',lower)
    mu = 10**16
    charge = Fraction(405*40,mu)
    assert charge < Fraction('1.9515491e-12')
    print('Conditional 405-draw union charge if variance targets hold:',charge,float(charge))
    print('Selected-history variance targets and complete BKZ remain unproved.')


if __name__ == '__main__':
    main()
