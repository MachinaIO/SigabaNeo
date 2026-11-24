"""Interval certificate for the sharp two-moment correlation MGF.

Only the compensator remainder is bounded, not the selected radius exit.
"""
from mpmath import iv
from fractions import Fraction as F


def alternative_threshold():
    I=iv.mpf
    rho=I(276)/1000;lam=I(3238)/1000
    mean=rho*rho
    variance=(iv.sin(iv.pi*rho)/(3329*iv.sin(iv.pi/3329)))**2*rho*(1-rho)
    low=mean-variance/(rho-mean)
    weight=variance/(variance+(rho-mean)**2)
    assert 0<low.a and low.b<mean.a and 0<weight.a and weight.b<1
    factor=weight*iv.exp(lam*rho)+(1-weight)*iv.exp(lam*low)
    remainder=iv.exp(-I('48.6')*lam+398*iv.ln(factor))
    assert remainder.b<I('2.982e-14').a
    ratio=F(70,69)
    seed=F('1.9704509e-12')*ratio
    later=F('5.030e-12')
    total=F('2.5035e-12')*ratio+later+F('2.982e-14')
    assert total<F('7.6e-12')
    assert later-seed>F('3.03099e-12')
    assert seed*F('1.00236')**390<F('5.012661e-12')<later
    assert seed*F('1.00237')**390>later
    print('Alternative rho=.276, lambda=3.238 remainder:',remainder)
    print('Alternative exact total allocation:',total)
    print('Alternative exact rescaled seed:',seed)
    print('Alternative residual allowance exceeds3.03099e-12; multiplier1.00236 fits.')
    print('This requires controlling the stricter .276 exit event; it is not proved.')


def early_block_refinement():
    I=iv.mpf
    rho=I(28)/100;lam=I(31724)/10000
    mean=rho*rho
    variance=(iv.sin(iv.pi*rho)/(3329*iv.sin(iv.pi/3329)))**2*rho*(1-rho)
    low=mean-variance/(rho-mean)
    weight=variance/(variance+(rho-mean)**2)
    assert 0<low.a and low.b<mean.a
    factor=weight*iv.exp(lam*rho)+(1-weight)*iv.exp(lam*low)
    raw_mean=F('0.28')*(F('7.150e-14')+F('2.432e-12')+F('1.9704509e-12'))
    T=I(raw_mean.numerator)/raw_mean.denominator
    early=1+iv.expm1(8*lam*rho)*T/8
    remainder=iv.exp(-I('48.6')*lam+390*iv.ln(factor))*early
    assert remainder.b<I('8.850e-14').a
    assert remainder.a>I('8.849e-14').b
    later=F('5.0075e-12');seed=F('1.9704509e-12')
    assert F('7.150e-14')+F('2.432e-12')+later+F('8.850e-14')==F('7.5995e-12')
    assert later-seed==F('3.0370491e-12')
    assert seed*F('1.00239')**390<F('4.999063e-12')<later
    assert seed*F('1.00240')**390>later
    print('Initial-eight-block raw mean sum bound:',raw_mean)
    print('Early-block MGF factor:',early)
    print('Same rho=.280 refined compensator remainder:',remainder)
    print('Later allocation5.0075e-12; residual3.0370491e-12; multiplier1.00239 fits.')


def main():
    iv.dps=70
    I=iv.mpf
    q=3329;rho=I(28)/100;lam=I(302)/100
    mean=rho*rho
    fourier=iv.sin(iv.pi*rho)/(q*iv.sin(iv.pi/q))
    variance=fourier**2*rho*(1-rho)
    low=mean-variance/(rho-mean)
    weight=variance/(variance+(rho-mean)**2)
    assert 0<low.a and low.b<mean.a and mean.b<rho.a
    assert 0<weight.a and weight.b<1
    sharp=weight*iv.exp(lam*rho)+(1-weight)*iv.exp(lam*low)
    remainder=iv.exp(-I('48.6')*lam+398*iv.ln(sharp))
    old=1+lam*mean+(iv.exp(lam*rho)-1-lam*rho)/rho**2*(mean**2+variance)
    assert sharp.b<old.a
    assert remainder.b<I('1.047e-12').a
    assert remainder.a>I('1.0466e-12').b
    assert F('7.6e-12')-F('1.047e-12')==F('6.553e-12')
    allowance=I('7.6e-12')-I('1.047e-12')
    assert allowance.a>I('6.5529e-12').b
    print('Lower support point:',low)
    print('Upper endpoint mass:',weight)
    print('Compensator remainder at lambda=3.020:',remainder)
    print('Rounded sufficient exit allowance: 6.553e-12')
    early=F('7.150e-14')+F('2.432e-12')
    later=F('4.049e-12')
    seed=F('1.9704509e-12')
    assert early+later+F('1.047e-12')==F('7.5995e-12')<F('7.6e-12')
    assert later-seed==F('2.0785491e-12')
    assert seed*F('1.00184')**390<F('4.035794e-12')<later
    assert seed*F('1.00185')**390>later
    print('Reconciled draws14..404 allocation: 4.049e-12')
    print('Remaining additive charge allowance after draw14 seed: 2.0785491e-12')
    print('Conditional multiplier 1.00184 fits for390steps; 1.00185 does not.')
    alternative_threshold()
    early_block_refinement()
    print('No bound on the selected-history exit probability is asserted.')


if __name__=='__main__':main()
