"""Exact arithmetic and interval checks for the linear-section obstruction."""
from fractions import Fraction
from math import factorial
from mpmath import iv


def main():
    q, g = 3329, 549
    mu = Fraction(q*q-1, 12*q*q)
    determinant_lower = Fraction(3**253 * g**506, factorial(253))
    radius_squared = Fraction(121, 100)*g*g
    # e<3; D>3^400 implies log D>400, sufficient for monotonicity in d.
    assert determinant_lower > 3**400
    assert (400*mu)**200 * determinant_lower > radius_squared**200
    iv.dps = 80
    determinant = iv.pi**253 / factorial(253) * g**506
    mean_lower = (iv.mpf(mu.numerator)/mu.denominator * 400
                  * determinant**(iv.mpf(1)/200))
    ratio = mean_lower / (iv.mpf(radius_squared.numerator)/radius_squared.denominator)
    assert ratio.a > iv.mpf('10.529').b
    print('Exact determinant, rank monotonicity and mean-radius comparisons passed.')
    print('Mean squared norm lower bound:', mean_lower)
    print('Ratio to (1.1*g)^2:', ratio)
    print('Scope: fixed positive tilt, unprojected linear section, radius <= 1.1*g.')


if __name__ == '__main__':
    main()
