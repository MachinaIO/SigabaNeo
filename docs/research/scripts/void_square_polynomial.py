"""Exact square certificates for zero counts; no reference-law assumption."""
from fractions import Fraction as F
from math import comb, factorial


def falling(x, degree):
    value = 1
    for j in range(degree):
        value *= x-j
    return value


def kernel_value(x, mu, degree):
    """Normalized Charlier kernel, evaluated from its defining polynomial sum."""
    mu = F(mu)
    if mu < 0 or degree < 0:
        raise ValueError('mu and degree must be nonnegative')
    normalizer = sum(mu**j/F(factorial(j)) for j in range(degree+1))
    kernel = sum(F((-1)**j, factorial(j))
                 * sum(comb(j, ell)*(-mu)**(j-ell)*falling(x, ell)
                       for ell in range(j+1)) for j in range(degree+1))
    return kernel/normalizer


def square_coefficients(mu, degree):
    """Coefficients of the normalized kernel square in the falling-factorial basis."""
    mu = F(mu)
    if mu < 0 or degree < 0:
        raise ValueError('mu and degree must be nonnegative')
    partial = [sum(mu**j/F(factorial(j)) for j in range(k+1)) for k in range(degree+1)]
    coefficients = [F((-1)**j, factorial(j))*partial[degree-j] for j in range(degree+1)]
    result = [F(0)]*(2*degree+1)
    for i, left in enumerate(coefficients):
        for j, right in enumerate(coefficients):
            for shared in range(min(i, j)+1):
                result[i+j-shared] += (left*right*comb(i, shared)*comb(j, shared)
                                       * factorial(shared)/partial[degree]**2)
    assert result[0] == 1
    return result


def mixed_square_expectation(subset_moments, mu, degree, center, *, event_count):
    """E[(J-center)^2 kernel(Z)^2] from sums over h-element event subsets.

    Row h is sum_{|S|=h} E[(1,J,J^2) 1_all(S)]. All required rows up to
    min(2*degree,event_count) must be supplied; otherwise this function fails.
    """
    coefficients = square_coefficients(mu, degree)
    if (event_count < 0 or len(subset_moments) < min(2*degree, event_count)+1
            or len(subset_moments) > event_count+1):
        raise ValueError('missing required subset moments')
    return sum(coefficient*factorial(h)*(row[2]-2*center*row[1]+center**2*row[0])
               for h, (coefficient, row) in enumerate(zip(coefficients, subset_moments)))
