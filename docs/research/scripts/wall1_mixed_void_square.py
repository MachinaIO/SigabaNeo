"""Exact polynomial checks; Poisson numbers below are reference-law values only."""
from fractions import Fraction as F
from math import factorial
from void_square_polynomial import (
    falling, kernel_value, mixed_square_expectation, square_coefficients,
)

checks = 0
for mu in (F(0), F(1, 3), F(1), F(58), F(715)):
    for degree in range(9):
        coefficients = square_coefficients(mu, degree)
        assert kernel_value(0, mu, degree) == 1
        for value in range(21):
            expanded = sum(c*falling(value, h) for h, c in enumerate(coefficients))
            assert expanded == kernel_value(value, mu, degree)**2 >= 0
            checks += 1
        # Poisson factorial moments are mu^h; this is not a design-law substitution.
        expectation = sum(c*mu**h for h, c in enumerate(coefficients))
        normalizer = sum(mu**j/F(factorial(j)) for j in range(degree+1))
        assert expectation == 1/normalizer

try:
    mixed_square_expectation([[1, 1, 1]], F(1), 2, F(0), event_count=3)
except ValueError:
    pass
else:
    raise AssertionError('incomplete mixed moments must be rejected')

# Dimension-506 radius ratio 1.10, solely as a transparent Poisson reference scale.
mu = F(11, 10)**506/2
normalizer = sum(mu**j/F(factorial(j)) for j in range(6))
bonferroni = sum((-1)**j*mu**j/F(factorial(j)) for j in range(11))
assert bonferroni > 10**199
assert 1/normalizer < F(1, 10**100)
print(f'Passed {checks} polynomial evaluations and 45 Poisson-reference identities.')
print('Reference only at mu=1.10^506/2: degree-10 Bonferroni > 10^199; '
      'degree-10 square expectation < 10^-100.')
