"""Interval certificate for the fixed-ball independent-reference obstruction.

This is not a lower bound on the actual affine or projected void probability.
"""
from fractions import Fraction
from itertools import product
from math import prod
from mpmath import iv

iv.dps = 80
I = iv.mpf
q, m = 3329, 400
volume = [I(1), I(2)]
for dimension in range(2, 521):
    volume.append(2 * iv.pi * volume[dimension - 2] / dimension)

# Exact checks of the product law, including zero-density fibers.
checks = 0
for densities in product([Fraction(0), Fraction(1, 7), Fraction(2, 7)], repeat=4):
    mass_zero = sum(
        (Fraction(1) if not any(bits) else Fraction(0))
        * prod(p if bit else 1 - p for p, bit in zip(densities, bits))
        for bits in product((0, 1), repeat=4))
    assert mass_zero == prod(1 - p for p in densities)
    checks += 1

for draw in (14, 15, 16):
    dimension = 504 + draw
    radius_sq = I('1.21') * iv.exp(
        2 * (I(400 - draw) * iv.ln(q) - iv.ln(volume[506])) / 506) - 2
    mean_upper = (2 * volume[dimension]
                  * (radius_sq + I(dimension) / 4) ** (I(dimension) / 2) / q**m)
    density_upper = 2 * volume[m] * (radius_sq + I(m) / 4) ** (I(m) / 2) / q**m
    assert 0 < density_upper < 1
    reference_void_lower = iv.exp(-mean_upper / (1 - density_upper))
    if draw == 15:
        assert mean_upper < I('9.287185')
        assert density_upper < I('1.192e-300')
        assert reference_void_lower > I('0.000092603')
        assert reference_void_lower / I('.280') > I('.000330725')
    if draw == 16:
        assert 1 - mean_upper > I('.292912')
    print('draw', draw, 'reference void lower:', reference_void_lower)
print(checks, 'exact product-law checks passed; interval barrier checks passed.')
