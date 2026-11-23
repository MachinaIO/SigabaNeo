"""Exact weighted optimizers, including singular and invalid moment matrices."""
from fractions import Fraction as F
from itertools import product
from math import comb
from optimal_void_square import check_psd, optimal_square, weighted_gram
from void_square_polynomial import falling

checks = 0
for weights in product(range(3), repeat=4):
    moments = [sum(w*comb(z, h) for z, w in enumerate(weights)) for h in range(4)]
    for degree in range(4):
        gram = weighted_gram(moments, degree, event_count=3)
        coefficients, value = optimal_square(gram)
        direct = sum(w*sum(c*falling(z, h) for h, c in enumerate(coefficients))**2
                     for z, w in enumerate(weights))
        assert value == direct >= weights[0]
        if degree == 3:
            # A cubic can vanish at every positive support point, leaving weight at zero.
            assert value == weights[0]
        checks += 1

for matrix in ([[1, 1], [1, 0]], [[0, 1], [1, 1]], [[1, 2], [0, 1]], [[-1]]):
    try:
        check_psd(matrix)
    except ValueError:
        pass
    else:
        raise AssertionError('invalid moment matrix was accepted')
for matrix, expected in (([[1, 0], [0, 0]], F(1)),
                         ([[1, 1], [1, 1]], F(0)),
                         ([[0, 0], [0, 0]], F(0))):
    assert optimal_square(matrix)[1] == expected
try:
    weighted_gram([1], 2, event_count=3)
except ValueError:
    pass
else:
    raise AssertionError('missing nonzero-order moments were accepted')
print(f'Passed {checks} weighted finite-law optimizations, singular cases and invalid-input checks.')
