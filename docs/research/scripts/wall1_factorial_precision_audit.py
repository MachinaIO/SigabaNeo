"""Exact sensitivity of the draw-14 reference polynomial, not a history bound."""
from fractions import Fraction as F

from wall1_affine_square_certificate import coefficients, partial_exp


def audit():
    # Fixed rational reference inside the previously used draw-14 scale.
    # This is not a claim that the production mean equals this rational.
    mu = F('58.15006220912')
    degree = 12
    _, coefficients_f, _ = coefficients(mu, degree)
    denominator = partial_exp(mu, degree) ** 2
    terms = [c * mu**k / denominator
             for k, c in enumerate(coefficients_f)]
    baseline = sum(terms)
    assert baseline == 1 / partial_exp(mu, degree)
    assert terms[0] == 1
    positive = sum(x for x in terms if x > 0)
    negative = -sum(x for x in terms if x < 0)
    # The zeroth factorial moment is exactly one and has no error.
    sensitivity = sum(abs(x) for x in terms[1:])
    target = F('.280') * F('3.922e-12')
    tolerance = (target - baseline) / sensitivity
    assert F('1.2052e-19') < tolerance < F('1.2053e-19')
    assert F('6990286') < sensitivity < F('6990287')
    print('Rational reference mean:', float(mu))
    print('Normalized positive and negative sums:', float(positive), float(negative))
    print('Poisson-reference expectation:', float(baseline))
    print('Nonconstant absolute moment sensitivity:', float(sensitivity))
    print('Independent relative-error-box tolerance:', float(tolerance))

    # A genuine integer law with the same first two Poisson factorial moments.
    p59 = mu * (59 - mu) / 59
    p60 = mu * (mu - 58) / 60
    p0 = 1 - p59 - p60
    assert min(p0, p59, p60) >= 0
    assert p0 + p59 + p60 == 1
    assert 59*p59 + 60*p60 == mu
    assert 59*58*p59 + 60*59*p60 == mu**2
    assert F('.0168') < p0 < F('.0170')
    print('Matching-two-moment integer law, void probability:', float(p0))
    print('This is a count-law obstruction, not a production lattice example.')
    print('Error-box tolerance is method-specific; moment errors may be correlated.')


if __name__ == '__main__':
    audit()
