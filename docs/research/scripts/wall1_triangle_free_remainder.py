"""Separate supports without eligible triangular six-point anchors."""
import contextlib
import io
from fractions import Fraction as F
from wall1_general_two_relations import draw14_bounds
from wall1_factorial_cumulants import difference_weights
from wall1_linear_remainder import remainder_weights, transfer


def actual_parameters():
    with contextlib.redirect_stdout(io.StringIO()):
        s, full, strata = draw14_bounds()
        _, free, free_strata = draw14_bounds(exclude_triangular_anchors=True)
    I, iv, mu = s['I'], s['iv'], s['mu']
    weights = [sum((I(abs(v.numerator))/v.denominator*mu**d
                    for d, v in enumerate(poly)), I(0))
               for poly in difference_weights(12)]
    baseline = {h: full[h] if h <= 13 else s['base'][h] for h in range(3, 25)}
    coefficients = remainder_weights(weights, baseline, 14)
    for h in range(14, 25):
        value = sum((v for (size, r, c), v in free_strata.items()
                     if size == h and r >= 3), I(0))
        print('size', h, 'triangle-free residual transfer log10',
              iv.log10(s['normalizer']*coefficients[h]*value), flush=True)
    for r in range(5, 10):
        print('size-14 rank', r, 'girth four triangle-free transfer log10',
              iv.log10(s['normalizer']*coefficients[14]*free_strata[14, r, 4]), flush=True)
    admitted = I(0)
    for (h, r, c), value in strata.items():
        if h == 14 and r >= 3:
            admitted += free_strata[h, r, c] if c == 4 and 5 <= r <= 9 else value
    baseline[14] += admitted
    candidate_charge = s['normalizer']*transfer(weights, baseline)
    assert candidate_charge < I('5.395e-13')
    assert F(5395, 10**16)+F(24693, 10**16) == F(30088, 10**16)
    assert F(9131, 10**16)+F(5395, 10**16)+F(24693, 10**16) < F(3922, 10**15)
    print('Known transfer including the admitted triangle-free size-14 strata:', candidate_charge, flush=True)
    print('OPEN: supports containing triangular anchors and larger-size residual classes.')


if __name__ == '__main__':
    actual_parameters()
