"""Exact linear transfer of components larger than half the truncation order."""
import contextlib
from fractions import Fraction as F
from math import factorial
import io
from wall1_affine_circuit_components import exponential
from wall1_factorial_cumulants import difference_weights


def remainder_weights(majorants, baseline, cutoff):
    order = len(majorants)-1
    if 2*cutoff <= order:
        raise ValueError('Two unknown components can fit; remainder is not linear.')
    zero = majorants[0]*0
    prefix = exponential([zero, zero]+[
        baseline.get(h, zero)/factorial(h) for h in range(2, order+1)])
    return {h: sum((majorants[j]*prefix[j-h] for j in range(h, order+1)), zero)
            /factorial(h) for h in range(cutoff, order+1)}


def transfer(majorants, activities):
    order = len(majorants)-1
    zero = majorants[0]*0
    series = exponential([zero, zero]+[
        activities.get(h, zero)/factorial(h) for h in range(2, order+1)], start=1)
    return sum((w*v for w, v in zip(majorants, series)), zero)


def finite_checks():
    checked = 0
    for order in (6, 8, 12, 24):
        for seed in range(12):
            cutoff = order//2+1
            baseline = {h: F((h+seed) % 5, h+1) for h in range(2, order+1)}
            unknown = {h: F((h*seed+3) % 7, h+2) for h in range(cutoff, order+1)}
            weights = [F((j+seed) % 9, j+1) for j in range(order+1)]
            combined = {h: baseline[h]+unknown.get(h, F(0)) for h in baseline}
            actual = transfer(weights, combined)-transfer(weights, baseline)
            coefficients = remainder_weights(weights, baseline, cutoff)
            predicted = sum((coefficients[h]*value for h, value in unknown.items()), F(0))
            assert actual == predicted
            assert all(v >= 0 for v in coefficients.values())
            # Baseline terms above order-cutoff cannot enter a mixed coefficient.
            shortened = {h: v for h, v in baseline.items() if h <= order-cutoff}
            assert coefficients == remainder_weights(weights, shortened, cutoff)
            checked += 1
    try:
        remainder_weights([F(1)]*7, {}, 3)
    except ValueError:
        pass
    else:
        raise AssertionError('Nonlinear threshold accepted.')
    print(f'Passed {checked} exact remainder identities and the nonlinear-threshold check.')


def actual_parameters():
    from wall1_general_two_relations import draw14_bounds
    with contextlib.redirect_stdout(io.StringIO()):
        s, full, strata = draw14_bounds()
    I, iv, mu = s['I'], s['iv'], s['mu']
    weights = [sum((I(abs(v.numerator))/v.denominator*mu**d
                    for d, v in enumerate(poly)), I(0))
               for poly in difference_weights(12)]
    baseline = {h: full[h] if h <= 13 else s['base'][h] for h in range(3, 25)}
    coefficients = remainder_weights(weights, baseline, 14)
    # Calculate the mixed correction separately to avoid subtracting near-equals.
    positive_prefix = exponential([I(0), I(0)]+[
        baseline.get(h, I(0))/factorial(h) for h in range(2, 25)], start=1)
    for h in range(14, 25):
        mixed = sum((weights[j]*positive_prefix[j-h] for j in range(h, 25)), I(0))
        ratio = mixed/weights[h]
        coefficient = s['normalizer']*coefficients[h]
        assert ratio < I('2e-42')
        if h >= 22:
            assert mixed == 0
        print('h', h, 'log10 mixed/direct', iv.log10(ratio),
              'log10 transfer coefficient', iv.log10(coefficient), flush=True)
    # Rank/girth diagnosis of the current first missing size; no acceptance claim.
    ranked = sorted(((value.b, r, c, value) for (h, r, c), value in strata.items()
                     if h == 14), reverse=True)
    for _, r, c, value in ranked[:5]:
        print('size-14 rank/girth', r, c, 'log10 weighted envelope',
              iv.log10(s['normalizer']*coefficients[14]*value), flush=True)
    for label, predicate in (
            ('girth other than four', lambda r, c: c != 4),
            ('outside rank 5..9 with girth four', lambda r, c: c != 4 or not 5 <= r <= 9)):
        subtotal = sum((value for (h, r, c), value in strata.items()
                        if h == 14 and predicate(r, c)), I(0))
        print('size-14', label, 'log10 weighted envelope',
              iv.log10(s['normalizer']*coefficients[14]*subtotal), flush=True)
    admitted = sum((value for (h, r, c), value in strata.items()
                    if h == 14 and r >= 3 and (c != 4 or not 5 <= r <= 9)), I(0))
    additional_charge = s['normalizer']*coefficients[14]*admitted
    assert additional_charge < I('6e-18')
    enlarged_baseline = dict(baseline)
    enlarged_baseline[14] += admitted
    enlarged_charge = s['normalizer']*transfer(weights, enlarged_baseline)
    assert enlarged_charge < I('2.175e-13')
    print('Known transfer including the admitted size-14 strata:', enlarged_charge, flush=True)
    print('OPEN: weighted sum of actual unknown activities and later-history probability.')


if __name__ == '__main__':
    finite_checks()
    actual_parameters()
