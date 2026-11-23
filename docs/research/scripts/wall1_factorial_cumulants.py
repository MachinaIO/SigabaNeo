"""Exact factorial-cumulant transfer and a connected-incidence error envelope."""
import contextlib
from fractions import Fraction as F
from math import comb, factorial
from itertools import product
from wall1_centered_affine_cancellation import rank
from pathlib import Path
import io
import runpy
from wall1_affine_circuit_components import exponential, multiply
from wall1_affine_square_certificate import coefficients, falling, partial_exp


def difference_weights(t):
    """Coefficient arrays for E_Poisson[Delta^j K_t(X;mu)^2]."""
    result = []
    for j in range(2*t+1):
        poly = [F(0)]*(t+1)
        for a in range(t+1):
            for b in range(t+1):
                if max(a, b) <= j <= a+b:
                    coefficient = F((-1)**(a+b)*factorial(j),
                                    factorial(j-a)*factorial(j-b)*factorial(a+b-j))
                    for d in range(t-max(a, b)+1):
                        poly[d] += coefficient/factorial(d)
        assert all(not value or d <= t-(j+1)//2 for d, value in enumerate(poly))
        result.append(poly)
    return result


def log_series(series):
    assert series[0] == 1
    zero = series[0]*0
    tail = [zero]+series[1:]
    power = [zero+1]+[zero]*(len(series)-1)
    result = [zero]*len(series)
    for k in range(1, len(series)):
        power = multiply(power, tail)
        result = [a+(-1)**(k-1)*b/k for a, b in zip(result, power)]
    return result


def profiles(total, lower=1):
    if not total:
        yield ()
    for value in range(lower, total+1):
        for rest in profiles(total-value, value):
            yield (value,)+rest


def all_joint_majorant(mu, full, order):
    zero = mu*0
    connected = [zero, mu]+[full.get(h, zero)/factorial(h) for h in range(2, order+1)]
    return [factorial(h)*v for h, v in enumerate(exponential(connected))]


def cumulant_errors(mu, rho_max, q, full, order):
    """Upper bounds for |kappa_j-F_j|, including repeated input labels."""
    zero = mu*0
    joints = all_joint_majorant(mu, full, order)
    result = [zero]*(order+1)
    for j in range(2, order+1):
        rank_charge = {}
        for size in range(1, j//2+1):
            rank_charge[size] = rho_max*sum(
                (comb(size, rank)*rank*q**(j-size+rank-2+(rank-1)*(size-rank))
                 *mu**(rank-1) for rank in range(1, size+1)), zero)
        for profile in profiles(j):
            blocks = len(profile)
            if blocks < 2:
                continue
            denominator = 1
            for size in profile:
                denominator *= factorial(size)
            for size in set(profile):
                denominator *= factorial(profile.count(size))
            count = factorial(j)//denominator
            product = zero+1
            for size in profile[1:]:
                product *= joints[size]
            result[j] += count*factorial(blocks-1)*rank_charge[profile[0]]*product
    return result


def finite_transfer_checks():
    checked = 0
    laws = ((F(1, 2), F(1, 2)), (F(1, 3), F(0), F(2, 3)),
            (F(1, 5), F(1, 5), F(2, 5), F(1, 5)),
            (F(1),), (F(0), F(1)))
    for t in range(1, 7):
        weights = difference_weights(t)
        for law in laws:
            mu = sum(F(x)*p for x, p in enumerate(law))
            moment_series = [sum(p*falling(x, h) for x, p in enumerate(law))/factorial(h)
                             for h in range(2*t+1)]
            cumulants = log_series(moment_series)
            assert cumulants[1] == mu
            cumulants[1] = F(0)
            corrections = exponential(cumulants)
            a, f, _ = coefficients(mu, t)
            actual = sum(p*sum(v*falling(x, j) for j, v in enumerate(a))**2
                         for x, p in enumerate(law))
            transformed = F(0)
            for j, poly in enumerate(weights):
                value = sum(v*mu**d for d, v in enumerate(poly))
                direct = sum(f[h]*factorial(h)*mu**(h-j)/factorial(h-j)
                             for h in range(j, 2*t+1))
                assert value == direct
                transformed += value*corrections[j]
                checked += 1
            assert actual == transformed
    print(f'Passed {checked} exact Poisson-difference and cumulant-transfer checks.')


def finite_connected_checks():
    q, order, checked = 3, 8, 0
    fixtures = ([ (t, 0, 0) for t in range(3)]+[(0, t, 1) for t in range(3)],
                [(0, 0), (1, 0), (2, 0), (0, 1), (1, 1)])
    for ys in fixtures:
        n = len(ys)
        subsets = {mask: [i for i in range(n) if mask >> i & 1] for mask in range(1 << n)}
        ranks = {mask: rank([(1, *ys[i]) for i in inds], q) for mask, inds in subsets.items()}
        connected = set()
        for mask in subsets:
            if not mask:
                continue
            sub = (mask-1) & mask
            while sub:
                if ranks[sub]+ranks[mask ^ sub] == ranks[mask]:
                    break
                sub = (sub-1) & mask
            if not sub:
                connected.add(mask)
        laws = [tuple((c[0]+sum(a*b for a, b in zip(c[1:], y))) % q for y in ys)
                for c in product(range(q), repeat=len(ys[0])+1)]
        for fixture in range(3):
            fibers = [{(i+fixture) % q} if (i+fixture) % 2 else {0, 1} for i in range(n)]
            if fixture == 2:
                fibers[0], fibers[1] = set(), {0, 1, 2}
            rho = [F(len(b), q) for b in fibers]
            mu = sum(rho)
            hits = [tuple(value in b for value, b in zip(law, fibers)) for law in laws]
            full = {j: F(0) for j in range(3, order+1)}
            cumulants = {}
            for mask, inds in subsets.items():
                values = [sum(row[i] for i in inds) for row in hits]
                moments = [sum((F(falling(x, j)) for x in values), F(0))
                           /len(values)/factorial(j) for j in range(order+1)]
                cumulants[mask] = [factorial(j)*v for j, v in enumerate(log_series(moments))]
                size = len(inds)
                if mask in connected and size >= 3:
                    full[size] += factorial(size)*F(sum(all(row[i] for i in inds)
                                                       for row in hits), len(hits))
            # Mobius inversion groups log coefficients by their exact label support,
            # including repeated labels. A disconnected support must cancel.
            for mask, inds in subsets.items():
                if not mask or mask in connected:
                    continue
                exact_support = [F(0)]*(order+1)
                sub = mask
                while True:
                    sign = (-1)**(len(inds)-sub.bit_count())
                    exact_support = [a+sign*b for a, b in zip(exact_support, cumulants[sub])]
                    if not sub:
                        break
                    sub = (sub-1) & mask
                assert all(v == 0 for v in exact_support)
                checked += order
            error = cumulant_errors(mu, max(rho), q, full, order)
            for j in range(2, order+1):
                assert abs(cumulants[(1 << n)-1][j]-full.get(j, F(0))) <= error[j]
                checked += 1
    print(f'Passed {checked} exact connected-support and cumulant-error checks.')


def draw14_probe():
    from wall1_general_two_relations import draw14_bounds
    with contextlib.redirect_stdout(io.StringIO()):
        s, full, _ = draw14_bounds()
        from wall1_rank_five_code import actual_parameters as refined_fourteen
        _, refined, _ = refined_fourteen()
        from wall1_larger_triangular_components import actual_parameters as refined_larger
        _, higher = refined_larger()
    # Use the complete size-14 decomposition and the valid (but still too large)
    # higher-size triangular refinements; no higher-size budget is certified.
    full[14] = refined[14]
    full.update(higher)
    I, mu, order, iv = [s[k] for k in ('I', 'mu', 'order', 'iv')]
    weights = difference_weights(s['t'])
    majorants = [sum((I(abs(v.numerator))/v.denominator*mu**d
                     for d, v in enumerate(poly)), I(0)) for poly in weights]
    def transfer(values):
        series = [I(0), I(0)]+[values.get(j, I(0))/factorial(j) for j in range(2, order+1)]
        correction = exponential(series, start=1)
        return s['normalizer']*sum((majorants[j]*correction[j] for j in range(2, order+1)), I(0))
    for cap in (11, 12, 13, 14, 15, 16, 17, 24):
        covered = {h: full[h] if h <= cap else s['base'][h] for h in range(3, order+1)}
        charge = transfer(covered)
        if cap == 11:
            assert charge < I('2.195e-45')
        if cap == 12:
            assert charge < I('4.247e-30')
        if cap == 13:
            assert charge < I('2.175e-13')
        if cap == 14:
            assert charge < I('3.419e-13')
        if cap == 15:
            assert charge < I('3.419e-13')
        if cap == 16:
            assert charge < I('3.459e-13')
        if cap == 17:
            assert charge < I('8.048e-13')
        print('Full-incidence cumulant transfer through', cap, ':', charge, flush=True)
    n, radius = s['N'], s['radius']
    mu_upper = 2*s['geometry']['volume'][n]*(radius**2+I(n)/4)**(I(n)/2)/s['q']**s['m']
    assert mu_upper < I(119)
    assert full[3] < mu**3
    for h in range(4, order+1):
        degree = max(d for d, value in enumerate(weights[h]) if value)
        leading = abs(weights[h][degree])
        implied_cap = (F(28, 100)*F(301, 10**14)*factorial(h)
                       *119**(24-h-degree)/(factorial(12)**2*leading))
        assert implied_cap < 1
    cap = {h: mu_upper**h for h in range(3, order+1)}
    errors = cumulant_errors(mu_upper, s['rho_max'], s['q'], cap, order)
    high_weights = [sum((I(abs(v.numerator))/v.denominator*mu_upper**d
                          for d, v in enumerate(poly)), I(0)) for poly in weights]
    prefix = exponential([I(0), I(0)]+[cap.get(j, I(0))/factorial(j)
                                      for j in range(2, order+1)])
    tail = exponential([I(0), I(0)]+[errors[j]/factorial(j) for j in range(2, order+1)], start=1)
    mixed = multiply(prefix, tail)
    error_charge = s['normalizer']*sum((high_weights[j]*mixed[j] for j in range(2, order+1)), I(0))
    assert error_charge < I('3.475e-121')
    assert F(2175, 10**16)+F(27913, 10**16) == F(30088, 10**16)
    assert F(9131, 10**16)+F(2175, 10**16)+F(27913, 10**16) < F(3922, 10**15)
    assert s['baseline']+error_charge < I('9.131e-13')
    assert F(3459+9131+26629,10**16) == F(39219,10**16)
    assert F(39219,10**16) < F(3922,10**15)
    assert F(10770+9131+19318,10**16)==F(39219,10**16)
    print('Conditional cumulant error log10:', iv.log10(error_charge))
    print('Caps follow from the still-unproved cumulant transfer target <=3.01e-12.')
    return s, full, weights, error_charge


if __name__ == '__main__':
    finite_transfer_checks()
    finite_connected_checks()
    draw14_probe()
