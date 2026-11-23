"""Reduce component discrepancies to full incidences; draw-14 bound is conditional."""
import contextlib
from fractions import Fraction as F
from itertools import product
from math import comb, factorial
from pathlib import Path
import io
import runpy
from wall1_affine_circuit_components import exponential, multiply
from wall1_centered_affine_cancellation import rank


def dependent_majorant(mu, full, order):
    """Ordered dependent joint counts from connected full-incidence counts."""
    zero = mu*0
    singletons = [zero, mu]+[zero]*(order-1)
    connected = [full.get(h, zero)/factorial(h) for h in range(order+1)]
    series = multiply(exponential(singletons), exponential(connected, start=1))
    return [factorial(h)*series[h] for h in range(order+1)]


def density_errors(mu, rho_max, q, full, order):
    """Independent products plus proper-subset errors on connected supports."""
    zero = mu*0
    joint = dependent_majorant(mu, full, order)
    independent = [zero]*3 + [h*q**(h-2)*rho_max*mu**(h-1)
                             for h in range(3, order+1)]
    return {h: independent[h]+q**(h-2)*rho_max*sum(
        (comb(h, j)*mu**(h-j-1)*(joint[j]+independent[j])
         for j in range(3, h)), zero) for h in range(3, order+1)}


def finite_checks():
    q = 3
    ys = list(product(range(q), repeat=2))
    size = len(ys)
    indices = {mask: [i for i in range(size) if mask >> i & 1]
               for mask in range(1 << size)}
    ranks = {mask: rank([(1, *ys[i]) for i in inds], q)
             for mask, inds in indices.items()}
    connected = set()
    for mask, inds in indices.items():
        if len(inds) < 3:
            continue
        sub = (mask-1) & mask
        while sub:
            if ranks[sub]+ranks[mask ^ sub] == ranks[mask]:
                break
            sub = (sub-1) & mask
        if sub == 0:
            connected.add(mask)
    laws = [tuple((c[0]+c[1]*y[0]+c[2]*y[1]) % q for y in ys)
            for c in product(range(q), repeat=3)]
    checks = 0
    for fixture in range(3):
        fibers = [{(i+fixture) % q} if (i+fixture) % 2 else {0, 1}
                  for i in range(size)]
        if fixture == 2:
            fibers[0], fibers[1] = set(), {0, 1, 2}
        rho = [F(len(b), q) for b in fibers]
        mu = sum(rho)
        hits = [tuple(value in b for value, b in zip(law, fibers)) for law in laws]
        joint, independent = {}, {}
        full = {h: F(0) for h in range(3, size+1)}
        dep_joint, dep_product = [F(0)]*(size+1), [F(0)]*(size+1)
        proper = [F(0)]*(size+1)
        for mask, inds in indices.items():
            joint[mask] = F(sum(all(row[i] for i in inds) for row in hits), len(hits))
            independent[mask] = F(1)
            for i in inds:
                independent[mask] *= rho[i]
            h = len(inds)
            if ranks[mask] < h:
                dep_joint[h] += factorial(h)*joint[mask]
                dep_product[h] += factorial(h)*independent[mask]
            if mask in connected:
                full[h] += factorial(h)*joint[mask]
        for mask in connected:
            sub = (mask-1) & mask
            while sub:
                if ranks[sub] < sub.bit_count():
                    proper[mask.bit_count()] += (factorial(mask.bit_count())
                        *abs(joint[sub]-independent[sub])*independent[mask ^ sub])
                sub = (sub-1) & mask
        majorant = dependent_majorant(mu, full, size)
        errors = density_errors(mu, max(rho), q, full, size)
        for h in range(3, size+1):
            assert dep_joint[h] <= majorant[h]
            assert dep_product[h] <= h*q**(h-2)*max(rho)*mu**(h-1)
            direct = q**(h-2)*max(rho)*sum(
                (comb(h, j)*mu**(h-j-1)*(dep_joint[j]+dep_product[j])
                 for j in range(3, h)), F(0))
            assert proper[h] <= direct
            assert proper[h]+dep_product[h] <= errors[h]
            checks += 4
    print(f'Passed {checks} exact full-incidence and proper-subset envelope checks.')


def draw14_checks():
    with contextlib.redirect_stdout(io.StringIO()):
        s = runpy.run_path(str(Path(__file__).with_name('wall1_draw14_frontier.py')))
    I, iv, mu, q, order = [s[k] for k in ('I', 'iv', 'mu', 'q', 'order')]
    n, radius, geom = s['N'], s['radius'], s['geometry']
    mu_upper = 2*geom['volume'][n]*(radius**2+I(n)/4)**(I(n)/2)/q**s['m']
    assert mu < mu_upper < I(119)
    # Existing one-circuit envelopes already imply the mild cap through size 9.
    for h in range(3, 10):
        full_bound = s['base'][h]+s['extra'].get(h, I(0))
        assert full_bound/mu**h < 1
    # A sufficiently small full-incidence transfer itself implies the cap above 9.
    for h in range(10, order+1):
        cap = F(28, 100)*F(301, 10**14)*119**(order-h)/s['S'][order][h]
        assert cap < 1
    full_cap = {h: mu_upper**h for h in range(3, order+1)}
    errors = density_errors(mu_upper, s['rho_max'], q, full_cap, order)
    # Bound every positive numerator monomial at the mean upper bound; retain
    # the existing lower bound in the normalizing denominator.
    central = s['central']
    coefficients = [sum((I(abs(c.numerator))/c.denominator*mu_upper**b
                         for (a, b), c in central.items() if a == j), I(0))
                    for j in range(order+1)]
    def active(values):
        return [sum((values.get(h, I(0))*s['S'][j][h] for h in range(3, j+1)), I(0))
                /factorial(j) for j in range(order+1)]
    free = [I(0), I(0)]+[mu_upper/factorial(j) for j in range(2, order+1)]
    # exp(free+full)*(exp(error)-1) includes all mixtures with a density error.
    prefix = exponential([x+y for x, y in zip(free, active(full_cap))])
    remainder = multiply(prefix, exponential(active(errors), start=1))
    charge = s['normalizer']*sum((coefficients[j]*factorial(j)*remainder[j]
                                 for j in range(3, order+1)), I(0))
    assert charge < I('4.107e-197')
    assert s['baseline']+s['bernoulli']+charge < I('9.131e-13')
    assert I('9.131e-13')+I('3.0088e-12') < I('3.922e-12')
    print('Mean upper bound:', mu_upper)
    print('Conditional mixed density-error charge log10:', iv.log10(charge))
    print('Mixed density-error charge < 4.107e-197 under F_h <= mu^h.')
    print('Caps through 9 follow from existing envelopes; above 9 follow from T(F)<=3.01e-12.')
    print('REQUIRED, NOT PROVED: full-incidence transfer T(F)<=3.01e-12.')
    print('Full-incidence transfer and later histories remain unbounded.')
    return charge


if __name__ == '__main__':
    finite_checks()
    draw14_checks()
