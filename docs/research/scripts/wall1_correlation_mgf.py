"""Interval and exhaustive finite checks for wall1_correlation_mgf.md."""
from fractions import Fraction
from itertools import product
from math import factorial
from mpmath import iv

iv.dps = 80
I = iv.mpf
q = 3329
assert 11**506*q**394*factorial(253)*113**253 > 10**506*q**506*355**253

def second_bound(p, prime):
    m = iv.sin(iv.pi*p)/(prime*iv.sin(iv.pi/prime))
    return p**4 + m*m*p*(1-p)

def tail(rho, lam, count):
    p, l = I(rho), I(lam)
    B = 1+l*p*p+(iv.exp(l*p)-1-l*p)*second_bound(p, q)/(p*p)
    return iv.exp(count*iv.ln(B)-I('48.6')*l)

for p, lam, upper, allowance in [
    ('.280', '3.004', '1.174e-12', '6.426e-12'),
    ('.281', '2.950', '2.736e-12', '4.864e-12'),
]:
    value = tail(p, lam, 398)
    assert value < I(upper)
    assert value+I(allowance) < I('7.6e-12')
    print(f'rho={p}, lambda={lam}, certified tail < {upper}')
assert I('1.9642e-11')+I('7.6e-12') < I('2.72513e-11')

# Compute correlations combinatorially, without floating-point Fourier transforms.
cases = 0
for prime, dim in [(3, 2), (7, 1)]:
    group = list(product(range(prime), repeat=dim))
    size = len(group)
    for mask in range(1 << size):
        A = {x for j, x in enumerate(group) if mask >> j & 1}
        if not A or len(A) == size:
            # Empty/full subsets give the exact variance-zero equality.
            assert len(A) in (0, size)
            cases += 1
            continue
        counts = [sum(tuple((x[j]+u[j]) % prime for j in range(dim)) in A
                      for x in A) for u in group]
        assert sum(counts) == len(A)**2
        exact_second = Fraction(sum(c*c for c in counts), size**3)
        p_exact = Fraction(len(A), size)
        if p_exact in (Fraction(1, prime), Fraction(prime-1, prime)):
            # sin(pi/q) cancels exactly; this includes subgroup equality cases.
            exact_bound = p_exact**4 + Fraction(1, prime**2)*p_exact*(1-p_exact)
            assert exact_second <= exact_bound
        else:
            bound = second_bound(I(len(A))/size, prime)
            assert I(exact_second.numerator)/exact_second.denominator < bound
        cases += 1
assert cases == 640
print(f'Passed period comparison and {cases} exhaustive finite-subset cases.')
