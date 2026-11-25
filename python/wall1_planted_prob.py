"""Exact rational certificates in base-two logarithms for the all-prefix obstruction."""
from fractions import Fraction as F
from math import ceil, factorial, floor

POWERS = {2: F(4, 3), 3: 2, 4: 4, 5: 8, 6: F(64, 3), 7: 64, 8: 256}


def hermite_power(h, pi_bound):
    if h in POWERS:
        return F(POWERS[h])
    j = h // 2
    if h % 2 == 0:
        return (2 / pi_bound)**h * factorial(j + 1)**2
    # Gamma(j+5/2) = sqrt(pi) (2j+4)! / (4^(j+2) (j+2)!).
    ratio = F(factorial(2*j+4), 4**(j+2) * factorial(j+2))
    return 2**h * ratio**2 / pi_bound**(h-1)


def certificate(m):
    beta, q, n = 406, 3329, 512
    N = n + m
    d, k = N + 1, N + 1 - beta
    assert 9*N+1 < 128**2
    assert 2**116 < q**10 < 2**118
    for h in range(2, beta+1):
        # Use an integer power for small h where rounding loses precision.
        power = hermite_power(h, F(22, 7))
        if h < 16:
            assert power**80 >= 2**(h*(h-1))
        else:
            assert power >= 2**ceil(F(h*(h-1), 80))
    cutoff = F(116*m*k, 10*d) + F(k*beta, 160)
    prefix = F(0)
    bounds = {0: prefix}
    for j in range(1, k+1):
        h = N-j+1
        power = hermite_power(h, F(3))
        bits = power.numerator.bit_length() - power.denominator.bit_length() + 1
        cost = F(bits, 2*h)
        prefix += (F(118*m, 10)-prefix)/h + cost
        bounds[j] = prefix
    witness = 1 + max(1+bounds[k], 7+bounds[k-1])
    assert witness < cutoff
    print(m, d, k, ceil(witness), floor(cutoff))


if __name__ == '__main__':
    for samples in (188, 511, 512):
        certificate(samples)
