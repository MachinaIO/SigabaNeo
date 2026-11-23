"""Exact finite checks for wall1_projected_occupancy.md; no external packages."""
from fractions import Fraction as F
from math import gcd, isqrt

q = 17
cases = 0
heights = set()
for u in range(q):
    # A vector of length q exists; hence this search contains every shortest vector.
    candidates = [(x*x+a*a, x, a) for x in range(-q, q+1)
                  for a in range(-q, q+1)
                  if (x or a) and x*x+a*a <= q*q and (x-a*u) % q == 0]
    s2, x, a = min(candidates)
    assert a != 0
    if a < 0:
        x, a = -x, -a
    heights.add(a)
    m0 = x-a*u
    assert gcd(a, m0//q) == 1  # primitive winner in the window basis
    # Scalar coordinates perpendicular to (x,a): (z,j) -> (a*z-x*j)/sqrt(s2).
    projected_step_numerator = gcd(a*q, a*u-x)
    assert projected_step_numerator == q
    # R=(q/a)Z, T=(1/a)Z, G=a^2/s2; T/R labels are k mod q.
    for b2 in (F(0), F(1, 4), F(1), F(4)):
        bound = b2*s2
        limit = isqrt(bound.numerator//bound.denominator)
        counts = [0]*q
        for k in range(-limit, limit+1):
            assert F(k*k, s2) <= b2
            counts[k % q] += 1
        for z in range(q):
            r = (a*z) % q
            direct_distance2 = F(min(r, q-r)**2, s2)
            assert (counts[r] > 0) == (direct_distance2 <= b2)
        N = sum(counts)
        J = sum(n*n for n in counts)
        void = F(counts.count(0), q)
        assert N > 0 and void <= 1-F(N*N, q*J)
        if 727*q*J <= 1000*N*N:
            assert void <= F(273, 1000)
        # Independent ordered-pair count for equation (5).
        points = range(-limit, limit+1)
        assert J == sum((y-z) % q == 0 for y in points for z in points)
        cases += 1
assert heights == {1, 2, 3}
print(f"Passed {cases} exact branch/radius cases; winner heights {sorted(heights)}.")
