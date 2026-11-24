"""Exact raw square baseline; actual-law transfer uses the draw15 certificate."""
import contextlib
import io
from fractions import Fraction as F
from math import comb
from pathlib import Path
import runpy

with contextlib.redirect_stdout(io.StringIO()):
    witness = runpy.run_path(str(Path(__file__).with_name('wall1_draw15_lower_witness.py')))
square = witness['mul'](witness['q'], witness['q'])
stirling = witness['S']
coefficients = [sum(square[i] * stirling[i][j] for i in range(j, 21))
                for j in range(21)]
# This coefficient comparison transfers the already certified absolute
# factorial-moment discrepancy, not merely the signed polynomial error.
assert all(abs(coefficients[j]) <= abs(witness['a'][j]) for j in range(2, 21))
cap = F('9.287185')
bernstein = []
for interval in range(40):
    lo, hi = cap * interval / 40, cap * (interval + 1) / 40
    shifted = [sum(coefficients[j] * comb(j, i) * lo**(j-i) * (hi-lo)**i
                   for j in range(i, 21)) for i in range(21)]
    bernstein.extend(sum(shifted[i] * F(comb(k, i), comb(20, i))
                         for i in range(k+1)) for k in range(21))
assert max(bernstein) == 1
assert min(bernstein) > F('0.00020014984')
endpoint = sum(c * cap**j for j, c in enumerate(coefficients))
assert endpoint < F('0.00020015')
assert coefficients[0] == 1
print('840 exact Bernstein coefficients: 0.00020014984 < Poisson square baseline <= 1.')
print('All 19 nontrivial factorial coefficients dominated by lower-witness coefficients.')
print('With the existing draw15 discrepancy <1e-25: 0.00020014983 < E[Q(Z)^2] < 1+1e-25.')
print('Upper-mean substitution is invalid: mean zero gives baseline 1; cap gives <0.00020015.')
print('No mixed selected moment or history exit estimate is certified here.')

# The same centered ball has a usable lower count, already used for draw14.
# Evaluate it at draw15 rather than treating the mean as arbitrarily small.
from wall1_draw15_incidence_transfer import geometry_state
state = geometry_state()
mean_lower = state['geometry']['candidate_lower'](state['N'], state['radius']) / state['q']**state['m']
assert mean_lower.a > state['I']('4.5740608').b
lower_cap = F('4.5740608')
tight_bernstein = []
for interval in range(40):
    lo = lower_cap + (cap-lower_cap) * interval / 40
    hi = lower_cap + (cap-lower_cap) * (interval+1) / 40
    shifted = [sum(coefficients[j] * comb(j, i) * lo**(j-i) * (hi-lo)**i
                   for j in range(i, 21)) for i in range(21)]
    tight_bernstein.extend(sum(shifted[i] * F(comb(k, i), comb(20, i))
                               for i in range(k+1)) for k in range(21))
assert min(tight_bernstein) > F('0.00020014984')
assert max(tight_bernstein) + F('1e-25') < F('0.015595758')
assert F(1) / F('0.015595758') > 64
print('Draw15 mean lower interval:', mean_lower)
print('840 additional exact Bernstein coefficients certify E[Q(Z)^2] <0.015595758.')
print('This improves the raw-only upper certificate by a factor exceeding64.')
