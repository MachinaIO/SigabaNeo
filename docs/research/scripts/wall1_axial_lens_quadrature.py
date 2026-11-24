"""Exact arithmetic constants for axial continuum-slice lens quadrature."""
from fractions import Fraction as F

rho2=(F(11,10)*F('32.18553'))**2-2
first=(F(630)/rho2)**2/4
second=(F(1512,3329))**2/4
assert first<F(8,125) and second<F(8,125)
assert 503*F(2,5)>1
print('rho² lower endpoint:',rho2)
print('Axial relative-excess cap, numerator-one case:',float(first))
print('Axial relative-excess cap, numerator-q case:',float(second))
print('Both caps are strictly below 0.064 by exact rational comparison.')
print('Actual transverse lattice-slice counts remain uncontrolled.')
