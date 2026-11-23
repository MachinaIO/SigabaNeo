"""Concrete draw-14 moment frontier; this does not certify the full draw-14 bound."""
import contextlib
import io
from math import comb, factorial
from pathlib import Path
import runpy
from wall1_affine_circuit_components import exponential, multiply, stirling
from wall1_affine_rank_extensions import activity
from wall1_affine_square_certificate import central_square, coefficients, partial_exp

with contextlib.redirect_stdout(io.StringIO()):
    geometry = runpy.run_path(str(Path(__file__).with_name('wall1_affine_void_moments.py')))
I, iv = geometry['I'], geometry['iv']
q, m, N, inputs, t = 3329, 400, 518, 118, 12
order = 2*t
radius = iv.sqrt(I('1.21')*iv.exp(
    2*(I(386)*iv.ln(q)-iv.ln(geometry['volume'][506]))/506)-2)
mu = geometry['candidate_lower'](N, radius)/q**m
assert I('58.15006220912') < mu < I('58.15006220913')
baseline = 1/(I('.280')*partial_exp(mu, t))
previous = 1/(I('.280')*partial_exp(mu, t-1))
assert previous > I('4.5177e-12') > I('3.922e-12')
assert baseline < I('9.131e-13')

rho_max = 2*geometry['volume'][m]*(radius**2+I(m)/4)**(I(m)/2)/q**m
_, _, majorant = coefficients(mu, t)
normalizer = factorial(t)**2/(I('.280')*mu**order)
bernoulli = rho_max*normalizer*sum(
    (majorant[h]*comb(h, 2)*mu**(h-1) for h in range(2, order+1)), I(0))
assert bernoulli < I('1.120e-289')
print('Draw 14: kernel degree 11 reference bound exceeds the 3.922e-12 remaining budget.')
print('Kernel degree 12 / polynomial degree 24 reference bound < 9.131e-13.')
print('Bernoulli correction log10:', iv.log10(bernoulli))

epsilon = {}
for j in range(3, order+1):
    beta = I((j-1)*N)/(2*j*radius**2)
    compatible = (geometry['affine_triple_count_upper'](beta, radius, N) if j == 3 else
                  q**(j-2)*iv.exp(j*beta*radius**2)
                  * geometry['relation_theta_upper'](j, beta)**N)
    beta0 = I(N)/(2*radius**2)
    scale = iv.sqrt(iv.pi/beta0)
    dependent_inputs = ((q**(j-1)-1)//(q-1)*iv.exp(j*beta0*radius**2)
                        * (1+scale)**(j*m+(j-2)*inputs)
                        * geometry['relation_theta_upper'](2, beta0)**inputs)
    epsilon[j] = compatible/q**(m*(j-1))+dependent_inputs/q**(m*j)

central = central_square(t)
assert all(a+b <= order for (a, b) in central)
central_majorants = [sum((I(abs(c.numerator))/c.denominator*mu**b
                         for (a, b), c in central.items() if a == j), I(0))
                     for j in range(order+1)]
S = stirling(order)
free = [I(0), I(0)]+[mu/factorial(i) for i in range(2, order+1)]
free_exp = exponential(free)


def transfer(activities):
    active = [sum((activities.get(j, I(0))*S[i][j] for j in range(3, i+1)), I(0))
              /factorial(i) for i in range(order+1)]
    corrections = multiply(free_exp, exponential(active, start=1))
    return normalizer*sum((central_majorants[j]*factorial(j)*corrections[j]
                           for j in range(3, order+1)), I(0))


circuit_bound = transfer(epsilon)
assert circuit_bound < I('4.682e-48')
print('All circuit-only components, correction log10:', iv.log10(circuit_bound))
base = {h: epsilon[h]+(2**h-1-h-comb(h, 2))*q**(h-3)*epsilon[3]
        for h in range(3, order+1)}
extra = {h: sum((activity(h, r, q, mu, epsilon) for r in range(3, h-1)), I(0))
         for h in range(5, 10)}
for cap in (0, 5, 6, 7, 8, 9):
    activities = {h: base[h]+(extra.get(h, I(0)) if h <= cap else I(0)) for h in base}
    bound = transfer(activities)
    if cap == 8:
        assert bound < I('1.160e-15')
        assert baseline+bernoulli+bound < I('9.143e-13')
    if cap == 9:
        assert bound > I('0.00185')
    print('All circuits/rank-two plus higher-nullity supports through', cap,
          ': correction log10:', iv.log10(bound))
print('UNBOUNDED: omitted higher-rank connected supports through size 24 and later draws.')
