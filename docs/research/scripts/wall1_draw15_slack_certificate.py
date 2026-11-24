"""Draw15 fixed-radius certificate on a determinant-slack gate.

All incidence counts use the original ungated matrix law. The gate only
licenses pointwise projection domination; its complement is not bounded.
"""
from math import factorial
from wall1_draw15_incidence_transfer import geometry_state
from wall1_general_two_relations import draw14_bounds
from wall1_factorial_cumulants import cumulant_errors, difference_weights
from wall1_affine_circuit_components import exponential


def main():
    s = geometry_state()
    I, iv, g = s['I'], s['iv'], s['geometry']
    q, m, n = s['q'], s['m'], s['N']
    slack = I(12)
    radius = iv.sqrt((s['radius']**2+2)*slack**(I(2)/506)-2)
    lower = g['candidate_lower'](n, radius)/q**m
    upper = 2*g['volume'][n]*(radius**2+I(n)/4)**(I(n)/2)/q**m
    rho = 2*g['volume'][m]*(radius**2+I(m)/4)**(I(m)/2)/q**m
    epsilon = {}
    for j in range(3,25):
        beta = I((j-1)*n)/(2*j*radius**2)
        count = (g['affine_triple_count_upper'](beta,radius,n) if j==3 else
                 q**(j-2)*iv.exp(j*beta*radius**2)*g['relation_theta_upper'](j,beta)**n)
        epsilon[j] = count/q**(m*(j-1))
    s.update(radius=radius,mu=upper,rho_max=rho,epsilon=epsilon)
    print('Slack gate C15>=12; fixed raw radius:',radius,flush=True)
    print('Mean lower:',lower,'mean upper:',upper,flush=True)
    assert lower.a>I('58.5115').b
    t, order = 12, 24
    denominator = sum((lower**j/factorial(j) for j in range(t+1)),I(0))
    baseline = 1/(I('.280')*denominator)
    assert baseline.b<I('8.49e-13').a
    print('Reference upper:',baseline,flush=True)
    _, full, _ = draw14_bounds(geometry_state=s)
    print('Complete incidence cover through24 finished.',flush=True)
    errors = cumulant_errors(upper,rho,q,full,order)
    series = [I(0),I(0)]+[(full.get(j,I(0))+errors[j])/factorial(j)
                          for j in range(2,order+1)]
    corrections = exponential(series,start=1)
    # The reference kernel may use the exact (deterministic) mean mu.
    # Bound its finite-difference weights uniformly over lower<=mu<=upper.
    weights = [sum((I(abs(c.numerator))/c.denominator*upper**d
                    for d,c in enumerate(poly)),I(0))
               for poly in difference_weights(t)]
    error = sum((weights[j]*corrections[j] for j in range(2,order+1)),I(0))
    error /= I('.280')*denominator**2
    total = baseline+error
    assert error.b < I('2.251e-13').a
    assert total.b < I('1.074e-12').a
    print('Transferred correction upper:',error,flush=True)
    print('Gated void-exit upper:',total,flush=True)
    print('Certified Pr(C15>=12, b15>=.280) <1.074e-12.',flush=True)
    print('Gate complement Pr(C15<12) is NOT bounded.',flush=True)
    print('No full BKZ or later-history certificate is asserted.',flush=True)


if __name__=='__main__':
    main()
