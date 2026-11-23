"""Exact Poisson polynomial certificates on the nonnegative integers.

This tests changing the certificate, not improving a dependent-law bound.
No existing production envelope is modified.
"""
from fractions import Fraction as F
from math import factorial, prod
import mpmath as mp

MU = F('58.15006220912')
RHO = F('0.280')
TARGET = F('3.922e-12')


def falling_coefficients(roots):
    """Integer coefficients of prod(x-root) in the falling-factorial basis."""
    coefficients = [1]
    for root in roots:
        new = [0] * (len(coefficients) + 1)
        for k, value in enumerate(coefficients):
            new[k] += (k-root)*value
            new[k+1] += value
        coefficients = new
    return coefficients


def expectation(roots, mu=MU):
    coefficients = falling_coefficients(roots)
    return sum((value*mu**k for k,value in enumerate(coefficients)), F(0))


def reference(starts, mu=MU):
    roots = [x for a in starts for x in (a,a+1)]
    return expectation(roots,mu)/prod(roots)


def initial_pairs(t):
    # Roots of C_t(x-1;mu), the Poisson optimal square kernel.
    mp.mp.dps = 50
    mu = mp.mpf(MU.numerator)/MU.denominator
    jacobi = mp.matrix(t)
    for k in range(t):
        jacobi[k,k] = mu+k+1
        if k:
            jacobi[k,k-1] = jacobi[k-1,k] = mp.sqrt(mu*k)
    roots = mp.eigsy(jacobi,eigvals_only=True)
    return [int(mp.floor(root)) for root in roots]


def optimize_pairs(t):
    starts = initial_pairs(t)
    value = reference(starts)
    steps = 0
    while True:
        changed = False
        for k, old in enumerate(starts):
            candidates = []
            for shift in (-2,-1,0,1,2):
                a = old+shift
                if a < 1 or (k and a <= starts[k-1]+1) or (k+1<t and a+1 >= starts[k+1]):
                    continue
                new = starts[:]
                new[k] = a
                candidates.append((reference(new),a))
            best,a = min(candidates)
            if best < value:
                starts[k],value = a,best
                steps += 1
                changed = True
        if not changed:
            return starts,value,steps


def quadrature(starts,mu=MU):
    """Exact degree-2t moment match on 0 and all the paired roots."""
    nodes = [0]+[x for a in starts for x in (a,a+1)]
    weights = []
    for x in nodes:
        others = [y for y in nodes if y != x]
        weights.append(expectation(others,mu)/prod(x-y for y in others))
    assert sum(weights) == 1
    # Lagrange interpolation already proves all these identities; check anyway.
    falling = [1]*len(nodes)
    for k in range(len(nodes)):
        assert sum((w*v for w,v in zip(weights,falling)),F(0)) == mu**k
        falling = [v*(x-k) for x,v in zip(nodes,falling)]
    assert weights[0] == reference(starts,mu)
    return weights


def difference_expectations(starts,mu=MU):
    roots = [x for a in starts for x in (a,a+1)]
    coefficients = [F(c,prod(roots)) for c in falling_coefficients(roots)]
    weights = [sum((c*F(factorial(h),factorial(h-j))*mu**(h-j)
                    for h,c in enumerate(coefficients) if h>=j),F(0))
               for j in range(len(coefficients))]
    assert weights[0] == reference(starts,mu)
    return coefficients,weights


def main():
    for t in (8,9,10,11,12):
        starts,value,steps = optimize_pairs(t)
        weights = quadrature(starts)
        dual = all(w>=0 for w in weights)
        assert dual, 'Do not claim global optimality without nonnegative quadrature'
        # The same optimum holds at odd degree 2t+1. Its interpolation
        # remainder is c*x*prod(x-root), with c>=0 for any polynomial
        # nonnegative on all nonnegative integers. The nodal polynomial
        # is pointwise nonnegative there (adjacent root pairs).
        nodes = [0]+[x for a in starts for x in (a,a+1)]
        nodal_expectation = expectation(nodes)
        assert nodal_expectation > 0
        degree = 2*t+1
        falling_values = [prod(x-k for k in range(degree)) for x in nodes]
        assert MU**degree-sum((w*v for w,v in zip(weights,falling_values)),F(0)) == nodal_expectation
        assert (value/RHO < TARGET) == (t == 12)
        square = 1/sum((MU**k/factorial(k) for k in range(t+1)),F(0))
        print('degree',2*t,'pairs',starts,'descent_steps',steps,flush=True)
        print('  optimal_integer_reference / rho',float(value/RHO),
              'optimal_square / rho',float(square/RHO),
              'ratio',float(value/square), 'dual_positive',dual,flush=True)
        print('  exact_decision_meets_target',value/RHO < TARGET,
              'minimum_dual_weight',float(min(weights)),flush=True)
        print('  same_optimum_at_odd_degree',degree,
              'positive_interpolation_remainder',True,flush=True)
    from wall1_factorial_cumulants import difference_weights
    starts,_,_ = optimize_pairs(12)
    coefficients,new_weights = difference_expectations(starts)
    old_weights = difference_weights(12)
    old_normalizer = F(factorial(12)**2,1)/(RHO*MU**24)
    print('degree24_falling_coefficients', [str(c) for c in coefficients])
    print('degree24_poisson_difference_weights', [str(w) for w in new_weights])
    for j in range(3,25):
        old = old_normalizer*sum((abs(c)*MU**k for k,c in enumerate(old_weights[j])),F(0))
        new = abs(new_weights[j])/RHO
        assert new_weights[j] > 0
        if j >= 17:
            assert F('0.6309') < new/old < F('0.6572')
        print('difference_order',j,'new_abs_over_old_majorant',float(new/old),
              'new_weight_sign',int(new_weights[j]>0)-int(new_weights[j]<0))
    # These are from the Part 384 outward-interval component log, and are only
    # a diagnostic snapshot, not recomputed proof data.
    logs = {18:17.333547946083172,19:51.234123252848125,
            20:85.23858928292798,21:119.06136689180402,
            22:153.08356260443578,23:189.80060548862087,
            24:226.8469476746379}
    budget_log = mp.log10(mp.mpf('2.6629e-12'))
    for h,value in logs.items():
        print('snapshot_size',h,'log10_envelope',value,
              'orders_above_entire_residual_budget',float(value-budget_log))


if __name__ == '__main__':
    main()
