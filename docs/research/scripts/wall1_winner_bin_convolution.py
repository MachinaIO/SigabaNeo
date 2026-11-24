"""Exact event-restricted convolution checks; no conditional uniformity."""
from fractions import Fraction as F
from itertools import product


def nested_budget_checks():
    checked = 0
    # Four nested threshold sets, hence two pointwise nested convolutions.
    for n in range(1,5):
        for labels in product(range(5), repeat=n):
            sets = [{v for v in range(n) if labels[v] >= t}
                    for t in (4,3,2,1)]
            hs = [[F(sum((v+u)%n in sets[2*j+1] for v in sets[2*j]),n)
                   for u in range(n)] for j in range(2)]
            budgets = [F(len(sets[2*j])*len(sets[2*j+1]),n*n)
                       for j in range(2)]
            assert all(hs[0][u] <= hs[1][u] for u in range(n))
            for mask in range(1 << n):
                masses = [sum((hs[j][u] for u in range(n)
                               if ((mask >> u) & 1) == j), F(0))/n
                          for j in range(2)]
                assert masses[0] <= budgets[0]
                assert sum(masses) <= budgets[1]
                checked += 1
    # Same profile in two bins: the old LP spends one budget twice.
    p = r = delta = F(1,4)
    alpha = F(1,2)
    slope = 1/delta
    independent_bin_bound = 2*min(alpha, slope*p*r)
    shared_budget_bound = slope*p*r
    exact_capped = F(1,4)  # A=C={0} in Z/4; only u=0 has a nonzero overlap.
    assert independent_bin_bound == F(1,2)
    assert shared_budget_bound == exact_capped
    print(f'Passed {checked} exact nested convolution budget checks.')
    print('Exact algebraic fixture: independent-bin bound 1/2, shared bound and value 1/4.')


def main():
    delta = F(7,25)
    count = 0
    wrong_product_refuted = False
    for n in range(1,6):
        for labels in product(range(3), repeat=n):
            a = {v for v in range(n) if labels[v] == 2}
            c = {v for v in range(n) if labels[v] >= 1}
            p, r = F(len(a),n), F(len(c),n)
            hs = [F(sum((v+u)%n in c for v in a),n) for u in range(n)]
            for k in (1,24):
                phi = lambda x: min(F(1),(x/delta)**k)
                beta = min(F(1),p*r/delta*min(F(1),p/delta)**(k-1))
                vals = [phi(h) for h in hs]
                for mask in range(1 << n):
                    indices = [u for u in range(n) if mask >> u & 1]
                    alpha = F(len(indices),n)
                    actual = sum((vals[u] for u in indices),F(0))/n
                    assert actual <= min(alpha*phi(p), beta)
                    wrong_product_refuted |= actual > alpha*beta
                    count += 1
    assert wrong_product_refuted
    print(f'Passed {count} exact event-restricted capped checks.')
    print('Multiplying the unconditional bound by event probability is refuted.')
    nested_budget_checks()


if __name__ == '__main__':
    main()
