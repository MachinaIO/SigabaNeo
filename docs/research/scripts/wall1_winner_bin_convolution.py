"""Exact event-restricted convolution checks; no conditional uniformity."""
from fractions import Fraction as F
from itertools import product


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


if __name__ == '__main__':
    main()
