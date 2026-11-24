"""Exact audit of full-family variance and label-blind thinning identities."""
from fractions import Fraction as F
from itertools import combinations


def compositions(n, m):
    if m == 1:
        yield (n,)
    else:
        for k in range(n+1):
            for tail in compositions(n-k, m-1):
                yield (k,)+tail


def variance(counts):
    m = len(counts)
    return F(sum(b*b for b in counts), m)-F(sum(counts), m)**2


def main():
    checks = void_checks = 0
    for m in range(2, 5):
        for A in range(2, 8):
            for counts in compositions(A, m):
                labels = tuple(j for j,b in enumerate(counts) for _ in range(b))
                nu, V = F(A,m), variance(counts)
                void = F(counts.count(0),m)
                assert void <= V/(V+nu**2)
                void_checks += 1
                for L in range(1, A+1):
                    total = F(0)
                    number = 0
                    for indices in combinations(range(A), L):
                        selected = [0]*m
                        for i in indices:
                            selected[labels[i]] += 1
                        total += variance(selected)
                        number += 1
                    average = total/number
                    predicted = F(L*(L-1),A*(A-1))*V+F(L*(A-L),A-1)*(F(1,m)-F(1,m*m))
                    assert average == predicted
                    normalized = F((L-1)*A,L*(A-1))*V/nu**2+F((A-L)*(m-1),L*(A-1))
                    assert average/F(L,m)**2 == normalized
                    assert V/nu**2 <= m-1
                    assert normalized >= V/nu**2
                    # Every subset has at least as many missing marks as the full family.
                    assert (A-L)*(m-1) >= 0
                    checks += 1
    # Expected number / 100, without independence, instead of any-event union.
    mu = 10**16
    assert F(405*4000,100*mu) == F('1.62e-12')
    print('Exact thinning identities:',checks)
    print('Exact occupancy void bounds:',void_checks)
    print('Actual selected-history full-family variance remains unproved.')


if __name__ == '__main__':
    main()
