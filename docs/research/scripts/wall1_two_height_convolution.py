"""Exact finite checks of the nonlinear two-height conditional bound."""
from fractions import Fraction as F
from itertools import product


def main():
    delta = F(7,25)
    count = 0
    for n in range(1,7):
        for labels in product(range(3), repeat=n):
            a0 = {v for v in range(n) if labels[v] == 2}
            a1 = {v for v in range(n) if labels[v] >= 1}
            p0, p1 = F(len(a0),n), F(len(a1),n)
            hs = [F(sum((v+u)%n in a1 for v in a0),n) for u in range(n)]
            assert sum(hs)/n == p0*p1
            assert all(h <= p0 for h in hs)
            for k in (1,2,24):
                assert sum(h**k for h in hs)/n <= p0**k*p1
                capped = sum(min(F(1),(h/delta)**k) for h in hs)/n
                bound = p0*p1/delta * min(F(1),p0/delta)**(k-1)
                assert capped <= bound
                count += 1
    print(f'Passed {count} exact nested-set moment and capped convolution checks.')


if __name__ == '__main__':
    main()
