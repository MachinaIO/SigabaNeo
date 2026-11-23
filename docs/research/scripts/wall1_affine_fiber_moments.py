"""Exact tests for input-fiber aggregation; no selected-history simulation."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations_with_replacement, product
from math import factorial
from wall1_centered_affine_cancellation import prod, rank


def check_fixture(points, m, q):
    assert len(set(points)) == len(points)
    d = len(points[0])-m
    Q = q**m
    all_inputs = sorted({z[m:] for z in points})
    laws = []
    for coefficients in product(range(q), repeat=m*(d+1)):
        laws.append({y: tuple(sum(coefficients[i*(d+1)+j]*u
                                 for j, u in enumerate((1, *y))) % q
                              for i in range(m)) for y in all_inputs})
    for mask in range(1, 1 << len(points)):
        fibers = defaultdict(set)
        for j, z in enumerate(points):
            if mask >> j & 1:
                fibers[z[m:]].add(z[:m])
        ys = sorted(fibers)
        rho = [F(len(fibers[y]), Q) for y in ys]
        mu = sum(rho)
        hits = [[int(law[y] in fibers[y]) for y in ys] for law in laws]
        joint = {}
        for submask in range(1 << len(ys)):
            indices = [i for i in range(len(ys)) if submask >> i & 1]
            rows = [(1, *ys[i]) for i in indices]
            r = rank(rows, q)
            count = 0
            for outputs in product(*(fibers[ys[i]] for i in indices)):
                full = [(*rows[j], *x) for j, x in enumerate(outputs)]
                count += rank(full, q) == r
            joint[submask] = F(count, Q**r)
            direct = F(sum(all(h[i] for i in indices) for h in hits), len(hits))
            assert joint[submask] == direct
            if r == len(indices):
                assert direct == prod(rho[i] for i in indices)
        variance = sum((F(sum(h))-mu)**2 for h in hits)/len(hits)
        assert variance == sum(p*(1-p) for p in rho)
        for k in (2, 4, 8):
            expanded = F(0)
            for indices in combinations_with_replacement(range(len(ys)), k):
                multiplicities = [indices.count(i) for i in range(len(ys))]
                support = [i for i, e in enumerate(multiplicities) if e]
                term = F(0)
                for submask in range(1 << len(support)):
                    selected = {support[j] for j in range(len(support)) if submask >> j & 1}
                    coefficient = prod(
                        ((1-rho[i])**multiplicities[i]-(-rho[i])**multiplicities[i]
                         if i in selected else (-rho[i])**multiplicities[i]) for i in support)
                    term += coefficient*joint[sum(1 << i for i in selected)]
                if len(support) == 1:
                    i = support[0]
                    assert term == rho[i]*(1-rho[i])**k+(1-rho[i])*(-rho[i])**k
                rows = [(1, *ys[i]) for i in support]
                r = rank(rows, q)
                if r == len(support)-1:
                    circuit = [support[j] for j in range(len(support))
                               if rank(rows[:j]+rows[j+1:], q) == r]
                    free = [i for i in support if i not in circuit]
                    def beta(i):
                        e, p = multiplicities[i], rho[i]
                        return p*(1-p)**e+(1-p)*(-p)**e
                    independent = prod(beta(i) for i in support)
                    delta = (joint[sum(1 << i for i in circuit)]
                             - prod(rho[i] for i in circuit))
                    expected_delta = (delta*prod(beta(i) for i in free)
                                      * prod((1-rho[i])**multiplicities[i]
                                             - (-rho[i])**multiplicities[i] for i in circuit))
                    assert term-independent == expected_delta
                multiplicity = factorial(k)
                for e in multiplicities:
                    multiplicity //= factorial(e)
                expanded += multiplicity*term
            actual = sum((F(sum(h))-mu)**k for h in hits)/len(hits)
            assert expanded == actual
        # The rank-one part of the older point-tuple majorant cannot be made small.
        C, Y = mask.bit_count(), len(ys)
        for k in (2, 4, 8):
            power_sum = sum(len(fibers[y])**k for y in ys)
            assert power_sum*Y**(k-1) >= C**k
            rank_one = F((Q-1)**(k-1)*power_sum, C**k)
            assert rank_one >= F(Q-1, Y)**(k-1)
    return (1 << len(points))-1


if __name__ == '__main__':
    total = 0
    for points, m, q in [
        (list(product(range(3), repeat=2)), 1, 3),
        (list(product(range(2), repeat=3)), 2, 2),
        ([(0, 0), (1, 0), (1, 1), (2, 2)], 1, 5),
        ([(0, 0, 0), (1, 0, 0), (0, 1, 0), (1, 1, 0),
          (0, 2, 0), (2, 2, 0), (1, 0, 1)], 1, 3),
    ]:
        cases = check_fixture(points, m, q)
        total += cases
        print(f'Passed {cases} fixed candidate sets over F_{q}, {m} output rows.')
    assert (3329**400-1)**7 > 10**6977*3329**(117*7)
    print(f'Passed all {total} grouped moment and rank-one barrier checks.')
    print('At draw 13 the old normalized rank-only majorant is necessarily > 10^6977.')
