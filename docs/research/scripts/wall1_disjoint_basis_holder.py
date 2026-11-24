"""Exact finite checks for the disjoint-basis Holder completion lemma."""
from fractions import Fraction as F
from itertools import product


def checks():
    checked = 0
    for q, r in ((3, 2), (3, 3), (5, 2)):
        points = list(product(range(q), repeat=r))
        hyperplanes = [[x for x in points if sum(x) % q == c] for c in range(q)]
        for seed in range(1, 9):
            f = {x: F((sum((i+seed)*v*v for i, v in enumerate(x)) + seed) % 11, 10)
                 for x in points}
            for t in (1, 2):
                # Two disjoint bases of the same rank-t column space.
                first = [(1,)] if t == 1 else [(1, 0), (0, 1)]
                second = [(2,)] if t == 1 else [(1, 1), (1, 2)]
                columns = first + second + [(0,)*t]
                offsets = [tuple((j+seed*i) % q for i in range(r))
                           for j in range(len(columns))]
                eta1 = max(sum((f[x] for x in h), F(0))/len(h) for h in hyperplanes)
                eta2 = max(sum((f[x]**2 for x in h), F(0))/len(h) for h in hyperplanes)
                total = F(0)
                count = 0
                for basis in product(hyperplanes[1], repeat=t):
                    value = F(1)
                    for b, offset in zip(columns, offsets):
                        x = tuple((sum(b[j]*basis[j][i] for j in range(t))+offset[i]) % q
                                  for i in range(r))
                        value *= f[x]
                    total += value
                    count += 1
                assert total/count <= eta2**t <= eta1**t
                checked += 1
    print(f'Passed {checked} exact disjoint-basis Holder checks, including affine offsets.')


def factor_checks():
    checked=0
    q=3;r0=2
    old=list(product(range(q),repeat=r0))
    for seed in range(1,5):
        f0={x:F((seed+sum((i+1)*v for i,v in enumerate(x)))%7,6) for x in old}
        g={x:F((x+seed)%5,4) for x in range(q)}
        eta0=max(sum((f0[x] for x in old if sum(x)%q==c),F(0))/q for c in range(q))
        for free in (1,2):
            for L in (2,3,4):
                rho=sum((v**L for v in g.values()),F(0))/q
                for c in range(q):
                    total=F(0)
                    for x in product(range(q),repeat=r0+free):
                        if sum(x)%q!=c:continue
                        value=f0[x[:r0]]
                        for y in x[r0:]:value*=g[y]
                        total+=value**L
                    assert total/q**(r0+free-1)<=eta0*rho**free
                    checked+=1
    print('Passed exact free-factor hyperplane moment checks:',checked)


if __name__ == '__main__':
    checks()
    factor_checks()
