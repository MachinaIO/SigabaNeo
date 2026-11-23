"""Bounds for direct sums of circuits only; connected higher-nullity blocks remain."""
from fractions import Fraction as F
from itertools import product
from math import factorial
from pathlib import Path
import runpy


def multiply(a, b):
    return [sum((a[j]*b[i-j] for j in range(i+1)), a[0]*0) for i in range(len(a))]


def exponential(a, start=0):
    assert a[0] == 0
    zero = a[0]*0
    power = [zero+1]+[zero]*(len(a)-1)
    result = [zero]*len(a)
    for r in range(len(a)):
        if r >= start:
            result = [x+y/factorial(r) for x, y in zip(result, power)]
        power = multiply(power, a)
    return result


def stirling(k):
    S = [[0]*(k+1) for _ in range(k+1)]
    S[0][0] = 1
    for i in range(1,k+1):
        for j in range(1,i+1):
            S[i][j] = j*S[i-1][j]+S[i-1][j-1]
    return S


def correction_bound(mu, epsilon, k, start=1):
    zero = mu*0
    S = stirling(k)
    free = [zero, zero]+[mu/factorial(i) for i in range(2,k+1)]
    active = [sum((epsilon.get(j, zero)*S[i][j] for j in range(3,i+1)), zero)
              /factorial(i) for i in range(k+1)]
    return factorial(k)*multiply(exponential(free), exponential(active, start))[k]


def finite_checks():
    # Two affine lines whose augmented spans form a direct sum over F_3.
    ys = [(t,0,0) for t in range(3)]+[(0,t,1) for t in range(3)]
    laws = [tuple((c[0]+sum(a*b for a,b in zip(c[1:], y))) % 3 for y in ys)
            for c in product(range(3), repeat=4)]
    tested = 0
    for mask in range(64):
        fibers = [{0, 1} if mask >> i & 1 else {0} for i in range(6)]
        rho = [F(len(b), 3) for b in fibers]
        mu = sum(rho)
        hits = [tuple(int(value in b) for value,b in zip(law,fibers)) for law in laws]
        deltas = []
        for block in (range(3),range(3,6)):
            joint = F(sum(all(h[i] for i in block) for h in hits),len(hits))
            independent = F(1)
            for i in block:
                independent *= rho[i]
            deltas.append(joint-independent)
        for e in ((1,)*6, (2,1,1,2,1,1), (2,)*6):
            block_moments = []
            for block in (range(3),range(3,6)):
                values = []
                for h in hits:
                    v = F(1)
                    for i in block:
                        v *= (h[i]-rho[i])**e[i]
                    values.append(v)
                block_moments.append(sum(values)/len(hits))
            whole = F(0)
            for h in hits:
                v = F(1)
                for i in range(6):
                    v *= (h[i]-rho[i])**e[i]
                whole += v/len(hits)
            assert whole == block_moments[0]*block_moments[1]
        for k in (6,8,12):
            actual = sum((F(sum(h))-mu)**k for h in hits)/len(hits)
            independent = F(0)
            for h in product(range(2), repeat=6):
                weight = F(1)
                for i in range(6):
                    weight *= rho[i] if h[i] else 1-rho[i]
                independent += weight*(F(sum(h))-mu)**k
            epsilon = {3: 6*sum(abs(delta) for delta in deltas)}
            assert abs(actual-independent) <= correction_bound(mu,epsilon,k)
            tested += 1
    print(f'Passed {tested} exact moment bounds for two independent circuit components.')


if __name__ == '__main__':
    finite_checks()
    s = runpy.run_path(str(Path(__file__).with_name('wall1_affine_nullity_one.py')))
    mu, I, k = s['mu'], s['I'], s['k']
    whole = correction_bound(mu,s['epsilon'],k)/(I('.280')*mu**k)
    higher = correction_bound(mu,s['epsilon'],k,start=2)/(I('.280')*mu**k)
    assert whole < I('2.468e-54')
    print('All direct-sum circuit corrections / (rho mu^12) < 2.468e-54')
    assert higher < I('4.174e-96')
    print('Two or more activated circuit factors / (rho mu^12) < 4.174e-96')
    print('UNBOUNDED: supports with a connected component of nullity at least two.')
