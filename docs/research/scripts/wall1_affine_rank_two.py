"""Collinear-input component bounds, not a complete selected-history certificate."""
from fractions import Fraction as F
from itertools import combinations, product
from math import comb, factorial
from pathlib import Path
import runpy
from wall1_affine_circuit_components import multiply, exponential, stirling, correction_bound


def finite_checks():
    q = 5
    laws = [tuple((a*y+b) % q for y in range(q)) for a,b in product(range(q), repeat=2)]
    checked = 0
    for mask in range(32):
        fibers = [{i,(i+1) % q} if mask >> i & 1 else {i} for i in range(q)]
        rho = [F(len(b),q) for b in fibers]
        hits = [tuple(int(x in b) for x,b in zip(law,fibers)) for law in laws]
        P, R = {}, {}
        for bits in range(1 << q):
            indices = [i for i in range(q) if bits >> i & 1]
            P[bits] = F(sum(all(h[i] for i in indices) for h in hits),len(hits))
            R[bits] = F(1)
            for i in indices:
                R[bits] *= rho[i]
        epsilon3 = factorial(3)*sum(P[sum(1 << i for i in t)]+R[sum(1 << i for i in t)]
                                    for t in combinations(range(q),3))
        for h in (4,5):
            aggregate = F(0)
            for support in combinations(range(q),h):
                envelope = F(0)
                for b in range(1 << h):
                    if b.bit_count() < 3:
                        continue
                    bits = sum(1 << support[j] for j in range(h) if b >> j & 1)
                    outside = sum(1 << support[j] for j in range(h) if not b >> j & 1)
                    envelope += abs(P[bits]-R[bits])*R[outside]
                aggregate += factorial(h)*envelope
                for e in ((1,)*h, (2,)+(1,)*(h-1), (2,)*h):
                    actual = F(0)
                    baseline = F(1)
                    for i,degree in zip(support,e):
                        t=rho[i]
                        baseline *= t*(1-t)**degree+(1-t)*(-t)**degree
                    for hit in hits:
                        value=F(1)
                        for i,degree in zip(support,e):
                            value *= (hit[i]-rho[i])**degree
                        actual += value/len(hits)
                    assert abs(actual-baseline) <= envelope
                    checked += 1
            eta=(2**h-1-h-comb(h,2))*q**(h-3)*epsilon3
            assert aggregate <= eta
    print(f'Passed {checked} exact collinear component corrections and 64 aggregate bounds.')


if __name__ == '__main__':
    finite_checks()
    s=runpy.run_path(str(Path(__file__).with_name('wall1_affine_nullity_one.py')))
    I,mu,k,q=s['I'],s['mu'],s['k'],s['q']
    eps=s['epsilon']
    eta={h:(2**h-1-h-comb(h,2))*q**(h-3)*eps[3] for h in range(4,k+1)}
    combined={j:eps.get(j,I(0))+eta.get(j,I(0)) for j in range(3,k+1)}
    total=correction_bound(mu,combined,k)/(I('.280')*mu**k)
    S=stirling(k)
    def activity(values):
        return [sum((values.get(j,I(0))*S[i][j] for j in range(3,i+1)),I(0))
                /factorial(i) for i in range(k+1)]
    free=[I(0),I(0)]+[mu/factorial(i) for i in range(2,k+1)]
    extra=factorial(k)*multiply(multiply(exponential(free),exponential(activity(eps))),
                               exponential(activity(eta),start=1))[k]/(I('.280')*mu**k)
    assert total < I('2.468e-54')
    print('All circuit and rank-two component corrections / (rho mu^12) < 2.468e-54')
    assert extra < I('4.506e-98')
    print('Extra activated rank-two component terms / (rho mu^12) < 4.506e-98')
    print('UNBOUNDED: connected components with rank >=3 and nullity >=2; later histories.')
