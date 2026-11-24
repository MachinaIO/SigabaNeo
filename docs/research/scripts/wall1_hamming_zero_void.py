"""Determinant-consistent, unit-generated zero-to-positive-void example."""
from fractions import Fraction as F
from itertools import combinations, product
from math import factorial


def odd_prime_checks():
    for q,rank,n,power,numerator in (
        (3,3,14,14,F(121,100)**14*(27*factorial(7))**2),
        (5,2,13,12,F(121,100)**13*F(25*135135,128)**2),
    ):
        # numerator/pi^power = (L^2)^n.
        assert numerator/F(22,7)**power > 2**n
        assert numerator/F(157,50)**power < 2**(n+1)
        assert F(4,3)**n > 2
        zero_mark = (0,)*rank
        marks = list(product(range(q),repeat=rank))
        neg = lambda v: tuple(-x%q for x in v)
        cols = [v for v in marks if v!=zero_mark and v<neg(v)]
        assert len(cols)==n-1
        assert set(cols)|{neg(v) for v in cols} == set(marks)-{zero_mark}
        units = [tuple(sign if j==i else 0 for j in range(n))
                 for i in range(n) for sign in (-1,1)]
        sphere2 = [tuple(a if k==i else b if k==j else 0 for k in range(n))
                   for i,j in combinations(range(n),2)
                   for a,b in product((-1,1),repeat=2)]

        def mark(z,u):
            return tuple((sum(z[i]*cols[i][a] for i in range(n-1))-z[-1]*u[a])%q
                         for a in range(rank))

        for u in marks:
            candidates = [z for z in units+sphere2 if mark(z,u)==zero_mark]
            w = min(candidates,key=lambda z:(sum(x*x for x in z),z))
            s2 = sum(x*x for x in w)
            assert s2==(1 if u==zero_mark else 2)
            if u==zero_mark:
                assert w[:-1]==(0,)*(n-1)
                continue
            hits = set()
            for z in [(0,)*n]+units:
                projected = F(sum(x*x for x in z))-F(sum(x*y for x,y in zip(z,w))**2,s2)
                assert projected in (F(0),F(1,2),F(1))
                if projected<1:
                    hits.add(mark(z,u))
            assert hits=={zero_mark,u,neg(u)}
            assert F(len(marks)-len(hits),len(marks))>F(7,25)
        print(f'Odd-prime q={q}, width={n}: all {len(marks)} winner branches passed.')


def main():
    # Standard rational pi bounds: 157/50 < pi < 22/7.
    # L2=(121/100)*(16*8!)^(1/8)/pi.
    numerator = F(121,100)**16*(16*factorial(8))**2
    assert numerator/F(22,7)**16 > 2**16
    assert numerator/F(157,50)**16 < 2**17
    assert F(4,3)**16 > 2
    # Therefore L2>2 and 1/2 < L2*2^(-1/16)-1 < 1.
    columns = [1,2,4,8]+[v for v in range(1,16) if v not in (1,2,4,8)]
    units = []
    for i in range(16):
        for sign in (-1,1):
            units.append(tuple(sign if j==i else 0 for j in range(16)))
    sphere2 = []
    for i,j in combinations(range(16),2):
        for a,b in product((-1,1),repeat=2):
            sphere2.append(tuple(a if k==i else b if k==j else 0 for k in range(16)))

    def mark(z,u):
        value = u if z[15]%2 else 0
        for x,c in zip(z[:15],columns):
            if x%2:
                value ^= c
        return value

    outgoing = []
    zero = (0,)*16
    for u in range(16):
        candidates = [z for z in units+sphere2 if mark(z,u)==0]
        w = min(candidates,key=lambda z:(sum(x*x for x in z),z))
        s2 = sum(x*x for x in w)
        assert s2 == (1 if u==0 else 2)
        if u==0:
            # All 16 incoming unit representatives remain horizontal and hit.
            assert w[:15] == (0,)*15
            outgoing.append(F(0))
            continue
        hits = set()
        for z in [zero]+units:
            dot = sum(x*y for x,y in zip(z,w))
            projected = F(sum(x*x for x in z))-F(dot*dot,s2)
            assert projected in (F(0),F(1,2),F(1))
            if projected < 1:  # Exact: 1/2 < actual radius squared < 1.
                hits.add(mark(z,u))
        assert hits == {0,u}
        outgoing.append(F(14,16))
    delta = F(7,25)
    for k in (1,24):
        assert sum(min(F(1),(p/delta)**k) for p in outgoing)/16 == F(15,16)
    print('All16 actual shortest-winner branches checked exactly.')
    print('Incoming void0; outgoing void7/8 on15 branches, zero onone branch.')
    print('Expected capped potential15/16 for k=1 and24; toy parameters only.')
    odd_prime_checks()


if __name__ == '__main__':
    main()
