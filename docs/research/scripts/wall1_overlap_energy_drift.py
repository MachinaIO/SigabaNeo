"""Exact overlap-energy and sharp moment checks for actual marked lattice balls."""
from collections import Counter
from fractions import Fraction as F
from itertools import product


def bound(r, eta, k):
    assert 0 <= r <= 1 and 0 <= eta <= r*(1-r)
    if r in (0, 1):
        assert eta == 0
        return r**k
    b = r-eta/(1-r)
    return (eta+(1-r)**2*b**k)/(eta+(1-r)**2)


def check_lattice(q, dim, radius2):
    group = list(product(range(q), repeat=dim)); h = len(group)
    norm = lambda v: sum(min(x,q-x)**2 for x in v)
    A = {v for v in group if norm(v)>radius2}
    C = {v for v in group if norm(v)>radius2-1}
    p, r = F(len(A),h), F(len(C),h)
    add = lambda v,u: tuple((x+y)%q for x,y in zip(v,u))
    sub = lambda v,u: tuple((x-y)%q for x,y in zip(v,u))
    counts = [sum(add(v,u) in C for v in A) for u in group]
    assert sum(counts) == len(A)*len(C)
    ea = Counter(sub(v,w) for v in A for w in A)
    ec = Counter(sub(v,w) for v in C for w in C)
    second = F(sum(x*x for x in counts),h**3)
    assert second == F(sum(c*ec[d] for d,c in ea.items()),h**3)
    if not p: return 1
    eta = second/p**2-r**2
    lower=max(F(0),(p+r-1)/p)
    assert eta <= (r-lower)*(1-r)
    for k in (2,4,24):
        moment = sum(F(x,len(A))**k for x in counts)/h
        assert r**k <= moment <= bound(r,eta,k) <= r
    return 4


def main():
    checks = sum(check_lattice(q,d,F(b,2)) for q in (3,5,7)
                 for d in (1,2) for b in range(2,19))
    # Test majorant pointwise, including x below its tangency point.
    for k in (2,3,4,24):
        for b in (F(j,10) for j in range(10)):
            slope=k*b**(k-1)
            curvature=(1-b**k-slope*(1-b))/(1-b)**2
            for x in (F(j,20) for j in range(21)):
                assert x**k <= b**k+slope*(x-b)+curvature*(x-b)**2
                checks += 1
    # Exact extremizers for the two-moment problem.
    for r in (F(j,10) for j in range(1,10)):
        for t in (F(j,10) for j in range(11)):
            eta=t*r*(1-r); b=r-eta/(1-r)
            mass=eta/(eta+(1-r)**2)
            assert mass+(1-mass)*b == r
            assert mass*(1-r)**2+(1-mass)*(b-r)**2 == eta
            assert mass+(1-mass)*b**24 == bound(r,eta,24)
            checks += 3
    # Rank-400 rectangular lattices whose distance sublevel sets depend on
    # one coordinate. Inactive mesh epsilon has 399 marked coordinates.
    for q in (5,3329):
        inactive=399*(F(q//2,100*q))**2
        assert inactive < F(1,100)
        p=F(q-3,q);r=F(q-1,q)
        eta=F(3,q*q*(q-3))
        exact=F(3,q)+F(q-3,q)*F(q-4,q-3)**24
        assert exact == bound(r,eta,24)
        print('rank400 q,p,r,eta,E(Y^24):',q,float(p),float(r),float(eta),float(exact))
        checks += 2
    r=F(7,25)
    for a in (F(11,10),F(13,10),F(41,25)):
        budget=(1-r)**2*(a**(-24)-r**24)
        assert budget>0 and a**24*bound(r,budget,24)<=1
        print('conditional r=.28 shell a / sufficient eta:',float(a),float(budget))
        checks += 1
    print('Passed exact checks:', checks)

if __name__ == '__main__': main()
