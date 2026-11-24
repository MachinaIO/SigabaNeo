"""Exact rational checks of the fixed-rectangle shared-u moment identity.

The replicas here only expand powers of a conditional finite average.
No independence of actual selected histories or of different heights is used.
Set ell^2=q^2 and theta=q^2*log(base), so all exponential weights are
rational powers of base. This tests the prefactor sign and all averages.
"""
from fractions import Fraction as F
from itertools import product


def centered(x,q):
    return (x+q//2)%q-q//2


def check(q,m,k,half,radius_sq):
    base=F(3,2)
    heights=tuple(range(-half,half+1))
    points=tuple(product(range(q),repeat=m))
    kernels=[]
    for u in range(q):
        kernels.append(sum((base**sum(centered(v+j*u,q)**2 for j in heights)
                            for v in range(q)),F(0))/q)
    prefactor=base**(sum(j*j for j in heights)-len(heights)*radius_sq)
    factored=prefactor**k*(sum((x**k for x in kernels),F(0))/q)**m
    direct=F(0)
    miss_moment=F(0)
    for u in points:
        energies={v:tuple(j*j+sum(centered(v[i]+j*u[i],q)**2
                                   for i in range(m)) for j in heights)
                  for v in points}
        misses=sum(all(e>radius_sq for e in es) for es in energies.values())
        miss_moment+=F(misses,len(points))**k
        for replicas in product(points,repeat=k):
            exponent=sum(sum(energies[v])-len(heights)*radius_sq for v in replicas)
            weight=base**exponent
            event=all(all(e>radius_sq for e in energies[v]) for v in replicas)
            assert int(event)<=weight
            direct+=weight
    direct/=q**(m*(k+1))
    miss_moment/=q**m
    assert direct==factored
    assert miss_moment<=factored
    # A different u per replica would incorrectly move the kth power outside.
    independent_u=prefactor**k*(sum(kernels,F(0))/q)**(m*k)
    return factored!=independent_u


def main():
    checks=0;shared_distinctions=0
    for q,m,k,half in ((3,2,2,1),(3,2,2,2),(5,1,3,1)):
        for radius_sq in (0,1,2):
            shared_distinctions+=check(q,m,k,half,radius_sq)
            checks+=1
    assert shared_distinctions>0
    print('Passed',checks,'exact shared-u moment, prefactor and indicator comparisons.')
    print('Incorrect independent-u factorization differs in',shared_distinctions,'cases.')


if __name__=='__main__':
    main()
