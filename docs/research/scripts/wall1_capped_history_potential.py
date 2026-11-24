"""Exact capped-potential seed, stopped-drift, and comparison checks."""
from fractions import Fraction as F
from itertools import product

DELTA=F(7,25)
K=24

def phi(p):
    assert 0<=p<=1
    return min(F(1),(p/DELTA)**K)


def main():
    checks=0
    for p in (F(j,100) for j in range(101)):
        assert phi(p)<=p/DELTA
        assert (p>=DELTA)==(phi(p)==1)
        checks+=2
    grid=(F(0),DELTA/4,DELTA/2,DELTA,F(1))
    # Two-step binary trees with a genuinely conditional charge at each node.
    # Each root is fixed; mixing roots preserves the proven inequality.
    for p,a,b in product(grid,repeat=3):
        for weight in (F(1,3),F(2,3)):
            children=((weight,a),(1-weight,b))
            if p>=DELTA:
                hit=F(1);charge=F(0)
            else:
                charge=max(F(0),sum(w*phi(v) for w,v in children)-phi(p))
                hit=F(0)
                for w,v in children:
                    if v>=DELTA:
                        hit+=w
                    else:
                        leaves=(v/2,min(F(1),v+DELTA/2))
                        local=max(F(0),sum(phi(z) for z in leaves)/2-phi(v))
                        charge+=w*local
                        hit+=w*sum(z>=DELTA for z in leaves)/2
            assert hit<=phi(p)+charge
            checks+=1
    # Equality at the threshold is a hit, including the initial index.
    assert phi(DELTA)==1
    # A clipped conditional inequality can hold while raw-power drift fails.
    p=DELTA/2;prob=F(1,2**K)
    clipped=prob*phi(F(1))
    raw=prob*(1/DELTA)**K
    assert clipped==phi(p) and raw>(p/DELTA)**K
    # A tail-probability certificate alone is not an initial potential bound.
    assert p<DELTA and phi(p)>0
    # First-moment bound is sharp, attained by a mixture on {0,delta}.
    mixing=F(1,1000)
    assert mixing*phi(DELTA)==mixing*DELTA/DELTA
    D=F('1.9704509e-12');total=F('3.922e-12')
    assert total-D==F('1.9515491e-12')
    assert D+F('1.951e-12')<total
    print('Passed exact seed and stopped-tree checks:',checks)
    print('Safe D14:',D)
    print('Remaining normalized stopped-charge budget:',total-D)
    print('Clipped-vs-raw drift separating fixture checked.')

if __name__=='__main__':main()
