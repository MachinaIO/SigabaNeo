"""Remaining draw-13 stratum: ten inputs, rank 4--7, containing a four-circuit."""
from fractions import Fraction as F
from itertools import product
from math import factorial
from pathlib import Path
import runpy
from wall1_centered_affine_cancellation import rank
from wall1_affine_rank_extensions import activity


def finite_checks():
    q=11
    ys=[(t,t*t % q,t*t*t % q) for t in range(10)]
    ranks={bits:rank([(1,*y) for i,y in enumerate(ys) if bits >> i & 1],q)
           for bits in range(1 << 10)}
    assert all(r==4 for bits,r in ranks.items() if bits.bit_count()==4)
    assert ranks[1023]==4
    laws=[tuple((a+b*y[0]+c*y[1]+d*y[2]) % q for y in ys)
          for a,b,c,d in product(range(q),repeat=4)]
    for config in range(2):
        fibers=[{0,1} if config and i % 2 else {0} for i in range(10)]
        rho=[F(len(b),q) for b in fibers]
        counts=[0]*(1 << 10)
        for law in laws:
            counts[sum(1 << i for i,(x,b) in enumerate(zip(law,fibers)) if x in b)]+=1
        for i in range(10):
            for bits in range(1 << 10):
                if not bits >> i & 1:
                    counts[bits]+=counts[bits | (1 << i)]
        P=[F(v,len(laws)) for v in counts]
        R=[]
        for bits in range(1 << 10):
            v=F(1)
            for i in range(10):
                if bits >> i & 1:
                    v*=rho[i]
            R.append(v)
        eps={c:F(0) for c in range(3,6)}
        for bits,r in ranks.items():
            c=bits.bit_count()
            if c>=3 and r==c-1 and all(ranks[bits ^ (1 << i)]==r
                                      for i in range(10) if bits >> i & 1):
                eps[c]+=factorial(c)*(P[bits]+R[bits])
        assert eps[3]==eps[4]==0 and eps[5]>0
        envelope=sum(abs(P[bits]-R[bits])*R[1023 ^ bits]
                     for bits,r in ranks.items() if r<bits.bit_count())
        bound=activity(10,4,q,sum(rho),{c:v for c,v in eps.items() if c!=4})
        assert factorial(10)*envelope <= bound
    print('Passed 210 four-subset independence checks and two no-four-circuit envelope checks.')


if __name__ == '__main__':
    finite_checks()
    s=runpy.run_path(str(Path(__file__).with_name('wall1_affine_nullity_one.py')))
    I,mu,q,eps=s['I'],s['mu'],s['q'],s['epsilon']
    edge=sum((activity(10,r,q,mu,eps) for r in (3,8)),I(0))/(I('.280')*mu**10)
    nofour={c:v for c,v in eps.items() if c!=4}
    rest=sum((activity(10,r,q,mu,nofour) for r in range(4,8)),I(0))/(I('.280')*mu**10)
    four=sum((activity(10,r,q,mu,{4:eps[4]}) for r in range(4,8)),I(0))/(I('.280')*mu**10)
    assert edge < I('2.197e-18')
    assert rest < I('3.981e-14')
    assert four > I('752')
    assert I('2.391e-12')+edge+rest < I('2.432e-12')
    print('Rank 3/8 contribution < 2.197e-18; no-four-circuit rank 4--7 contribution < 3.981e-14')
    print('The four-circuit anchor part of the old majorant exceeds 752: insufficient.')
    print('UNBOUNDED: rank 4--7 connected ten-input supports containing a four-circuit; later draws.')
