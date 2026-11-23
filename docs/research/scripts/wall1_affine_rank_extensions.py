"""Rank-extension envelopes; records their limitation for large connected supports."""
from fractions import Fraction as F
from itertools import product
from math import comb, factorial
from pathlib import Path
import runpy
from wall1_centered_affine_cancellation import rank
from wall1_affine_circuit_components import correction_bound


def activity(h,r,q,mu,epsilon):
    result=mu*0
    for j in range(3,h+1):
        for t in range(2,min(j-1,r)+1):
            if r-t>h-j:
                continue
            for c in range(3,t+2):
                count=comb(h,j)*comb(j,c)*comb(j-c,t-c+1)*comb(h-j,r-t)
                exponent=(t-1)*(j-t-1)+(r-1)*(h-j-r+t)
                assert exponent >= 0 and r-c+1 >= 0
                result += count*q**exponent*mu**(r-c+1)*epsilon.get(c,mu*0)
    return result


def finite_checks():
    q=3
    ys=list(product(range(q),repeat=2))
    laws=[tuple((c[0]+c[1]*y[0]+c[2]*y[1]) % q for y in ys)
          for c in product(range(q),repeat=3)]
    tested=0
    for config in range(3):
        fibers=[{(i+config) % q} if (i+config) % 2 else
                {(i+config) % q,(i+config+1) % q} for i in range(len(ys))]
        rho=[F(len(b),q) for b in fibers]
        mu=sum(rho)
        hits=[tuple(int(v in b) for v,b in zip(law,fibers)) for law in laws]
        P,R,ranks={}, {}, {}
        circuits={c:F(0) for c in range(3,5)}
        for bits in range(1 << len(ys)):
            indices=[i for i in range(len(ys)) if bits >> i & 1]
            rows=[(1,*ys[i]) for i in indices]
            r=rank(rows,q)
            ranks[bits]=r
            P[bits]=F(sum(all(h[i] for i in indices) for h in hits),len(hits))
            R[bits]=F(1)
            for i in indices:
                R[bits] *= rho[i]
            c=len(indices)
            if c>=3 and r==c-1 and all(rank(rows[:j]+rows[j+1:],q)==r for j in range(c)):
                circuits[c] += factorial(c)*(P[bits]+R[bits])
        aggregates={}
        for bits,r in ranks.items():
            h=bits.bit_count()
            if r < 3 or r > h-2:
                continue
            envelope=F(0)
            sub=bits
            while sub:
                if ranks[sub] < sub.bit_count():
                    envelope += abs(P[sub]-R[sub])*R[bits ^ sub]
                sub=(sub-1)&bits
            aggregates[h,r]=aggregates.get((h,r),F(0))+factorial(h)*envelope
            tested+=1
        for (h,r),value in aggregates.items():
            assert value <= activity(h,r,q,mu,circuits)
    print(f'Passed exact dependent-subset envelopes for {tested} rank-three supports.')


if __name__ == '__main__':
    finite_checks()
    s=runpy.run_path(str(Path(__file__).with_name('wall1_affine_nullity_one.py')))
    I,mu,k,q,eps=s['I'],s['mu'],s['k'],s['q'],s['epsilon']
    extra={h:sum((activity(h,r,q,mu,eps) for r in range(3,h-1)),I(0))
           for h in range(5,k+1)}
    base={h:eps[h]+((2**h-1-h-comb(h,2))*q**(h-3)*eps[3] if h>=4 else I(0))
          for h in range(3,k+1)}
    for cap in (8,9):
        combined={h:base[h]+(extra.get(h,I(0)) if h<=cap else I(0)) for h in base}
        bound=correction_bound(mu,combined,k)/(I('.280')*mu**k)
        ceiling = '1.562e-23' if cap == 8 else '5.218e-12'
        assert bound < I(ceiling)
        print(f'Components through size {cap}: normalized correction < {ceiling}')
    assert extra[12]/(I('.280')*mu**12) > I('9e32')
    print('The size-12 envelope alone exceeds 9e32 after normalization: unusable.')
    print('No full draw-13 exit bound: large connected components and later histories remain.')
