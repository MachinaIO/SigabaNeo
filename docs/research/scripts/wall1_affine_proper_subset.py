"""Suppress proper-subset corrections for connected ten-input supports."""
from fractions import Fraction as F
from itertools import product
from math import comb
from pathlib import Path
import runpy
from wall1_centered_affine_cancellation import rank


def finite_checks():
    q=3
    points=list(product(range(q),repeat=2))
    ranks={bits:rank([(1,*p) for i,p in enumerate(points) if bits >> i & 1],q)
           for bits in range(1 << len(points))}
    checked=0
    for bits,r in ranks.items():
        if bits.bit_count()<2:
            continue
        no_coloop=all(ranks[bits ^ (1 << i)]==r for i in range(len(points)) if bits >> i & 1)
        if not no_coloop:
            continue
        sub=(bits-1)&bits
        while sub:
            w=(bits.bit_count()-sub.bit_count())-r+ranks[sub]
            assert w>=1
            checked+=1
            sub=(sub-1)&bits
    print(f'Passed {checked} proper-subset rank-deficit checks on coloop-free supports.')


if __name__ == '__main__':
    finite_checks()
    s=runpy.run_path(str(Path(__file__).with_name('wall1_affine_nullity_one.py')))
    I,mu,R,q,eps=s['I'],s['mu'],s['R'],s['q'],s['epsilon']
    rho_max=2*s['s']['volume'][400]*(R**2+I(100))**200/q**400
    h=10
    proper=I(0)
    triangles=I(0)
    for r in range(4,8):
        for j in range(3,h):
            for t in range(2,min(j-1,r)+1):
                w=h-j-r+t
                if w<1:
                    continue
                for c in range(3,t+2):
                    count=comb(h,j)*comb(j,c)*comb(j-c,t-c+1)*comb(h-j,r-t)
                    exponent=(t-1)*(j-t-1)+(r-1)*w
                    proper+=count*q**exponent*mu**(r-c+1)*eps[c]*rho_max**w
        triangles+=comb(h,3)*comb(h-3,r-2)*eps[3]*mu**(r-2)*q**((r-1)*(h-r-1))
    proper/=I('.280')*mu**10
    triangles/=I('.280')*mu**10
    assert proper < I('6.927e-293')
    assert triangles < I('4.803e-59')
    assert (I('2.391e-12')+I('2.197e-18')+I('3.981e-14')
            +proper+triangles < I('2.432e-12'))
    print('Proper-subset correction < 6.927e-293')
    print('Compatible full tuples containing a three-circuit < 4.803e-59')
    print('UNBOUNDED: positive full-incidence count with no three-circuit and with a four-circuit.')
