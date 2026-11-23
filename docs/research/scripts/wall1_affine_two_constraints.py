"""Two-relation bound for the residual draw-13 count; later histories remain open."""
from fractions import Fraction as F
from itertools import combinations, product
from math import comb
from pathlib import Path
import runpy
from wall1_centered_affine_cancellation import rank


def finite_rearrangement_checks():
    tested=0
    for q in (3,5):
        sets=[{i for i in range(q) if bits >> i & 1} for bits in range(1 << q)
              if bits.bit_count() % 2]
        centers={n:{x % q for x in range(-(n//2),n//2+1)} for n in range(1,q+1,2)}
        for A in sets:
            for B in sets:
                conv=[sum((x-a) % q in B for a in A) for x in range(q)]
                Ap,Bp=centers[len(A)],centers[len(B)]
                centered=[sum((x-a) % q in Bp for a in Ap) for x in range(q)]
                for C in sets:
                    assert sum(conv[x] for x in C)<=sum(centered[x] for x in centers[len(C)])
                    tested+=1
    print(f'Passed {tested} exact odd-set rearrangement checks.')
    q=5
    directions=[(1,t) for t in range(q)]+[(0,1)]
    f=[F(1,1+min(u,q-u)) for u in range(q)]
    triangle=sum(f[u]**2*f[v]**2*f[(u+v) % q]**2
                 for u,v in product(range(q),repeat=2))/q**2
    tested=0
    for multiplicities in product(range(3),repeat=len(directions)):
        if sum(multiplicities)!=6:
            continue
        columns=[d for d,n in zip(directions,multiplicities) for _ in range(n)]
        # Two triples with three distinct projective directions in each.
        assert any(len({columns[i] for i in A})==3 and
                   len({columns[i] for i in range(6) if i not in A})==3
                   for A in combinations(range(6),3))
        for scale in (tuple([1]*6),tuple(1+i % (q-1) for i in range(6))):
            total=F(0)
            for u,v in product(range(q),repeat=2):
                weight=F(1)
                for (a,b),c in zip(columns,scale):
                    weight*=f[c*(a*u+b*v) % q]
                total+=weight/q**2
            assert total<=triangle
            tested+=1
    print(f'Passed {tested} exact six-form bounds with no direction repeated three times.')


def finite_ear_checks():
    q=3
    points=list(product(range(2),repeat=3))
    ranks={bits:rank([(1,*p) for i,p in enumerate(points) if bits >> i & 1],q)
           for bits in range(1 << len(points))}
    circuits=[bits for bits,r in ranks.items() if bits.bit_count()>=2 and r==bits.bit_count()-1
              and all(ranks[bits ^ (1 << i)]==r for i in range(len(points)) if bits >> i & 1)]
    assert not any(bits.bit_count()==3 for bits in circuits)
    tested=0
    for T,r in ranks.items():
        if r<4:
            continue
        connected=True
        U=(T-1)&T
        while U:
            if ranks[U]+ranks[T ^ U]==r:
                connected=False
                break
            U=(U-1)&T
        if not connected:
            continue
        for C in circuits:
            if C.bit_count()!=4 or C & T != C:
                continue
            outside=[i for i in range(len(points)) if T >> i & 1 and ranks[C | (1 << i)]>3]
            found=False
            for t in range(2,r-1):
                for O in combinations(outside,t):
                    obits=sum(1 << i for i in O)
                    if ranks[C | obits]!=t+2:
                        continue
                    for D in circuits:
                        if D & ~C == obits and 1<=(D & C).bit_count()<=3:
                            found=True
            assert found
            tested+=1
    print(f'Passed {tested} exact first-extension witnesses from a four-circuit.')


if __name__ == '__main__':
    finite_rearrangement_checks()
    finite_ear_checks()
    s=runpy.run_path(str(Path(__file__).with_name('wall1_affine_nullity_one.py')))
    I,iv,mu,R,q=s['I'],s['iv'],s['mu'],s['R'],s['q']
    theta_geometric=s['s']['theta_upper']
    def theta(x):
        return (theta_geometric(x) if x>iv.pi else
                iv.sqrt(iv.pi/x)*theta_geometric(iv.pi**2/x))
    def moment(power,beta):
        T=iv.sqrt(iv.pi/beta)
        a=iv.pi**2/beta
        delta=2*iv.exp(-a/4)/(1-iv.exp(-2*a))
        return T**power/q*(theta(a*power/q**2)**(1/power)+I(q)**(1/power)*delta)**power
    def gaussian_bound(h,beta):
        if h==6:
            T=iv.sqrt(iv.pi/beta)
            a=iv.pi**2/beta
            alpha=a/q**2
            delta=2*iv.exp(-a/4)/(1-iv.exp(-2*a))
            error=sum(comb(6,j)*delta**j for j in range(1,7))
            return T**6*(theta(4*alpha)*theta(3*alpha)/q**2+iv.exp(-a/4)+error)
        if h<=8:
            return moment(I(h)/2,beta)**2
        return theta(beta)**(h-8)*moment(I(4),beta)**2
    total=I(0)
    per_rank={}
    for r in range(4,8):
        per_rank[r]=I(0)
        for t in range(2,r-1):
            h=4+t
            beta=I((h-2)*517)/(2*h*R**2)
            U=gaussian_bound(h,beta)
            for overlap in (1,2,3):
                d=t+overlap
                if d<4:  # Three-circuits have already been excluded.
                    continue
                pair_count=q**d*iv.exp(h*beta*R**2)*U**517
                positions=comb(10,4)*comb(6,t)*comb(4,overlap)*comb(6-t,r-t-2)
                charge=(positions*pair_count/q**(400*(t+2))*mu**(r-t-2)
                        *q**((r-1)*(8-r))/(I('.280')*mu**10))
                total+=charge
                per_rank[r]+=charge
    assert total < I('3.510e-31')
    earlier=(I('2.391e-12')+I('2.197e-18')+I('3.981e-14')
             +I('6.927e-293')+I('4.803e-59'))
    assert earlier+total < I('2.432e-12')
    assert I('7.150e-14')+I('2.432e-12')+I('3.922e-12')+I('1.174e-12') < I('7.6e-12')
    print('Residual positive full-incidence charge < 3.510e-31')
    print('Certified paper bound: P(b_13 > 0.280) < 2.432e-12')
    print('Remaining sufficient draw-14--404 history allowance: 3.922e-12')
    print('Remaining outside this calculation: draws 14--404 and other BKZ success obligations.')
