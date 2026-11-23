"""Exact same-span energy versus connected union incidences.

All weights below are actual affine-map incidence probabilities, not substituted
Gaussian upper bounds. No production estimate is claimed.
"""
from itertools import product
from fractions import Fraction as F
from math import comb, factorial


def falling(c,j):
    out=1
    for i in range(j):out*=c-i
    return out


def ball_fixture(q, radius_sq, H=4):
    half=q//2
    centered=lambda x:(x+half)%q-half
    points=list(product(range(q),repeat=2))
    normals=[(1,i) for i in range(q)]+[(0,1)]
    lines=[[y for y in points if (a*y[0]+b*y[1]-t)%q==0]
           for a,b in normals for t in range(q)]
    maps=list(product(range(q),repeat=3))
    weights=[]; diagonal=F(0)
    incidence={j:F(0) for j in range(H,2*H+1)}
    for line in lines:
        occupancy=[]
        for u,a,b in maps:
            count=sum(centered((u+a*y[0]+b*y[1])%q)**2
                      +sum(centered(x)**2 for x in y)<=radius_sq for y in line)
            occupancy.append(count)
        n=[falling(c,H) for c in occupancy]
        mean=F(sum(n),len(maps))
        weights.append(mean)
        diagonal+=F(sum(x*x for x in n),len(maps))
        for j in incidence:
            incidence[j]+=F(sum(falling(c,j) for c in occupancy),len(maps))
        assert mean*mean <= F(sum(x*x for x in n),len(maps))
    energy=sum(w*w for w in weights)
    union=sum(comb(H,i)**2*factorial(i)*incidence[2*H-i] for i in range(H+1))
    assert diagonal==union and energy<=diagonal
    z=sum(weights); L=len(lines)
    assert z>0
    chi=L*energy/z**2-1
    chi_upper=L*diagonal/z**2-1
    assert chi>=0 and chi_upper>=chi
    print(f'q={q}, R^2={radius_sq}, H={H}, L={L}, Z={z}')
    print(f'  E={energy}, diagonal_union={diagonal}, D/E={diagonal/energy}, '
          f'chi={chi}, union_chi_upper={chi_upper}')
    print('  connected rank2 incidences',incidence)


def incompatible_pair():
    # General fibers: two connected rank2 H4 anchors spanning the same line
    # can each have positive incidence but incompatible union.
    q=5
    fibers={0:{0,1},1:{0,1},2:{0,1},3:{0},4:{1}}
    A=(0,1,2,3); B=(0,1,2,4)
    maps=list(product(range(q),repeat=2))
    hit=lambda T,a,b:all((a+b*y)%q in fibers[y] for y in T)
    pa=F(sum(hit(A,a,b) for a,b in maps),len(maps))
    pb=F(sum(hit(B,a,b) for a,b in maps),len(maps))
    joint=F(sum(hit(set(A)|set(B),a,b) for a,b in maps),len(maps))
    assert pa==pb==F(1,25) and joint==0
    # Aggregating the SAME anchor family restores Jensen, including diagonal.
    n=[int(hit(A,a,b))+int(hit(B,a,b)) for a,b in maps]
    assert F(sum(n),25)**2<=F(sum(x*x for x in n),25)
    print('Incompatible pair: P(A)=P(B)=1/25, P(A union B)=0; aggregate Jensen holds.')


if __name__=='__main__':
    incompatible_pair()
    ball_fixture(5,4)
    ball_fixture(7,9)
    print('PASS: exact Gaussian-free incidence weights, rank2 overlap identity, and aggregate energy bound.')
