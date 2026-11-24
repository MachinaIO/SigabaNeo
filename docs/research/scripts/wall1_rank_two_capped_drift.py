"""Exact rank-two marked-lattice experiment; not a production reachability claim."""
from fractions import Fraction as F
from itertools import product
from math import isqrt


def rootfloor(x):
    return isqrt(x.numerator // x.denominator)


def points(a, b, cap):
    for x in range(-rootfloor(cap / (a*a)), rootfloor(cap / (a*a))+1):
        for y in range(-rootfloor(cap / (b*b)), rootfloor(cap / (b*b))+1):
            rest = cap-a*a*x*x-b*b*y*y
            if rest < 0:
                continue
            for j in range(-rootfloor(rest), rootfloor(rest)+1):
                yield (x,y,j), a*a*x*x+b*b*y*y+j*j


def winner(q,a,b,u):
    candidates = [(norm, w) for w,norm in points(a,b,min(q*a,q*b)**2)
                  if any(w) and (w[0]-w[2]*u[0])%q == 0
                  and (w[1]-w[2]*u[1])%q == 0]
    return min(candidates)  # norm, then lexicographic integer coordinates


def projection_minima(q,a,b,u,win,max_radius):
    s2,w = win
    minima = {}
    # Integer winner translations make the parallel component at most |w|/2.
    for z,norm in points(a,b,max_radius+s2/4):
        dot=a*a*z[0]*w[0]+b*b*z[1]*w[1]+z[2]*w[2]
        p2=norm-dot*dot/s2
        assert p2 >= 0
        v=((z[0]-z[2]*u[0])%q,(z[1]-z[2]*u[1])%q)
        if v not in minima or p2 < minima[v]:
            minima[v]=p2
    return minima


def hit(p2,L2,s2):
    t=(p2+1)/L2
    return t.numerator**506*s2.numerator <= t.denominator**506*s2.denominator


def potential(p):
    return min(F(1),(p/F(7,25))**24)


def experiment():
    checked=0; positive=[]; best=None
    for q in (3,5):
        for a,b in ((F(1),F(1)),(F(1),F(3,2)),(F(1),F(2)),
                    (F(3,2),F(3,2)),(F(3,2),F(2)),(F(2),F(2))):
            residues=list(product(range(-(q//2),q//2+1),repeat=2))
            norms=[a*a*x*x+b*b*y*y for x,y in residues]
            thresholds=sorted(set(norms))
            radii=sorted({t+e for t in thresholds for e in (F(-1,100),F(-1,1000),F(0),F(1,1000),F(1,100)) if t+e>=0})
            radii=[R2 for R2 in radii if F(sum(v>R2 for v in norms),q*q)<F(7,25)]
            if not radii: continue
            data=[]
            for u in product(range(q),repeat=2):
                win=winner(q,a,b,u)
                assert win[0]>=1
                data.append((u,win,projection_minima(q,a,b,u,win,max(radii))))
            for R2 in radii:
                L2=R2+1
                pin=F(sum(v>R2 for v in norms),q*q)
                outgoing=[]
                for u,win,mins in data:
                    s2,w=win
                    hits=sum(hit(v,L2,s2) for v in mins.values())
                    pout=F(q*q-hits,q*q)
                    outgoing.append((u,s2,w,pout))
                mean=sum((potential(p) for _,_,_,p in outgoing),F(0))/(q*q)
                drift=mean-potential(pin)
                checked+=1
                row=(drift,q,a,b,R2,pin,outgoing)
                if best is None or drift>best[0]: best=row
                if drift>0: positive.append(row)
    assert any(q==3 and a==b==1 and R2==F(2001,1000) and pin==0
               for _,q,a,b,R2,pin,_ in positive)
    assert 3*3000**506 > 3001**506
    print('Exact configurations:',checked,'positive:',len(positive))
    drift,q,a,b,R2,pin,outgoing=best
    print('Maximum drift fixture q,a,b,R2,Pin:',q,a,b,R2,pin)
    print('Exact drift:',drift)
    print('Drift decimal (display only):',float(drift))
    print('Outgoing (u, winner norm squared, winner integer coordinates, Pout):')
    for row in outgoing: print(row)
    return checked,positive,best


if __name__=='__main__':
    experiment()
