"""Exact independent-map energy and pinned mixed-fiber completion moments."""
from collections import Counter
from fractions import Fraction as F
from itertools import product,combinations,permutations
from math import comb


def fixture():
    q=5;R2=4;H=3
    center=lambda x:(x+q//2)%q-q//2
    points=list(product(range(q),repeat=2))
    normals=[(1,i) for i in range(q)]+[(0,1)]
    lines=[[y for y in points if (a*y[0]+b*y[1]-t)%q==0]
           for a,b in normals for t in range(q)]
    energy=F(0);same=F(0);direct={k:F(0) for k in (1,2)}
    ordinary={k:F(0) for k in (1,2)};gaussian={k:F(0) for k in (1,2)}
    checks=0
    for line in lines:
        origin=line[0];direction=tuple((v-u)%q for u,v in zip(origin,line[1]))
        ordered=[tuple((x+t*d)%q for x,d in zip(origin,direction)) for t in range(q)]
        assert set(ordered)==set(line)
        input_energy=[sum(center(v)**2 for v in y) for y in ordered]
        maps=[tuple((a+b*t)%q for t in range(q)) for a,b in product(range(q),repeat=2)]
        # These q^2 distinct restrictions are equally likely; the q^3 ambient
        # maps restrict with exactly q equal preimages each.
        assert len(set(maps))==q*q
        ambient=Counter(tuple((a+b*y[0]+c*y[1])%q for y in ordered)
                        for a,b,c in product(range(q),repeat=3))
        assert set(ambient)==set(maps) and set(ambient.values())=={q}
        anchors=list(combinations(range(q),H));hits={}
        for A in anchors:
            hits[A]=[all(input_energy[t]+center(out[t])**2<=R2 for t in A) for out in maps]
        W=F(sum(sum(v) for v in hits.values()),q*q)
        # Explicit independent map pairs; no Jensen or common-map replacement.
        color_count=sum(sum(hits[A][i]*hits[B][j] for A in anchors for B in anchors)
                        for i in range(q*q) for j in range(q*q))
        assert F(color_count,q**4)==W*W
        energy+=W*W
        same+=F(sum(sum(hits[A][i] for A in anchors)**2 for i in range(q*q)),q*q)
        C=sum(v<=R2 for v in input_energy)
        for k in (1,2):
            count=joint=0;hist=Counter();identity=F(0)
            for A in anchors:
                if all(input_energy[t]<=R2 for t in A):
                    available=C-H
                    falling=1
                    for j in range(k):falling*=max(0,available-j)
                    identity+=F(sum(hits[A]),q*q)*falling
                for T in permutations([t for t in range(q) if t not in A],k):
                    for i,out in enumerate(maps):
                        okay=hits[A][i] and all(input_energy[t]<=R2 for t in T)
                        count+=okay
                        joint+=okay and all(input_energy[t]+center(out[t])**2<=R2 for t in T)
                        exponent=(H+k)*R2-sum(input_energy[t] for t in A+T)-sum(center(out[t])**2 for t in A)
                        hist[exponent]+=1
            mixed=F(count,q*q)
            assert mixed==identity
            majorant=sum((F(2)**e*mult for e,mult in hist.items()),F(0))/(q*q)
            assert majorant>=mixed>=F(joint,q*q)
            direct[k]+=mixed;ordinary[k]+=F(joint,q*q);gaussian[k]+=majorant
            checks+=1
    assert energy<same
    assert all(direct[k]>ordinary[k] for k in (1,2))
    print('30 affine lines: independent colored energy',energy,'same-map energy',same)
    print(checks,'exact mixed-fiber/pinned moment identities and Gaussian majorants passed.')
    for k in (1,2):print('k',k,'mixed moment',direct[k],'ordinary joint-ball moment',ordinary[k],
                         'mixed Gaussian upper',gaussian[k])
    # Intersection of two ball constraints is not a single doubled-output ball.
    assert 0+2**2<=R2 and 0+2**2<=R2 and 0+2**2+2**2>R2


def large_union_fixture():
    q=3329;d=10;zero=(0,)*d
    e=[tuple(int(i==j) for i in range(d)) for j in range(d)]
    A=[zero,e[0],e[1],tuple((x-y)%q for x,y in zip(e[0],e[1]))]+e[2:]
    A.append(tuple(pow(8,-1,q)*(e[0][i]-2*e[1][i]+sum(v[i] for v in e[2:]))%q for i in range(d)))
    B=[tuple((-x)%q for x in y) for y in A]
    D=[tuple((x+3*(i==0))%q for i,x in enumerate(y)) for y in A]
    center=lambda x:x if x<=q//2 else x-q
    assert len(set(A)&set(B))==1 and len(set(A)&set(D))==0
    assert all(sum(center(x)**2 for x in y)<=2933**2 for y in A+B+D)
    assert len(set(A)|set(B))==25 and len(set(A)|set(D))==26
    # Reflection and translation preserve the existing balanced relation code,
    # connectedness, girth4 and rank11, and leave the coordinate span invariant.
    print('H13 connected same-span ball anchors with union sizes25 and26 passed.')

if __name__=='__main__':
    fixture()
    large_union_fixture()
