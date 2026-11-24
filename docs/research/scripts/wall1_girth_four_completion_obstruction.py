"""Exact girth-four completion obstruction, including the H13/r11 fixture."""
from fractions import Fraction as F
from itertools import product,combinations
from math import comb,log10


def secants(points,q):
    return {tuple((x+t*(y-x))%q for x,y in zip(a,b))
            for a,b in combinations(points,2) for t in range(q)}


def finite_checks():
    cases=0
    for q in (5,7):
        anchor=[(0,0,0),(1,0,0),(0,1,0),(0,0,1),(1,1,1)]
        # Unique relation (2,-1,-1,-1,1) has no zero coefficient.
        assert all(sum(c*v[i] for c,v in zip((2,-1,-1,-1,1),anchor))%q==0 for i in range(3))
        for a,b,c in combinations(anchor,3):assert c not in secants([a,b],q)
        centered=lambda x:min(x,q-x)
        for radius2 in (3,6,12,27):
            candidates={v for v in product(range(q),repeat=3)
                        if sum(centered(x)**2 for x in v)<=radius2}
            assert set(anchor)<=candidates
            L=len(candidates);m=len(anchor)
            first=candidates-secants(anchor,q)
            assert len(first)>=max(0,L-q*comb(m,2))
            actual=sum(len(candidates-secants(anchor+[v],q)) for v in first)
            lower=max(0,L-q*comb(m,2))*max(0,L-q*comb(m+1,2))
            assert lower<=actual<=L*L
            cases+=1
    print('Passed',cases,'exact arbitrary-ball two-completion counts.')


def production_fixture():
    q=3329;d=10
    zero=(0,)*d
    e=[tuple(int(i==j) for i in range(d)) for j in range(d)]
    points=[zero,e[0],e[1],tuple((x-y)%q for x,y in zip(e[0],e[1]))]+e[2:]
    inv8=pow(8,-1,q)
    last=tuple(inv8*(e[0][i]-2*e[1][i]+sum(v[i] for v in e[2:]))%q for i in range(d))
    points.append(last)
    assert len(points)==13 and len(set(points))==13
    a=(1,1,-1,-1)+(0,)*9
    b=(1,1,-2,0)+(1,)*8+(-8,)
    for row in (a,b):
        assert sum(row)==0
        assert all(sum(c*v[i] for c,v in zip(row,points))%q==0 for i in range(d))
    # The positions other than3,12 are 0,e1,...,e10: rank11.
    assert [points[i] for i in range(13) if i not in (3,12)]==[zero]+e
    # Any relation outside span(a) has all nine new coefficients nonzero;
    # thus girth is exactly4, and a,b connect all thirteen positions.
    assert all(x%q for x in b[4:])
    assert set(i for i,x in enumerate(a) if x)&set(i for i,x in enumerate(b) if x)
    assert all(x or y for x,y in zip(a,b))
    centered=lambda x:x if x<=q//2 else x-q
    norms=[sum(centered(x)**2 for x in v) for v in points]
    assert max(norms)==2249728<2933**2
    assert all(abs(centered(x))<=927 for point in points for x in point)
    side=1855;L=side**10
    assert 10*927**2<=2933**2 and 927<q//2
    loss=q*sum(comb(13+j,2) for j in range(6))
    assert loss==2273707
    ratio=F(1)
    for j in range(6):ratio*=1-F(q*comb(13+j,2),L)
    assert ratio>=1-F(loss,L)>0
    print('q3329 H13 rank11, c4/t9/o3 ball fixture passed; max squared norm',max(norms))
    print('candidate cube lower count',L,'log10',log10(L))
    print('girth4/connectivity relative deletion <=',float(F(loss,L)))
    print('ordered six-completion lower log10 >=',6*log10(L)+log10(float(ratio)))

if __name__=='__main__':
    finite_checks()
    production_fixture()
