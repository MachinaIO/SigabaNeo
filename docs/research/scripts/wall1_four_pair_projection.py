"""Projection minimum and balanced pattern count for four equal pair sums."""
from fractions import Fraction as F
from itertools import combinations,product


def pairings(items):
    if not items:
        yield ()
        return
    first,*rest=items
    for j,second in enumerate(rest):
        for tail in pairings(rest[:j]+rest[j+1:]):
            yield ((first,second),)+tail


def rref(rows,q):
    rows=[[x%q for x in row] for row in rows]
    pivot=0
    for col in range(8):
        found=next((i for i in range(pivot,3) if rows[i][col]),None)
        if found is None:continue
        rows[pivot],rows[found]=rows[found],rows[pivot]
        inv=pow(rows[pivot][col],-1,q)
        rows[pivot]=[x*inv%q for x in rows[pivot]]
        for i in range(3):
            if i==pivot:continue
            scale=rows[i][col]
            rows[i]=[(x-scale*y)%q for x,y in zip(rows[i],rows[pivot])]
        pivot+=1
        if pivot==3:break
    assert pivot==3
    return tuple(map(tuple,rows))


def checks():
    a=(1,1,-1,-1,0,0,0,0)
    b=(0,0,1,1,-1,-1,0,0)
    c=(0,0,0,0,1,1,-1,-1)
    adj=((12,8,4),(8,16,8),(4,8,12))
    rows=(a,b,c)
    gram=[[sum(x*y for x,y in zip(u,v)) for v in rows] for u in rows]
    assert [[sum(gram[i][k]*adj[k][j] for k in range(3)) for j in range(3)]
            for i in range(3)]==[[32 if i==j else 0 for j in range(3)] for i in range(3)]
    def energy(v):
        dots=[sum(x*y for x,y in zip(row,v)) for row in rows]
        return 32*sum(x*x for x in v)-sum(dots[i]*adj[i][j]*dots[j] for i in range(3) for j in range(3))
    checked=0;positive=[]
    for norm in range(3):
        for support in combinations(range(8),norm):
            for signs in product((-1,1),repeat=norm):
                v=[0]*8
                for i,sign in zip(support,signs):v[i]=sign
                value=energy(v)
                assert value==16*sum((v[2*i]-v[2*i+1])**2 for i in range(4))+4*sum(v)**2
                assert value>=0
                if value:positive.append(value)
                checked+=1
    assert checked==129 and min(positive)==16
    assert energy((1,1,0,0,0,0,0,0))==16
    radius=(F(4)+F(3)+F(8,3))/4
    assert radius==F(29,12) and radius+F(1,2)==F(35,12)<3
    keys={q:set() for q in (7,3329)}
    patterns=0
    for pairs in pairings(list(range(8))):
        signs=[((1,1),)*4]+[((1,-1),)+tuple((s,-s) for s in tail) for tail in product((-1,1),repeat=3)]
        for pattern in signs:
            sums=[]
            for pair,sign in zip(pairs,pattern):
                row=[0]*8
                for i,s in zip(pair,sign):row[i]=s
                sums.append(row)
            relations=[tuple(x-y for x,y in zip(sums[i],sums[i+1])) for i in range(3)]
            assert all(sum(row)==0 for row in relations)
            for q in keys:keys[q].add(rref(relations,q))
            patterns+=1
    assert patterns==945 and all(len(v)==945 for v in keys.values())
    assert 32*24**4<3329**2
    print('Passed129 projection checks; projected squared minimum1/2, rounding radius29/12.')
    print('Verified945 distinct balanced patterns at each of q=7,3329.')


if __name__=='__main__':checks()
