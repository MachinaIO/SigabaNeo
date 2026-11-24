"""Exact affine coefficient pushforward by a fixed dual completion matrix."""
from collections import Counter
from fractions import Fraction as F
from itertools import product


def rank(rows,q,n):
    rows=[list(x) for x in rows];r=0
    for j in range(n):
        p=next((i for i in range(r,len(rows)) if rows[i][j]%q),None)
        if p is None:continue
        rows[r],rows[p]=rows[p],rows[r]
        inv=pow(rows[r][j]%q,-1,q)
        rows[r]=[(v*inv)%q for v in rows[r]]
        for i in range(len(rows)):
            if i!=r:
                z=rows[i][j]
                rows[i]=[(v-z*w)%q for v,w in zip(rows[i],rows[r])]
        r+=1
    return r


def configurations(r,k,q):
    for flat in product(range(q),repeat=(r-1)*k):
        lower=[flat[i*k:(i+1)*k] for i in range(r-1)]
        first=tuple((1-sum(row[j] for row in lower))%q for j in range(k))
        yield (first,*lower)


def image(V,B,n,q):
    return tuple(tuple(sum(v*b[j] for v,b in zip(row,B))%q for j in range(n)) for row in V)


def add(T,U,q):return tuple(tuple((a+b)%q for a,b in zip(x,y)) for x,y in zip(T,U))


def tests():
    matrices=0;configs=0;restricted=0
    for q in (2,3):
        for r in (1,2,3):
            for k in range(3):
                for n in range(3):
                    for flat in product(range(q),repeat=k*n):
                        B=tuple(tuple(flat[i*n:(i+1)*n]) for i in range(k))
                        t=rank(B,q,n)
                        rows=set(tuple(sum(c*b[j] for c,b in zip(coeff,B))%q for j in range(n))
                                 for coeff in product(range(q),repeat=k))
                        assert len(rows)==q**t
                        s=tuple(sum(b[j] for b in B)%q for j in range(n))
                        expected=set()
                        for Y in product(sorted(rows),repeat=r-1):
                            expected.add((tuple((s[j]-sum(y[j] for y in Y))%q for j in range(n)),*Y))
                        allV=list(configurations(r,k,q))
                        counts=Counter(image(V,B,n,q) for V in allV)
                        assert set(counts)==expected
                        assert len(counts)==q**((r-1)*t)
                        assert set(counts.values())=={q**((r-1)*(k-t))}
                        offset=tuple(tuple((i+2*j+1)%q for j in range(n)) for i in range(r))
                        def f(T):
                            centered=lambda x:(x+q//2)%q-q//2
                            return F(2)**(-sum(centered(x)**2 for row in T for x in row))
                        lhs=sum((f(add(image(V,B,n,q),offset,q)) for V in allV),F(0))
                        rhs=sum((f(add(T,offset,q)) for T in expected),F(0))
                        assert lhs==q**((r-1)*(k-t))*rhs
                        assert lhs/q**((r-1)*k)==rhs/q**((r-1)*t)
                        pinned=(1,)+(0,)*(r-1)
                        def valid(V):
                            cols=[tuple(V[i][j] for i in range(r)) for j in range(k)]
                            return pinned not in cols and len(set(cols))==len(cols)
                        validV=[V for V in allV if valid(V)]
                        fall=1
                        for j in range(k):fall*=max(0,q**(r-1)-1-j)
                        assert len(validV)==fall
                        partial=sum((f(add(image(V,B,n,q),offset,q)) for V in validV),F(0))
                        assert partial<=lhs
                        if validV:assert partial/len(validV)<=lhs/len(validV)
                        matrices+=1;configs+=len(allV);restricted+=1
    # A restricted average need not be <= the unrestricted average.
    q=3;values=list(configurations(2,1,q));pin=(1,0)
    test=lambda V:int(tuple(row[0] for row in V)!=pin)
    assert F(sum(test(V) for V in values),len(values))==F(2,3)
    assert F(sum(test(V) for V in values if test(V)),sum(test(V) for V in values))==1
    # Distinctness/pinning destroys constant fibers after rank compression.
    B=((1,),(1,));V=list(configurations(2,2,q))
    allowed=[v for v in V if len(set(zip(*v)))==2 and pin not in set(zip(*v))]
    assert len(allowed)==2
    assert Counter(image(v,B,1,q) for v in allowed)=={((2,),(0,)):2}
    print(matrices,'dual matrices;',configs,'affine coefficient configurations;',restricted,'restricted sums passed.')
    print('Verified rank-zero/full-rank/empty cases, offsets, Gaussian tests, sums vs averages.')
    print('Restricted-average and nonuniform-fiber counterexamples passed.')

if __name__=='__main__':tests()
