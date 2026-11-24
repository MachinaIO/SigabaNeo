"""Exact rational small-width shortest/project/fresh-append transitions.

Tracks quotient rank drops. Finite verification, not a production BKZ bound.
"""
from fractions import Fraction as F
from itertools import product
from math import gcd,isqrt
from functools import lru_cache
from collections import defaultdict,Counter


def identity(d):return [[F(int(i==j)) for j in range(d)] for i in range(d)]
def inverse(a):
    n=len(a);r=[list(map(F,row))+identity(n)[i] for i,row in enumerate(a)]
    for j in range(n):
        p=next(i for i in range(j,n) if r[i][j]);r[j],r[p]=r[p],r[j]
        t=r[j][j];r[j]=[x/t for x in r[j]]
        for i in range(n):
            if i!=j:
                t=r[i][j];r[i]=[x-t*y for x,y in zip(r[i],r[j])]
    return tuple(tuple(row[n:]) for row in r)
def determinant(a):
    a=[list(map(F,row)) for row in a];out=F(1)
    for j in range(len(a)):
        p=next((i for i in range(j,len(a)) if a[i][j]),None)
        if p is None:return F(0)
        if p!=j:a[j],a[p]=a[p],a[j];out=-out
        t=a[j][j];out*=t
        for i in range(j+1,len(a)):
            ratio=a[i][j]/t
            for k in range(j+1,len(a)):a[i][k]-=ratio*a[j][k]
    return out

def bezout(x,y):
    a,b,aa,bb=1,0,0,1
    while y:
        k=x//y;x,y=y,x-k*y;a,aa=aa,a-k*aa;b,bb=bb,b-k*bb
    if x<0:x,a,b=-x,-a,-b
    return x,a,b

def completion(w):
    d=len(w);s=identity(d);v=list(w)
    for i in range(1,d):
        x,y=v[0],v[i]
        if not x and not y:continue
        g,a,b=bezout(x,y)
        for row in s:
            z,t=row[0],row[i]
            row[0]=z*(x//g)+t*(y//g)
            row[i]=-b*z+a*t
        v[0],v[i]=g,0
    assert v==[1]+[0]*(d-1)
    assert tuple(row[0] for row in s)==tuple(w) and abs(determinant(s))==1
    return tuple(tuple(int(x) for x in row) for row in s)

def label(b,x,q):return tuple(sum(t*v for t,v in zip(row,x))%q for row in b)
def energy(g,x):return sum((x[i]*g[i][j]*x[j] for i in range(len(x)) for j in range(len(x))),F(0))

@lru_cache(None)
def freeze(q,g,b):
    d=len(g);m=len(b)
    # q times every K basis vector lies in M. Inverse Gram bounds each
    # coordinate of every vector inside this complete shortest-search ball.
    cap=q*q*min(g[i][i] for i in range(d));inv=inverse(g)
    bounds=[isqrt((cap*inv[i][i]).numerator//(cap*inv[i][i]).denominator) for i in range(d)]
    candidates=(x for x in product(*(range(-k,k+1) for k in bounds))
                if next((t>0 for t in x if t),False) and not any(label(b,x,q)))
    length,v=min((energy(g,x),x) for x in candidates)
    assert 0<length<=cap
    divisor=gcd(*v);w=tuple(x//divisor for x in v)
    bw=label(b,w,q)
    assert divisor==(q if any(bw) else 1)
    s=completion(w)
    transformed=tuple(tuple(sum((s[k][i]*g[k][l]*s[l][j] for k in range(d) for l in range(d)),F(0))
                            for j in range(d)) for i in range(d))
    projected=tuple(tuple(transformed[i][j]-transformed[i][0]*transformed[0][j]/transformed[0][0]
                          for j in range(1,d)) for i in range(1,d))
    columns=tuple(tuple(sum(row[k]*s[k][j] for k in range(d))%q for j in range(d)) for row in b)
    if any(bw):
        pivot=next(i for i,t in enumerate(bw) if t)
        quotient=tuple(tuple((columns[i][j]-bw[i]*pow(bw[pivot],-1,q)*columns[pivot][j])%q
                             for j in range(1,d)) for i in range(m) if i!=pivot)
    else:quotient=tuple(row[1:] for row in columns)
    # Independently check quotient-zero iff some lift along primitive w is in M.
    for y in product(range(q),repeat=d-1):
        can_lift=any(not any(label(columns,(t,)+y,q)) for t in range(q))
        assert can_lift==(not any(label(quotient,y,q)))
    # Determinant squared avoids irrational shortest lengths.
    before=q**(2*m)*determinant(g)
    after=q**(2*len(quotient))*determinant(projected)
    assert after==before/length
    assert len({label(quotient,y,q) for y in product(range(q),repeat=d-1)})==q**len(quotient)
    return projected,quotient,length,divisor


def append(g,b,u,q):
    d=len(g)
    newg=tuple(tuple(g[i][j] if i<d and j<d else F(int(i==j))
                     for j in range(d+1)) for i in range(d+1))
    newb=tuple(tuple(row)+((-u[i])%q,) for i,row in enumerate(b))
    assert determinant(newg)==determinant(g)
    return newg,newb


def main():
    q=3
    initial=tuple(tuple(row) for row in identity(3))
    states={(initial,((1,(-a)%q,(-b)%q),)):F(1,q*q)
            for a,b in product(range(q),repeat=2)}
    for step in range(1,4):
        following=defaultdict(F);rank_mass=defaultdict(F);drops=F(0)
        for (g,b),mass in states.items():
            pg,pb,length,divisor=freeze(q,g,b)
            if divisor==q:drops+=mass
            rank_mass[len(pb)]+=mass
            for u in product(range(q),repeat=len(pb)):
                following[append(pg,pb,u,q)]+=mass/F(q**len(pb))
        assert sum(following.values())==1
        print('step',step,'incoming states',len(states),'outgoing states',len(following),
              'rank-drop probability',drops,'retained rank law',dict(rank_mass))
        states=dict(following)
    # Force a genuine rank drop: q e1 wins in a thin marked direction.
    thin=((F(1,100),F(0),F(0)),(F(0),F(1),F(0)),(F(0),F(0),F(1)))
    pg,pb,length,divisor=freeze(q,thin,((1,0,0),))
    assert divisor==q and length==F(9,100) and pb==()
    assert determinant(pg)==1
    assert len(tuple(product(range(q),repeat=len(pb))))==1
    print('Forced rank-drop and trivial fresh quotient checks passed.')
    print('PASS: three chronological transitions conserve exact probability and determinant identities.')
    print('No high-dimensional tail estimate is claimed.')


if __name__=='__main__':main()
