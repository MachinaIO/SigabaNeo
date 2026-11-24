"""Exact shared-affine-coefficient pivot bound for nonnegative periodic tests."""
from fractions import Fraction as F
from itertools import product


def rank(a,q):
    a=[list(row) for row in a];out=0
    for j in range(len(a[0])):
        pos=next((i for i in range(out,len(a)) if a[i][j]%q),None)
        if pos is None:continue
        a[out],a[pos]=a[pos],a[out]
        z=pow(a[out][j]%q,-1,q);a[out]=[(v*z)%q for v in a[out]]
        for i in range(len(a)):
            if i!=out:
                z=a[i][j];a[i]=[(x-z*y)%q for x,y in zip(a[i],a[out])]
        out+=1
        if out==len(a):break
    return out


def main():
    tested=0
    for q in (3,5):
        k=n=r=2;d=r-1
        f=[F(1,2)**min(i,q-i)**2 for i in range(q)]
        h=max(f);Q=sum(f)
        for entries in product(range(q),repeat=k*n):
            b=[entries[:n],entries[n:]];t=rank(b,q)
            for offset in (0,1):
                total=F(0)
                for v in product(range(q),repeat=k):
                    rows=[v,tuple((1-x)%q for x in v)]
                    weight=F(1)
                    for j in range(r):
                        for i in range(n):
                            x=(sum(rows[j][a]*b[a][i] for a in range(k))+offset*(j+i+1))%q
                            weight*=f[x]
                    total+=weight
                cap=q**(d*(k-t))*(h*Q**d)**t*h**(r*(n-t))
                assert total<=cap
                assert total/q**(d*k)<=h**(r*n)*(Q/(q*h))**(d*t)
                tested+=1
    # Rank averaging identity for every distribution supported in {0,...,k}.
    for weights in product(range(3),repeat=4):
        if not sum(weights):continue
        p=[F(x,sum(weights)) for x in weights];zeta=F(2,5);k=3
        expectation=sum(p[t]*zeta**t for t in range(k+1))
        tail=zeta**k+sum((zeta**t-zeta**(t+1))*sum(p[:t+1]) for t in range(k))
        assert expectation==tail
    print('Passed',tested,'exact fixed-dual coefficient sums and 80 rank-tail identities.')

if __name__=='__main__':main()
