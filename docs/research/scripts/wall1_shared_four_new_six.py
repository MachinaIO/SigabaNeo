"""Exact norm-six split for a shared seven-position anchor and four new points."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations
from math import comb
from wall1_rare_second_line import norm_rows

A=(1,1,-1,-1,0,0,0,0,0,0,0)
B=(1,0,0,0,1,-1,-1,0,0,0,0)

def checks():
    counts=Counter()
    rows=[v for v in norm_rows(11,6,minimum_support=6) if all(v[7:])]
    assert len(rows)==210
    for v in rows:
        x=sum(a*b for a,b in zip(A,v))
        y=sum(a*b for a,b in zip(B,v))
        determinant=90-4*x*x+2*x*y-4*y*y
        assert determinant>=74
        # Old a,b unit minor + a new unit entry give a saturated rank3 basis.
        assert abs(A[1]*B[4]*v[7])==1
        counts[determinant]+=1
    assert dict(counts)==COUNTS
    print('exact norm-six witness counts',dict(sorted(counts.items())))
    return dict(sorted(counts.items()))

COUNTS={74:64,80:46,84:44,86:28,90:28}

def ball_bound(s,height):
    I,iv,n,q,m,R=[s[k] for k in ('I','iv','N','q','m','radius')]
    size,rank,cutoff=11,8,29
    assert 15*cutoff**4<q*q
    beta=I(rank*n)/(2*size*R**2)
    a=iv.pi**2/beta
    alpha=a/q**2
    def theta(x):
        geom=lambda y:1+2*iv.exp(-y)/(1-iv.exp(-3*y))
        return geom(x) if x>iv.pi else iv.sqrt(iv.pi/x)*geom(iv.pi**2/x)
    short=theta(4*alpha)*theta(I(15)/4*alpha)*theta(height*alpha)
    tail=iv.exp(-I(cutoff**2)*alpha/2)*theta(alpha/2)**3
    delta=2*iv.exp(-a/4)/(1-iv.exp(-2*a))
    periodic=sum((comb(size,j)*delta**j for j in range(1,size+1)),I(0))
    kernel=(iv.pi/beta)**(I(size)/2)*((short+tail)/q**3+periodic)
    return iv.exp(size*beta*R**2)*kernel**n/q**(rank*m)


def refined_bound(s,coefficients,old):
    I=s['I']
    rare=sum((count*ball_bound(s,I(d)/15) for d,count in COUNTS.items()),I(0))
    remainder=coefficients*ball_bound(s,I(32)/5)
    return min((old,rare+remainder),key=lambda v:v.b),rare,remainder

if __name__=='__main__':checks()
