"""Complete cover for a six-position determinant24 rank-four anchor."""
from math import comb
from fractions import Fraction as F
from itertools import product,combinations
from wall1_parallel_contraction import parallel_completion_count,marked_parallel_completion_count


def checks():
    from wall1_short_relation_shapes import balanced_rows
    from wall1_rare_second_line import norm_rows
    a=(1,1,-1,-1,0,0)
    b=(1,-1,1,-1,1,-1)
    checked=0
    for v in product((-1,0,1),repeat=6):
        norm=sum(x*x for x in v)
        if norm>2:continue
        x=sum(c*d for c,d in zip(a,v));y=sum(c*d for c,d in zip(b,v))
        residual=F(norm)-F(x*x,4)-F(y*y,6)
        assert residual==0 or residual>=F(1,3)
        checked+=1
    assert checked==73 and F(5,2)+F(1,3)<3
    witness=0
    for support in combinations(range(6),4):
        for a in balanced_rows(support,6):
            for b in norm_rows(6,6,minimum_support=6):
                if sum(x*y for x,y in zip(a,b)):continue
                old=[(a[i],b[i]) for i in support]
                new=[b[i] for i in range(6) if i not in support]
                assert set(old)=={(1,1),(1,-1),(-1,1),(-1,-1)}
                assert sorted(new)==[-1,1]
                assert any(abs(a[i]*b[j]-a[j]*b[i])==1 for i,j in combinations(range(6),2))
                witness+=1
    assert witness==180
    print('Passed73 projected-vector checks and180 balanced saturated affine-anchor witnesses.')


def code_bound(s,t=0,no_four=False):
    I,iv,n,q,m,R=[s[k] for k in ('I','iv','N','q','m','radius')]
    H=6+t;dimension=2 if t==0 else 3;rank=H-dimension
    beta=I(rank*n)/(2*H*R**2);a=iv.pi**2/beta;alpha=a/q**2
    def theta(x):
        geo=lambda y:1+2*iv.exp(-y)/(1-iv.exp(-3*y))
        return geo(x) if x>iv.pi else iv.sqrt(iv.pi/x)*geo(iv.pi**2/x)
    short=theta(4*alpha)*theta(6*alpha)
    if t:
        height=I(t)+I(1)/3
        if no_four:height=max(height,I(7)/2)
        short*=theta(height*alpha)
        cutoff=26
        assert 24*cutoff**4<q*q
    else:
        cutoff=40
        assert 2*cutoff**2<q
    tail=iv.exp(-I(cutoff**2)*alpha/2)*theta(alpha/2)**dimension
    delta=2*iv.exp(-a/4)/(1-iv.exp(-2*a))
    periodic=sum((comb(H,j)*delta**j for j in range(1,H+1)),I(0))
    gaussian=(iv.pi/beta)**(I(H)/2)*((short+tail)/q**dimension+periodic)
    return iv.exp(H*beta*R**2)*gaussian**n/q**(rank*m)


def envelope(s,h,r, *, _joints=None, _nofour=None):
    assert h>=7 and 4<=r<h
    I,q,mu=s['I'],s['q'],s['mu'];choices=comb(h,6)*180
    if r==h-2:return I(0),{}
    joint=(_joints if _joints is not None else {t:code_bound(s,t) for t in range(max(2,r-2))})
    nofour=(_nofour if _nofour is not None else {t:code_bound(s,t,True) for t in range(1,min(5,r-2))})
    def weighted(t,C):
        old=C*joint[t]
        if t>4:return old
        return min((old,3*comb(6,4-t)*joint[t]+C*nofour[t]),key=lambda v:v.b)
    if r==4:
        C=sum(comb(4,a)*q**(a-1) for a in range(3,5))
        return min((choices*joint[0]*q**(3*(h-6)),choices*weighted(1,C)*q**(3*(h-7))),key=lambda v:v.b),{}
    parts={}
    for t in range(2,min(r-3,h-6)+1):
        extra=r-4-t+1
        C=sum(comb(4,a)*q**(t+a-2) for a in range(max(1,4-t),5))
        parts[t]=(choices*comb(h-6,t)*comb(h-6-t,extra)*weighted(t,C)*mu**extra*q**((r-1)*(h-r-3))/(extra+1))
    parallel=choices*joint[0]*mu**(r-4)*parallel_completion_count(h-6,r-4,4,q)
    marked=(choices*comb(h-6,2)*weighted(2,sum(comb(4,a)*q**a for a in range(2,5)))*mu**(r-5)*marked_parallel_completion_count(h-8,r-5,4,q))
    parts[2]=min((parts[2],parallel,marked),key=lambda v:v.b)
    return sum(parts.values(),I(0)),parts


def envelopes(s):
    joint={t:code_bound(s,t) for t in range(19)}
    nofour={t:code_bound(s,t,True) for t in range(1,5)}
    return {(h,r):envelope(s,h,r,_joints=joint,_nofour=nofour)[0]
            for h in range(15,25) for r in range(4,h-1)}


if __name__=='__main__':checks()
