"""Fourth-relation cover for the nine-position determinant44 anchor."""
from math import comb
from wall1_parallel_contraction import parallel_completion_count, marked_parallel_completion_count


def code_bound(s,t=0,*,no_new_norm_four=False):
    I,iv,n,q,m,R=[s[k] for k in ('I','iv','N','q','m','radius')]
    H=9+t
    dimension=3 if t==0 else 4
    rank=H-dimension
    cutoff=20
    assert 44*cutoff**4<q**2 and H*cutoff**2<q**2
    beta=I(rank*n)/(2*H*R**2)
    a=iv.pi**2/beta
    alpha=a/q**2
    def theta(x):
        geo=lambda y:1+2*iv.exp(-y)/(1-iv.exp(-3*y))
        return geo(x) if x>iv.pi else iv.sqrt(iv.pi/x)*geo(iv.pi**2/x)
    short=theta(4*alpha)*theta(3*alpha)*theta(I(11)/3*alpha)
    if t:
        height=I(11*t+6)/11
        if no_new_norm_four:
            assert q**2>6*H
            height=I(max(3*(11*t+6),110))/33
        short*=theta(height*alpha)
    else:
        assert not no_new_norm_four
    tail=iv.exp(-200*alpha)*theta(alpha/2)**dimension
    delta=2*iv.exp(-a/4)/(1-iv.exp(-2*a))
    periodic=sum((comb(H,j)*delta**j for j in range(1,H+1)),I(0))
    gaussian=(iv.pi/beta)**(I(H)/2)*((short+tail)/q**dimension+periodic)
    return iv.exp(H*beta*R**2)*gaussian**n/q**(rank*m)


def envelopes(s):
    I,q,mu=s['I'],s['q'],s['mu']
    # Choose six old labels, one of75 triangular codes, and one of18 extensions.
    patterns=comb(9,6)*75*18
    assert patterns==113400
    joints={t:code_bound(s,t) for t in range(16)}
    restricted={t:code_bound(s,t,no_new_norm_four=True) for t in range(1,5)}
    def weighted(t,coefficient):
        old=coefficient*joints[t]
        if t>4:return old
        rare=3*comb(9,4-t) if t<4 else 0
        return min((old,rare*joints[t]+coefficient*restricted[t]),key=lambda v:v.b)
    result={}
    for h in range(14,25):
        for r in range(4,h-1):
            if r<6 or r>=h-3:
                result[h,r]=I(0)
                continue
            choices=comb(h,9)*patterns
            if r==6:
                old=choices*joints[0]*q**(5*(h-9))
                dependent=choices*weighted(1,sum(comb(6,a)*q**(a-1) for a in range(3,7)))*q**(5*(h-10))
                result[h,r]=min((old,dependent),key=lambda v:v.b)
                continue
            large,small=I(0),I(0)
            for t in range(2,min(r-5,h-9)+1):
                extra=r-t-5
                coefficient=sum(comb(6,a)*q**(t+a-2) for a in range(max(1,4-t),7))
                charge=(choices*comb(h-9,t)*comb(h-9-t,extra)*weighted(t,coefficient)
                    *mu**extra*q**((r-1)*(h-r-4))/(extra+1))
                if t==2:small+=charge
                else:large+=charge
            parallel=choices*joints[0]*mu**(r-6)*parallel_completion_count(h-9,r-6,6,q)
            marked=(choices*comb(h-9,2)*weighted(2,sum(comb(6,a)*q**a for a in range(2,7)))
                *mu**(r-7)*marked_parallel_completion_count(h-11,r-7,6,q))
            result[h,r]=large+min((small,parallel,marked),key=lambda v:v.b)
    return result
