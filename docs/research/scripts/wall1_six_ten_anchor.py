"""Complete same-rank cover for ten-position two-six determinant32 anchors."""
from math import comb
from wall1_six_ten_dependent_codes import UPPER_COUNTS


def code_bound(s,*,extended=False,determinant=None,no_new_norm_six=False):
    I,iv,n,q,m,R=[s[k] for k in ('I','iv','N','q','m','radius')]
    H=11 if extended else 10
    dimension=3 if extended else 2
    assert determinant is None or (extended and not no_new_norm_six and determinant in UPPER_COUNTS)
    assert not no_new_norm_six or extended
    cutoff=24 if extended else 40
    assert (32*cutoff**4<q**2 if extended else 2*cutoff**2<q)
    assert H*cutoff**2<q**2
    beta=I(8*n)/(2*H*R**2)
    a=iv.pi**2/beta;alpha=a/q**2
    def theta(x):
        geo=lambda y:1+2*iv.exp(-y)/(1-iv.exp(-3*y))
        return geo(x) if x>iv.pi else iv.sqrt(iv.pi/x)*geo(iv.pi**2/x)
    short=theta(6*alpha)*theta(I(16)/3*alpha)
    if extended:
        height=I(7)/4
        if no_new_norm_six:
            assert q**2>8*H
            height=I(31)/6
        if determinant is not None:height=I(determinant)/32
        short*=theta(height*alpha)
    tail=iv.exp(-I(cutoff**2)*alpha/2)*theta(alpha/2)**dimension
    delta=2*iv.exp(-a/4)/(1-iv.exp(-2*a))
    periodic=sum((comb(H,j)*delta**j for j in range(1,H+1)),I(0))
    gaussian=(iv.pi/beta)**(I(H)/2)*((short+tail)/q**dimension+periodic)
    return iv.exp(H*beta*R**2)*gaussian**n/q**(8*m)


def rank_eight_envelopes(s):
    I,q=s['I'],s['q']
    patterns=comb(10,6)*780
    assert patterns==163800
    anchor=code_bound(s)
    coefficient=sum(comb(8,a)*q**(a-1) for a in range(5,9))
    exceptional=sum((count*code_bound(s,extended=True,determinant=d) for d,count in UPPER_COUNTS.items()),I(0))
    joint=min((coefficient*code_bound(s,extended=True),
        exceptional+coefficient*code_bound(s,extended=True,no_new_norm_six=True)),key=lambda v:v.b)
    return {h:comb(h,10)*patterns*min((anchor*q**(7*(h-10)),joint*q**(7*(h-11))),key=lambda v:v.b)
            for h in range(15,25)}
