"""Complete same-rank dependent-point cover for the four-pair rank-five anchor."""
from math import comb
from wall1_short_relation_shapes import equal_pair_sum_ball_bound,equal_pair_sum_alias_bound
from wall1_four_pair_dependent_codes import UPPER_COUNTS


def dependent_kernel(s,*,determinant=None,no_new_norm_four=False):
    I,iv,n,q,m,R=[s[k] for k in ('I','iv','N','q','m','radius')]
    assert determinant is None or (determinant in UPPER_COUNTS and not no_new_norm_four)
    height=I(3)/2
    if no_new_norm_four:height=I(43)/12
    if determinant is not None:height=I(determinant)/32
    assert 32*24**4<q**2 and 9*24**2<q**2 and q**2>6*9
    beta=I(5*n)/(18*R**2)
    a=iv.pi**2/beta;alpha=a/q**2
    def theta(x):
        geo=lambda y:1+2*iv.exp(-y)/(1-iv.exp(-3*y))
        return geo(x) if x>iv.pi else iv.sqrt(iv.pi/x)*geo(iv.pi**2/x)
    short=theta(4*alpha)*theta(3*alpha)*theta(I(8)/3*alpha)*theta(height*alpha)
    tail=iv.exp(-288*alpha)*theta(alpha/2)**4
    delta=2*iv.exp(-a/4)/(1-iv.exp(-2*a))
    periodic=sum((comb(9,j)*delta**j for j in range(1,10)),I(0))
    gaussian=(iv.pi/beta)**(I(9)/2)*((short+tail)/q**4+periodic)
    return iv.exp(9*beta*R**2)*gaussian**n/q**(5*m)


def rank_five_envelope(s,h):
    assert h>=9
    I,q,n,m,R=[s[k] for k in ('I','q','N','m','radius')]
    anchor=(equal_pair_sum_ball_bound(R**2,n,4)+equal_pair_sum_alias_bound(R**2,n,4,q))/q**(5*m)
    choices=comb(h,8)*945
    old=choices*anchor*q**(4*(h-8))
    coefficients=sum(comb(5,a)*q**(a-1) for a in range(3,6))
    exceptional=sum((count*dependent_kernel(s,determinant=d) for d,count in UPPER_COUNTS.items()),I(0))
    joint=min((coefficients*dependent_kernel(s),exceptional+coefficients*dependent_kernel(s,no_new_norm_four=True)),key=lambda v:v.b)
    extended=choices*joint*q**(4*(h-9))
    return min((old,extended),key=lambda v:v.b)
