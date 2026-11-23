"""Orthogonal norm-four/norm-six plane on eight positions."""
from fractions import Fraction as F
from itertools import product
from math import comb
from wall1_parallel_contraction import parallel_completion_count, marked_parallel_completion_count


def finite_checks():
    from wall1_short_relation_shapes import balanced_rows
    from wall1_rare_second_line import norm_rows
    a,b=(1,1,1,1,0,0,0,0),(1,-1,0,0,1,1,1,1)
    checked=0
    for v in product((-1,0,1),repeat=8):
        norm=sum(z*z for z in v)
        if norm>3:continue
        x,y=sum(z*w for z,w in zip(a,v)),sum(z*w for z,w in zip(b,v))
        D=F(norm)-F(x*x,4)-F(y*y,6)
        assert D==0 or D>=F(7,12)
        checked+=1
    assert checked==577
    count=0
    for a in balanced_rows((0,1,2,3),8):
        for b in norm_rows(8,6):
            if all(b[4:]) and sum(x*y for x,y in zip(a,b))==0:
                count+=1
    assert count==84 and comb(8,4)*count==5880
    assert 24*26**4<3329**2
    print('Passed all 577 integer vectors of squared norm <=3, and 84 short pairs per first support.')


def code_bound(s,new_positions=0, *, no_new_norm_four=False, one_point_determinant=None):
    """The optional restriction requires covering additional norm-four codes separately."""
    I,iv,n,q,m,R=[s[k] for k in ('I','iv','N','q','m','radius')]
    H=8+new_positions
    dimension=2 if new_positions==0 else 3
    rank=H-dimension
    beta=I(rank*n)/(2*H*R**2)
    a=iv.pi**2/beta
    alpha=a/q**2
    def theta(x):
        geo=lambda y:1+2*iv.exp(-y)/(1-iv.exp(-3*y))
        return geo(x) if x>iv.pi else iv.sqrt(iv.pi/x)*geo(iv.pi**2/x)
    short=theta(4*alpha)*theta(6*alpha)
    if new_positions:
        height=I(new_positions)+I(7)/12
        if no_new_norm_four:
            assert q**2>6*H
            # Fundamental triangles have circumradius squared 5/2.
            height=max(height,I(7)/2)
        if one_point_determinant is not None:
            from wall1_twenty_four_dependent_codes import UPPER_COUNTS
            assert new_positions==1 and not no_new_norm_four
            assert one_point_determinant in UPPER_COUNTS
            height=I(one_point_determinant)/24
        short*=theta(height*alpha)
        cutoff=26
        assert 24*cutoff**4<q**2
    else:
        cutoff=40
        assert 2*cutoff**2<q
    tail=iv.exp(-I(cutoff**2)*alpha/2)*theta(alpha/2)**dimension
    delta=2*iv.exp(-a/4)/(1-iv.exp(-2*a))
    periodic=sum((comb(H,j)*delta**j for j in range(1,H+1)),I(0))
    gaussian=(iv.pi/beta)**(I(H)/2)*((short+tail)/q**dimension+periodic)
    return iv.exp(H*beta*R**2)*gaussian**n/q**(rank*m)


def envelopes(s):
    I,q,mu=s['I'],s['q'],s['mu']
    size,rank,patterns=8,6,5880
    joints={t:code_bound(s,t) for t in range(17)}
    restricted={t:code_bound(s,t,no_new_norm_four=True) for t in range(1,5)}
    from wall1_twenty_four_dependent_codes import UPPER_COUNTS
    dependent_rare=sum((count*code_bound(s,1,one_point_determinant=d)
                        for d,count in UPPER_COUNTS.items()),I(0))
    def weighted(t,coefficient):
        old=coefficient*joints[t]
        if t>4:
            return old
        rare=dependent_rare if t==1 else 3*comb(size,4-t)*joints[t]
        split=rare+coefficient*restricted[t]
        return min((old,split),key=lambda v:v.b)
    result={}
    for h in range(15,25):
        for r in range(4,h-1):
            if r<rank or r==h-2:
                result[h,r]=I(0)
                continue
            choices=comb(h,size)*patterns
            if r==rank:
                old=choices*joints[0]*q**((rank-1)*(h-size))
                dependent=(choices*weighted(1,sum(comb(rank,a)*q**(a-1) for a in range(3,rank+1)))
                           *q**((rank-1)*(h-size-1)))
                result[h,r]=min((old,dependent),key=lambda v:v.b)
                continue
            large,small=I(0),I(0)
            for t in range(2,min(r-rank+1,h-size)+1):
                extra=r-rank-t+1
                coefficient=sum(comb(rank,a)*q**(t+a-2) for a in range(max(1,4-t),rank+1))
                charge=(choices*comb(h-size,t)*comb(h-size-t,extra)*weighted(t,coefficient)
                        *mu**extra*q**((r-1)*(h-r-3))/(extra+1))
                if t==2:small+=charge
                else:large+=charge
            parallel=choices*joints[0]*mu**(r-rank)*parallel_completion_count(h-size,r-rank,rank,q)
            marked=(choices*comb(h-size,2)*weighted(2,sum(comb(rank,a)*q**a for a in range(2,rank+1)))
                    *mu**(r-rank-1)*marked_parallel_completion_count(h-size-2,r-rank-1,rank,q))
            result[h,r]=large+min((small,parallel,marked),key=lambda v:v.b)
    return result


if __name__=='__main__':
    finite_checks()
