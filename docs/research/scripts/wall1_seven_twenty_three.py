"""Seven-position norm-four/norm-six determinant23 anchor."""
from fractions import Fraction as F
from itertools import product
from math import comb
from wall1_parallel_contraction import parallel_completion_count, marked_parallel_completion_count


def finite_checks():
    from wall1_short_relation_shapes import balanced_rows
    from wall1_rare_second_line import norm_rows
    a,b=(1,1,1,1,0,0,0),(1,-1,0,1,1,1,1)
    checked=0
    for v in product((-1,0,1),repeat=7):
        norm=sum(z*z for z in v)
        if norm>2:continue
        x,y=sum(z*w for z,w in zip(a,v)),sum(z*w for z,w in zip(b,v))
        D=F(norm)-F(6*x*x-2*x*y+4*y*y,23)
        assert D==0 or D>=F(11,23)
        checked+=1
    assert checked==99 and F(48+11,23)<3
    count=sum(1 for a in balanced_rows((0,1,2,3),7)
              for b in norm_rows(7,6) if all(b[4:])
              and abs(sum(x*y for x,y in zip(a,b)))==1)
    assert count==84 and comb(7,4)*count==2940
    assert 23*26**4<3329**2
    print('Passed all 99 integer vectors of squared norm <=2 and 84 short pairs per first support.')


def code_bound(s,new_positions=0, *, no_new_norm_four=False, anchor_size=7,
               one_point_determinant=None):
    """The optional restriction requires covering additional norm-four codes separately."""
    I,iv,n,q,m,R=[s[k] for k in ('I','iv','N','q','m','radius')]
    assert anchor_size in (7,10,11)
    determinant={7:23,10:28,11:31}[anchor_size]
    H=anchor_size+new_positions
    dimension=2 if new_positions==0 else 3
    rank=H-dimension
    beta=I(rank*n)/(2*H*R**2)
    a=iv.pi**2/beta
    alpha=a/q**2
    def theta(x):
        geo=lambda y:1+2*iv.exp(-y)/(1-iv.exp(-3*y))
        return geo(x) if x>iv.pi else iv.sqrt(iv.pi/x)*geo(iv.pi**2/x)
    short=theta(4*alpha)*theta(I(determinant)*alpha/4)
    if new_positions:
        height=I(new_positions)+{7:I(11)/23,10:I(1)/2,11:I(21)/31}[anchor_size]
        if no_new_norm_four:
            assert q**2>6*H
            # Squared rounding radii48/23,16/7,47/16 respectively.
            height=max(height,{7:I(90)/23,10:I(26)/7,11:I(49)/16}[anchor_size])
        if one_point_determinant is not None:
            if anchor_size==10:
                from wall1_ten_dependent_codes import UPPER_COUNTS
            else:
                from wall1_eleven_dependent_codes import UPPER_COUNTS
            assert anchor_size in (10,11) and new_positions==1 and not no_new_norm_four
            assert one_point_determinant in UPPER_COUNTS
            height=I(one_point_determinant)/determinant
        short*=theta(height*alpha)
        cutoff={7:26,10:25,11:24}[anchor_size]
        assert determinant*cutoff**4<q**2
    else:
        cutoff=40
        assert 2*cutoff**2<q
    tail=iv.exp(-I(cutoff**2)*alpha/2)*theta(alpha/2)**dimension
    delta=2*iv.exp(-a/4)/(1-iv.exp(-2*a))
    periodic=sum((comb(H,j)*delta**j for j in range(1,H+1)),I(0))
    gaussian=(iv.pi/beta)**(I(H)/2)*((short+tail)/q**dimension+periodic)
    return iv.exp(H*beta*R**2)*gaussian**n/q**(rank*m)


def envelopes(s, *, anchor_size=7):
    I,q,mu=s['I'],s['q'],s['mu']
    assert anchor_size in (7,10,11)
    size,rank,patterns=anchor_size,anchor_size-2,{7:2940,10:69300,11:138600}[anchor_size]
    joints={t:code_bound(s,t,anchor_size=size) for t in range(25-size)}
    restricted={t:code_bound(s,t,no_new_norm_four=True,anchor_size=size) for t in range(1,5)}
    if size in (10,11):
        if size==10:
            from wall1_ten_dependent_codes import UPPER_COUNTS
        else:
            from wall1_eleven_dependent_codes import UPPER_COUNTS
        dependent_rare=sum((count*code_bound(s,1,anchor_size=size,one_point_determinant=d)
                            for d,count in UPPER_COUNTS.items()),I(0))
    def weighted(t,coefficient):
        old=coefficient*joints[t]
        if t>4:
            return old
        rare=(dependent_rare if size in (10,11) and t==1 else 3*comb(size,4-t)*joints[t])
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
