"""Girth-three six-position norm-four/norm-six determinant-twenty anchor."""
from fractions import Fraction as F
from itertools import product, combinations
from math import comb
from wall1_parallel_contraction import parallel_completion_count, marked_parallel_completion_count


def finite_checks():
    from wall1_short_relation_shapes import balanced_rows
    from wall1_rare_second_line import norm_rows
    a,b=(1,1,1,1,0,0),(2,0,0,0,1,1)
    checked=0
    for v in product(range(-2,3),repeat=6):
        x,y=sum(z*w for z,w in zip(a,v)),sum(z*w for z,w in zip(b,v))
        D=F(sum(z*z for z in v))-F(6*x*x-4*x*y+4*y*y,20)
        sa,sb=sum(v[1:4]),sum(v[4:])
        explicit=(sum(F((v[i]-v[j])**2,3) for i in range(1,4) for j in range(i+1,4))
                  +F((v[4]-v[5])**2,2)+F((3*v[0]-sa-3*sb)**2,30))
        assert D==explicit
        if D:assert D>=F(3,10)
        else:assert len(set(v[1:4]))==1 and v[4]==v[5] and v[0]==v[1]+2*v[4]
        checked+=1
    count=0
    for support in combinations(range(6),4):
        for a in balanced_rows(support,6):
            for b in norm_rows(6,6,minimum_support=3):
                if sum(bool(x) for x in b)!=3:continue
                if all(x or y for x,y in zip(a,b)) and abs(sum(x*y for x,y in zip(a,b)))==2:
                    count+=1
    assert count==180 and 20*27**4<3329**2
    print(f'Passed {checked} projection identities and 180 girth-three anchor witnesses.')


def five_position_checks():
    from wall1_short_relation_shapes import balanced_rows
    from wall1_rare_second_line import norm_rows
    a,b=(1,1,1,1,0),(1,1,0,0,2)
    for v in product(range(-2,3),repeat=5):
        x,y=sum(z*w for z,w in zip(a,v)),sum(z*w for z,w in zip(b,v))
        D=F(sum(z*z for z in v))-F(6*x*x-4*x*y+4*y*y,20)
        explicit=(F((v[0]-v[1])**2+(v[2]-v[3])**2,2)
                  +F((v[0]+v[1]-v[2]-v[3]-v[4])**2,5))
        assert D==explicit and (D==0 or D>=F(1,5))
    count=0
    for support in combinations(range(5),4):
        for a in balanced_rows(support,5):
            for b in norm_rows(5,6,minimum_support=3):
                if all(x or y for x,y in zip(a,b)) and abs(sum(x*y for x,y in zip(a,b)))==2:
                    assert any(abs(a[i]*b[j]-a[j]*b[i])==1 for i,j in combinations(range(5),2))
                    count+=1
    assert count==30
    print('Passed3125 five-position projection identities and30 primitive anchor witnesses.')


def code_bound(s,new_positions=0, *, no_new_norm_four=False, anchor_size=6,
               determinant=20):
    """The optional restriction requires covering additional norm-four codes separately."""
    I,iv,n,q,m,R=[s[k] for k in ('I','iv','N','q','m','radius')]
    assert anchor_size in (5,6)
    assert determinant==20 or (determinant==15 and anchor_size==5) or (determinant==23 and anchor_size==6)
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
        projected_minimum=(F(1,3) if determinant==15 else F(7,23) if determinant==23
                           else F(1,5) if anchor_size==5 else F(3,10))
        height_fraction=F(new_positions)+projected_minimum
        if no_new_norm_four:
            assert q**2>6*H
            covering={15:F(8,5),20:F(9,5),23:F(48,23)}[determinant]
            height_fraction=max(height_fraction,F(6)-covering)
        height=I(height_fraction.numerator)/height_fraction.denominator
        short*=theta(height*alpha)
        cutoff={15:29,20:27,23:26}[determinant]
        assert determinant*cutoff**4<q**2
    else:
        cutoff=40
        assert 2*cutoff**2<q
    tail=iv.exp(-I(cutoff**2)*alpha/2)*theta(alpha/2)**dimension
    delta=2*iv.exp(-a/4)/(1-iv.exp(-2*a))
    periodic=sum((comb(H,j)*delta**j for j in range(1,H+1)),I(0))
    gaussian=(iv.pi/beta)**(I(H)/2)*((short+tail)/q**dimension+periodic)
    return iv.exp(H*beta*R**2)*gaussian**n/q**(rank*m)


def envelopes(s, *, anchor_size=6, determinant=20):
    I,q,mu=s['I'],s['q'],s['mu']
    assert anchor_size in (5,6)
    assert determinant==20 or (determinant==15 and anchor_size==5) or (determinant==23 and anchor_size==6)
    size,rank=anchor_size,anchor_size-2
    patterns=60 if determinant==15 else 360 if determinant==23 else 30 if anchor_size==5 else 180
    joints={t:code_bound(s,t,anchor_size=size,determinant=determinant) for t in range(25-size)}
    restricted={t:code_bound(s,t,no_new_norm_four=True,anchor_size=size,determinant=determinant) for t in range(1,5)}
    def weighted(t,coefficient):
        old=coefficient*joints[t]
        if t>4:
            return old
        rare=3*comb(size,4-t)*joints[t]
        split=rare+coefficient*restricted[t]
        return min((old,split),key=lambda v:v.b)
    result={}
    for h in range(15,25):
        for r in range(rank,h-1):
            if r<rank or r==h-2:
                result[h,r]=I(0)
                continue
            choices=comb(h,size)*patterns
            if r==rank:
                old=choices*joints[0]*q**((rank-1)*(h-size))
                dependent=(choices*weighted(1,sum(comb(rank,a)*q**(a-1) for a in range(2,rank+1)))
                           *q**((rank-1)*(h-size-1)))
                result[h,r]=min((old,dependent),key=lambda v:v.b)
                continue
            large,small=I(0),I(0)
            for t in range(2,min(r-rank+1,h-size)+1):
                extra=r-rank-t+1
                coefficient=sum(comb(rank,a)*q**(t+a-2) for a in range(max(1,3-t),rank+1))
                charge=(choices*comb(h-size,t)*comb(h-size-t,extra)*weighted(t,coefficient)
                        *mu**extra*q**((r-1)*(h-r-3))/(extra+1))
                if t==2:small+=charge
                else:large+=charge
            parallel=choices*joints[0]*mu**(r-rank)*parallel_completion_count(h-size,r-rank,rank,q)
            marked=(choices*comb(h-size,2)*weighted(2,sum(comb(rank,a)*q**a for a in range(1,rank+1)))
                    *mu**(r-rank-1)*marked_parallel_completion_count(h-size-2,r-rank-1,rank,q))
            result[h,r]=large+min((small,parallel,marked),key=lambda v:v.b)
    return result


if __name__=='__main__':
    finite_checks()
    five_position_checks()
