"""Nine-position girth-six determinant27 anchor and complete extensions."""
from fractions import Fraction as F
from itertools import combinations, product
from math import comb
from wall1_parallel_contraction import parallel_completion_count, marked_parallel_completion_count


def finite_checks():
    from wall1_rare_second_line import norm_rows
    a=(1,)*6+(0,)*3
    b=(1,)*3+(0,)*3+(1,)*3
    for v in product((-1,0,1),repeat=9):
        sums=[sum(v[j:j+3]) for j in (0,3,6)]
        within=sum(F((v[i]-v[k])**2,3) for j in (0,3,6)
                   for i,k in combinations(range(j,j+3),2))
        explicit=within+F((sums[0]-sums[1]-sums[2])**2,9)
        x,y=sum(z*w for z,w in zip(a,v)),sum(z*w for z,w in zip(b,v))
        D=F(sum(z*z for z in v))-F(6*x*x-6*x*y+6*y*y,27)
        assert D==explicit and (D==0 or D>=F(2,3))
    count=0
    for first in norm_rows(6,6,minimum_support=6):
        first=first+(0,)*3
        for second in norm_rows(9,6,minimum_support=6):
            if not all(second[6:]):continue
            if abs(sum(x*y for x,y in zip(first,second)))!=3:continue
            assert any(abs(first[i]*second[j]-first[j]*second[i])==1
                       for i,j in combinations(range(9),2))
            count+=1
    assert count==560 and comb(9,6)*count==47040
    assert 27*25**4<3329**2
    print('Passed19683 projection checks and560 primitive witnesses per fixed first support.')


def code_bound(s,t=0):
    I,iv,n,q,m,R=[s[k] for k in ('I','iv','N','q','m','radius')]
    H=9+t
    dimension=3 if t else 2
    rank=H-dimension
    beta=I(rank*n)/(2*H*R**2)
    a=iv.pi**2/beta
    alpha=a/q**2
    def theta(x):
        geo=lambda y:1+2*iv.exp(-y)/(1-iv.exp(-3*y))
        return geo(x) if x>iv.pi else iv.sqrt(iv.pi/x)*geo(iv.pi**2/x)
    short=theta(6*alpha)*theta(I(9)*alpha/2)
    if t:
        # Girth six and covering radius squared2 give height >=6-2=4.
        assert q**2>6*H and 27*25**4<q**2
        short*=theta(I(max(3*t+2,12))*alpha/3)
    cutoff=25 if t else 40
    tail=iv.exp(-I(cutoff**2)*alpha/2)*theta(alpha/2)**dimension
    delta=2*iv.exp(-a/4)/(1-iv.exp(-2*a))
    periodic=sum((comb(H,j)*delta**j for j in range(1,H+1)),I(0))
    kernel=(iv.pi/beta)**(I(H)/2)*((short+tail)/q**dimension+periodic)
    return iv.exp(H*beta*R**2)*kernel**n/q**(rank*m)


def envelopes(s):
    I,q,mu=s['I'],s['q'],s['mu']
    size,rank,patterns=9,7,47040
    joints={t:code_bound(s,t) for t in range(16)}
    result={}
    for h in range(15,25):
        for r in range(5,h-1):
            if r<rank or r==h-2:
                result[h,r]=I(0)
                continue
            choices=comb(h,size)*patterns
            if r==rank:
                old=choices*joints[0]*q**((rank-1)*(h-size))
                dependent=(choices*sum(comb(rank,a)*q**(a-1) for a in range(5,rank+1))
                           *joints[1]*q**((rank-1)*(h-size-1)))
                result[h,r]=min((old,dependent),key=lambda v:v.b)
                continue
            large,small=I(0),I(0)
            for t in range(2,min(r-rank+1,h-size)+1):
                extra=r-rank-t+1
                coefficient=sum(comb(rank,a)*q**(t+a-2) for a in range(max(1,6-t),rank+1))
                charge=(choices*comb(h-size,t)*comb(h-size-t,extra)*coefficient*joints[t]
                        *mu**extra*q**((r-1)*(h-r-3))/(extra+1))
                if t==2:small+=charge
                else:large+=charge
            parallel=choices*joints[0]*mu**(r-rank)*parallel_completion_count(h-size,r-rank,rank,q)
            marked=(choices*comb(h-size,2)*sum(comb(rank,a)*q**a for a in range(4,rank+1))
                    *joints[2]*mu**(r-rank-1)*marked_parallel_completion_count(h-size-2,r-rank-1,rank,q))
            result[h,r]=large+min((small,parallel,marked),key=lambda v:v.b)
    return result


if __name__=='__main__':
    finite_checks()
