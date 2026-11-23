"""Fixed norm-four/norm-six plane of Gram determinant twenty."""
from fractions import Fraction as F
from itertools import product
from math import comb
from collections import Counter
from wall1_parallel_contraction import parallel_completion_count, marked_parallel_completion_count


def anchor_checks():
    from wall1_short_relation_shapes import balanced_rows
    from wall1_rare_second_line import norm_rows
    for q in (7,17,3329):
        codes=Counter()
        for a in balanced_rows((0,1,2,3),8):
            for b in norm_rows(8,6):
                dot=sum(x*y for x,y in zip(a,b))
                if not all(b[4:]) or abs(dot)!=2:
                    continue
                inverse=pow(b[4]%q,-1,q)
                key=(a,tuple((x-b[0]*y)*inverse%q for x,y in zip(b,a)))
                codes[key]+=1
        assert len(codes)==48 and set(codes.values())=={2}
        print(f'q={q}: 48 determinant-twenty planes, each with two short-pair witnesses.')


def projection_checks():
    # Signs are changed so both rows are constant on their three groups.
    a,b=(1,1,1,1,0,0,0,0),(1,1,0,0,1,1,1,1)
    checked=0
    for v in product((-1,0,1),repeat=8):
        x,y=sum(c*d for c,d in zip(a,v)),sum(c*d for c,d in zip(b,v))
        residual=F(sum(c*c for c in v))-F(6*x*x-4*x*y+4*y*y,20)
        s0,s1,s2=sum(v[:2]),sum(v[2:4]),sum(v[4:])
        explicit=(F((v[0]-v[1])**2+(v[2]-v[3])**2,2)
                  +sum(F((v[i]-v[j])**2,4) for i in range(4,8) for j in range(i+1,8))
                  +F((2*s0-2*s1-s2)**2,20))
        assert residual==explicit
        if residual:
            assert residual>=F(7,10)
        else:
            assert v[0]==v[1] and v[2]==v[3] and len(set(v[4:]))==1
            assert v[0]==v[2]+v[4]
        checked+=1
    assert 20*27**4<3329**2
    print(f'Passed {checked} exact determinant-twenty projection identities.')


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
    short=theta(4*alpha)*theta(5*alpha)
    if new_positions:
        height=I(new_positions)+I(7)/10
        if no_new_norm_four:
            assert q**2>6*H
            # Fundamental triangles have circumradius squared 9/5.
            height=max(height,I(21)/5)
        if one_point_determinant is not None:
            assert new_positions==1 and not no_new_norm_four
            assert one_point_determinant in (44,50,56,60,64,66,74,76,80)
            height=I(one_point_determinant)/20
        short*=theta(height*alpha)
        cutoff=27
        assert 20*cutoff**4<q**2
    else:
        cutoff=40
        assert 2*cutoff**2<q
    tail=iv.exp(-I(cutoff**2)*alpha/2)*theta(alpha/2)**dimension
    delta=2*iv.exp(-a/4)/(1-iv.exp(-2*a))
    periodic=sum((comb(H,j)*delta**j for j in range(1,H+1)),I(0))
    gaussian=(iv.pi/beta)**(I(H)/2)*((short+tail)/q**dimension+periodic)
    return iv.exp(H*beta*R**2)*gaussian**n/q**(rank*m)


def envelopes(s, *, exclude_two_short=False):
    """Restricted mode requires a full triangular and other-two-four cover."""
    I,q,mu=s['I'],s['q'],s['mu']
    # 70 first four-supports, each with 48 planes. Each plane has one
    # norm-four line and two norm-six lines; see anchor_checks and the note.
    patterns=3360
    joints={t:code_bound(s,t) for t in range(17)}
    restricted={t:code_bound(s,t,no_new_norm_four=True) for t in range(1,5)}
    from wall1_twenty_dependent_codes import UPPER_COUNTS
    dependent_rare=sum((count*code_bound(s,1,one_point_determinant=d)
                        for d,count in UPPER_COUNTS.items()),I(0))
    if exclude_two_short:
        dependent_rare=I(9)*code_bound(s,1,one_point_determinant=76)
    def weighted(t,coefficient):
        old=coefficient*joints[t]
        if t>4:
            return old
        rare=dependent_rare if t==1 else 3*comb(8,4-t)*joints[t]
        split=rare+coefficient*restricted[t]
        return min((old,split),key=lambda v:v.b)
    result={}
    for h in range(15,25):
        for r in range(4,h-1):
            if r<6 or r==h-2:
                result[h,r]=I(0)
                continue
            choices=comb(h,8)*patterns
            if r==6:
                old=choices*joints[0]*q**(5*(h-8))
                dependent=choices*weighted(1,sum(comb(6,a)*q**(a-1) for a in range(3,7)))*q**(5*(h-9))
                result[h,r]=min((old,dependent),key=lambda v:v.b)
                continue
            large,small=I(0),I(0)
            for t in range(2,min(r-5,h-8)+1):
                extra=r-t-5
                coefficient=sum(comb(6,a)*q**(t+a-2) for a in range(max(1,4-t),7))
                charge=(choices*comb(h-8,t)*comb(h-8-t,extra)*weighted(t,coefficient)
                        *mu**extra*q**((r-1)*(h-r-3))/(extra+1))
                if t==2:small+=charge
                else:large+=charge
            parallel=choices*joints[0]*mu**(r-6)*parallel_completion_count(h-8,r-6,6,q)
            marked=(choices*comb(h-8,2)*weighted(2,sum(comb(6,a)*q**a for a in range(2,7)))
                    *mu**(r-7)*marked_parallel_completion_count(h-10,r-7,6,q))
            result[h,r]=large+min((small,parallel,marked),key=lambda v:v.b)
    return result


if __name__=='__main__':
    anchor_checks()
    projection_checks()
