"""Complete D32 crossing covers for ranks eleven and twelve (t<=5 only)."""
from collections import Counter
from itertools import combinations
from functools import reduce
from math import comb,gcd
from wall1_six_ten_projection import REPRESENTATIVES
from wall1_six_ten_rank_nine import COUNTS as TWO_COUNTS,cross
from wall1_six_ten_rank_ten import THREE_COUNTS


HIGHER_COUNTS={4:{160:6,168:64,170:88,176:84,184:80,186:80,192:66},
               5:{184:20,186:80}}

def short_counts(t):
    assert t in (4,5)
    H=10+t;results=[]
    for aa,bb in REPRESENTATIVES:
        a=aa+(0,)*t;b=bb+(0,)*t;counts=Counter();total=0
        for old in combinations(range(10),6-t):
            support=old+tuple(range(10,H))
            for plus in combinations(support[1:],2):
                signs={support[0],*plus}
                v=tuple(1 if i in signs else -1 if i in support else 0 for i in range(H))
                total+=1
                x=sum(i*j for i,j in zip(a,v));y=sum(i*j for i,j in zip(b,v))
                d=192-6*x*x+4*x*y-6*y*y
                cols=list(zip(a,b,v));normals=set();minors=[]
                for i,j in combinations(range(H),2):
                    c=cross(cols[i],cols[j])
                    minors.extend(sum(z*w for z,w in zip(c,cols[k])) for k in range(j+1,H))
                    g=reduce(gcd,c)
                    if g:
                        c=tuple(z//g for z in c)
                        if next(z for z in c if z)<0:c=tuple(-z for z in c)
                        normals.add(c)
                assert 1 in map(abs,minors) and max(map(abs,minors))<7
                if any(sum(sum(x*y for x,y in zip(c,w))==0 for w in cols)>=H-5 for c in normals):continue
                assert d>=32*t+24
                counts[d]+=1
        assert total==comb(10,6-t)*10 and sum(counts.values())==total
        print('t',t,'type retained',total,dict(sorted(counts.items())))
        results.append(counts)
    upper={d:max(c.get(d,0) for c in results) for d in set().union(*results)}
    assert upper==HIGHER_COUNTS[t]
    print('t',t,'componentwise upper',dict(sorted(upper.items())))
    return upper


def code_bound(s,t,height):
    I,iv,n,q,m,R=[s[k] for k in ('I','iv','N','q','m','radius')]
    assert 2<=t<=5
    H,rank,cutoff=10+t,7+t,24
    assert 32*cutoff**4<q*q and H*cutoff**2<q*q
    beta=I(rank*n)/(2*H*R**2);a=iv.pi**2/beta;alpha=a/q**2
    def theta(x):
        geo=lambda y:1+2*iv.exp(-y)/(1-iv.exp(-3*y))
        return geo(x) if x>iv.pi else iv.sqrt(iv.pi/x)*geo(iv.pi**2/x)
    short=theta(6*alpha)*theta(I(16)/3*alpha)*theta(height*alpha)
    tail=iv.exp(-I(cutoff**2)*alpha/2)*theta(alpha/2)**3
    delta=2*iv.exp(-a/4)/(1-iv.exp(-2*a))
    periodic=sum((comb(H,j)*delta**j for j in range(1,H+1)),I(0))
    kernel=(iv.pi/beta)**(I(H)/2)*((short+tail)/q**3+periodic)
    return iv.exp(H*beta*R**2)*kernel**n/q**(rank*m)


def envelopes(s,counts=None):
    if counts is None:counts={2:TWO_COUNTS,3:THREE_COUNTS,**HIGHER_COUNTS}
    I,q,mu=s['I'],s['q'],s['mu']
    from wall1_ball_slice_completion import completion_bound
    joints={}
    for t,strata in counts.items():
        C=sum(comb(8,a)*q**(t+a-2) for a in range(6-t,9))
        base=I(t)+I(3)/4
        generic=C*code_bound(s,t,base)
        rare=sum((count*code_bound(s,t,I(d)/32) for d,count in strata.items()),I(0))
        regular=C*code_bound(s,t,max(base,I(31)/6))
        joints[t]=min((generic,rare+regular),key=lambda v:v.b)
    result={};terms={}
    for r in (11,12):
        M=completion_bound(s,r-1)
        for h in range(max(15,r+3),25):
            common=comb(h,10)*163800*M**(h-r-3)
            for t in range(2,r-6):
                extra=r-7-t
                terms[h,r,t]=(common*comb(h-10,t)*comb(h-10-t,extra)
                               *mu**extra*joints[t])
            result[h,r]=sum((terms[h,r,t] for t in range(2,r-6)),I(0))
    return result,terms


def diagnostic(counts):
    import contextlib,io
    from wall1_general_two_relations import draw14_bounds
    from wall1_nine_twenty_seven import envelopes as d27_envelopes
    with contextlib.redirect_stdout(io.StringIO()):
        s,_,unrestricted=draw14_bounds()
        _,_,no27=draw14_bounds(exclude_nine_twenty_seven=True)
        _,_,no32=draw14_bounds(exclude_nine_twenty_seven=True,exclude_six_ten_thirty_two=True)
    iv=s['iv'];d27=d27_envelopes(s);cover,terms=envelopes(s,counts)
    for h in (18,19,20,24):
        for r in (11,12):
            key=h,r,6
            old=min((unrestricted[key],no27[key]+d27[h,r]),key=lambda v:v.b)
            candidate=no32[key]+d27[h,r]+cover[h,r]
            selected=min((old,candidate),key=lambda v:v.b)
            print('h,r',h,r,'complete candidate/actual old log10',iv.log10(candidate/old),
                  'selected new/old',iv.log10(selected/old))
            print('parts/old',{'remainder':str(iv.log10(no32[key]/old)),
                  'D27':str(iv.log10(d27[h,r]/old)),
                  **{'t'+str(t):str(iv.log10(terms[h,r,t]/old)) for t in range(2,r-6)}})

if __name__=='__main__':
    diagnostic({2:TWO_COUNTS,3:THREE_COUNTS,4:short_counts(4),5:short_counts(5)})
