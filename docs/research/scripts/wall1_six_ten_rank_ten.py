"""Rank-ten D32 anchor cover: both two- and three-new-point crossings."""
from collections import Counter
from itertools import combinations
from functools import reduce
from math import comb,gcd
from wall1_six_ten_projection import REPRESENTATIVES
from wall1_six_ten_rank_nine import COUNTS as TWO_COUNTS,cross


THREE_COUNTS={138:48,144:72,154:132,160:92,168:168,170:152,176:64,184:120,186:348,192:80}

def three_counts():
    results=[]
    for aa,bb in REPRESENTATIVES:
        a=aa+(0,)*3;b=bb+(0,)*3;counts=Counter();total=0
        for old in combinations(range(10),3):
            support=old+(10,11,12)
            for plus in combinations(support[1:],2):
                signs={support[0],*plus}
                v=tuple(1 if i in signs else -1 if i in support else 0 for i in range(13))
                total+=1
                x=sum(i*j for i,j in zip(a,v));y=sum(i*j for i,j in zip(b,v))
                d=192-6*x*x+4*x*y-6*y*y
                cols=list(zip(a,b,v));normals=set();minors=[]
                for i,j in combinations(range(13),2):
                    c=cross(cols[i],cols[j])
                    minors.extend(sum(z*w for z,w in zip(c,cols[k])) for k in range(j+1,13))
                    g=reduce(gcd,c)
                    if g:
                        c=tuple(z//g for z in c)
                        if next(z for z in c if z)<0:c=tuple(-z for z in c)
                        normals.add(c)
                assert 1 in map(abs,minors) and max(map(abs,minors))<7
                if any(sum(sum(x*y for x,y in zip(c,w))==0 for w in cols)>=8 for c in normals):continue
                counts[d]+=1
        assert total==1200 and sum(counts.values())==1200
        results.append(counts)
        print('H13 affine type retained',sum(counts.values()),dict(sorted(counts.items())))
    upper={d:max(c.get(d,0) for c in results) for d in set().union(*results)}
    assert upper==THREE_COUNTS
    print('H13 componentwise witness upper counts',dict(sorted(upper.items())))
    return upper


def code_bound(s,t,height):
    I,iv,n,q,m,R=[s[k] for k in ('I','iv','N','q','m','radius')]
    H,rank,cutoff=10+t,7+t,24
    assert t in (2,3) and 32*cutoff**4<q*q and H*cutoff**2<q*q
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


def envelopes(s,counts=None,*,use_ball_slice=True):
    if counts is None:counts=THREE_COUNTS
    I,q,mu=s['I'],s['q'],s['mu']
    from wall1_ball_slice_completion import completion_bound
    M=completion_bound(s,9) if use_ball_slice else I(q**9)
    joints={}
    for t,strata in ((2,TWO_COUNTS),(3,counts)):
        C=sum(comb(8,a)*q**(t+a-2) for a in range(max(1,6-t),9))
        generic=C*code_bound(s,t,I(t)+I(3)/4)
        rare=sum((count*code_bound(s,t,I(d)/32) for d,count in strata.items()),I(0))
        regular=C*code_bound(s,t,I(31)/6)
        joints[t]=min((generic,rare+regular),key=lambda v:v.b)
    terms={}
    for h in range(15,25):
        common=comb(h,10)*163800*M**(h-13)
        # No multiplicity division: a conservative union over basis extensions.
        terms[h,2]=common*comb(h-10,2)*(h-12)*mu*joints[2]
        terms[h,3]=common*comb(h-10,3)*joints[3]
    return {h:terms[h,2]+terms[h,3] for h in range(15,25)},terms


def diagnostic(counts):
    import contextlib,io
    from wall1_general_two_relations import draw14_bounds
    from wall1_nine_twenty_seven import envelopes as d27_envelopes
    with contextlib.redirect_stdout(io.StringIO()):
        s,_,unrestricted=draw14_bounds()
        _,_,no27=draw14_bounds(exclude_nine_twenty_seven=True)
        _,_,no32=draw14_bounds(exclude_nine_twenty_seven=True,exclude_six_ten_thirty_two=True)
    iv=s['iv'];I=s['I']
    d27=d27_envelopes(s)
    cover,terms=envelopes(s,counts)
    coarse,_=envelopes(s,counts,use_ball_slice=False)
    for h in (18,19,20,24):
        key=h,10,6
        old=min((unrestricted[key],no27[key]+d27[h,10]),key=lambda v:v.b)
        candidate=no32[key]+d27[h,10]+cover[h]
        selected=min((old,candidate),key=lambda v:v.b)
        print('size',h,'complete candidate/actual old log10',iv.log10(candidate/old),
              'selected new/old log10',iv.log10(selected/old))
        print('parts/old log10',{'remainder':str(iv.log10(no32[key]/old)),
              'D27':str(iv.log10(d27[h,10]/old)),
              't2':str(iv.log10(terms[h,2]/old)),
              't3':str(iv.log10(terms[h,3]/old))})
        print('ball-slice/coarse D32 cover log10',iv.log10(cover[h]/coarse[h]))

if __name__=='__main__':diagnostic(three_counts())
