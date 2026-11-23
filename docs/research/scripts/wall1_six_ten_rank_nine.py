"""Complete rank-nine crossing cover for the ten-position D32 two-six anchor."""
from collections import Counter
from itertools import combinations
from functools import reduce
from math import comb,gcd
from wall1_six_ten_projection import REPRESENTATIVES
from wall1_rare_second_line import norm_rows

COUNTS={120:72,128:54,138:288,144:96,154:128,160:52,168:196,170:264,176:172,184:172,186:408,192:132}

def cross(a,b):
    return (a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])

def checks():
    results=[]
    for aa,bb in REPRESENTATIVES:
        a=aa+(0,0);b=bb+(0,0);counts=Counter();total=0
        for v in norm_rows(12,6,minimum_support=6):
            if not all(v[-2:]):continue
            total+=1
            x=sum(i*j for i,j in zip(a,v));y=sum(i*j for i,j in zip(b,v))
            d=192-6*x*x+4*x*y-6*y*y
            cols=list(zip(a,b,v));normals=set();minors=[]
            for i,j in combinations(range(12),2):
                c=cross(cols[i],cols[j])
                minors.extend(sum(z*w for z,w in zip(c,cols[k])) for k in range(j+1,12))
                g=reduce(gcd,c)
                if g:
                    c=tuple(z//g for z in c)
                    if next(z for z in c if z)<0:c=tuple(-z for z in c)
                    normals.add(c)
            assert 1 in map(abs,minors) and max(map(abs,minors))<7
            # Girth>=6 iff no plane through the origin contains >=7 columns.
            # Such a plane has a rank-two pair, or its rank-one subset can be
            # extended by another column. Unit minors guarantee total rank3.
            if any(sum(sum(x*y for x,y in zip(c,w))==0 for w in cols)>=7 for c in normals):continue
            counts[d]+=1
        assert total==2100 and sum(counts.values())==1908
        results.append(counts)
    upper={d:max(c.get(d,0) for c in results) for d in set().union(*results)}
    assert upper==COUNTS
    print('Passed4200 norm-six witnesses, unit minors, finite-field rank stability; upper counts',upper)

def code_bound(s,height):
    I,iv,n,q,m,R=[s[k] for k in ('I','iv','N','q','m','radius')]
    H,rank,cutoff=12,9,24
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

def envelopes(s):
    I,q=s['I'],s['q']
    C=sum(comb(8,a)*q**a for a in range(4,9))
    rare=sum((count*code_bound(s,I(d)/32) for d,count in COUNTS.items()),I(0))
    regular=C*code_bound(s,I(31)/6)
    joint=min((C*code_bound(s,I(11)/4),rare+regular),key=lambda v:v.b)
    return {h:comb(h,10)*163800*comb(h-10,2)*joint*q**(8*(h-12)) for h in range(15,25)}

if __name__=='__main__':checks()
