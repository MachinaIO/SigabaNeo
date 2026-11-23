"""Exact H5 determinant23 weights and complete Gaussian-kernel diagnostic."""
import contextlib
import io
import runpy
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
from math import prod,comb
from wall1_rare_second_line import norm_rows
from wall1_three_five_six_pairs import chart

SHARED=F(3,20)
EXCLUSIVE=F(47,30)

def checks():
    fours=list(norm_rows(5,4,minimum_support=3))
    sixes=list(norm_rows(5,6,minimum_support=3))
    families={q:set() for q in (7,17,3329)}
    checked=0
    grams=set()
    for a in fours:
        for b in sixes:
            dot=sum(x*y for x,y in zip(a,b))
            if 24-dot*dot != 23:continue
            if not all(x or y for x,y in zip(a,b)):continue
            shared=[i for i,(x,y) in enumerate(zip(a,b)) if x and y]
            assert len(shared)==2 and sorted(abs(b[i]) for i in shared)==[1,2]
            weights=[SHARED if x and y else EXCLUSIVE for x,y in zip(a,b)]
            assert sum(weights)==5
            inner=lambda x,y:sum((F(u*v)/w for u,v,w in zip(x,y,weights)),F(0))
            first=inner(a,a)
            second=inner(b,b)-inner(a,b)**2/first
            grams.add((first,second,prod(weights)*first*second))
            assert any(abs(a[i]*b[j]-a[j]*b[i])==1 for i,j in combinations(range(5),2))
            for q in families:
                key=chart(a,b,q)
                if key is not None:
                    f,v=key
                    for w in fours:
                        if w==a:continue
                        u=w[0]%q
                        z=(w[3]-u*f[3])%q
                        assert any((w[i]-u*f[i]-z*v[i])%q for i in range(5))
                    families[q].add(key)
            checked+=1
    # A norm-eight D23 partner reduces to norm six by subtracting +/-a.
    for a in fours:
        for b in norm_rows(5,8,minimum_support=3):
            dot=sum(x*y for x,y in zip(a,b))
            if 32-dot*dot!=23 or not all(x or y for x,y in zip(a,b)):continue
            reduced=tuple(y-(1 if dot>0 else -1)*x for x,y in zip(a,b))
            assert sum(x*x for x in reduced)==6 and sum(reduced)==0
            assert all(x or y for x,y in zip(a,reduced))
            for q in families:
                key=chart(a,b,q)
                if key is not None:assert key in families[q]
    assert checked==60
    assert all(len(v)==6 for v in families.values())
    assert len(grams)==1
    first,second,detprod=grams.pop()
    assert detprod>23
    print('Passed',checked,'full-support D23 pairs; prescribed charts=6 at q7,17,3329.')
    print('weighted GS:',first,second,'determinant times product weights:',detprod)
    return first,second,detprod


def diagnostic(first,second):
    with contextlib.redirect_stdout(io.StringIO()):
        s=runpy.run_path(str(Path(__file__).with_name('wall1_draw14_frontier.py')))
    I,iv,q,n,R=[s[k] for k in ('I','iv','q','N','radius')]
    beta=I(3*n)/(10*R**2)
    a=iv.pi**2/beta
    alpha=a/q**2
    def theta(x):
        geometric=s['geometry']['theta_upper']
        return geometric(x) if x>iv.pi else iv.sqrt(iv.pi/x)*geometric(iv.pi**2/x)
    def kernel(g1,g2,weighted=False):
        scale=I(30)/47 if weighted else I(1)
        delta=2*iv.exp(-a*scale/4)/(1-iv.exp(-2*a*scale))
        periodic=sum((comb(5,j)*delta**j for j in range(1,6)),I(0))
        tail=iv.exp(-800*alpha*scale)*theta(I(5)/2*alpha*scale/2)**2
        pref=1/iv.sqrt((I(3)/20)**2*(I(47)/30)**3) if weighted else I(1)
        return (iv.pi/beta)**(I(5)/2)*pref*((theta(g1*alpha)*theta(g2*alpha)+tail)/q**2+periodic)
    old={23:kernel(I(4),I(23)/4),24:kernel(I(4),I(6)),31:kernel(I(4),I(31)/4),36:kernel(I(4),I(9))}
    new=kernel(I(first.numerator)/first.denominator,I(second.numerator)/second.denominator,True)
    Q=q**3
    counts={23:6,24:6,31:12,36:15*q}
    parts={d:I(counts[d])/Q*k**n for d,k in old.items()}
    largest=max(parts.values(),key=lambda v:v.b)
    for d,v in parts.items():print('old component',d,'relative log10',iv.log10(v/largest))
    print('weighted D23 kernel power / old D23 power log10:',iv.log10((new/old[23])**n))
    old_sum=sum(parts.values(),I(0))
    new_sum=old_sum-parts[23]+I(6)/Q*new**n
    print('complete one-four split new/old log10',iv.log10(new_sum/old_sum))
    assert parts[23].a>sum((v for d,v in parts.items() if d!=23),I(0)).b
    assert new.b<old[23].a
    assert iv.log10((new/old[23])**n).b < -58
    assert iv.log10(new_sum/old_sum).b < -4.78



if __name__=='__main__':
    first,second,_=checks()
    diagnostic(first,second)
