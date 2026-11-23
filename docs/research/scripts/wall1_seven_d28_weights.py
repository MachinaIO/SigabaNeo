"""Weighted D28 norm-four/eight plane with a prescribed four-circuit on H7."""
import contextlib,io,runpy
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
from math import comb,prod
from wall1_short_relation_shapes import balanced_rows
from wall1_rare_second_line import norm_rows

def checks():
    count=0
    chart_counts={q:{a:set() for a in (1,2,3)} for q in (7,17,3329)}
    for a in balanced_rows((0,1,2,3),7):
        for b in norm_rows(7,8,minimum_support=4):
            if not all(b[4:]):continue
            dot=sum(x*y for x,y in zip(a,b))
            if 32-dot*dot!=28:continue
            assert sum(bool(x) for x in b[:4])==2
            assert sorted(abs(x) for x in b[4:])==[1,1,2]
            weights=[F(1)]*4+[F(1,5) if abs(x)==2 else F(7,5) for x in b[4:]]
            assert sum(weights)==7
            inner=lambda u,v:sum((F(x*y)/w for x,y,w in zip(u,v,weights)),F(0))
            first=inner(a,a)
            second=inner(b,b)-inner(a,b)**2/first
            assert (first,second)==(F(4),F(157,7))
            assert prod(weights)*first*second==F(4396,125)>28
            assert any(abs(a[i]*b[j]-a[j]*b[i])==1 for i,j in combinations(range(7),2))
            for q,out in chart_counts.items():
                inverse=pow(b[4]%q,-1,q)
                key=(a,tuple((x-b[0]*y)*inverse%q for x,y in zip(b,a)))
                for scalar in {(-b[i]*pow(a[i]%q,-1,q))%q for i in range(4)}:
                    support=tuple(i for i in range(4) if (b[i]+scalar*a[i])%q)
                    for overlap in (1,2,3):
                        if support==tuple(range(overlap)):out[overlap].add(key)
            count+=1
    print('D28 exact weighted Gram witnesses',count)
    for q,counts in chart_counts.items():print('q',q,'charts',{a:len(v) for a,v in counts.items()})
    assert count==108
    assert all({a:len(v) for a,v in counts.items()}=={1:0,2:18,3:0} for counts in chart_counts.values())


def diagnostic():
    with contextlib.redirect_stdout(io.StringIO()):
        s=runpy.run_path(str(Path(__file__).with_name('wall1_draw14_frontier.py')))
    I,iv,q,n,R=[s[k] for k in ('I','iv','q','N','radius')]
    beta=I(5*n)/(14*R**2);a=iv.pi**2/beta;alpha=a/q**2
    def theta(x):
        geometric=s['geometry']['theta_upper']
        return geometric(x) if x>iv.pi else iv.sqrt(iv.pi/x)*geometric(iv.pi**2/x)
    def kernel(g1,g2,weighted=False):
        scale=I(5)/7 if weighted else I(1)
        delta=2*iv.exp(-a*scale/4)/(1-iv.exp(-2*a*scale))
        periodic=sum((comb(7,j)*delta**j for j in range(1,8)),I(0))
        tail=iv.exp(-800*alpha*scale)*theta(I(7)/2*alpha*scale/2)**2
        pref=iv.sqrt(I(125)/49) if weighted else I(1)
        return (iv.pi/beta)**(I(7)/2)*pref*((theta(g1*alpha)*theta(g2*alpha)+tail)/q**2+periodic)
    old={28:kernel(I(4),I(7)),31:kernel(I(4),I(31)/4),32:kernel(I(4),I(8)),36:kernel(I(4),I(9))}
    new=kernel(I(4),I(157)/7,True)
    one_count=min(q**5,105*q**2+3*q**3)
    counts={28:18,31:10,32:18,36:one_count}
    parts={d:I(counts[d])/q**5*k**n for d,k in old.items()}
    print('component ratios to D28',{d:str(iv.log10(v/parts[28])) for d,v in parts.items()})
    print('weighted D28 power ratio log10',iv.log10((new/old[28])**n))
    before=sum(parts.values(),I(0));after=before-parts[28]+I(18)/q**5*new**n
    print('complete one-four split ratio log10',iv.log10(after/before))
    assert new.b<old[28].a
    assert iv.log10((new/old[28])**n).b < -25
    assert iv.log10(after/before).b < -11.7

if __name__=='__main__':
    checks()
    diagnostic()
