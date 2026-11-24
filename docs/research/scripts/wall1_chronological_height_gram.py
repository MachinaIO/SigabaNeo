"""Exact small-width shortest-select/project/append experiments.

Uses actual chronological winner strata, rational projected geometry, and a
fresh independent uniform column. This is not a width506 estimate.
"""
from collections import defaultdict,Counter
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import gcd,isqrt
from mpmath import iv
from fixed_quotient_graph_space import FixedQuotientGraphSpace
from wall1_mixed_exclusion_gates import exclude
from wall1_selected_height_geometry import ball
from wall1_selected_height_gram import selected_height_gram,optimal_height_void


def norm(x):return sum(t*t for t in x)
def dot(x,y):return sum(a*b for a,b in zip(x,y))
def positive(x):return next((t>0 for t in x if t),False)


@lru_cache(None)
def projected_ball(v,radius_squared):
    """One integer representative per P_v Z^d point, with a half-open strip."""
    if radius_squared<0:return ()
    n=norm(v)
    # In the strip, ||x||²=||Px||²+<x,v>²/n <=R²+n/4.
    cutoff=(radius_squared+F(n,4)).__floor__()
    return tuple(x for x in ball(len(v),cutoff)
                 if -n<=2*dot(x,v)<n
                 and F(n*norm(x)-dot(x,v)**2,n)<=radius_squared)



def determinant_radius(q,v):
    """Certified rational enclosure of (1.1*(det M/V_d)^(1/d))²."""
    iv.dps=60
    I=iv.mpf
    d=len(v)
    volume=iv.pi**(I(d)/2)/iv.gamma(I(d)/2+1)
    determinant=I(q*q)/iv.sqrt(norm(v))
    squared=(I(121)/100)*iv.exp((I(2)/d)*iv.ln(determinant/volume))
    # Floating midpoint is only a proposal. Exact interval comparisons below
    # certify both rational endpoints, independently of that proposal.
    scale=10**10
    k=int(float(squared.mid)*scale)
    lower,upper=F(k-2,scale),F(k+3,scale)
    assert (I(lower.numerator)/lower.denominator).b<squared.a
    assert squared.b<(I(upper.numerator)/upper.denominator).a
    assert 1<lower<upper<9
    # Equal endpoint sets certify every intervening irrational radius.
    for j in (0,1,2):
        assert projected_ball(v,lower-j*j)==projected_ball(v,upper-j*j)
    return lower,upper


def run(q,inputs=1,radius=F(11,2)):
    dimension=2+inputs
    variable_radius=radius is None
    fixed_radius=radius
    radius_ranges=[]
    ordered=sorted((x for x in ball(dimension,q*q) if positive(x)),key=lambda x:(norm(x),x))
    strata=defaultdict(list)
    def get_label(a,x):
        return tuple((x[i]-sum(a[i*inputs+k]*x[2+k] for k in range(inputs)))%q
                     for i in range(2))
    for a in product(range(q),repeat=2*inputs):
        label=lambda x:get_label(a,x)
        v=next(x for x in ordered if not any(label(x)))
        assert norm(v)<q*q and gcd(*v)==1
        strata[v].append(a)
    total_actual=F(0);total_bound=F(0);one_bound=F(0)
    surviving=0;checked=0;improved=0
    mixed=0
    survivor_sizes=[]
    for v,maps in strata.items():
        if variable_radius:
            lower,radius=determinant_radius(q,v)
            radius_ranges.append((lower,radius))
        else:radius=fixed_radius
        model=FixedQuotientGraphSpace(q,2,inputs,0,(v,),(v,))
        old=tuple(x for x in projected_ball(v,radius) if any(x))
        families=tuple((j,projected_ball(v,radius-j*j)) for j in (1,2))
        states={((),()):1}
        # Canonical tie-breaking is part of the actual first-winner event.
        for x in ordered:
            if x==v:break
            states=exclude(states,'quotient',x,model)
        for x in old:states=exclude(states,'quotient',x,model)
        mass,first,gram=selected_height_gram(model,states,families,
                                            positive_quotient=(v,))
        weights,bound=optimal_height_void(mass,first,gram)
        single=optimal_height_void(mass,first[:1],(gram[0][:1],))[1]
        bm=F(0);bf=[F(0)]*2;bg=[[F(0)]*2 for _ in range(2)]
        actual=F(0);square=F(0);surviving_here=0
        for a in maps:
            def label(x):return get_label(a,x)
            if any(not any(label(x)) for x in old):continue
            surviving+=1;surviving_here+=1
            for u in product(range(q),repeat=2):
                hits=tuple(sum(label(x)==tuple(j*t%q for t in u) for x in xs)
                           for j,xs in families)
                # Independently enumerate all signed heights and the larger
                # projected ball, then test exact total squared length.
                short=False
                for j in range(-2,3):
                    for x in projected_ball(v,radius):
                        if not any(x) and j==0:continue
                        if F(norm(v)*norm(x)-dot(x,v)**2,norm(v))+j*j>radius:continue
                        if label(x)==tuple(j*t%q for t in u):short=True
                assert short==any(hits)
                checked+=1
                if not any(u):
                    assert short
                    continue
                bm+=1;actual+=int(not short)
                square+=(1-sum(w*z for w,z in zip(weights,hits)))**2
                for i in range(2):
                    bf[i]+=hits[i]
                    for j in range(2):bg[i][j]+=hits[i]*hits[j]
        mixed+=surviving_here>1
        survivor_sizes.append(surviving_here)
        denominator=q**(2*inputs+2)
        assert mass==bm/denominator
        assert first==tuple(z/denominator for z in bf)
        assert gram==tuple(tuple(z/denominator for z in row) for row in bg)
        assert bound==square/denominator
        assert actual/denominator<=bound<=single
        total_actual+=actual/denominator;total_bound+=bound;one_bound+=single
        improved+=bound<single
    assert surviving>0
    if not variable_radius:assert improved>0
    else:
        assert total_bound==one_bound and all(hi<4 for lo,hi in radius_ranges)
        print("Certified squared-radius outer range:",min(lo for lo,hi in radius_ranges),
              max(hi for lo,hi in radius_ranges))
    print('q=',q,'inputs=',inputs,'first-winner strata=',len(strata),'old-gate histories=',surviving,
          'fresh columns checked=',checked,'improved strata=',improved,
          'surviving nonsingleton strata=',mixed)
    if inputs>1:
        assert mixed>0 and any(len(maps)<q**(2*(inputs-1)) for maps in strata.values())
        print("Winner-stratum size histogram:",dict(sorted(Counter(map(len,strata.values())).items())))
        print("After old gate size histogram:",dict(sorted(Counter(survivor_sizes).items())))
    print('Joint old-gate AND next strict-long probability:',total_actual)
    print('Chronological two-height upper:',total_bound,'height-one upper:',one_bound)
    print('PASS: winner-stratified rank moments agree with complete chronological enumeration.')
    print('Histories outside the old gate have a short horizontal vector, so next long is impossible.')
    return total_actual,total_bound


if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser()
    parser.add_argument("--residual",action="store_true")
    parser.add_argument("--production-radius",action="store_true")
    args=parser.parse_args()
    if args.production_radius:run(5,2,None)
    elif args.residual:run(5,2,F(9,2))
    else:run(7)
