"""Exact geometric checks for unequal-height selected Gram certificates.

Low-dimensional q-ary lattices, not width506 production histories.
"""
from fractions import Fraction as F
from itertools import product
from math import isqrt
from fixed_quotient_graph_space import FixedQuotientGraphSpace
from wall1_mixed_exclusion_gates import exclude
from wall1_selected_height_gram import selected_height_gram, optimal_height_void


def ball(dimension,squared):
    edge=isqrt(squared)
    return tuple(x for x in product(range(-edge,edge+1),repeat=dimension)
                 if sum(t*t for t in x)<=squared)


def fixture(q):
    # K=Z^3; M_a={(x,y,z): (x,y)=a*z mod q}. det(M_a)=q².
    # Gate is lambda1(M_a)²>11/2, equivalently no nonzero norm²<=5 point.
    model=FixedQuotientGraphSpace(q,2,1,0)
    old=tuple(x for x in ball(3,5) if any(x))
    families=((1,ball(3,4)),(2,ball(3,1)))
    states={((),()):1}
    for x in old:
        states=exclude(states,'quotient',x,model)
    mass,first,gram=selected_height_gram(model,states,families)
    weights,bound=optimal_height_void(mass,first,gram)
    first_only=optimal_height_void(mass,first[:1],(gram[0][:1],))[1]
    bm=F(0);bf=[F(0)]*2;bg=[[F(0)]*2 for _ in range(2)]
    void=F(0);square=F(0);gate_count=0;marks_checked=0
    short4=tuple(x for x in ball(4,5) if any(x))
    for a in product(range(q),repeat=2):
        def label(x):return tuple((x[i]-a[i]*x[2])%q for i in range(2))
        if any(not any(label(x)) for x in old):continue
        gate_count+=1
        for u in product(range(q),repeat=2):
            def graph_member(v):
                return label(v[:3])==tuple(v[3]*t%q for t in u)
            short=any(graph_member(v) for v in short4)
            hits=tuple(sum(label(x)==tuple(j*t%q for t in u) for x in points)
                       for j,points in families)
            # Symmetric points encode negative heights too. The old gate
            # removes height zero; |j|>=3 cannot have norm²<=5.
            assert short==any(hits)
            if not any(u):
                assert short
                continue
            marks_checked+=1;bm+=1;void+=int(not short)
            square+=(1-sum(w*z for w,z in zip(weights,hits)))**2
            for i in range(2):
                bf[i]+=hits[i]
                for j in range(2):bg[i][j]+=hits[i]*hits[j]
    denom=q**4
    assert mass==bm/denom
    assert first==tuple(v/denom for v in bf)
    assert gram==tuple(tuple(v/denom for v in row) for row in bg)
    assert square/denom==bound
    assert void/denom<=bound<=first_only
    assert gate_count>0 and mass>0
    print('q=',q,'old gate maps=',gate_count,'of',q*q,
          'nonzero graph marks checked=',marks_checked)
    print('Joint strict-long probability=',void/denom,
          'height-one upper=',first_only,'optimized two-height upper=',bound,
          'weights=',weights)
    print('Conditional on old gate: actual=',void/F(gate_count*q*q),
          'optimized upper=',bound/F(gate_count,q*q))
    return bound<first_only


if __name__=='__main__':
    improved=[fixture(q) for q in (7,11)]
    assert any(improved)
    print('PASS: complete geometric short-vector enumeration agrees with shared-mark moments.')
    print('Old-minimum conditioning is not the complete chronological BKZ selection law.')
