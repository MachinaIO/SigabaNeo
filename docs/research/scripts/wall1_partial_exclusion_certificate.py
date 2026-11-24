"""Certified arbitrary event-prefix exclusion with a nonnegative remainder.

Each processed prefix is evaluated by complete grouped inclusion-exclusion.
Remaining event intersections are bounded by a union bound applied to each
nonnegative statistic 1,N,J,C inside that processed event. This is not a
truncation by inclusion-exclusion degree. Finite q=3 fixture only.
"""
from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from time import perf_counter
from conditional_graph_space import row_basis
from fixed_quotient_graph_space import FixedQuotientGraphSpace
from wall1_overlapping_selected_incidence import W, label


def main():
    start=perf_counter()
    q=3
    model=FixedQuotientGraphSpace(q,3,3,0,(W,),(W,))
    axes=tuple(tuple(int(i==j) for i in range(6)) for j in range(6))
    a=(1,1,0)
    bad={(0,0,0),a,tuple(-x%q for x in a)}
    for i in range(3):
        for sign in (1,-1):
            bad.add(tuple(sign%q if j==i else 0 for j in range(3)))
    events=[]
    for col in (1,2):
        events.extend(value+tuple(int(j==col) for j in range(3)) for value in sorted(bad))
    events.extend(((0,0,0,0,1,2),(0,0,0,0,1,1)))
    assert len(events)==20

    @lru_cache(maxsize=None)
    def joint(basis,quotient=()):
        return model.joint_probability(basis,quotient)

    @lru_cache(maxsize=None)
    def terms(basis):
        mass=joint(basis)
        if not mass:
            return (F(0),)*4
        def collision(z,zp,t):
            diff=tuple((b-t*a)%q for a,b in zip(z,zp))
            return joint(basis,row_basis((diff,),q))-joint(basis,row_basis((diff,z),q))
        count=sum((mass-joint(basis,row_basis((z,),q)) for z in axes),F(0))
        equal=sum((collision(z,zp,1) for z,zp in product(axes,repeat=2)),F(0))
        scalar=sum((collision(z,zp,t) for z,zp,t in product(axes,axes,(1,2))),F(0))
        return mass,count,equal,scalar

    def weighted(states,event=None):
        result=[F(0)]*4
        for basis,coefficient in states.items():
            augmented=basis if event is None else row_basis(basis+(event,),q)
            result=[v+coefficient*t for v,t in zip(result,terms(augmented))]
        assert all(v>=0 for v in result)
        return tuple(result)

    # Independent direct selected-map targets, not inferred from IE.
    totals=[0]*4
    for b,c in product(product(range(q),repeat=3),repeat=2):
        matrix=tuple((a[i],b[i],c[i]) for i in range(3))
        if any(not any(label(matrix,event)) for event in events):
            continue
        labels=[label(matrix,z) for z in axes]
        covered={tuple(t*x%q for x in v) for v in labels for t in (1,2) if any(v)}
        assert len(covered)==12
        totals[0]+=1
        totals[1]+=sum(any(v) for v in labels)
        totals[2]+=sum(any(v) and v==w for v,w in product(labels,repeat=2))
        totals[3]+=sum(any(v) and w==tuple(t*x%q for x in v)
                       for v,w,t in product(labels,labels,(1,2)))
    assert totals==[288,1728,1728,1728]
    target=tuple(F(v,q**9) for v in totals)
    states={row_basis((W,),q):1}
    previous_upper=None
    lower_envelope=[F(0)]*4
    first_positive_n=first_saving=None
    certificates=[]
    for prefix in range(len(events)+1):
        upper=weighted(states)
        remaining=[F(0)]*4
        for event in events[prefix:]:
            intersection=weighted(states,event)
            assert all(x<=u for x,u in zip(intersection,upper))
            remaining=[v+x for v,x in zip(remaining,intersection)]
        lower=tuple(max(F(0),u-rem) for u,rem in zip(upper,remaining))
        assert all(lo<=truth<=hi for lo,truth,hi in zip(lower,target,upper))
        if previous_upper is not None:
            assert all(u<=previous for u,previous in zip(upper,previous_upper))
        previous_upper=upper
        lower_envelope=[max(old,new) for old,new in zip(lower_envelope,lower)]
        assert all(lo<=truth for lo,truth in zip(lower_envelope,target))
        mass_upper,_,_,scalar_upper=upper
        n_lower=lower[1]
        tail_naive=F(26,27)*mass_upper
        if scalar_upper:
            tail=F(26,27)*(mass_upper-F(2)*n_lower*n_lower/(26*scalar_upper))
        else:
            assert n_lower==0
            tail=tail_naive
        assert 0<=tail<=tail_naive
        # In this fixture every selected map has six distinct nonzero scalar
        # lines among its candidate labels, so exact witness-only miss
        # probability is (26-12)/27, multiplied by selected mass.
        # This is not equality with the full geometric shortest-vector tail.
        witness_miss=F(14,27)*target[0]
        assert witness_miss<=tail
        if n_lower>0 and first_positive_n is None:
            first_positive_n=prefix
        if tail<tail_naive and first_saving is None:
            first_saving=prefix
        certificates.append((prefix,len(states),upper,lower,tail))
        if prefix==len(events):
            assert upper==lower==target
            assert tail==witness_miss
            break
        event=events[prefix]
        updated=defaultdict(int)
        for basis,coefficient in states.items():
            updated[basis]+=coefficient
            extended=row_basis(basis+(event,),q)
            if joint(extended):
                updated[extended]-=coefficient
        states={basis:coefficient for basis,coefficient in updated.items() if coefficient}
    print('Processed event prefixes:',len(certificates),'statistics per prefix:4')
    print('Exact full selected targets:',target)
    print('First positive N lower bound:',first_positive_n,'first strict tail saving:',first_saving)
    for prefix in sorted({0,first_positive_n,20}):
        print('Certificate (prefix,states,upper,lower,tail):',certificates[prefix])
    print('Terminal exact witness-only miss bound:',certificates[-1][-1])
    print('Cached span moment tuples:',terms.cache_info(),'joint queries:',joint.cache_info())
    print('Elapsed seconds:',round(perf_counter()-start,3))
    print('All arbitrary-prefix certificates, monotone uppers, lower envelopes and tail bounds passed.')


if __name__=='__main__':
    main()
