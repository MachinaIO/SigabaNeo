"""Direct finite-field and large-dimension checks of fixed-quotient incidence.

The evaluator gives unconditional fixed-stratum probabilities. Nothing here
adds geometric eligibility, actual winner tests, or production history laws.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product, combinations
from fixed_quotient_graph_space import FixedQuotientGraphSpace
from wall1_fixed_quotient_law import canonical, subspaces, span, sigma


def direct_quotient(a,z):
    return (z[0]-a[2]*z[1]-a[3]*z[2])%3


def selected_moment_checks(matrices):
    model=FixedQuotientGraphSpace(3,2,2,1,((1,0,0,0),),())
    competitors=((0,0,1,0),(1,1,0,1))
    candidates=((1,0,0),(0,1,0),(0,0,1),(0,0,0))
    terms=[]
    for degree in range(3):
        total=[F(0)]*4
        for chosen in combinations(competitors,degree):
            mass=model.joint_probability(chosen)
            n=sum((mass-model.joint_probability(chosen,(z,)) for z in candidates),F(0))
            j=sum((model.scalar_nonzero_probability(z,zp,1,chosen)
                   for z,zp in product(candidates,repeat=2)),F(0))
            scalar=sum((model.scalar_nonzero_probability(z,zp,t,chosen)
                        for z,zp,t in product(candidates,candidates,(1,2))),F(0))
            total=[x+y for x,y in zip(total,(mass,n,j,scalar))]
        terms.append(total)
    direct=[F(0)]*4
    for a in matrices:
        if any(not any(sigma(a,z)) for z in competitors):
            continue
        labels=[direct_quotient(a,z) for z in candidates]
        labels=[v for v in labels if v]
        values=(1,len(labels),sum(v==w for v,w in product(labels,repeat=2)),
                sum(w==t*v%3 for v,w,t in product(labels,labels,(1,2))))
        direct=[x+F(y,81) for x,y in zip(direct,values)]
    partial=[F(0)]*4
    for degree,term in enumerate(terms):
        partial=[x+(-1)**degree*y for x,y in zip(partial,term)]
        assert all((p>=v if degree%2==0 else p<=v) for p,v in zip(partial,direct))
    assert partial==direct
    print('Selected avoidance moments (mass,N,J,Csc):',direct)
    print('Full/quotient inclusion-exclusion and odd/even count bounds passed.')


def main():
    matrices=list(product(range(3),repeat=4))
    strata=joint_checks=collision_checks=0
    cases=[((),()),(((0,0,1,0),),()),((),((0,1,0),)),
           (((0,0,0,1),),((0,1,0),)),(((1,0,0,0),),()),
           ((),((1,0,0),)),(((1,1,1,0),),((1,0,1),))]
    for e in subspaces(4):
        vectors=span(e,4)
        groups=defaultdict(list)
        for a in matrices:
            image=canonical([sigma(a,z) for z in e],2)
            if image!=((1,0),):
                continue
            f=canonical([z for z in vectors if not any(sigma(a,z))],4)
            groups[f].append(a)
        for f,members in groups.items():
            model=FixedQuotientGraphSpace(3,2,2,1,e,f)
            assert model.joint_probability()==F(len(members),81)
            strata+=1
            for full,quotient in cases:
                observed=sum(all(not any(sigma(a,z)) for z in full)
                             and all(direct_quotient(a,z)==0 for z in quotient)
                             for a in members)
                assert model.joint_probability(full,quotient)==F(observed,81)
                joint_checks+=1
            for z,zp,t,full in [((0,1,0),(0,0,1),1,()),
                                ((1,1,0),(2,0,1),2,((0,0,1,0),))]:
                observed=sum(all(not any(sigma(a,w)) for w in full)
                             and direct_quotient(a,z)!=0
                             and direct_quotient(a,zp)==t*direct_quotient(a,z)%3
                             for a in members)
                assert model.scalar_nonzero_probability(z,zp,t,full)==F(observed,81)
                collision_checks+=1
    # Both extreme image dimensions, including an empty residual output.
    empty=FixedQuotientGraphSpace(3,2,2,0)
    fullimage=FixedQuotientGraphSpace(3,2,2,2,((1,0,0,0),(0,1,0,0)))
    assert empty.joint_probability()==fullimage.joint_probability()==1
    assert fullimage.joint_probability((),((1,0),))==1
    assert fullimage.scalar_nonzero_probability((1,0),(0,1),1)==0
    selected_moment_checks(matrices)

    q,m,d,s=3329,400,117,12
    e=tuple(tuple(int(j==i) for j in range(m+d)) for i in range(s))
    model=FixedQuotientGraphSpace(q,m,d,s,e,())
    fullzero=(0,)*(m+d)
    fullone=(0,)*m+(1,)+(0,)*(d-1)
    z=(0,)*(m-s)+(1,)+(0,)*(d-1)
    zp=(0,)*(m-s)+(0,1)+(0,)*(d-2)
    assert model.joint_probability()==1
    assert model.joint_probability((fullzero,),((0,)*(m-s+d),))==1
    assert model.joint_probability((),(z,))==F(1,q**388)
    assert model.joint_probability((fullone,),())==F(1,q**400)
    assert model.scalar_nonzero_probability(z,zp,1)==F(1,q**388)-F(1,q**776)
    bad_calls=[lambda: model.joint_probability(((0,),),()),
               lambda: model.joint_probability((),((0,),)),
               lambda: model.scalar_nonzero_probability((0,),zp,1),
               lambda: model.scalar_nonzero_probability(z,zp,0),
               lambda: FixedQuotientGraphSpace(3,2,2,0,(),((0,0,1,0),)),
               lambda: FixedQuotientGraphSpace(3,2,2,1,(),())]
    for call in bad_calls:
        try:
            call()
        except ValueError:
            pass
        else:
            raise AssertionError('invalid dimensions/stratum/scalar accepted')
    print('Coordinate-image finite strata:',strata,'base masses verified.')
    print('Direct full/quotient joint checks:',joint_checks,'nonzero scalar collision checks:',collision_checks)
    print('Image dimensions0/2 and six invalid-input cases passed.')
    print('q3329 m400 d117 s12: base1, quotient q^-388, full q^-400, collision q^-388-q^-776 verified.')
    print('All exact fixed-quotient incidence checks passed; no geometric production claim.')


if __name__=='__main__':
    main()
