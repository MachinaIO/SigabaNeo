"""End-to-end actual-winner incidence with exact finite exclusion.

q=3,m=8,d=1, w=-3e1. Forbidden graph vectors (x,1) have centered
x in {-1,0,1}^8 with <=7 nonzero entries. Each imposes A=x mod3;
these 6305 graph events are pairwise disjoint, so degree-one subtraction
is the full inclusion-exclusion identity. Two distinct candidates have the
same input1 and different outputs: subtracting their equations gives an
impossible nonzero pure-output graph vector. No pair enumeration is needed.

The actual selection and tie rule are imported from the complete prior
winner checker. All probability terms below are computed by the generic
FixedQuotientGraphSpace evaluator; direct raw-matrix enumeration is only
an independent validation. No production estimate is asserted.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from time import perf_counter
from conditional_graph_space import row_basis
from fixed_quotient_graph_space import FixedQuotientGraphSpace
from wall1_fixed_quotient_selection import winner_test


def main():
    start=perf_counter()
    q=3
    model=FixedQuotientGraphSpace(q,8,1,1,((1,)+(0,)*8,),())
    candidates=((1,1,1,0,0,0,0,0),(0,0,0,1,1,1,1,-1))
    forbidden=tuple(x+(1,) for x in product((-1,0,1),repeat=8)
                    if sum(v!=0 for v in x)<=7)
    assert len(forbidden)==6305
    forbidden_outputs={tuple(v%q for v in z[:-1]) for z in forbidden}
    assert len(forbidden_outputs)==len(forbidden)
    # A fixed input1 makes every distinct output pair inconsistent. Sample
    # the generic evaluator as an additional check of that structural proof.
    for i in range(16):
        assert model.joint_probability((forbidden[i],forbidden[-i-1]),())==0

    @lru_cache(maxsize=None)
    def evaluated(full,quotient_basis):
        return model.joint_probability(full,quotient_basis)

    def joint(full,quotient=()):
        return evaluated(full,row_basis(quotient,q))

    def collision(full,z,zp,t):
        difference=tuple((b-t*a)%q for a,b in zip(z,zp))
        return joint(full,(difference,))-joint(full,(difference,z))

    def terms(full):
        mass=joint(full)
        count=sum((mass-joint(full,(z,)) for z in candidates),F(0))
        equality=sum((collision(full,z,zp,1)
                      for z,zp in product(candidates,repeat=2)),F(0))
        collinear=sum((collision(full,z,zp,t)
                       for z,zp,t in product(candidates,candidates,(1,2))),F(0))
        return mass,count,equality,collinear

    base=terms(())
    removed=[F(0)]*4
    for forbidden_vector in forbidden:
        values=terms((forbidden_vector,))
        removed=[a+b for a,b in zip(removed,values)]
    selected=tuple(a-b for a,b in zip(base,removed))
    expected=tuple(F(x,6561) for x in (256,512,516,520))
    assert selected==expected

    direct=[0]*4
    selection_checks=0
    for a in product(range(q),repeat=8):
        actual,_=winner_test(a)
        absent=a not in forbidden_outputs
        assert actual==absent
        selection_checks+=1
        if not actual:
            continue
        labels=[tuple((z[i]-a[i+1]*z[-1])%q for i in range(7))
                for z in candidates]
        direct[0]+=1
        direct[1]+=sum(any(v) for v in labels)
        direct[2]+=sum(any(v) and v==w for v,w in product(labels,repeat=2))
        direct[3]+=sum(any(v) and w==tuple(t*x%q for x in v)
                       for v,w,t in product(labels,labels,(1,2)))
    assert tuple(direct)==(256,512,516,520)
    assert tuple(F(x,6561) for x in direct)==selected
    mass,count,equality,collinear=selected
    h=q**7
    # Conditional Cauchy-Schwarz across the selected ensemble, r=0 on the
    # q=3 sign quotient: (q-1)*E[N|selected]^2 / ((h-1)*E[C|selected]).
    coverage=(q-1)*count*count/((h-1)*mass*collinear)
    assert coverage==F(128,71045)
    print('Forbidden disjoint membership events:',len(forbidden))
    print('Actual winner / exact absence checks:',selection_checks)
    print('Generic evaluator base terms:',base)
    print('Selected unconditional (a,n,j,c):',selected)
    print('Direct selected integer counts:',tuple(direct))
    print('Conditional ensemble weighted-CS coverage bound:',coverage)
    print('Generic evaluator cache:',evaluated.cache_info())
    print('Elapsed seconds:',round(perf_counter()-start,3))
    print('All actual-selection, exact exclusion, incidence, and multiplicity checks passed.')


if __name__=='__main__':
    main()
