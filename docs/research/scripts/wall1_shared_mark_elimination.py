"""Exact elimination of a shared fresh mark, assignment by assignment.

For a nonzero anchor height j0, equations lambda(zi)=ji*U eliminate U
as j0*lambda(zi)-ji*lambda(z0)=0. Exclude lambda(z0)=0 and divide by
h, the quotient mark order, for its unique fresh U. Collision equations
are quotient constraints; old exclusion gates remain full graph equations.
No independence between the several fresh-height witnesses is introduced.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations,product
from math import factorial
from conditional_graph_space import row_basis
from fixed_quotient_graph_space import FixedQuotientGraphSpace
from wall1_shared_mark_factorial import CANDIDATES, HEIGHTS


def check_fixture(image_dimension,fixed_e,candidates):
    q=3
    old=FixedQuotientGraphSpace(q,2,1,image_dimension,fixed_e,())
    augmented=FixedQuotientGraphSpace(q,2,2,image_dimension,
                                     tuple(z+(0,) for z in fixed_e),())
    # This gate is full A=0, i.e. both old output coordinates vanish.
    bad=(0,0,1)
    augmented_bad=bad+(0,)
    quotient_outputs=2-image_dimension
    u_zero=(0,)*quotient_outputs+(0,1)
    h=q**quotient_outputs

    @lru_cache(maxsize=None)
    def old_selected(constraints):
        return old.joint_probability((),constraints)-old.joint_probability((bad,),constraints)

    def selected(constraints):
        return old_selected(row_basis(constraints,q))

    def augmented_mass(hits):
        return (augmented.joint_probability((),hits)
                -augmented.joint_probability((),hits+(u_zero,))
                -augmented.joint_probability((augmented_bad,),hits)
                +augmented.joint_probability((augmented_bad,),hits+(u_zero,)))

    # k=0 has no anchor. Nonzero U is independent of the old full gate.
    m0=selected(())*F(h-1,h)
    assert m0==augmented_mass(())
    moments=[m0]
    augmented_moments=[m0]
    assignments=pivots=0
    for k in range(1,len(candidates)+1):
        total=F(0)
        augmented_total=F(0)
        for ids in combinations(range(len(candidates)),k):
            zs=tuple(candidates[i] for i in ids)
            for heights in product(HEIGHTS,repeat=k):
                hits=tuple(z+(j,) for z,j in zip(zs,heights))
                reference=augmented_mass(hits)
                first=None
                for anchor in range(k):
                    z0=zs[anchor]
                    j0=heights[anchor]
                    constraints=tuple(tuple((j0*x-j*y)%q for x,y in zip(z,z0))
                                      for z,j in zip(zs,heights))
                    mass=(selected(constraints)-selected(constraints+(z0,)))/h
                    assert mass==reference and mass>=0
                    if first is None:
                        first=mass
                    else:
                        assert mass==first
                    pivots+=1
                total+=first
                augmented_total+=reference
                assignments+=1
        moments.append(factorial(k)*total)
        augmented_moments.append(factorial(k)*augmented_total)
    assert moments==augmented_moments
    return tuple(moments),assignments,pivots


def main():
    original,assignments,pivots=check_fixture(0,(),CANDIDATES)
    assert original==(F(64,81),F(64,81),F(8,27),F(0),F(0))
    # Nontrivial fixed image: only the second output survives. The image
    # saturation factor and full old gate are retained by both evaluators.
    second,a2,p2=check_fixture(1,((1,0,0),),((1,0),(0,1),(1,1)))
    assert second[0]==F(16,27)
    print('Original fixture M0..M4:',original)
    print('Nontrivial image S fixture M0..M3:',second)
    print('Original nonempty height assignments:',assignments,'anchor checks:',pivots)
    print('Nontrivial S height assignments:',a2,'anchor checks:',p2)
    print('Total assignment comparisons:',assignments+a2,'all-anchor comparisons:',pivots+p2)
    print('M0 handled separately; full gates and quotient collisions kept distinct.')
    print('All shared-mark elimination and augmented evaluator checks passed.')


if __name__=='__main__':
    main()
