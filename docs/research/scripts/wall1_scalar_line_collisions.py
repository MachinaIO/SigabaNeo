"""Exact residual-map collision and projective-line multiplicity identities.

Exhaustive small finite-field checks only; no production probability bound.
The nonzero condition is enforced by subtracting the joint zero event.
Occupied-label identities require reciprocal fiber weights for repeated
candidates; the separate multiplicity certificate avoids those weights.
Zero-label candidates are explicitly omitted.
"""
from fractions import Fraction as F
from itertools import product

Q=3


def system_probability(rows,rhs,dimension):
    """Uniform F3^dimension solution probability by rank and consistency."""
    matrix=[list(row)+[target%Q] for row,target in zip(rows,rhs)]
    assert all(len(row)==dimension+1 for row in matrix)
    rank=0
    for col in range(dimension):
        pivot=next((i for i in range(rank,len(matrix)) if matrix[i][col]%Q),None)
        if pivot is None:
            continue
        matrix[rank],matrix[pivot]=matrix[pivot],matrix[rank]
        inverse=pow(matrix[rank][col]%Q,-1,Q)
        matrix[rank]=[x*inverse%Q for x in matrix[rank]]
        for i in range(len(matrix)):
            if i!=rank:
                scalar=matrix[i][col]%Q
                matrix[i]=[(x-scalar*y)%Q for x,y in zip(matrix[i],matrix[rank])]
        rank+=1
    if any(all(x%Q==0 for x in row[:-1]) and row[-1]%Q for row in matrix):
        return F(0),rank
    return F(1,Q**rank),rank


def residual_checks():
    total=generic=0
    by_dimension={}
    for dimension in (0,1,2):
        inputs=list(product(range(Q),repeat=dimension))
        maps=inputs
        candidates=[(u,v) for u in range(Q) for v in inputs]
        checked=0
        for (u,v),(up,vp),t in product(candidates,candidates,(1,2)):
            difference=tuple((x-t*y)%Q for x,y in zip(vp,v))
            target=(up-t*u)%Q
            first,r1=system_probability([difference],[target],dimension)
            joint,r2=system_probability([difference,v],[target,u],dimension)
            probability=first-joint
            observed=0
            for linear in maps:
                label=(sum(x*y for x,y in zip(linear,v))-u)%Q
                labelp=(sum(x*y for x,y in zip(linear,vp))-up)%Q
                observed+=label!=0 and labelp==t*label%Q
            assert probability==F(observed,len(maps))
            assert 0<=probability<=1
            if r1==1 and r2==2:
                assert first==F(1,3) and joint==F(1,9)
                assert probability==F(2,9)
                generic+=1
            checked+=1
        by_dimension[dimension]=checked
        total+=checked
    return total,generic,by_dimension


def line_checks():
    zero=(0,0)
    labels=[v for v in product(range(Q),repeat=2) if v!=zero]
    scale=lambda t,v:tuple(t*x%Q for x in v)
    lines={tuple(sorted({scale(t,v) for t in (1,2)})) for v in labels}
    assert len(lines)==4
    count=0
    zero_points=0
    strict_unweighted=0
    for mask in range(1<<len(labels)):
        occupied={v for i,v in enumerate(labels) if mask&(1<<i)}
        numerator=sum(sum(scale(t,v) in occupied for v in occupied) for t in (1,2))
        # nu is the mean squared occupancy density on a nonzero projective line.
        nu=sum((F(len(occupied.intersection(line)),Q-1)**2 for line in lines),F(0))/len(lines)
        assert nu==F(numerator,(Q**2-1)*(Q-1))
        # Deterministic multiplicities 1..3, plus two deliberately present
        # zero-label candidate points. They never enter either line sum.
        multiplicities={v:1+i%3 for i,v in enumerate(labels) if v in occupied}
        candidates=[zero,zero]+[v for v,n in multiplicities.items() for _ in range(n)]
        weighted=F(0)
        unweighted=0
        for v,w,t in product(candidates,candidates,(1,2)):
            if v==zero or w==zero:
                zero_points+=1
                continue
            if w==scale(t,v):
                weighted+=F(1,multiplicities[v]*multiplicities[w])
                unweighted+=1
        assert weighted==numerator
        assert weighted<=unweighted
        strict_unweighted+=weighted<unweighted
        count+=1
    return count,strict_unweighted,zero_points


def multiplicity_bridge_checks():
    """q=3: the sign quotient has one element, so r=0 is valid.

    Its +/-1 dilation fills every occupied projective line. Symmetrizing
    labels retains total mass and per-line masses while reducing squared
    point mass. Uniform duplication must not alter the homogeneous bound.
    """
    q=3
    labels=[v for v in product(range(q),repeat=2) if any(v)]
    negate=lambda v:tuple(-x%q for x in v)
    lines={tuple(sorted((v,negate(v)))) for v in labels}
    strict=nonempty=even_strict=0
    for mask in range(1<<len(labels)):
        counts={v:(1+i%3 if mask&(1<<i) else 0) for i,v in enumerate(labels)}
        mass=sum(counts.values())
        squared=sum(n*n for n in counts.values())
        line_squared=sum(sum(counts[v] for v in line)**2 for line in lines)
        even={v:F(counts[v]+counts[negate(v)],2) for v in labels}
        squared_even=sum((n*n for n in even.values()),F(0))
        assert sum(even.values(),F(0))==mass
        assert sum((sum(even[v] for v in line)**2 for line in lines),F(0))==line_squared
        assert squared_even<=squared
        even_strict+=squared_even<squared
        occupied={v for v in labels if counts[v]>0}
        union=occupied|{negate(v) for v in occupied}
        actual=F(len(union),q*q-1)
        if not mass:
            assert squared==line_squared==actual==0
            continue
        nonempty+=1
        r=F(0)
        denominator=r*(q-1)*squared+(1-r)*line_squared
        bound=F((q-1)*mass*mass,(q*q-1)*denominator)
        old=F(mass*mass,(q*q-1)*squared)
        assert actual>=bound>=old
        even_bound=F((q-1)*mass*mass,
                     (q*q-1)*(r*(q-1)*squared_even+(1-r)*line_squared))
        assert even_bound==bound  # r=0 suppresses the J term here.
        duplicate=F((q-1)*(2*mass)**2,
                    (q*q-1)*(r*(q-1)*(4*squared)+(1-r)*(4*line_squared)))
        assert duplicate==bound
        strict+=bound>old
    return nonempty,strict,even_strict


def q7_bridge_checks():
    """G=F7*/+/-1 is cyclic of order 3; D={1,2} has rho^2=1/4.

    For a nontrivial cube root omega, |1+omega|^2=1, proving that
    spectral constant exactly. Here H=F7 has a single projective line.
    """
    q=7
    r=F(1,4)
    strict_even=0
    for mask in range(1<<6):
        counts={v:(1+(v-1)%3 if mask&(1<<(v-1)) else 0) for v in range(1,q)}
        mass=sum(counts.values())
        squared=sum(n*n for n in counts.values())
        even={v:F(counts[v]+counts[q-v],2) for v in counts}
        jeven=sum((n*n for n in even.values()),F(0))
        assert sum(even.values(),F(0))==mass and jeven<=squared
        if not mass:
            continue
        k=mass*mass
        occupied={v for v,n in counts.items() if n}
        union={pow(t%q,-1,q)*v%q for t in (1,2,-1,-2) for v in occupied}
        actual=F(len(union),q-1)
        bound=F((q-1)*mass*mass,(q-1)*(r*(q-1)*squared+(1-r)*k))
        evenbound=F((q-1)*mass*mass,(q-1)*(r*(q-1)*jeven+(1-r)*k))
        old=F(mass*mass,(q-1)*squared)
        assert actual>=evenbound>=bound>=old
        duplicate=F((q-1)*(2*mass)**2,
                    (q-1)*(r*(q-1)*4*squared+(1-r)*4*k))
        assert duplicate==bound
        strict_even+=evenbound>bound
    return strict_even


def main():
    total,generic,dimensions=residual_checks()
    subsets,strict,excluded=line_checks()
    print('Residual collision checks by input dimension:',dimensions,'total:',total)
    print('Generic rank-two cases with probability 1/3-1/9=2/9:',generic)
    print('Nonzero-label subset checks:',subsets)
    print('Strict overcounts without reciprocal multiplicity weights:',strict)
    print('Zero-containing ordered candidate/scalar terms explicitly skipped:',excluded)
    nonempty,strict_bridge,strict_even=multiplicity_bridge_checks()
    print('Multiplicity spectral bridge: 256 subsets;',nonempty,'nonempty cases; r=0.')
    print('Strict improvements over M^2/((h-1)J):',strict_bridge)
    print('Strict J reduction by sign symmetrization:',strict_even)
    print('Uniform duplication invariance verified in every nonempty case.')
    print('q=7,D={1,2},rho^2=1/4: 64 subsets; strict even-bound improvements:',q7_bridge_checks())
    print('All exact rank/consistency, direct-map, line occupancy, and multiplicity checks passed.')


if __name__=='__main__':
    main()
