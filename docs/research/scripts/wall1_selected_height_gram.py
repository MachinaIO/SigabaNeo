"""Exact selected shared-mark Gram matrix for unequal-height witnesses.

Finite fixtures verify the algebra, not production witness geometry.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from conditional_graph_space import row_basis
from fixed_quotient_graph_space import FixedQuotientGraphSpace
from wall1_mixed_exclusion_gates import exclude
from optimal_void_square import optimal_square


def selected_height_gram(model, states, families, positive_full=(), positive_quotient=()):
    """families contains (integer height, fixed quotient-coordinate points).

    Heights must be invertible modulo q. Repeated points/heights are retained.
    states must represent an actual gate; geometry is the caller's obligation.
    Returns joint gate-and-nonzero-mark mass, first moments, and second moments.
    """
    q=model.prime
    h=q**model.quotient_outputs
    if h<=1:
        raise ValueError('requires nontrivial quotient')
    normalized=[]
    for height,points in families:
        if height%q==0:
            raise ValueError('height must be nonzero modulo q')
        inverse=pow(height,-1,q)
        points=tuple(tuple(x) for x in points)
        if any(len(x)!=model.quotient_outputs+model.inputs for x in points):
            raise ValueError('candidate dimension mismatch')
        normalized.append(tuple(tuple(v*inverse%q for v in x) for x in points))
    @lru_cache(None)
    def Q(rows):
        return sum((weight*model.joint_probability(full+positive_full,
                    quotient+positive_quotient+rows)
                    for (full,quotient),weight in states.items()),F(0))
    mass=Q(())*F(h-1,h)
    first=tuple(sum((Q(())-Q(row_basis((x,),q)) for x in points),F(0))/h
                for points in normalized)
    gram=[]
    for xs in normalized:
        row=[]
        for ys in normalized:
            total=F(0)
            for x in xs:
                for y in ys:
                    delta=tuple(a-b for a,b in zip(x,y))
                    total+=Q(row_basis((delta,),q))-Q(row_basis((delta,x),q))
            row.append(total/h)
        gram.append(tuple(row))
    return mass,first,tuple(gram)


def coverage_lower(first,gram,weights):
    weights=tuple(F(w) for w in weights)
    if len(weights)!=len(first) or any(w<0 for w in weights):
        raise ValueError('one nonnegative weight per family is required')
    mean=sum((w*b for w,b in zip(weights,first)),F(0))
    second=sum((w*v*gram[i][j] for i,w in enumerate(weights)
                for j,v in enumerate(weights)),F(0))
    if second==0:
        assert mean==0
        return F(0)
    return mean*mean/second


def optimal_height_void(mass,first,gram):
    """Optimize all affine squares, with signed coefficients and singular G.

    Return weights w and the upper bound mass-b.w for the joint void.
    Moment provenance and witness geometry remain caller obligations.
    """
    n=len(first)
    if len(gram)!=n or any(len(row)!=n for row in gram):
        raise ValueError('moment dimensions do not agree')
    augmented=[[F(mass)]+list(first)]
    augmented.extend([[first[i]]+list(gram[i]) for i in range(n)])
    coefficients,bound=optimal_square(augmented)
    weights=tuple(-c for c in coefficients[1:])
    assert all(sum(gram[i][j]*weights[j] for j in range(n))==first[i]
               for i in range(n))
    assert bound==mass-sum(b*w for b,w in zip(first,weights))
    return weights,bound


def signed_fixture():
    # Equal-mass outcomes (0,0),(1,1),(2,3). A negative weight is necessary
    # to make the affine square vanish on both nonzero outcomes.
    mass=F(1); first=(F(1),F(4,3))
    gram=((F(5,3),F(7,3)),(F(7,3),F(10,3)))
    w,bound=optimal_height_void(mass,first,gram)
    assert w==(F(2),F(-1)) and bound==F(1,3)
    # A cone certificate proves 3/5 is the BEST nonnegative-weight coverage:
    # v>=0, Gv>=b, v.(Gv-b)=0, hence (u.b)^2/(uGu)<=vGv.
    v=(F(3,5),F(0))
    gv=tuple(sum(gram[i][j]*v[j] for j in range(2)) for i in range(2))
    assert all(gv[i]>=first[i] for i in range(2))
    assert all(v[i]*(gv[i]-first[i])==0 for i in range(2))
    assert coverage_lower(first,gram,v)==F(3,5)
    # Empty and singular families must still optimize without inverses.
    assert optimal_height_void(F(1),(),())==((),F(1))
    assert optimal_height_void(F(0),(F(0),),((F(0),),))[1]==0
    assert optimal_height_void(F(1),(F(1,2),F(1,2)),
                               ((F(1,2),F(1,2)),(F(1,2),F(1,2))))[1]==F(1,2)
    print('Signed optimum 1/3 versus best nonnegative void bound 2/5; singular checks passed.')


def checks():
    count=0
    improved=0
    for q,image in product((3,5,7),(0,1)):
        outputs=1+image
        fixed=((1,0,0),) if image else ()
        model=FixedQuotientGraphSpace(q,outputs,1,image,fixed,())
        base={((),()):1}
        bad=(0,0,1) if image else (0,1)
        gate=exclude(base,'full',bad,model)
        families=((1,((0,0),(1,0),(q+1,0),(0,1))),
                  (2,((1,0),(0,1))),
                  (-1,((1,1),)))
        maps=tuple(product(range(q),repeat=outputs))
        for states,positive in product((base,gate),((),((1,1),))):
            mass,first,gram=selected_height_gram(model,states,families,
                                                positive_quotient=positive)
            bm=F(0);bf=[F(0)]*3;bg=[[F(0)]*3 for _ in range(3)]
            covered=F(0)
            observations=[]
            for a in maps:
                if states==gate and not any(a):
                    continue
                t=a[-1]
                if any((x-t*y)%q for x,y in positive):
                    continue
                for u in range(1,q):
                    z=[sum((x-t*y-j*u)%q==0 for x,y in points)
                       for j,points in families]
                    observations.append(z)
                    bm+=1;covered+=int(any(z))
                    for i in range(3):
                        bf[i]+=z[i]
                        for j in range(3):bg[i][j]+=z[i]*z[j]
            denom=len(maps)*q
            assert mass==bm/denom
            assert first==tuple(v/denom for v in bf)
            assert gram==tuple(tuple(v/denom for v in row) for row in bg)
            optimal_weights,void_bound=optimal_height_void(mass,first,gram)
            direct=sum(((1-sum(w*x for w,x in zip(optimal_weights,z)))**2
                        for z in observations),F(0))/denom
            assert direct==void_bound
            assert mass-covered/denom<=void_bound<=mass
            one=max(coverage_lower(first,gram,w) for w in
                    ((1,0,0),(0,1,0),(0,0,1)))
            best=one
            for weights in product((F(0),F(1,2),F(1),F(2)),repeat=3):
                lower=coverage_lower(first,gram,weights)
                assert 0<=lower<=covered/denom<=mass
                assert void_bound<=mass-lower
                best=max(best,lower)
                count+=1
            improved+=best>one
    assert improved>0
    print('Exact weighted coverage checks:',count)
    print('Fixtures improved over the best individual-height moment bound:',improved)
    signed_fixture()
    # Height zero and width mismatch must not silently change the experiment.
    for bad_family in (((0,((1,0),)),),((1,((1,0,0),)),)):
        try:selected_height_gram(model,base,bad_family)
        except ValueError:pass
        else:raise AssertionError('invalid family accepted')
    print('PASS: shared-mark moments retain gates, zero anchors, signs, and multiplicities.')
    print('No production selected-history moment bound is asserted.')


if __name__=='__main__':
    checks()
