"""Selected pair moments via grouped quotient differences, with exact fixtures."""
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from itertools import product

from conditional_graph_space import row_basis
from fixed_quotient_graph_space import FixedQuotientGraphSpace
from wall1_mixed_exclusion_gates import exclude


def nonzero_mark_moments(model, states, candidates, center, positive_full=(), positive_quotient=()):
    """Nonnegative statistics under a possibly incomplete exclusion gate.

    Unlike selected_pair_moments, this retains zero-anchor subtractions.
    The supplied center is fixed, not assumed to equal this gate's mean.
    """
    q = model.prime
    h = q**model.quotient_outputs
    if h <= 1:
        raise ValueError('nonzero marks require h>1')
    candidates = tuple(tuple(z) for z in candidates)
    if any(len(z)!=model.quotient_outputs+model.inputs for z in candidates):
        raise ValueError('candidate dimension mismatch')
    @lru_cache(None)
    def selected(constraints):
        return sum((coefficient*model.joint_probability(full+positive_full,
                    quotient+positive_quotient+constraints)
                    for (full,quotient),coefficient in states.items()),F(0))
    m0 = selected(())*F(h-1,h)
    m1 = sum((selected(())-selected(row_basis((z,),q)) for z in candidates),F(0))/h
    terms = Counter()
    for i,x in enumerate(candidates):
        for j,y in enumerate(candidates):
            if i==j:
                continue
            diff = tuple(a-b for a,b in zip(x,y))
            terms[row_basis((diff,),q),row_basis((diff,x),q)] += 1
    m2 = sum((weight*(selected(diff)-selected(anchored))
              for (diff,anchored),weight in terms.items()),F(0))/h
    centered = m2+(1-2*center)*m1+center**2*m0
    assert all(value>=0 for value in (m0,m1,m2,centered))
    return m0,m1,m2,centered


def selected_pair_moments(model, states, candidates):
    """Return unnormalized moments; states must encode an exact old gate.

    Candidates use quotient coordinates, are fixed on this stratum, and
    must have nonzero labels everywhere on the supplied gate. Distinct
    geometric points may have identical residues: keep their multiplicity.
    """
    q = model.prime
    h = q**model.quotient_outputs
    if h <= 1:
        raise ValueError('nonzero mark conditioning needs h>1')
    candidates = tuple(tuple(z) for z in candidates)
    if any(len(z)!=model.quotient_outputs+model.inputs for z in candidates):
        raise ValueError('candidate dimension mismatch')
    @lru_cache(None)
    def selected(constraints):
        return sum((coefficient*model.joint_probability(full, quotient+constraints)
                    for (full,quotient),coefficient in states.items()),F(0))
    mass = selected(())
    for z in candidates:
        if selected(row_basis((z,),q)) != 0:
            raise ValueError('candidate may have zero label on the gate')
    differences = Counter(row_basis((tuple(x-y for x,y in zip(a,b)),),q)
                          for i,a in enumerate(candidates)
                          for j,b in enumerate(candidates) if i!=j)
    A = len(candidates)
    mu = F(A,h-1)
    m0 = mass*F(h-1,h)
    m1 = mass*F(A,h)
    m2 = sum((weight*selected(v) for v,weight in differences.items()),F(0))/h
    centered = m2+m1-m0*mu**2
    assert m1 == m0*mu and centered >= 0
    return (m0,m1,m2,centered),differences,selected


def fixture(image_dimension):
    q = 5
    outputs = 2+image_dimension
    fixed_e = ((1,0,0,0),) if image_dimension else ()
    model = FixedQuotientGraphSpace(q,outputs,1,image_dimension,fixed_e,())
    candidates = tuple(z for z in product((-1,0,1),repeat=3)
                       if 0<sum(x*x for x in z)<=2)
    old_short = tuple(z for z in product((-1,0,1),repeat=3) if any(z))
    # Complete list for norm²<7/2. Candidate norm²+height²<=3<7/2.
    bad_full = ((0,) if image_dimension else ())+(2,1,1)
    events = [('quotient',z) for z in old_short]+[('full',bad_full)]
    states = {((),()):1}
    for tag,z in events:
        states = exclude(states,tag,z,model)
    result,differences,selected = selected_pair_moments(model,states,candidates)
    h = q**2
    mu = F(len(candidates),h-1)
    brute = [F(0)]*4
    old_count = 0
    pair_counts = Counter()
    maps = tuple(product(range(q),repeat=outputs))
    for a in maps:
        aq = a[image_dimension:]
        def label(z):
            return tuple((z[i]-aq[i]*z[2])%q for i in range(2))
        if any(not any(label(z)) for z in old_short):
            continue
        if all((bad_full[i]-a[i]*bad_full[-1])%q==0 for i in range(outputs)):
            continue
        old_count += 1
        for v in differences:
            if all(not any(label(z)) for z in v):
                pair_counts[v] += 1
        for u in product(range(q),repeat=2):
            if not any(u):
                continue
            z = sum(label(x)==u for x in candidates)
            for k,val in enumerate((1,z,z*(z-1),(F(z)-mu)**2)):
                brute[k] += val
    brute = tuple(x/(len(maps)*h) for x in brute)
    assert tuple(result)==brute
    assert selected(())==F(old_count,len(maps))
    changed = enhanced = 0
    for v in differences:
        assert selected(v)==F(pair_counts[v],len(maps))
        if selected(v)!=selected(())*model.joint_probability((),v):
            changed += 1
        if selected(v)>selected(())*model.joint_probability((),v):
            enhanced += 1
    assert changed>0
    assert enhanced>0
    naive_m2 = sum((weight*selected(())*model.joint_probability((),v)
                    for v,weight in differences.items()),F(0))/h
    assert naive_m2 != result[2]
    print('image dimension',image_dimension,'gate mass',selected(()),
          'moments',result,'ordered pairs',len(candidates)*(len(candidates)-1),
          'grouped constraints',len(differences),'biased constraints',changed)
    print('Constraints whose incidence increases after the gate:',enhanced)
    print('Incorrect gate-independent second factorial moment:',naive_m2,
          'actual minus incorrect:',result[2]-naive_m2)


def boundary_checks():
    q=3
    model=FixedQuotientGraphSpace(q,2,1,1,((1,0,0),),())
    empty={((),()):1}
    gate=exclude(empty,'full',(0,0,1),model)
    families=(((0,0),(1,0),(4,0),(0,1)),((1,0),(4,0)))
    checks=0
    for states,candidates,center,full,quotient in product(
            (empty,gate),families,(F(0),F(1,2),F(2)),
            ((),((1,0,1),)),((),((1,1),))):
        actual=nonzero_mark_moments(model,states,candidates,center,full,quotient)
        expected=[F(0)]*4
        for a,b,u in product(range(q),range(q),(1,2)):
            if states==gate and a==b==0:
                continue
            if any((x-a*z)%q or (y-b*z)%q for x,y,z in full):
                continue
            if any((x-b*z)%q for x,z in quotient):
                continue
            z=sum((x-b*y)%q==u for x,y in candidates)
            values=(1,z,z*(z-1),(F(z)-center)**2)
            expected=[v+w for v,w in zip(expected,values)]
        assert actual==tuple(v/q**3 for v in expected)
        checks+=1
    exact,_,_=selected_pair_moments(model,empty,((1,0),(4,0)))
    assert exact==nonzero_mark_moments(model,empty,((1,0),(4,0)),F(1))
    for bad in (((0,0),),((1,0,0),)):
        try:
            selected_pair_moments(model,empty,bad)
        except ValueError:
            pass
        else:
            raise AssertionError('invalid selected candidate accepted')
    print('Nontrivial-image, positive-constraint, zero/repeated-residue checks:',checks)


if __name__ == '__main__':
    fixture(0)
    fixture(1)
    boundary_checks()
    print('PASS: mixed gates and selected pair moments match complete map/mark enumeration.')
    print('Production selected-history collision bounds remain unproved.')
