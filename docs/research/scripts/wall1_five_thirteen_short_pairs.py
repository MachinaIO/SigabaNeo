"""H13 c5: no outside norm8, no (10,10), and counted (8,10) pairs."""
from collections import Counter,defaultdict
from itertools import combinations
from math import comb

EIGHT_TEN_WITNESSES=25200


def unit_lines(size,support):
    support=tuple(sorted(support));half=len(support)//2
    assert len(support)%2==0
    for plus in combinations(support[1:],half-1):
        positive={support[0],*plus}
        yield tuple(1 if i in positive else -1 if i in support else 0 for i in range(size))


def checks():
    from wall1_rare_second_line import norm_rows
    inside=[v+(0,)*8 for v in norm_rows(5,8,minimum_support=5)]
    outside8=list(unit_lines(13,range(5,13)))
    outside10=[v for old in combinations(range(5),2)
               for v in unit_lines(13,old+tuple(range(5,13)))]
    assert len(inside)==20 and len(outside8)==35 and len(outside10)==1260
    # Old restriction of every combination with a new-only row is0 orfullC.
    for a in inside:
        for b in outside8:
            for q in (7,17,3329):
                assert all(a[i]%q for i in range(5)) and not any(b[:5])
                assert sum(bool((a[i]+b[i])%q) for i in range(5))==5
    counts=Counter()
    for a in inside:
        for b in outside10:
            dot=sum(x*y for x,y in zip(a,b))
            assert abs(dot)<=3
            assert any(abs(a[i])==1 and not b[i] for i in range(5))
            # Such an old coordinate and any new unit coordinate give a unit minor.
            counts[80-dot*dot]+=1
    assert sum(counts.values())==EIGHT_TEN_WITNESSES
    assert dict(counts)=={71:5320,76:7560,79:4760,80:7560}
    grouped=defaultdict(list)
    for b in outside10:
        normalized=tuple(b[5]*x for x in b)
        grouped[normalized[5:]].append(normalized)
    excluded=0
    for rows in grouped.values():
        for a,b in combinations(rows,2):
            difference=tuple(x-y for x,y in zip(a,b))
            assert not any(difference[5:])
            assert 0<sum(bool(x) for x in difference)<=4
            excluded+=1
    assert excluded==9170
    print('inside norm8',len(inside),'forbidden new-only norm8',len(outside8),
          'outside norm10',len(outside10))
    print('saturated8/10 witnesses',sum(counts.values()),'Gram strata',dict(sorted(counts.items())))
    print('outside10 pairs excluded by girth5',excluded)


def kernels(s,overlap):
    I,iv,q,n,R=[s[k] for k in ('I','iv','q','N','radius')]
    beta=I(11*n)/(26*R**2);a=iv.pi**2/beta;alpha=a/q**2
    assert 14**3<q and 13*14**2<q*q
    def theta(x):
        geo=s['geometry']['theta_upper']
        return geo(x) if x>iv.pi else iv.sqrt(iv.pi/x)*geo(iv.pi**2/x)
    delta=2*iv.exp(-a/4)/(1-iv.exp(-2*a))
    periodic=sum((comb(13,j)*delta**j for j in range(1,14)),I(0))
    tail=iv.exp(-98*alpha)*theta(I(5)*alpha/2)**2
    def kernel(g1,g2):
        return (iv.pi/beta)**(I(13)/2)*((theta(g1*alpha)*theta(g2*alpha)+tail)/q**2+periodic)
    old=kernel(I(8),I(6))**n
    low=kernel(I(8),I(71)/8)**n
    ten=kernel(I(10),I(19)/2)**n
    twelve=kernel(I(12),I(9))**n
    direct=low+ten+twelve
    Q=q**(9+overlap)
    counted=(I(min(Q,EIGHT_TEN_WITNESSES))/Q*low
             +kernel(I(8),I(10))**n+ten+twelve)
    return old,direct,counted


def diagnostic():
    import contextlib,inspect,io,sys
    from wall1_general_two_relations import draw14_bounds
    source,start=inspect.getsourcelines(draw14_bounds)
    line=start+next(i for i,l in enumerate(source) if 'charge = (choices*q**(c+t+a-4)' in l)
    stratum_line=start+next(i for i,l in enumerate(source) if 'strata[h, r, c] = chosen' in l)
    anchor_line=start+next(i for i,l in enumerate(source) if 'anchors[c, t, overlap] =' in l)
    raw={};ones={};prior_gaussians={}
    def trace(frame,event,arg):
        if frame.f_code is not draw14_bounds.__code__:return None
        if event=='line':
            v=frame.f_locals
            if frame.f_lineno==anchor_line and v['c']==5 and v['t']==8:
                prior_gaussians[v['overlap']]=v['chosen_gaussian']**v['n']
            if frame.f_lineno==line+2 and v['h'] in (18,19) and v['r']==11 and v['c']==5:
                raw[v['h'],v['t'],v['a']]=v['charge']
            if frame.f_lineno==stratum_line and v['h'] in (18,19) and v['r']==11 and v['c']==5:
                ones[v['h']]=v['one']
        return trace
    sys.settrace(trace)
    try:
        with contextlib.redirect_stdout(io.StringIO()):s,_,strata=draw14_bounds()
    finally:sys.settrace(None)
    I,iv=s['I'],s['iv'];ratios={}
    for overlap in range(1,5):
        old,direct,counted=kernels(s,overlap)
        actual=s['five_circuit_anchor_parts'][8,overlap]['selected']
        old_reference=min((prior_gaussians[overlap],old),key=lambda v:v.b)
        new=min((old_reference,counted),key=lambda v:v.b)
        relative=actual/new
        tolerance=I('1e-60')
        assert relative.a>(1-tolerance).b and relative.b<(1+tolerance).a
        ratios[overlap]=new/old_reference
        print('overlap',overlap,'direct/previous selected log10',iv.log10(direct/old_reference),
              'counted/previous selected log10',iv.log10(counted/old_reference))
        assert new.b<old_reference.a
    for h in (18,19):
        terms={key[1:]:value for key,value in raw.items() if key[0]==h}
        before_terms={key:value/ratios[key[1]] if key[0]==8 else value for key,value in terms.items()}
        before=min((ones[h],sum(before_terms.values(),I(0))),key=lambda v:v.b)
        after=strata[h,11,5]
        print('size',h,'rank11c5 selected before/after raw log10',iv.log10(before),iv.log10(after),
              'gain log10',iv.log10(after/before))
        for (t,o),v in sorted(before_terms.items(),key=lambda kv:kv[1].b,reverse=True)[:3]:
            print('previous leading family',t,o,'share log10',iv.log10(v/before))
    return s


if __name__=='__main__':
    checks()
    diagnostic()
