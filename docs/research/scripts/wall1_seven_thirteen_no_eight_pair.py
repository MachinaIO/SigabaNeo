"""Girth7,H13: independent norm-eight pairs are impossible; complete tails."""
from collections import defaultdict
from itertools import combinations
from math import comb


def checks():
    from wall1_five_thirteen_short_pairs import unit_lines
    rows=[v for old in combinations(range(7),2)
          for v in unit_lines(13,old+tuple(range(7,13)))]
    assert len(rows)==735
    grouped=defaultdict(list)
    for b in rows:
        assert sum(b)==0 and sum(x*x for x in b)==8
        normalized=tuple(b[7]*x for x in b)
        grouped[normalized[7:]].append(normalized)
    checked=0
    for members in grouped.values():
        for a,b in combinations(members,2):
            difference=tuple(x-y for x,y in zip(a,b))
            assert not any(difference[7:])
            assert 0<sum(bool(x) for x in difference)<=4
            for q in (7,17,3329):
                assert 0<sum(bool(x%q) for x in difference)<=4
            checked+=1
    assert checked==11760
    print('norm8 crossing lines',len(rows),'proportional-new pairs excluded',checked)


def diagnostic():
    import contextlib,inspect,io,sys
    from wall1_general_two_relations import draw14_bounds
    source,start=inspect.getsourcelines(draw14_bounds)
    anchor_line=start+next(i for i,l in enumerate(source) if 'anchors[c, t, overlap] =' in l)
    charge_line=start+next(i for i,l in enumerate(source) if 'charge = (choices*q**(c+t+a-4)' in l)+2
    stratum_line=start+next(i for i,l in enumerate(source) if 'strata[h, r, c] = chosen' in l)
    local={};raw={};ones={}
    def trace(frame,event,arg):
        if frame.f_code is not draw14_bounds.__code__:return None
        if event=='line':
            v=frame.f_locals
            if frame.f_lineno==anchor_line and v['c']==7 and v['t']==6:
                local[v['overlap']]={k:v[k] for k in ('power_bound','chosen_gaussian','tail_plane','periodic_plane','alpha','beta','power')}
            if frame.f_lineno==charge_line and v['h'] in (18,19) and v['r']==11 and v['c']==7:
                raw[v['h'],v['t'],v['a']]=v['charge']
            if frame.f_lineno==stratum_line and v['h'] in (18,19) and v['r']==11 and v['c']==7:
                ones[v['h']]=v['one']
        return trace
    sys.settrace(trace)
    try:
        with contextlib.redirect_stdout(io.StringIO()):s,_,strata=draw14_bounds()
    finally:sys.settrace(None)
    I,iv,n,q=[s[k] for k in ('I','iv','N','q')]
    assert 14**3<q and 13*14**2<q*q
    ratios={}
    for overlap,v in local.items():
        assert v['power']==I(13)/2
        alpha,beta=v['alpha'],v['beta']
        def theta(x):
            geo=s['geometry']['theta_upper']
            return geo(x) if x>iv.pi else iv.sqrt(iv.pi/x)*geo(iv.pi**2/x)
        tolerance=I('1e-60')
        def matches(actual,expected):
            ratio=actual/expected
            assert ratio.a>(1-tolerance).b and ratio.b<(1+tolerance).a
        # Recompute corrections independently, not by reusing production tails.
        tail=iv.exp(-98*alpha)*theta(I(13)/4*alpha)**2
        a0=iv.pi**2/beta
        delta=2*iv.exp(-a0/4)/(1-iv.exp(-2*a0))
        periodic=sum((comb(13,j)*delta**j for j in range(1,14)),I(0))
        matches(v['tail_plane'],tail)
        matches(v['periodic_plane'],periodic)
        def kernel(g1,g2):
            return (iv.pi/beta)**(I(13)/2)*((theta(g1*alpha)*theta(g2*alpha)+tail)/q**2+periodic)
        bound=kernel(I(8),I(8))**n+kernel(I(10),I(15)/2)**n
        # Prior H13/c7 had no specialized branch: its selected bound was
        # exactly the generic chosen_gaussian**N, including overlap alternatives.
        old=v['chosen_gaussian']**n
        new=min((old,bound),key=lambda x:x.b)
        matches(v['power_bound'],new)
        ratios[overlap]=new/old
        print('overlap',overlap,'production matched; new / reconstructed previous selected log10',iv.log10(ratios[overlap]))
        assert new.b<old.a
    for h in (18,19):
        terms={key[1:]:value for key,value in raw.items() if key[0]==h}
        old_two=sum((value/ratios[o] if t==6 else value for (t,o),value in terms.items()),I(0))
        before=min((ones[h],old_two),key=lambda x:x.b)
        after=strata[h,11,7]
        matches(after,min((ones[h],sum(terms.values(),I(0))),key=lambda x:x.b))
        assert after.b<before.a
        print('size',h,'rank11c7 selected improvement log10',iv.log10(after/before))
    return s


if __name__=='__main__':
    checks()
    diagnostic()
