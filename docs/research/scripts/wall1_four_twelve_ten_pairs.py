"""H12/c4: counted norm12 one-four crossings and the complete no-four split."""
from collections import Counter,defaultdict
from itertools import combinations
from math import comb
from wall1_rare_second_line import norm_rows

PAIR_BOUND=9072
TWELVE_PAIR_BOUND=7434


def checks():
    inside=[a+(0,)*8 for a in norm_rows(4,10,minimum_support=4)]
    outside=[]
    for old in combinations(range(4),2):
        support=old+tuple(range(4,12))
        for plus in combinations(support[1:],4):
            positives={support[0],*plus}
            outside.append(tuple(1 if i in positives else -1 if i in support else 0 for i in range(12)))
    assert len(inside)==12 and len(outside)==756
    grams=Counter()
    for a in inside:
        assert sorted(abs(x) for x in a[:4])==[1,1,2,2]
        for b in outside:
            dot=sum(x*y for x,y in zip(a,b))
            assert abs(dot)<=4
            assert any(abs(a[i]*b[j]-a[j]*b[i])==1 for i,j in combinations(range(12),2))
            grams[100-dot*dot]+=1
    assert sum(grams.values())==PAIR_BOUND
    groups=defaultdict(list)
    for b in outside:groups[tuple(b[4]*x for x in b[4:])].append(tuple(b[4]*x for x in b))
    rejected=Counter()
    for rows in groups.values():
        for a,b in combinations(rows,2):
            diff=tuple(x-y for x,y in zip(a,b))
            weight=sum(bool(x) for x in diff)
            assert not any(diff[4:]) and 0<weight<=4
            if weight==4:
                assert sum(x*x for x in diff)==4
                rejected['norm4']+=1
            else:rejected['girth<4']+=1
    print('inside10',len(inside),'outside10',len(outside),'pairs',PAIR_BOUND,'Gram',dict(sorted(grams.items())))
    print('excluded outside/outside pairs',dict(rejected))


def twelve_checks():
    firsts=[a+(0,)*8 for a in norm_rows(4,4)]
    outside=list()
    for plus in combinations(range(1,12),5):
        ps={0,*plus}
        outside.append(tuple(1 if i in ps else -1 for i in range(12)))
    for old in range(4):
        support=(old,)+tuple(range(4,12))
        for double in support:
            single=tuple(i for i in support if i!=double)
            for plus in combinations(single,3):
                ps=set(plus)
                outside.append(tuple(2 if i==double else 1 if i in ps else -1 if i in single else 0 for i in range(12)))
    assert len(outside)==462+2016
    assert len(firsts)*len(outside)==TWELVE_PAIR_BOUND
    for q in (7,17,3329):
        charts=defaultdict(set);witnesses=Counter()
        for a in firsts:
            f=tuple(x*pow(a[0]%q,-1,q)%q for x in a)
            for b in outside:
                assert sum(b)==0 and sum(x*x for x in b)==12
                dot=sum(x*y for x,y in zip(a,b));D=48-dot*dot
                assert any(abs(a[i]*b[j]-a[j]*b[i])==1 for i,j in combinations(range(12),2))
                scalar=-b[3]*pow(a[3]%q,-1,q)%q
                if tuple(i for i in range(4) if (b[i]+scalar*a[i])%q)!=(0,1,2):continue
                assert D in (44,47)
                key=(f,tuple((b[i]-b[0]*f[i])*pow(b[4]%q,-1,q)%q for i in range(12)))
                charts[D].add(key);witnesses[D]+=1
        assert {d:len(v) for d,v in charts.items()}=={44:168,47:1344}
        print('q',q,'norm12 overlap3 charts',{d:len(v) for d,v in charts.items()},'witnesses',dict(witnesses))

def diagnostic():
    import contextlib,inspect,io,sys
    from wall1_general_two_relations import draw14_bounds
    states={}
    source,start=inspect.getsourcelines(draw14_bounds)
    line=start+next(i for i,x in enumerate(source) if 'anchors[c, t, overlap] =' in x)
    before=start+next(i for i,x in enumerate(source) if 'twelve_split=(I(546)' in x)
    def trace(frame,event,arg):
        if frame.f_code is not draw14_bounds.__code__:return None
        if event=='line' and frame.f_lineno in (before,line):
            l=frame.f_locals
            if l['c']==4 and l['t']==8:
                v=states.setdefault(l['overlap'],{})
                if frame.f_lineno==before:
                    v.update(previous_one=l['one_power'],initial=l['power_bound'])
                else:
                    v.update({k:l[k] for k in ('one_power','none_power','power_bound','coefficient_count','one_count','one_tail','no_tail','periodic_plane','alpha','beta','rare_split','direct_one')})
        return trace
    sys.settrace(trace)
    try:
        with contextlib.redirect_stdout(io.StringIO()):s,_,_=draw14_bounds()
    finally:sys.settrace(None)
    I,iv,q,n=s['I'],s['iv'],s['q'],s['N']
    for overlap,v in states.items():
        alpha,beta=v['alpha'],v['beta'];Q=v['coefficient_count']
        def theta(x):
            geo=s['geometry']['theta_upper']
            return geo(x) if x>iv.pi else iv.sqrt(iv.pi/x)*geo(iv.pi**2/x)
        def K(x,y,tail=None):return (iv.pi/beta)**6*((theta(I(x)*alpha)*theta(I(y)*alpha)+(v['no_tail'] if tail is None else tail))/q**2+v['periodic_plane'])
        direct=K(10,I(42)/5)**n+K(12,9)**n
        rare=I(min(Q,PAIR_BOUND))/Q*K(10,I(42)/5)**n
        complement=K(10,I(19)/2)**n+K(12,9)**n
        counted=rare+complement
        newnone=min((v['none_power'],direct,counted),key=lambda x:x.b)
        new=min((v['power_bound'],v['one_power']+newnone),key=lambda x:x.b)
        print('overlap',overlap,'one/selected',iv.log10(v['one_power']/v['power_bound']),
              'none/selected',iv.log10(v['none_power']/v['power_bound']))
        print(' direct/oldnone',iv.log10(direct/v['none_power']),
              ' counted/oldnone',iv.log10(counted/v['none_power']))
        print(' unintegrated nofour candidate/actualselected',iv.log10(new/v['power_bound']),
              ' rare/complement',iv.log10(rare/complement))
        if overlap==3:
            ten=I(546)/Q*K(4,10,v['one_tail'])**n
            twelve=I(min(v['one_count'],TWELVE_PAIR_BOUND))/Q*K(4,11,v['one_tail'])**n
            higher=I(v['one_count'])/Q*K(4,13,v['one_tail'])**n
            previous_one=min((v['previous_one'],v['rare_split'],v['direct_one']),key=lambda x:x.b)
            previous_selected=min((v['initial'],previous_one+v['none_power']),key=lambda x:x.b)
            one_refined=min((previous_one,ten+twelve+higher),key=lambda x:x.b)
            integrated=min((v['initial'],one_refined+v['none_power']),key=lambda x:x.b)
            assert one_refined.a<=v['one_power'].b and v['one_power'].a<=one_refined.b
            assert integrated.a<=v['power_bound'].b and v['power_bound'].a<=integrated.b
            print('Production one-four and selected interval matches verified; no-four unchanged.')
            print('integrated onefour/previous onefour',iv.log10(one_refined/previous_one))
            print('integrated selected / previous selected',iv.log10(integrated/previous_selected))
            print('norm10/norm12/higher relative previous onefour',*[iv.log10(x/previous_one) for x in (ten,twelve,higher)])
            assert iv.log10(integrated/previous_selected).b < -18



if __name__=='__main__':checks();twelve_checks();diagnostic()
