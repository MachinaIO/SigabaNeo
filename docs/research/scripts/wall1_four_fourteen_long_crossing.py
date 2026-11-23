"""H14/c4/t10: count norm12 crossings and retain full complementary tails."""
from collections import Counter
from itertools import combinations
from math import comb
from wall1_rare_second_line import norm_rows


def checks():
    firsts=[a+(0,)*10 for a in norm_rows(4,4)]
    outside=[]
    for old in combinations(range(4),2):
        supp=old+tuple(range(4,14))
        for plus in combinations(supp,6):
            ps=set(plus)
            b=tuple((1 if i in ps else -1) if i in supp else 0 for i in range(14))
            if b[supp[0]]>0:outside.append(b)
    assert len(firsts)==3 and len(outside)==2772
    for q in (7,17,3329):
        codes={a:set() for a in (1,2,3)};grams={a:Counter() for a in codes}
        for a in firsts:
            f=tuple(x*pow(a[0]%q,-1,q)%q for x in a)
            for b in outside:
                dot=sum(x*y for x,y in zip(a,b));D=48-dot*dot
                assert any(abs(a[i]*b[j]-a[j]*b[i])==1 for i,j in combinations(range(14),2))
                key=(f,tuple((b[i]-b[0]*f[i])*pow(b[4]%q,-1,q)%q for i in range(14)))
                for o in codes:
                    scale=-b[o]*pow(a[o]%q,-1,q)%q
                    if tuple(i for i in range(4) if (b[i]+scale*a[i])%q)!=tuple(range(o)):continue
                    codes[o].add(key);grams[o][D]+=1
        assert set(grams[3])=={48}
        assert {o:len(v) for o,v in codes.items()}=={1:0,2:1386,3:2016}
        assert grams[3][48]==2016
        print('q',q,'charts',{o:len(v) for o,v in codes.items()},'D3',dict(grams[3]))


def diagnostic():
    """Reconstruct pre-integration bounds and verify current production kernels."""
    import contextlib,inspect,io,sys
    from wall1_general_two_relations import draw14_bounds
    states={o:{} for o in (1,2,3)}
    lines,start=inspect.getsourcelines(draw14_bounds)
    def location(text):return start+next(i for i,x in enumerate(lines) if text in x)
    rare_line=location('if union==14 and overlap==3:')
    none_line=location('if c==4 and union==14:')
    final_line=location('anchors[c, t, overlap] =')
    def local(frame,event,arg):
        if event!='line' or frame.f_lineno not in (rare_line,none_line,final_line):return local
        l=frame.f_locals
        if l.get('c')!=4 or l.get('t')!=10:return local
        state=states[l['overlap']]
        if frame.f_lineno==rare_line:
            state.update(old_one=l['one_power'],old_rare=l['rare_split'],initial=l['power_bound'])
        elif frame.f_lineno==none_line:
            state.update(old_none=l['none_power'],direct=l['direct_one'])
        else:
            state.update({k:l[k] for k in ('one_power','none_power','power_bound',
                'coefficient_count','one_count','one_tail','no_tail','periodic_plane','alpha','beta')})
        return local
    def global_(frame,event,arg):
        if event=='call' and frame.f_code is draw14_bounds.__code__:return local
    sys.settrace(global_)
    try:
        with contextlib.redirect_stdout(io.StringIO()):s,_,_=draw14_bounds()
    finally:sys.settrace(None)
    I,iv,n,q=s['I'],s['iv'],s['N'],s['q']
    def same(x,y):assert x.a<=y.b and y.a<=x.b,(x,y)
    for overlap,state in states.items():
        alpha,beta=state['alpha'],state['beta'];Q=state['coefficient_count']
        def theta(x):
            geo=s['geometry']['theta_upper']
            return geo(x) if x>iv.pi else iv.sqrt(iv.pi/x)*geo(iv.pi**2/x)
        def K(x,y,tail):return (iv.pi/beta)**7*((theta(I(x)*alpha)*theta(I(y)*alpha)+tail)/q**2+state['periodic_plane'])
        oldone=min((state['old_one'],state['old_rare'],state['direct']),key=lambda x:x.b)
        oldnone=state['old_none']
        oldselected=min((state['initial'],oldone+oldnone),key=lambda x:x.b)
        newone=oldone
        if overlap==3:
            rare=I(min(state['one_count'],8316))/Q*K(4,12,state['one_tail'])**n
            complement=I(state['one_count'])/Q*K(4,13,state['one_tail'])**n
            newone=min((oldone,rare+complement),key=lambda x:x.b)
            print('rare/complement',iv.log10(rare/complement))
        newnone=min((oldnone,K(10,9,state['no_tail'])**n),key=lambda x:x.b)
        newselected=min((state['initial'],newone+newnone),key=lambda x:x.b)
        same(newone,state['one_power'])
        same(newnone,state['none_power'])
        same(newselected,state['power_bound'])
        print('overlap',overlap,'production one/no-four/selected interval matches verified')
        print('previous one/no-four/selected log10',*[iv.log10(x) for x in (oldone,oldnone,oldselected)])
        print('integrated / previous selected log10',iv.log10(state['power_bound']/oldselected))
        if overlap==3:
            assert iv.log10(state['power_bound']/oldselected).b<-27.94
            print('newone/oldone',iv.log10(newone/oldone))
            print('newnone/oldnone',iv.log10(newnone/oldnone))


if __name__=='__main__':checks();diagnostic()
