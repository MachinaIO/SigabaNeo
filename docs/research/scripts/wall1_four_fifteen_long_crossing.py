"""H15 c4,t11: counted norm4/12 crossings with complete long-row complements."""
from collections import Counter
from itertools import combinations
from wall1_rare_second_line import norm_rows
PAIR_BOUND=5544


def checks():
    firsts=[a+(0,)*11 for a in norm_rows(4,4)]
    outside=[]
    for old in range(4):
        support=(old,)+tuple(range(4,15))
        for plus in combinations(support[1:],5):
            positives={old,*plus}
            outside.append(tuple(1 if i in positives else -1 if i in support else 0 for i in range(15)))
    assert len(firsts)==3 and len(outside)==1848 and len(firsts)*len(outside)==PAIR_BOUND
    for q in (7,17,3329):
        codes={o:set() for o in (1,2,3)}
        for a in firsts:
            f=tuple(x*pow(a[0]%q,-1,q)%q for x in a)
            for b in outside:
                assert abs(sum(x*y for x,y in zip(a,b)))==1
                assert any(abs(a[i]*b[j]-a[j]*b[i])==1 for i,j in combinations(range(15),2))
                key=(f,tuple((b[i]-b[0]*f[i])*pow(b[4]%q,-1,q)%q for i in range(15)))
                for o in codes:
                    scalar=-b[o]*pow(a[o]%q,-1,q)%q
                    if tuple(i for i in range(4) if (b[i]+scalar*a[i])%q)==tuple(range(o)):
                        codes[o].add(key)
        assert {o:len(v) for o,v in codes.items()}=={1:1386,2:0,3:1386}
        print('q',q,'norm4/12 charts',{o:len(v) for o,v in codes.items()},'D47 and unit minors verified')
    # Any two outside norm12 lines with proportional new coordinates differ
    # on at most two old positions, forbidden by girth4.
    groups={}
    for b in outside:groups.setdefault(tuple(b[4]*x for x in b[4:]),[]).append(tuple(b[4]*x for x in b))
    rejected=0
    for rows in groups.values():
        for a,b in combinations(rows,2):
            diff=tuple(x-y for x,y in zip(a,b))
            assert not any(diff[4:]) and 0<sum(bool(x) for x in diff)<=2
            rejected+=1
    print('outside12/outside12 excluded pairs',rejected)
    assert not list(norm_rows(4,14,minimum_support=4))
    outside14=[]
    for old in combinations(range(4),3):
        support=old+tuple(range(4,15))
        for plus in combinations(support[1:],6):
            positives={support[0],*plus}
            outside14.append(tuple(1 if i in positives else -1 if i in support else 0 for i in range(15)))
    assert len(outside14)==6864
    groups14={}
    for b in outside14:groups14.setdefault(tuple(b[4]*x for x in b[4:]),[]).append(tuple(b[4]*x for x in b))
    mixed=equal=0
    for key,rows in groups14.items():
        for a in groups.get(key,[]):
            for b in rows:
                diff=tuple(x-y for x,y in zip(a,b))
                weight=sum(bool(x) for x in diff)
                assert not any(diff[4:]) and 0<weight<=4
                assert weight<=3 or sum(x*x for x in diff)==4
                mixed+=1
        for a,b in combinations(rows,2):
            diff=tuple(x-y for x,y in zip(a,b))
            assert not any(diff[4:]) and 0<sum(x*x for x in diff)<=10
            equal+=1
    print('outside14 lines',len(outside14),'excluded12/14 pairs',mixed,'excluded14/14 pairs',equal)


def diagnostic():
    """Private AST copy: capture branch boundaries without global tracing."""
    import ast,contextlib,inspect,io,textwrap
    from wall1_general_two_relations import draw14_bounds
    tree=ast.parse(textwrap.dedent(inspect.getsource(draw14_bounds)))
    root=tree.body[0];states={};inserted={'rare':0,'none':0,'final':0}
    def marker(tag,node):
        inserted[tag]+=1
        return ast.copy_location(ast.Expr(ast.Call(ast.Name('_h15_capture',ast.Load()),
            [ast.Constant(tag),ast.Call(ast.Name('locals',ast.Load()),[],[])],[])),node)
    class Capture(ast.NodeTransformer):
        def visit_FunctionDef(self,node):return self.generic_visit(node) if node is root else node
        def visit_If(self,node):
            text=ast.unparse(node.test).replace(' ','')
            tag='rare' if text=='union==15' else 'none' if text=='c==4andunion==15' else None
            self.generic_visit(node)
            return [marker(tag,node),node] if tag else node
        def visit_Assign(self,node):
            if any(isinstance(t,ast.Subscript) and isinstance(t.value,ast.Name) and t.value.id=='anchors' for t in node.targets):
                return [marker('final',node),node]
            return node
    tree=Capture().visit(tree);ast.fix_missing_locations(tree)
    assert inserted=={'rare':1,'none':1,'final':1},inserted
    def hook(tag,l):
        if l.get('c')!=4 or l.get('t')!=11:return
        state=states.setdefault(l['overlap'],{})
        if tag=='rare':state.update(old_one=l['one_power'],old_rare=l['rare_split'],initial=l['power_bound'])
        elif tag=='none':state.update(old_none=l['none_power'],direct=l['direct_one'])
        else:state.update({k:l[k] for k in ('one_power','none_power','power_bound','one_count','coefficient_count','one_tail','no_tail','periodic_plane','alpha','beta')})
    namespace=dict(draw14_bounds.__globals__);namespace['_h15_capture']=hook
    exec(compile(tree,inspect.getsourcefile(draw14_bounds)+'::h15-capture','exec'),namespace)
    instrumented=namespace['draw14_bounds']
    assert inspect.signature(instrumented)==inspect.signature(draw14_bounds)
    assert '_h15_capture' not in draw14_bounds.__globals__
    with contextlib.redirect_stdout(io.StringIO()):s,_,_=instrumented()
    I,iv,n,q=s['I'],s['iv'],s['N'],s['q']
    for o,v in states.items():
        alpha,beta=v['alpha'],v['beta'];Q=v['coefficient_count']
        def theta(x):
            geo=s['geometry']['theta_upper']
            return geo(x) if x>iv.pi else iv.sqrt(iv.pi/x)*geo(iv.pi**2/x)
        def K(x,y,tail):return (iv.pi/beta)**(I(15)/2)*((theta(I(x)*alpha)*theta(I(y)*alpha)+tail)/q**2+v['periodic_plane'])
        rare=I(min(v['one_count'],PAIR_BOUND))/Q*K(4,I(47)/4,v['one_tail'])**n
        higher=I(v['one_count'])/Q*K(4,13,v['one_tail'])**n
        oldone=min((v['old_one'],v['old_rare'],v['direct']),key=lambda x:x.b)
        oldnone=v['old_none']
        previous=min((v['initial'],oldone+oldnone),key=lambda x:x.b)
        newone=min((oldone,rare+higher),key=lambda x:x.b)
        basic=K(10,9,v['no_tail'])**n
        stronger=(K(10,I(23)/2,v['no_tail'])**n+K(12,I(45)/4,v['no_tail'])**n
                  +K(14,I(25)/2,v['no_tail'])**n+K(16,12,v['no_tail'])**n)
        newnone=min((oldnone,stronger),key=lambda x:x.b)
        new=min((v['initial'],newone+newnone),key=lambda x:x.b)
        for expected,actual in ((newone,v['one_power']),(newnone,v['none_power']),(new,v['power_bound'])):
            assert expected.a<=actual.b and actual.a<=expected.b,(o,expected,actual)
        print('overlap',o,'production one/no-four/selected interval matches verified')
        print('previous one/selected',iv.log10(oldone/previous),'previous none/selected',iv.log10(oldnone/previous))
        print('newone/previousone',iv.log10(newone/oldone),'basicnone/previousnone',iv.log10(basic/oldnone),'strongernone/previousnone',iv.log10(stronger/oldnone))
        print('integrated/previousselected',iv.log10(new/previous),'rare/higher',iv.log10(rare/higher))
        assert iv.log10(new/previous).b < (-15.57 if o==2 else -17.93)



if __name__=='__main__':checks();diagnostic()
