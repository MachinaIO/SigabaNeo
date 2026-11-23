"""H9 c5 complete counted short-pair covers; standalone production comparison."""
from itertools import combinations,product
from math import comb

SIX_EIGHT_COUNTS={1:0,2:200,3:60,4:560}
EIGHT_EIGHT_COUNTS={1:400,2:126,3:258,4:2212}


def counts(q=3329):
    from wall1_rare_second_line import norm_rows
    rows={e:[v for v in norm_rows(9,e,minimum_support=5)
             if not any(v[5:]) or all(v[5:])] for e in (6,8)}
    assert len(rows[6])==100 and len(rows[8])==295
    out={kind:{o:set() for o in range(1,5)} for kind in ('six-eight','eight-eight')}
    for kind,pairs in [('six-eight',product(rows[6],rows[8])),('eight-eight',combinations(rows[8],2))]:
        for a,b in pairs:
            if not all(x or y for x,y in zip(a,b)):continue
            if any(a[i]*b[j]-a[j]*b[i] for i,j in combinations(range(5,9),2)):continue
            p=5
            f=tuple((b[p]*x-a[p]*y)%q for x,y in zip(a,b))
            if not all(f[:5]):continue
            f=tuple(x*pow(f[0],-1,q)%q for x in f)
            v=b if b[5] else a
            v=tuple((v[i]-v[0]*f[i])*pow(v[5]%q,-1,q)%q for i in range(9))
            scalars={(-v[i]*pow(f[i],-1,q))%q for i in range(5)}
            words=[tuple((v[i]+z*f[i])%q for i in range(9)) for z in scalars]
            if any(sum(bool(x) for x in w)<5 for w in words):continue
            for o in range(1,5):
                target=tuple(range(o))+tuple(range(5,9))
                if any(tuple(i for i,x in enumerate(w) if x)==target for w in words):
                    out[kind][o].add((f,v))
    result={kind:{o:len(v) for o,v in by.items()} for kind,by in out.items()}
    assert result=={'six-eight':SIX_EIGHT_COUNTS,'eight-eight':EIGHT_EIGHT_COUNTS}
    print('q',q,'counts',result,flush=True)
    return result


def bounds(s,o,counts):
    I,iv,n,q,R=[s[k] for k in ('I','iv','N','q','radius')]
    assert 6*36**4<q*q and 14**3<q and 9*36**2<q*q
    beta=I(7*n)/(18*R**2);a=iv.pi**2/beta;alpha=a/q**2
    def theta(x):
        f=s['geometry']['theta_upper']
        return f(x) if x>iv.pi else iv.sqrt(iv.pi/x)*f(iv.pi**2/x)
    half=theta(I(9)/4*alpha)**2
    tails={36:iv.exp(-648*alpha)*half,14:iv.exp(-98*alpha)*half}
    delta=2*iv.exp(-a/4)/(1-iv.exp(-2*a))
    periodic=sum((comb(9,j)*delta**j for j in range(1,10)),I(0))
    def K(u,v,cut):return (iv.pi/beta)**(I(9)/2)*((theta(u*alpha)*theta(v*alpha)+tails[cut])/q**2+periodic)
    Q=q**(5+o);C=min(Q,840*q**3)
    one=I(min(C,counts['six-eight'][o]))/Q*K(I(6),I(13)/2,36)**n+I(C)/Q*K(I(6),I(17)/2,36)**n
    none=I(min(Q,counts['eight-eight'][o]))/Q*K(I(8),I(6),14)**n+K(I(8),I(8),14)**n+K(I(10),I(15)/2,14)**n
    return one,none,I(C)/Q*K(I(6),I(13)/2,36)**n,K(I(8),I(6),14)**n


def diagnostic(cs):
    import ast,contextlib,inspect,io
    from wall1_general_two_relations import draw14_bounds
    tree=ast.parse(inspect.getsource(draw14_bounds))
    class Capture(ast.NodeTransformer):
        def visit_Assign(self,node):
            if any(ast.unparse(t)=='anchors[c, t, overlap]' for t in node.targets):
                return [ast.parse('if c == 5 and t == 4:\n    _gaussians[overlap] = chosen_gaussian**n').body[0],node]
            return self.generic_visit(node)
        def visit_AugAssign(self,node):
            if ast.unparse(node.target)=='two' and ast.unparse(node.value)=='charge':
                return [ast.parse('if h == 18 and r == 9 and c == 5:\n    _terms[t,a] = charge').body[0],node]
            return self.generic_visit(node)
    tree=Capture().visit(tree);ns=dict(draw14_bounds.__globals__);ns['_terms']={};ns['_gaussians']={}
    exec(compile(ast.fix_missing_locations(tree),'<H9 capture>','exec'),ns)
    with contextlib.redirect_stdout(io.StringIO()):s,_,st=ns['draw14_bounds']()
    I,iv=s['I'],s['iv'];new=st[18,9,5];old=new
    total=sum(ns['_terms'].values(),I(0));assert total.a<=new.b and new.a<=total.b
    reconstructed=dict(ns['_terms'])
    for o in range(1,5):
        p=s['five_circuit_anchor_parts'][4,o]
        one,none,old_one,old_none=bounds(s,o,cs)
        one=min(one,old_one,key=lambda x:x.b);none=min(none,old_none,key=lambda x:x.b)
        old_selected=min(ns['_gaussians'][o],old_one+old_none,key=lambda x:x.b)
        chosen=min(old_selected,one+none,key=lambda x:x.b)
        for actual,expected in ((p['one-six'],one),(p['no-six'],none),(p['selected'],chosen)):
            quotient=actual/expected;tolerance=I('1e-60')
            assert quotient.a>(1-tolerance).b and quotient.b<(1+tolerance).a
        assert p['two-six']==I(0)
        ratio=chosen/old_selected
        reconstructed[4,o]=ns['_terms'][4,o]/ratio
        old+=reconstructed[4,o]-ns['_terms'][4,o]
        print('overlap',o,'onegain',iv.log10(one/old_one),'nonegain',iv.log10(none/old_none),'selectedgain',iv.log10(ratio),'one/none',iv.log10(one/none),flush=True)
        print('production one-six/no-six/selected match relative1e-60',flush=True)
    for key,value in sorted(reconstructed.items(),key=lambda kv:kv[1].b,reverse=True)[:8]:
        print('reconstructed old rawterm',key,'relative',iv.log10(value/old),flush=True)
    print('rank9 c5 size18 old',iv.log10(old),'new',iv.log10(new),'gain',iv.log10(new/old),flush=True)

if __name__=='__main__':
    cs=counts();assert counts(17)==cs and counts(7)==cs
    diagnostic(cs)
