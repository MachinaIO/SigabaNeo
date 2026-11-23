"""H9/c3: counted (6,8) pairs and the complete no-six complement."""
from collections import Counter
from itertools import combinations
from math import comb
from wall1_rare_second_line import norm_rows

PAIR_BOUND=315

def checks():
    inside=[v+(0,)*6 for v in norm_rows(3,6,minimum_support=3)]
    outside=[v for v in norm_rows(9,8,minimum_support=3) if all(v[3:])]
    assert len(inside)==3 and len(outside)==105
    determinants=Counter()
    for a in inside:
        for b in outside:
            assert sum(bool(x) for x in b[:3])==2
            assert all(abs(x)<=1 for x in b)
            dot=sum(x*y for x,y in zip(a,b))
            assert abs(dot)<=3
            assert any(abs(a[i]*b[j]-a[j]*b[i])==1 for i,j in combinations(range(9),2))
            determinants[48-dot*dot]+=1
    assert sum(determinants.values())==PAIR_BOUND
    excluded=Counter()
    for a,b in combinations(outside,2):
        ratio=a[3]*b[3]
        if any(x!=ratio*y for x,y in zip(a[3:],b[3:])):continue
        d=tuple(x-ratio*y for x,y in zip(a,b))
        support=sum(bool(x) for x in d)
        norm=sum(x*x for x in d)
        assert sum(d)==0 and 0<support<=3
        assert support==2 or norm==6
        excluded[support,norm]+=1
    print('inside/outside:',len(inside),len(outside),'Gram strata:',dict(sorted(determinants.items())))
    print('outside pairs:',dict(sorted(excluded.items())))
    return determinants


def kernels(s,overlap,counts):
    I,iv,q,n,R=[s[k] for k in ('I','iv','q','N','radius')]
    beta=I(7*n)/(18*R**2);a=iv.pi**2/beta;alpha=a/q**2
    assert 14**3<q and 9*14**2<q*q and 6*36**4<q*q
    def theta(x):
        geo=s['geometry']['theta_upper']
        return geo(x) if x>iv.pi else iv.sqrt(iv.pi/x)*geo(iv.pi**2/x)
    delta=2*iv.exp(-a/4)/(1-iv.exp(-2*a))
    periodic=sum((comb(9,j)*delta**j for j in range(1,10)),I(0))
    half=theta(I(3)*alpha/2)**2
    def kernel(x,y,cut):
        tail=iv.exp(-I(cut*cut)*alpha/2)*half
        return (iv.pi/beta)**(I(9)/2)*((theta(I(x)*alpha)*theta(I(y)*alpha)+tail)/q**2+periodic)
    Q=q**(5+overlap)
    six_count=3*q**(4+overlap)
    rare=sum((I(count)/Q*kernel(6,I(det)/6,36)**n for det,count in counts.items()),I(0))
    six_rest=I(six_count)/Q*kernel(6,I(17)/2,36)**n
    no_six=kernel(8,8,14)**n+kernel(10,I(15)/2,14)**n
    oldparts=s['three_circuit_no_four_parts'][6,overlap]
    uniform=I(min(six_count,PAIR_BOUND))/Q*kernel(6,I(39)/6,36)**n
    one=min((oldparts['one-six'],rare+six_rest),key=lambda x:x.b)
    none=min((oldparts['no-six'],no_six),key=lambda x:x.b)
    new=min((oldparts['selected'],one+none),key=lambda x:x.b)
    production=min((oldparts['selected'],
        min((oldparts['one-six'],uniform+six_rest),key=lambda x:x.b)+none),key=lambda x:x.b)
    return production,new,{'rare':rare,'six-rest':six_rest,'no-six':none,'one-six':one}


def previous_evaluator(function):
    """Private AST copy removing exactly the two new H9 refinements."""
    import ast,inspect,textwrap
    tree=ast.parse(textwrap.dedent(inspect.getsource(function)))
    target=ast.dump(ast.parse('c == 3 and union == 9',mode='eval').body)
    class Remove(ast.NodeTransformer):
        count=0
        def visit_If(self,node):
            if ast.dump(node.test)==target:
                self.count+=1
                assert not node.orelse
                return []
            return self.generic_visit(node)
    transform=Remove();tree=transform.visit(tree)
    assert transform.count==2, transform.count
    ast.fix_missing_locations(tree)
    namespace=dict(function.__globals__)
    exec(compile(tree,inspect.getsourcefile(function)+'::pre-H9', 'exec'),namespace)
    return namespace[function.__name__]


def diagnostic(counts):
    import contextlib,io
    from wall1_general_two_relations import draw14_bounds
    from wall1_high_order_frontier import _capture_copy
    flags=dict(exclude_three_circuit_twenty=True,exclude_five_twenty=True,
               exclude_five_fifteen=True,exclude_six_twenty_three=True)
    states={}
    wrapped=_capture_copy(draw14_bounds,lambda value,state:states.update(state))
    original=previous_evaluator(draw14_bounds)
    # Only final state is needed: the function's return tuple includes s and
    # strata; anchors reconstruct from the actual changed local kernels below.
    with contextlib.redirect_stdout(io.StringIO()):
        s,_,strata=wrapped(**flags)
        olds,_,oldstrata=original(**flags)
    I,iv,q,n,R=[s[k] for k in ('I','iv','q','N','radius')]
    anchors=states['anchors'];m=s['m'];mu=s['mu'];completion=states['completions'][9]
    ratios={}
    for overlap in (1,2):
        uniform,exact,parts=kernels(olds,overlap,counts)
        beta=I(7*n)/(18*R**2)
        factor=iv.exp(9*beta*R**2)/q**(m*7)
        actual=anchors[3,6,overlap]/factor
        tolerance=I('1e-60')
        assert (actual/uniform).a>(1-tolerance).b
        assert (actual/uniform).b<(1+tolerance).a
        old=olds['three_circuit_no_four_parts'][6,overlap]['selected']
        ratios[6,overlap]=actual/old
        print('overlap',overlap,'integrated/previous log10',iv.log10(actual/old),
              'optional exact/uniform log10',iv.log10(exact/actual))
    for h in (17,18):
        terms={}
        for t in range(2,9):
            for o in (1,2):
                if t+o<3:continue
                choices=comb(h,3)*comb(h-3,t)*comb(3,o)*comb(h-3-t,8-t)
                terms[t,o]=(choices*q**(t+o-1)*anchors[3,t,o]*mu**(8-t)
                            *completion**(h-11)/(9-t))
        newtwo=sum(terms.values(),I(0))
        oldtwo=sum((value/ratios.get(key,I(1)) for key,value in terms.items()),I(0))
        one=(comb(h,3)*comb(h-3,7)*s['epsilon'][3]*mu**7*completion**(h-10)/8)
        oldselected=min((one,oldtwo),key=lambda x:x.b)
        newselected=min((one,newtwo),key=lambda x:x.b)
        for reconstructed,reference in ((oldselected,oldstrata[h,9,3]),
                                         (newselected,strata[h,9,3])):
            assert (reconstructed/reference).a>I('0.999999999999').b
            assert (reconstructed/reference).b<I('1.000000000001').a
        print('size',h,'rank9c3 integrated/previous residual log10',iv.log10(newselected/oldselected))
    return ratios

if __name__=='__main__':diagnostic(checks())
