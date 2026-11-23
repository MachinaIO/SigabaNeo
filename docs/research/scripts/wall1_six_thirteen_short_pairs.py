"""H13,c6,t7: counted norm6/8 pairs and a complete no-six complement."""
from collections import Counter,defaultdict
from itertools import combinations
from math import comb

SIX_EIGHT_WITNESSES=2100


def checks():
    from wall1_five_thirteen_short_pairs import unit_lines
    inside=list(unit_lines(13,range(6)))
    outside=[v for old in range(6) for v in unit_lines(13,(old,)+tuple(range(6,13)))]
    assert len(inside)==10 and len(outside)==210
    determinants=Counter();charts={q:{o:set() for o in range(1,6)} for q in (7,17,3329)}
    for a in inside:
        for b in outside:
            dot=sum(x*y for x,y in zip(a,b))
            assert abs(dot)==1
            assert any(abs(a[i])==1 and not b[i] for i in range(6))
            assert all(abs(x)==1 for x in b[6:])
            determinants[48-dot*dot]+=1
            for q,out in charts.items():
                f=tuple(x*pow(a[0]%q,-1,q)%q for x in a)
                key=(f,tuple((x-b[0]*y)*pow(b[6]%q,-1,q)%q for x,y in zip(b,f)))
                for scalar in {(-b[i]*pow(a[i]%q,-1,q))%q for i in range(6)}:
                    support=tuple(i for i in range(6) if (b[i]+scalar*a[i])%q)
                    for o in out:
                        if support==tuple(range(o)):out[o].add(key)
    assert dict(determinants)=={47:SIX_EIGHT_WITNESSES}
    grouped=defaultdict(list)
    for b in outside:
        normalized=tuple(b[6]*x for x in b)
        grouped[normalized[6:]].append(normalized)
    excluded=0
    for members in grouped.values():
        for a,b in combinations(members,2):
            difference=tuple(x-y for x,y in zip(a,b))
            assert not any(difference[6:])
            for q in (7,17,3329):assert 0<sum(bool(x%q) for x in difference)<=2
            excluded+=1
    assert excluded==525
    # Norm10 support-seven rows would be new-only, prohibited by proper overlap.
    from wall1_rare_second_line import norm_rows
    new_only_ten=list(norm_rows(7,10,minimum_support=7))
    assert len(new_only_ten)==105
    outside_ten=[v for old in combinations(range(6),3)
                 for v in unit_lines(13,old+tuple(range(6,13)))]
    assert len(outside_ten)==2520
    ten_groups=defaultdict(list)
    for b in outside_ten:
        normalized=tuple(b[6]*x for x in b)
        ten_groups[normalized[6:]].append(normalized)
    mixed_count=0
    for key,eights in grouped.items():
        for a in eights:
            for b in ten_groups.get(key,[]):
                diff=tuple(x-y for x,y in zip(a,b))
                assert not any(diff[6:])
                for q in (7,17,3329):assert 0<sum(bool(x%q) for x in diff)<=4
                mixed_count+=1
    ten_rejected=Counter()
    for members in ten_groups.values():
        for a,b in combinations(members,2):
            diff=tuple(x-y for x,y in zip(a,b))
            assert not any(diff[6:])
            support=sum(bool(x) for x in diff)
            assert 0<support<=6
            if support==6:
                assert sum(diff)==0 and sum(x*x for x in diff)==6
                ten_rejected['norm6']+=1
            else:ten_rejected['girth<6']+=1
    assert mixed_count==12600
    assert dict(ten_rejected)=={'girth<6':62580,'norm6':3360}
    print('outside norm10',len(outside_ten),'excluded new-only norm10',len(new_only_ten),
          'excluded8/10 pairs',mixed_count,'excluded10/10',dict(ten_rejected))
    print('inside norm6',len(inside),'outside norm8',len(outside),'saturated Gram47 pairs',SIX_EIGHT_WITNESSES)
    print('outside/outside pairs forbidden by girth6',excluded)
    for q,out in charts.items():
        actual={o:len(v) for o,v in out.items()}
        assert actual=={1:350,2:0,3:0,4:0,5:350}
        print('q',q,'eligible chart counts',actual)


def bounds(s,overlap, *, strong=True):
    I,iv,n,q,R=[s[k] for k in ('I','iv','N','q','radius')]
    beta=I(11*n)/(26*R**2);a=iv.pi**2/beta;alpha=a/q**2
    assert 6*36**4<q*q and 14**3<q and 13*36**2<q*q
    def theta(x):
        geo=s['geometry']['theta_upper']
        return geo(x) if x>iv.pi else iv.sqrt(iv.pi/x)*geo(iv.pi**2/x)
    half_sum=theta(3*alpha)**2
    long_tail=iv.exp(-648*alpha)*half_sum
    short_tail=iv.exp(-98*alpha)*half_sum
    delta=2*iv.exp(-a/4)/(1-iv.exp(-2*a))
    periodic=sum((comb(13,j)*delta**j for j in range(1,14)),I(0))
    def kernel(g1,g2,tail):
        return (iv.pi/beta)**(I(13)/2)*((theta(g1*alpha)*theta(g2*alpha)+tail)/q**2+periodic)
    Q=q**(9+overlap);C=min(Q,10*q**(5+overlap))
    rare=I(min(C,SIX_EIGHT_WITNESSES))/Q*kernel(I(6),I(47)/6,long_tail)**n
    remainder=I(C)/Q*kernel(I(6),I(17)/2,long_tail)**n
    no_six=(kernel(I(8),I(10),short_tail)**n
            +kernel(I(10),I(19)/2,short_tail)**n+kernel(I(12),I(9),short_tail)**n) if strong else (
            kernel(I(8),I(8),short_tail)**n+kernel(I(10),I(15)/2,short_tail)**n)
    old_one=I(C)/Q*kernel(I(6),I(13)/2,long_tail)**n
    old_none=kernel(I(8),I(6),short_tail)**n
    return rare+remainder,no_six,rare,remainder,old_one,old_none


def diagnostic():
    import ast,contextlib,inspect,io
    from wall1_general_two_relations import draw14_bounds
    # Instrument only an in-memory copy with one dictionary assignment. This
    # avoids global line tracing and never changes the production source.
    tree=ast.parse(inspect.getsource(draw14_bounds))
    class Capture(ast.NodeTransformer):
        hits=0
        def visit_Assign(self,node):
            if any(ast.unparse(t)=='anchors[c, t, overlap]' for t in node.targets):
                self.hits+=1
                capture=ast.parse('if c == 6 and t == 7:\n    _prior_gaussians[overlap] = chosen_gaussian**n').body[0]
                return [capture,node]
            return self.generic_visit(node)
    transform=Capture();tree=transform.visit(tree);assert transform.hits==1
    namespace=dict(draw14_bounds.__globals__);namespace['_prior_gaussians']={}
    exec(compile(ast.fix_missing_locations(tree),'<c6H13 capture>','exec'),namespace)
    with contextlib.redirect_stdout(io.StringIO()):s,_,_=namespace['draw14_bounds']()
    prior_gaussians=namespace['_prior_gaussians']
    I,iv=s['I'],s['iv']
    for overlap in range(1,6):
        parts=s['six_circuit_split_parts'][7,overlap]
        one,none,rare,rest,old_one,old_none=bounds(s,overlap)
        previous_none=bounds(s,overlap,strong=False)[1]
        assert parts['two-six']==I(0)
        tolerance=I('1e-60')
        new_one=min((old_one,one),key=lambda x:x.b)
        new_none=min((old_none,none),key=lambda x:x.b)
        old_selected=min((prior_gaussians[overlap],old_one+old_none),key=lambda x:x.b)
        new=min((old_selected,new_one+new_none),key=lambda x:x.b)
        for actual,expected in ((parts['one-six'],new_one),(parts['no-six'],new_none),(parts['selected'],new)):
            ratio=actual/expected
            assert ratio.a>(1-tolerance).b and ratio.b<(1+tolerance).a
        print('overlap',overlap,'one-six improvement log10',iv.log10(new_one/old_one),
              'no-six improvement log10',iv.log10(new_none/old_none))
        print(' selected improvement log10',iv.log10(new/old_selected),
              'new one/no-six log10',iv.log10(new_one/new_none),'rare/remainder log10',iv.log10(rare/rest))
        assert new.b<old_selected.a
        previous_selected=min((old_selected,new_one+min(old_none,previous_none)),key=lambda x:x.b)
        print(' strong no-six / previous no-six log10',iv.log10(new_none/previous_none),
              'strong selected / previous selected log10',iv.log10(new/previous_selected))
        print(' production one-six/no-six/selected match relative1e-60')
    return s


if __name__=='__main__':
    checks()
    diagnostic()
