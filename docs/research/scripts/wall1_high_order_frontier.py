"""Read-only capture of actual high-order production strata and selected covers."""
import contextlib
import io
import ast
import inspect
import textwrap
from math import comb
from wall1_larger_triangular_components import actual_parameters


def _capture_copy(function, callback, *, globals_override=None):
    """Clone one function, wrapping only its own returns in a locals hook.

    Nested functions are not transformed. The original return expression is
    evaluated once, before locals are read; the hook returns the same object.
    All changes occur in a private globals dictionary, never a loaded module.
    """
    assert function.__closure__ is None
    source=textwrap.dedent(inspect.getsource(function))
    tree=ast.parse(source)
    root=tree.body[0]
    assert isinstance(root,ast.FunctionDef) and not root.decorator_list
    hook_name='_high_order_return_capture_hook'
    locals_name='_high_order_return_capture_locals'
    names={n.id for n in ast.walk(tree) if isinstance(n,ast.Name)}
    assert hook_name not in names and locals_name not in names
    class WrapReturns(ast.NodeTransformer):
        count=0
        def visit_FunctionDef(self,node):
            return self.generic_visit(node) if node is root else node
        def visit_AsyncFunctionDef(self,node):return node
        def visit_Lambda(self,node):return node
        def visit_Return(self,node):
            self.count+=1
            value=node.value if node.value is not None else ast.Constant(None)
            return ast.copy_location(ast.Return(ast.Call(
                ast.Name(hook_name,ast.Load()),
                [value,ast.Call(ast.Name(locals_name,ast.Load()),[],[])],[])),node)
    transform=WrapReturns()
    tree=transform.visit(tree)
    assert transform.count>0
    ast.fix_missing_locations(tree)
    namespace=dict(function.__globals__)
    if globals_override:namespace.update(globals_override)
    def hook(value,state):
        callback(value,state)
        return value
    namespace[hook_name]=hook
    namespace[locals_name]=locals
    exec(compile(tree,inspect.getsourcefile(function)+'::return-capture','exec'),namespace)
    result=namespace[function.__name__]
    assert inspect.signature(result)==inspect.signature(function)
    return result


def _capture_probe(value, *, stop=False):
    def nested(x):return {'nested':x}
    answer=nested(value)
    if stop:return None
    return answer


def capture_checks():
    records=[]
    wrapped=_capture_copy(_capture_probe,lambda value,state:records.append((value,state)))
    for stop in (False,True):
        before=len(records)
        result=wrapped(7,stop=stop)
        assert result==_capture_probe(7,stop=stop)
        assert len(records)==before+1  # No hook for nested().
        captured,state=records[-1]
        assert captured is result
        assert state['value']==7 and state['stop']==stop
        assert state['answer']=={'nested':7}
    assert '_high_order_return_capture_hook' not in _capture_probe.__globals__
    print('Passed return-capture checks: normal/early returns, object identity, nested exclusion, globals isolation.')


def main():
    from wall1_general_two_relations import draw14_bounds
    captured={};draws={}
    def capture_draw(value,state):
        assert isinstance(value,tuple) and len(value)==3
        draws[id(value[2])]={'anchors':state['anchors'],'s':state['s'],
                            'completions':state.get('completions'),
                            'theta_anchors':state['theta_anchors'],
                            'dual_completions':state['dual_completions'],
                            'extended_dual_completions':state['extended_dual_completions'],
                            'gaussian_free':state['gaussian_free'],
                            'optimized_gaussian_free':state['optimized_gaussian_free'],
                            'anisotropic_dual_completions':state['anisotropic_dual_completions']}
    instrumented_draw=_capture_copy(draw14_bounds,capture_draw)
    instrumented_actual=_capture_copy(actual_parameters,
        lambda value,state:captured.update(state),
        globals_override={'draw14_bounds':instrumented_draw})
    with contextlib.redirect_stdout(io.StringIO()):instrumented_actual()
    l=captured;s=l['s'];I,iv,q,mu=s['I'],s['iv'],s['q'],s['mu']
    def covers(h,r,c):
        key=(h,r,c);old=l['strata'][key]
        result={'original':({'unrestricted':old},'strata')}
        if c==4 and r>=4:
            added={}
            for name,residual,label,source in (
                ('triangle','free','triangle','triangular'),
                ('two-four','no_double','other-two-four','other'),
                ('D20-eight','no_twenty','D20-eight','twenty'),
                ('D23-nine','no_twenty_three','D23-nine','twenty_three'),
                ('D24-eight','no_twenty_four','D24-eight','twenty_four'),
                ('D23-seven','no_seven_six','D23-seven','seven_six'),
                ('D28-ten','no_ten_eight','D28-ten','ten_eight'),
                ('D31-eleven','no_eleven_thirty_one','D31-eleven','eleven_thirty_one')):
                added[label]=l[source][h,r]
                result[name]=({'remaining':l[residual][key],**added},residual)
        if c==3 and r>=4:
            added={}
            for name,residual,source in (
                ('D20-six','no_girth_three_twenty','girth_three_twenty'),
                ('D20-five','no_five_twenty','five_twenty'),
                ('two-four-five','no_five_fifteen','five_fifteen'),
                ('D23-six','no_six_twenty_three','six_twenty_three')):
                added[name]=l[source][h,r]
                result[name]=({'remaining':l[residual][key],**added},residual)
        if c==6 and r>=7:
            added={'D27-nine':l['nine_twenty_seven'][h,r]}
            result['D27-nine']=({'remaining':l['no_nine_twenty_seven'][key],**added},'no_nine_twenty_seven')
            if r in (8,9,10,11,12) or (r>=13 and (h,r) in l["six_ten_all_rank"]):
                if r>=13:
                    added["D32-ten"]=l["six_ten_all_rank"][h,r]
                elif r>=11:
                    added['D32-ten']=l['six_ten_higher_rank'][h,r]
                else:
                    source={8:'six_ten_thirty_two',9:'six_ten_rank_nine',10:'six_ten_rank_ten'}[r]
                    added['D32-ten']=l[source][h]
                result['D32-ten']=({'remaining':l['no_six_ten_thirty_two'][key],**added},'no_six_ten_thirty_two')
        if c==4 and r>=4 and 'no_six_d24' in l:
            previous=result['D31-eleven'][0]
            result['D24-six']=({**previous,'remaining':l['no_six_d24'][key],'D24-six':l['six_d24'][h,r]},'no_six_d24')
        return result
    for h in (18,19,24):
        factor=s['normalizer']*l['linear'][h]
        entries=sorted(((v.b,r,c,v) for (hh,r,c),v in l['refined_strata'].items() if hh==h),reverse=True)
        print('SIZE',h,'TOTAL',iv.log10(factor*sum((v for _,r,c,v in entries),I(0))),flush=True)
        for _,r,c,v in entries[:6]:
            choices=covers(h,r,c)
            totals={k:sum(p.values(),I(0)) for k,(p,res) in choices.items()}
            win=min(totals,key=lambda k:totals[k].b);parts,res=choices[win]
            assert totals[win].a<=v.b and v.a<=totals[win].b
            print('STRATUM',h,r,c,'nullity',h-r,'LOG',iv.log10(factor*v),'COVER',win,flush=True)
            for label,p in sorted(parts.items(),key=lambda kv:kv[1].b,reverse=True):
                print(' PART',label,iv.log10(factor*p),flush=True)
            dd=draws[id(l[res])];ss=dd['s'];anchors=dd['anchors']
            M=dd['completions'][r] if dd['completions'] is not None else I(q**(r-1))
            one=(comb(h,c)*comb(h-c,r-c+1)*ss['epsilon'][c]*mu**(r-c+1)*M**(h-r-1))
            if c==r+1:one/=comb(h,c)
            one/=r-c+2
            terms=[]
            for t in range(1 if r==c-1 else 2,min(r-c+2,h-c)+1):
                for a in range(1,c):
                    if t+a<c:continue
                    choices0=comb(h,c)*comb(h-c,t)*comb(c,a)*comb(h-c-t,r-c-t+2)
                    if c==r+1:choices0=1
                    charge=choices0*q**(c+t+a-4)*anchors[c,t,a]*mu**(r-c-t+2)*M**(h-r-2)/(r-c-t+3)
                    free_basis=r-c-t+2
                    theta_charge=(choices0*q**(c+t+a-4)*dd['theta_anchors'][c,t,a]
                                  *dd['gaussian_free'][c+t]**free_basis
                                  *dd['extended_dual_completions'][h,r,c+t]/(free_basis+1))
                    anisotropic_charge=(choices0*q**(c+t+a-4)*dd['theta_anchors'][c,t,a]
                                        *dd['optimized_gaussian_free']**free_basis
                                        *dd['anisotropic_dual_completions'][h,r,c+t]/(free_basis+1))
                    charge=min((charge,theta_charge,anisotropic_charge),key=lambda x:x.b)
                    if c==4 and t==2 and a==2:charge/=2
                    terms.append((charge.b,t,a,charge))
            two=sum((x[3] for x in terms),I(0))
            chosen=min((one,two),key=lambda x:x.b)
            target=l[res][h,r,c]
            assert chosen.a<=target.b and target.a<=chosen.b
            print(' REMAINDER_MIN','two' if two.b<one.b else 'one','one-log',iv.log10(factor*one),'two-log',iv.log10(factor*two))
            print(' TWO_COMPLETION_Q_EXP',(r-1)*(h-r-2),'LOG',iv.log10(I(q))*((r-1)*(h-r-2)))
            print(' FULL_ANCHOR_DUAL_CAP_LOG',iv.log10(dd['dual_completions'][h,r]))
            print(' TWO_COMPLETION_ACTUAL_LOG',iv.log10(M)*(h-r-2),'LOG_RATIO_TO_Q',iv.log10(M/I(q**(r-1)))*(h-r-2))
            for _,t,a,x in sorted(terms,reverse=True)[:3]:
                print(' TWO_TERM',t,a,'LOG',iv.log10(factor*x),'free_basis',r-c-t+2)


if __name__=='__main__':capture_checks();main()
