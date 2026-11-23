"""Inspect the selected D28-ten residual without modifying production code."""
import contextlib,inspect,io,sys
from wall1_general_two_relations import draw14_bounds

def main():
    source,start=inspect.getsourcelines(draw14_bounds)
    target=start+next(i for i,line in enumerate(source) if 'anchors[c, t, overlap] =' in line)
    captured={}
    def trace(frame,event,arg):
        if frame.f_code is not draw14_bounds.__code__:return None
        if event=='line' and frame.f_lineno==target:
            v=frame.f_locals
            if v['c']==4 and v['t'] in (2,3):
                captured[v['t'],v['overlap']]={k:v[k] for k in ('one_power','none_power','power_bound','split','one_six_term','two_six_term','no_six_power','coefficient_count','one_count','fixed_four_plane','no_four_plane','six_tail','no_tail','alpha','a','beta')}
        return trace
    sys.settrace(trace)
    try:
        with contextlib.redirect_stdout(io.StringIO()):
            s,_,_=draw14_bounds(exclude_double_short_anchors=True,exclude_four_six_twenty=True,
                exclude_four_six_twenty_three=True,exclude_four_six_twenty_four=True,
                exclude_seven_four_six=True,exclude_ten_twenty_eight=True)
    finally:sys.settrace(None)
    iv=s['iv']
    candidate=s['size17_stratum_candidates'][8,4]['selected']
    terms={k:v for k,v in s['size17_two_relation_terms'].items() if k[:2]==(8,4)}
    for key,value in sorted(terms.items(),key=lambda kv:kv[1].b,reverse=True)[:6]:
        print('term',key,'selected residual share log10',iv.log10(value/candidate))
    for key,v in captured.items():
        print('kernel',key,{k:str(iv.log10(v[k]/v['power_bound'])) for k in ('one_power','none_power','split','one_six_term','two_six_term','no_six_power')})
    return s,captured

if __name__=='__main__':main()
