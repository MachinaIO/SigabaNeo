"""Diagnose selected rank9 girth5 residual at component sizes17 and18."""
import contextlib,io,inspect,sys
from wall1_general_two_relations import draw14_bounds

def main():
    raw={}
    source,start=inspect.getsourcelines(draw14_bounds)
    line=start+next(i for i,l in enumerate(source) if 'charge = (choices*q**(c+t+a-4)' in l)
    def trace(frame,event,arg):
        if frame.f_code is not draw14_bounds.__code__:return None
        if event=='line' and frame.f_lineno==line+2:
            v=frame.f_locals
            if v['h'] in (17,18) and v['r']==9 and v['c']==5:
                raw[v['h'],v['t'],v['a']]=v['charge']
        return trace
    sys.settrace(trace)
    try:
        with contextlib.redirect_stdout(io.StringIO()):s,_,strata=draw14_bounds()
    finally:sys.settrace(None)
    iv=s['iv']
    for h in (17,18):
        candidate=strata[h,9,5]
        print('size',h,'selected stratum log10',iv.log10(candidate))
        terms=({k[2:]:v for k,v in s['size17_two_relation_terms'].items() if k[:2]==(9,5)} if h==17
               else {k[1:]:v for k,v in raw.items() if k[0]==h})
        for key,value in sorted(terms.items(),key=lambda kv:kv[1].b,reverse=True)[:6]:
            parts=s['five_circuit_anchor_parts'][key]
            print('term',key,'share log10',iv.log10(value/candidate))
            print('kernel',{k:str(iv.log10(v/parts['selected'])) for k,v in parts.items()})
    return s,raw

if __name__=='__main__':main()
