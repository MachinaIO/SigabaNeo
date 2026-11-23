"""Read-only capture of actual high-order production strata and selected covers."""
import contextlib
import io
import sys
from math import comb
from wall1_larger_triangular_components import actual_parameters


def main():
    captured={};draws={}
    def local_trace(frame,event,arg):
        if event=='return':
            if frame.f_code.co_name=='actual_parameters':captured.update(frame.f_locals)
            else:
                l=frame.f_locals
                if isinstance(arg,tuple) and len(arg)==3:draws[id(arg[2])]={'anchors':l['anchors'],'s':l['s'],'completions':l.get('completions')}
        return local_trace
    def global_trace(frame,event,arg):
        if event=='call' and ((frame.f_code.co_name=='actual_parameters' and frame.f_code.co_filename.endswith('wall1_larger_triangular_components.py')) or (frame.f_code.co_name=='draw14_bounds' and frame.f_code.co_filename.endswith('wall1_general_two_relations.py'))):
            frame.f_trace_lines=False
            return local_trace
        return None
    sys.settrace(global_trace)
    try:
        with contextlib.redirect_stdout(io.StringIO()):actual_parameters()
    finally:sys.settrace(None)
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
            if r in (8,9):
                added['D32-ten']=l['six_ten_thirty_two' if r==8 else 'six_ten_rank_nine'][h]
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
                    if c==4 and t==2 and a==2:charge/=2
                    terms.append((charge.b,t,a,charge))
            two=sum((x[3] for x in terms),I(0))
            chosen=min((one,two),key=lambda x:x.b)
            target=l[res][h,r,c]
            assert chosen.a<=target.b and target.a<=chosen.b
            print(' REMAINDER_MIN','two' if two.b<one.b else 'one','one-log',iv.log10(factor*one),'two-log',iv.log10(factor*two))
            print(' TWO_COMPLETION_Q_EXP',(r-1)*(h-r-2),'LOG',iv.log10(I(q))*((r-1)*(h-r-2)))
            print(' TWO_COMPLETION_ACTUAL_LOG',iv.log10(M)*(h-r-2),'LOG_RATIO_TO_Q',iv.log10(M/I(q**(r-1)))*(h-r-2))
            for _,t,a,x in sorted(terms,reverse=True)[:3]:
                print(' TWO_TERM',t,a,'LOG',iv.log10(factor*x),'free_basis',r-c-t+2)


if __name__=='__main__':main()
