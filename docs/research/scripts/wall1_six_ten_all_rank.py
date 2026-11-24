"""Complete D32 covers through rank21 using the safe new-coordinate height."""
from math import comb
from wall1_six_ten_rank_nine import COUNTS as TWO_COUNTS
from wall1_six_ten_rank_ten import THREE_COUNTS
from wall1_six_ten_higher_rank import HIGHER_COUNTS


def code_bound(s,t,height):
    I,iv,n,q,m,R=[s[k] for k in ('I','iv','N','q','m','radius')]
    assert 2<=t<=14
    H,rank,cutoff=10+t,7+t,24
    assert 32*cutoff**4<q*q and H*cutoff**2<q*q
    beta=I(rank*n)/(2*H*R**2);a=iv.pi**2/beta;alpha=a/q**2
    def theta(x):
        geo=lambda y:1+2*iv.exp(-y)/(1-iv.exp(-3*y))
        return geo(x) if x>iv.pi else iv.sqrt(iv.pi/x)*geo(iv.pi**2/x)
    short=theta(6*alpha)*theta(I(16)/3*alpha)*theta(height*alpha)
    tail=iv.exp(-I(cutoff**2)*alpha/2)*theta(alpha/2)**3
    delta=2*iv.exp(-a/4)/(1-iv.exp(-2*a))
    periodic=sum((comb(H,j)*delta**j for j in range(1,H+1)),I(0))
    kernel=(iv.pi/beta)**(I(H)/2)*((short+tail)/q**3+periodic)
    return iv.exp(H*beta*R**2)*kernel**n/q**(rank*m)


def envelopes(s,*,full_projection_bonus=False):
    I,q,mu=s['I'],s['q'],s['mu']
    from wall1_ball_slice_completion import completion_bound
    counts={2:TWO_COUNTS,3:THREE_COUNTS,**HIGHER_COUNTS}
    joints={}
    for t in range(2,15):
        C=sum(comb(8,a)*q**(t+a-2) for a in range(max(1,6-t),9))
        base=I(t)+I(3)/4 if t<=5 else I(t)
        generic=C*code_bound(s,t,base)
        if full_projection_bonus and t>=6:
            generic=min((generic,C*code_bound(s,t,I(t)+I(3)/4)),key=lambda v:v.b)
        if t<=5:
            rare=sum((count*code_bound(s,t,I(d)/32) for d,count in counts[t].items()),I(0))
            regular=C*code_bound(s,t,max(base,I(31)/6))
            generic=min((generic,rare+regular),key=lambda v:v.b)
        joints[t]=generic
    result={};terms={}
    for h in range(15,25):
        for r in range(9,h-2):
            assert r<=21
            M=completion_bound(s,r-1)
            common=comb(h,10)*163800*M**(h-r-3)
            for t in range(2,r-6):
                extra=r-7-t
                terms[h,r,t]=(common*comb(h-10,t)*comb(h-10-t,extra)
                               *mu**extra*joints[t])
            result[h,r]=sum((terms[h,r,t] for t in range(2,r-6)),I(0))
    return result,terms


def diagnostic():
    import contextlib,io
    from wall1_larger_triangular_components import actual_parameters
    from wall1_high_order_frontier import _capture_copy
    state={}
    wrapped=_capture_copy(actual_parameters,lambda value,locals_:state.update(locals_))
    with contextlib.redirect_stdout(io.StringIO()):wrapped()
    s=state['s'];I,iv=s['I'],s['iv']
    covers,terms=envelopes(s)
    actual=state['refined_strata'];residual=state['no_six_ten_thirty_two']
    d27=state['nine_twenty_seven'];new=dict(actual)
    changed=[]
    for (h,r),cover in covers.items():
        key=h,r,6
        candidate=residual[key]+d27[h,r]+cover
        selected=min((actual[key],candidate),key=lambda v:v.b)
        new[key]=selected
        if h in (19,24):
            print('h,r',h,r,'complete candidate/current log10',iv.log10(candidate/actual[key]),
                  'selected new/current',iv.log10(selected/actual[key]))
        if r>=13:changed.append((iv.log10(candidate/actual[key]).b,h,r))
    print('best higher-rank candidate/current log10:',min(changed))
    for h in (18,19,20,24):
        oldtotal=sum((v for (hh,r,c),v in actual.items() if hh==h),I(0))
        newtotal=sum((v for (hh,r,c),v in new.items() if hh==h),I(0))
        # Isolate added scope r>=13, independently of lower-rank integration timing.
        highertotal=sum((new[key] if key[1]>=13 else v for key,v in actual.items() if key[0]==h),I(0))
        print('size',h,'all-strata new/current log10',iv.log10(newtotal/oldtotal),
              'r>=13-only log10',iv.log10(highertotal/oldtotal))

if __name__=='__main__':diagnostic()
