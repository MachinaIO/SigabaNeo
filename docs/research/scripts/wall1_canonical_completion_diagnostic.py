"""Expose current canonical completion moment terms; not a probability estimate."""
import sys
from mpmath import iv
import wall1_anchored_dual_completion as a


def main():
    iv.dps=45;I=iv.mpf;q=3329
    R2=I('1.21')*iv.exp(2*(386*iv.log(q)-iv.log(iv.pi**253/iv.factorial(253)))/506)-2
    s={'iv':iv,'q':q,'N':518,'radius':iv.sqrt(R2)}
    captured=[]
    def capture(frame,event,arg):
        if event=='return' and frame.f_code is a.completion_details.__code__:
            state=frame.f_locals
            if 'holder_etas' in state and state['n']==518:captured.append(dict(state))
    for D in (12,16):
        for mode,beta in (('same',None),('free',I(518)/(2*R2))):
            sys.setprofile(capture)
            try:cap,gs=a.completion_details(s,11,24,anchor_size=6,
                free_beta=beta,coordinate_count=518,anchor_gram_det=D)
            finally:sys.setprofile(None)
            state=captured.pop();eta=state['eta'];k=state['k'];n=state['n']
            gamma=state['best'][1];tails=a.rank_tails(q,n,k,gamma)
            remainder=(1-eta)*sum((eta**t*tails[t] for t in range(k)),I(0))
            candidates=[]
            for L,etaL in state['holder_etas'].items():
                power=etaL**k;packing=eta**k*a.packing_tail(q,n,k,L,gamma)
                candidates.append((power+packing+remainder,L,power,packing))
            best=min(candidates,key=lambda x:x[0].b)
            print('D',D,'mode',mode,'cap log10',iv.log10(cap),'chosen gamma',gs,
                  'full gamma',gamma,'L',best[1])
            print('moment terms log10 power/packing/rank',
                  *(iv.log10(v) for v in (best[2],best[3],remainder)))
            print('hyperplane moment eta / etaL',iv.log10(eta),
                  iv.log10(state['holder_etas'][best[1]]))

if __name__=='__main__':main()
