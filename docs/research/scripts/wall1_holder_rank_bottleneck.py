"""Diagnose the dominant rank-tail terms; no actual-history probability."""
from mpmath import iv
import wall1_anchored_dual_completion as a


def main():
    iv.dps=65;I=iv.mpf;q=3329;n=118;k=14
    R2=I('1.21')*iv.exp(2*(386*iv.log(q)-iv.log(iv.pi**253/iv.factorial(253)))/506)-2
    beta=I(4*518)/(12*R2);free=I(518)/(2*R2)
    s={'iv':iv,'q':q,'N':518,'radius':iv.sqrt(R2)}
    _,gs=a.completion_details(s,8,24,anchor_size=6,free_beta=free)
    Q=a.theta(iv.pi**2/(beta*q*q));rho=Q/(q*a.theta(iv.pi**2/beta))
    rf=a.theta(iv.pi**2/(free*q*q))/(q*a.theta(iv.pi**2/free))
    eta=min((I(1),Q**2*rho**3*rf**4,Q**2*rho**4*rf**3),key=lambda v:v.b)
    tails=a.rank_tails(q,n,k,gs)
    terms=[(t,(1-eta)*eta**t*tails[t]) for t in range(k)]
    print('chosen gamma',gs,'eta log10',iv.log10(eta))
    print('full rank log10',iv.log10(eta**k))
    for t,x in sorted(terms,key=lambda z:z[1].b,reverse=True)[:3]:
        print('rank tail',t,'log10',iv.log10(x))


if __name__=='__main__':main()
