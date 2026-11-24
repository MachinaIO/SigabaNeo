"""Eq3 rank-pivot upper bounds relative to the FREE BASIS input theta kernel."""
from mpmath import iv
from wall1_dual_frequency_rank import gauss_binomial

def theta(t):
    if t<iv.pi:return iv.sqrt(iv.pi/t)*theta(iv.pi**2/t)
    low=1+2*sum((iv.exp(-t*j*j) for j in range(1,21)),iv.mpf(0))
    tail=2*iv.exp(-t*21**2)/(1-iv.exp(-43*t))
    return iv.mpf([low.a,(low+tail).b])

def main():
    iv.dps=75;I=iv.mpf;q=3329;r=11;d=10;n=118;k=6;sA=2
    V506=iv.pi**253/iv.factorial(253)
    R2=I('1.21')*iv.exp(2*(386*iv.log(q)-iv.log(V506))/506)-2
    alpha=I(11*518)/(26*R2)
    h=theta(iv.pi**2/alpha);Q=theta(iv.pi**2/(alpha*q*q));zeta=(Q/(q*h))**d
    assert 0<zeta<1
    Mcomp=min(I(q**d),(iv.pi**5/iv.factorial(5))*(iv.sqrt(R2)+iv.sqrt(d)/2)**d,key=lambda x:x.b)
    caplog=k*iv.log10(Mcomp)
    print('R',iv.sqrt(R2),'alpha',alpha,'log10 zeta',iv.log10(zeta),flush=True)
    best=None
    for gs in ('.5e-6','.75e-6','1e-6','1.25e-6','1.5e-6','1.75e-6','2e-6','2.25e-6','2.5e-6','3e-6','4e-6','5e-6','6.85e-6'):
        gamma=I(gs);tau=iv.pi**2/(q*q*gamma)
        atom=theta(tau*q*q)/theta(tau)
        tails=[min(I(1),I(gauss_binomial(k,t,q))*atom**(n*(k-t)),key=lambda x:x.b) for t in range(k)]
        ez=zeta**k+(1-zeta)*sum((zeta**t*tails[t] for t in range(k)),I(0))
        # Exact Poisson simplification of C^n*h^(rn)/theta(alpha)^(rn).
        logfactor=I(d*k)*iv.log(q)+k*gamma*R2+sA*n*iv.log(theta(q*q*alpha))+k*n*iv.log(theta(q*q*gamma))+iv.log(ez)
        result=logfactor/iv.log(10)
        if best is None or result.b<best[1].b:best=(gs,result,ez,tails)
        print('gamma',gs,'log10 free-basis multiplier upper',result,'log10 rank moment upper',iv.log10(ez),flush=True)
    gs,result,ez,tails=best
    print('GRID BEST',gs,result,flush=True)
    for t in range(k):print('best weighted rank-tail term',t,iv.log10((1-zeta)*zeta**t*tails[t]),flush=True)
    print('best fullrank base term',iv.log10(zeta**k),flush=True)
    print('allowed log10 free-basis / actual-anchor-input penalty to beat cap',caplog-result,flush=True)
    print('conditional allowed penalty to move39.9478 to-12',caplog-result-I('51.9478'),flush=True)
    print('No global optimum or production gain asserted; anchor-input comparison remains required.')
if __name__=='__main__':main()
