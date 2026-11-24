"""Anchored rank-pivot numeric upper bounds, with two uniform eta certificates."""
from mpmath import iv
from wall1_dual_rank_pivot_numeric import theta
from wall1_dual_frequency_rank import gauss_binomial

def main():
    iv.dps=75;I=iv.mpf;q=3329;r=11;d=10;n=118;k=6
    R2=I('1.21')*iv.exp(2*(386*iv.log(q)-iv.log(iv.pi**253/iv.factorial(253)))/506)-2
    alpha=I(11*518)/(26*R2);h=theta(iv.pi**2/alpha);Q=theta(iv.pi**2/(alpha*q*q))
    Dcap=1+r*((q-1)//2)**2
    etas={'determinant':I(Dcap)*theta(alpha*q*q)**2*h*(Q/q)**d,
          'anchor-dual-zero':Q**2*(Q/(q*h))**d}
    caplog=k*iv.log10(min(I(q**d),(iv.pi**5/iv.factorial(5))*(iv.sqrt(R2)+iv.sqrt(d)/2)**d,key=lambda x:x.b))
    for name,eta in etas.items():
        assert 0<eta<1
        print('eta certificate',name,'Dcap',Dcap,'log10 eta upper',iv.log10(eta),flush=True)
        best=None
        for gs in ('1e-6','1.25e-6','1.5e-6','1.75e-6','2e-6','2.25e-6','2.5e-6','3e-6','4e-6','5e-6','6.85e-6'):
            gamma=I(gs);tau=iv.pi**2/(q*q*gamma);atom=theta(tau*q*q)/theta(tau)
            tails=[min(I(1),I(gauss_binomial(k,t,q))*atom**(n*(k-t)),key=lambda x:x.b) for t in range(k)]
            ez=eta**k+(1-eta)*sum((eta**t*tails[t] for t in range(k)),I(0))
            result=(d*k*iv.log(q)+k*gamma*R2+k*n*iv.log(theta(q*q*gamma))+iv.log(ez))/iv.log(10)
            if best is None or result.b<best[1].b:best=(gs,result)
            print('gamma',gs,'log10 multiplier upper',result,flush=True)
        print('BEST',name,best,'gain versus M10^6',caplog-best[1],flush=True)
        print('conditional target relaxed-anchor/reference budget',caplog-best[1]-I('51.9478'),flush=True)
if __name__=='__main__':main()
