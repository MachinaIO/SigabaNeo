"""Cached anchored Gaussian dual completion caps, including independent extensions.

The extended anchor has r+2 points; extra basis points use the original anchor weight.
The caller must establish the common relaxed-anchor theta reference.
"""
from mpmath import iv
from math import comb
from wall1_dual_frequency_rank import gauss_binomial

GAMMA_GRID=('.5e-6','.75e-6','1e-6','1.25e-6','1.5e-6','1.75e-6',
            '2e-6','2.25e-6','2.5e-6','3e-6','4e-6','5e-6','6.85e-6')
_theta_cache={};_tail_cache={};_cap_cache={}
_packing_cache={};_free_moment_cache={}
HOLDER_ORDERS=(2,3,4,5,6,8)


def theta(t):
    t=iv.mpf(t);key=(iv.dps,t._mpi_)
    if key in _theta_cache:return _theta_cache[key]
    assert t>0
    if t<iv.pi:answer=iv.sqrt(iv.pi/t)*theta(iv.pi**2/t)
    else:
        low=1+2*sum((iv.exp(-t*j*j) for j in range(1,21)),iv.mpf(0))
        tail=2*iv.exp(-441*t)/(1-iv.exp(-43*t))
        answer=iv.mpf([low.a,(low+tail).b])
    _theta_cache[key]=answer
    return answer


def rank_tails(q,n,k,gamma_text):
    key=(iv.dps,q,n,k,gamma_text)
    if key not in _tail_cache:
        I=iv.mpf;gamma=I(gamma_text);tau=iv.pi**2/(q*q*gamma)
        atom=theta(tau*q*q)/theta(tau)
        # Select actual generating rows instead of unioning all ambient
        # subspaces. Fixed selected rows leave independent fresh rows.
        _tail_cache[key]=tuple(min((I(1),
            I(gauss_binomial(k,t,q))*atom**(n*(k-t)),
            I(comb(k,t))*atom**((n-t)*(k-t))),key=lambda x:x.b)
            for t in range(k))
    return _tail_cache[key]


def free_moment(q,beta,L):
    """Upper bound on the normalized one-coordinate periodized L-moment."""
    key=(iv.dps,q,beta._mpi_,L)
    if key not in _free_moment_cache:
        a=iv.pi**2/beta
        delta=2*iv.exp(-a/4)/(1-iv.exp(-2*a))
        value=delta**L+sum((comb(L,j)*delta**(L-j)
              *theta(j*a/(q*q))/q for j in range(1,L+1)),iv.mpf(0))
        _free_moment_cache[key]=min((iv.mpf(1),value),key=lambda x:x.b)
    return _free_moment_cache[key]


def packing_tail(q,n,k,L,gs):
    key=(iv.dps,q,n,k,L,gs)
    if key not in _packing_cache:
        assert n>=L*k
        tau=iv.pi**2/(q*q*iv.mpf(gs))
        M=theta(q*q*tau)/theta(tau)
        candidates=[iv.mpf(1),sum((comb(n,j)*(1-M)**j*M**(n-j)
                    for j in range(L*k)),iv.mpf(0))]
        for numerator in (1,2,3,4,5,6,7,8,9):
            z=1+(1/M-1)*iv.mpf(numerator)/10
            if not (z.a>1 and (z*M).b<1):continue
            value=z**(-(n-L*k+1))
            for c in range(1,k+1):
                value*=((1-M**c)/(1-z*M**c))**L
            candidates.append(value)
        _packing_cache[key]=min(candidates,key=lambda x:x.b)
    return _packing_cache[key]


def completion_details(s,r,h,*,anchor_size=None,free_beta=None):
    """Return (cap, chosen_gamma_text) for k=h-r-2 dependent positions.

    q=3329 and N=518 are the audited parameter domain. s['radius'] is the
    existing interval radius; the caller's iv precision is not changed.
    anchor_size selects the original common Gaussian weight. Additional
    free_beta optionally changes only the independent extension weights.
    Free-point Gaussian costs are NOT included in this completion cap.
    No anchor Chernoff prefactor or output normalization is included.
    """
    assert s['iv'] is iv
    q=s['q'];N=s['N'];n=118;k=h-r-2;I=iv.mpf
    assert q==3329 and N==518 and 2<=r and 0<=k<=n
    H0=r+2 if anchor_size is None else anchor_size
    assert 4<=H0<=r+2
    if k==0:return I(1),'none'
    R2=s['radius']**2
    alpha=I((H0-2)*N)/(2*H0*R2)
    r0=H0-2;f=r-r0
    beta_free=alpha if free_beta is None or f==0 else I(free_beta)
    assert beta_free>0
    key=(iv.dps,q,N,n,r,k,H0,R2._mpi_,alpha._mpi_,beta_free._mpi_,GAMMA_GRID,HOLDER_ORDERS)
    if key in _cap_cache:return _cap_cache[key]
    base_h=theta(iv.pi**2/alpha);Q=theta(iv.pi**2/(alpha*q*q));d=r-1
    rho_old=Q/(q*base_h)
    if f:
        free_h=theta(iv.pi**2/beta_free)
        rho_free=theta(iv.pi**2/(beta_free*q*q))/(q*free_h)
    else:rho_free=I(1)
    eta_candidates=[I(1),Q**2*rho_old**(r0-1)*rho_free**f]
    if f:eta_candidates.append(Q**2*rho_old**r0*rho_free**(f-1))
    eta=min(eta_candidates,key=lambda x:x.b)
    assert 0<eta<=1
    holder_etas={}
    if f:
        old_eta=min((I(1),Q**2*rho_old**(r0-1)),key=lambda x:x.b)
        for L in HOLDER_ORDERS:
            if L*k<=n:
                holder_etas[L]=min((eta,old_eta*free_moment(q,beta_free,L)**f),key=lambda x:x.b)
    best=None
    for gs in GAMMA_GRID:
        gamma=I(gs);tails=rank_tails(q,n,k,gs)
        # Upper bound in rank's exact tail identity; never assume full rank.
        rank_remainder=(1-eta)*sum((eta**t*tails[t] for t in range(k)),I(0))
        moment=eta**k+rank_remainder
        for L,etaL in holder_etas.items():
            candidate=etaL**k+eta**k*packing_tail(q,n,k,L,gs)+rank_remainder
            moment=min((moment,candidate),key=lambda x:x.b)
        logcap=d*k*iv.log(q)+k*gamma*R2+k*n*iv.log(theta(q*q*gamma))+iv.log(moment)
        if best is None or logcap.b<best[0].b:best=(logcap,gs)
    answer=(iv.exp(best[0]),best[1]);_cap_cache[key]=answer
    return answer


def completion_bound(s,r,h,*,anchor_size=None,free_beta=None):
    return completion_details(s,r,h,anchor_size=anchor_size,free_beta=free_beta)[0]


def main():
    iv.dps=75;I=iv.mpf;q=3329
    R2=I('1.21')*iv.exp(2*(386*iv.log(q)-iv.log(iv.pi**253/iv.factorial(253)))/506)-2
    s={'iv':iv,'q':q,'N':518,'radius':iv.sqrt(R2)}
    tested=0
    for h in range(15,25):
        for r in range(3,min(21,h-2)+1):
            cap,gs=completion_details(s,r,h)
            assert cap>0
            if h==r+2:assert cap==I(1)
            else:assert completion_bound(s,r,h) is cap
            if h==24 or (r,h)==(11,19):print('rank,size,k,gamma,logcap',r,h,h-r-2,gs,iv.log10(cap),flush=True)
            tested+=1
    reference=completion_bound(s,11,19)
    assert 0<reference and iv.log10(reference)<I('101.44950507205331')
    print('Passed cached full-anchor cap cases:',tested,'theta cache:',len(_theta_cache),'rank-tail cache:',len(_tail_cache))

if __name__=='__main__':main()
