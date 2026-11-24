"""Cached anchored Gaussian dual completion caps, including independent extensions.

The extended anchor has r+2 points; extra basis points use the original anchor weight.
The caller must establish the common relaxed-anchor theta reference.
"""
from mpmath import iv
from math import comb
from functools import lru_cache
from fractions import Fraction
from wall1_correlated_anchor_moments import moment_profiles
from wall1_dual_frequency_rank import gauss_binomial

GAMMA_GRID=('.5e-6','.75e-6','1e-6','1.25e-6','1.5e-6','1.75e-6',
            '2e-6','2.25e-6','2.5e-6','3e-6','4e-6','5e-6','6.85e-6')
_theta_cache={};_tail_cache={};_cap_cache={}
_correlated_cache={};
_packing_cache={};_raw_moment_cache={};_hyperplane_cache={}
HOLDER_ORDERS=(2,3,4,5,6,8)
FULL_HOLDER_ORDERS=HOLDER_ORDERS+(10,12,14,16,20,24,32)


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


def raw_moment(q,beta,L):
    """Upper bound on the unnormalized wrapped Gaussian L-moment."""
    key=(iv.dps,q,beta._mpi_,L)
    if key not in _raw_moment_cache:
        a=iv.pi**2/beta
        delta=2*iv.exp(-a/4)/(1-iv.exp(-2*a))
        value=delta**L+sum((comb(L,j)*delta**(L-j)
              *theta(j*a/(q*q))/q for j in range(1,L+1)),iv.mpf(0))
        _raw_moment_cache[key]=value
    return _raw_moment_cache[key]


def free_moment(q,beta,L):
    """Normalized moment: its normalizer is at least one and its maximum is one."""
    return min((iv.mpf(1),raw_moment(q,beta,L)),key=lambda x:x.b)


@lru_cache(maxsize=3)
def canonical_moment_profiles(anchor_size):
    if anchor_size==5:
        # All six H5 exceptional charts have this exact pair of profiles.
        F=Fraction
        return {15:(((F(1,3),F(3,5),F(1,3)),(F(14,15),F(5,14))),)}
    return moment_profiles()


def correlated_moments(q,alpha,L,determinant,anchor_size=None):
    """Uniform (hyperplane, full) raw moment bounds over every certified chart."""
    H0=(7 if determinant==15 else 6) if anchor_size is None else anchor_size
    assert (H0,determinant) in ((5,15),(6,12),(6,16),(7,15))
    key=(iv.dps,q,alpha._mpi_,L,H0,determinant)
    if key not in _correlated_cache:
        I=iv.mpf;r0=H0-2
        lam={12:6,16:4,15:5}[determinant]
        tau=iv.pi**2/(q*q*alpha)
        alias=theta(iv.pi**2/(alpha*L*lam))**(r0*(L-1))
        fulls=[];hypers=[]
        for full,root in canonical_moment_profiles(H0)[determinant]:
            values=[]
            for pivots in (full,root):
                value=I(1)
                for p in pivots:value*=theta(L*tau*I(p.numerator)/p.denominator)
                values.append(value)
            fulls.append(alias*values[0]/q**r0)
            hypers.append(alias*values[1]*theta(L*iv.pi**2/(alpha*H0))/q**(r0-1))
        # Maximize over charts before minimizing against other valid bounds.
        _correlated_cache[key]=(max(hypers,key=lambda x:x.b),max(fulls,key=lambda x:x.b))
    return _correlated_cache[key]


def diagonal_spectral_profiles(determinant,anchor_size=None):
    """Certified diagonal majorizers, invariant up to coordinate permutation.

    Positive weights are one on shared support and t on the remaining rows.
    D-G is a sum of weighted squares. Scalar profiles retain Part 438.
    """
    I=iv.mpf
    if anchor_size==5:
        assert determinant==15
        return [(I(5),)*3]
    profiles=[tuple(I({12:6,16:4,15:5}[determinant])
                    for _ in range(5 if determinant==15 else 4))]
    for t in (I(1),I(3)/2,I(2),I(3)):
        if determinant==12:profiles.append((5+2*t,)*2+(2+2/t,)*2)
        if determinant==15:profiles.append((3+4*t,)+(3+1/t,)*4)
    return profiles


def hyperplane_sum_bound(q,alpha,beta_free,r0,f):
    """Unnormalized hyperplane sum via all r+2 affine Gaussian factors."""
    key=(iv.dps,q,alpha._mpi_,beta_free._mpi_,r0,f)
    if key not in _hyperplane_cache:
        m=r0+2;a=q*q*alpha;b=q*q*beta_free
        da=2*iv.exp(-a/4)/(1-iv.exp(-2*a))
        db=2*iv.exp(-b/4)/(1-iv.exp(-2*b))
        raw=iv.mpf(0)
        for j in range(m+1):
            for ell in range(f+1):
                term=comb(m,j)*comb(f,ell)*da**(m-j)*db**(f-ell)
                if j or ell:term*=theta((j*a+ell*b)/(q*q))/q
                raw+=term
        scale=(q*iv.sqrt(alpha/iv.pi))**m*(q*iv.sqrt(beta_free/iv.pi))**f
        _hyperplane_cache[key]=scale*raw
    return _hyperplane_cache[key]


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


def completion_details(s,r,h,*,anchor_size=None,free_beta=None,coordinate_count=118,anchor_gram_det=None):
    """Return (cap, chosen_gamma_text) for k=h-r-2 dependent positions.

    q=3329 and N=518 are the audited parameter domain. s['radius'] is the
    existing interval radius; the caller's iv precision is not changed.
    anchor_size selects the original common Gaussian weight. Additional
    free_beta optionally changes only the independent extension weights.
    Free-point Gaussian costs are NOT included in this completion cap.
    No anchor Chernoff prefactor or output normalization is included.
    coordinate_count=518 requires a full joint-incidence target; it cannot
    bound the input-only mixed-fiber relaxation. The input candidate is retained.
    anchor_gram_det requires a certified canonical chart: H6 two-four with
    determinant12/16, H5 exceptional or H7 shared-four with determinant15.
    Anchor size distinguishes the two D15 families. Not a general family.
    """
    assert s['iv'] is iv
    q=s['q'];N=s['N'];n=coordinate_count;k=h-r-2;I=iv.mpf
    assert n in (118,518)
    assert q==3329 and N==518 and 2<=r and 0<=k<=118
    H0=r+2 if anchor_size is None else anchor_size
    assert 4<=H0<=r+2
    assert anchor_gram_det is None or (H0==6 and anchor_gram_det in (12,16)) or (H0 in (5,7) and anchor_gram_det==15)
    if k==0:return I(1),'none'
    R2=s['radius']**2
    alpha=I((H0-2)*N)/(2*H0*R2)
    r0=H0-2;f=r-r0
    beta_free=alpha if free_beta is None or f==0 else I(free_beta)
    assert beta_free>0
    gamma_grid=(('.2e-6','.25e-6','.3e-6','.35e-6','.4e-6',
                 '.55e-6','.6e-6','.65e-6','.7e-6','.8e-6','.9e-6')+GAMMA_GRID
                if n==518 else GAMMA_GRID)
    holder_orders=FULL_HOLDER_ORDERS if n==518 else HOLDER_ORDERS
    key=(iv.dps,q,N,n,r,k,H0,R2._mpi_,alpha._mpi_,beta_free._mpi_,gamma_grid,holder_orders,anchor_gram_det)
    if key in _cap_cache:return _cap_cache[key]
    base_h=theta(iv.pi**2/alpha);Q=theta(iv.pi**2/(alpha*q*q));d=r-1
    rho_old=Q/(q*base_h)
    boost=I(1)
    if anchor_gram_det is not None:
        # Caller certifies the canonical short-relation chart, not a general anchor.
        boost=max((I(1),q*q*alpha/(iv.pi*iv.sqrt(anchor_gram_det)*base_h**r0)),
                  key=lambda x:x.a)
    if f:
        free_h=theta(iv.pi**2/beta_free)
        rho_free=theta(iv.pi**2/(beta_free*q*q))/(q*free_h)
    else:rho_free=I(1);free_h=I(1)
    eta_candidates=[I(1),Q**2*rho_old**(r0-1)*rho_free**f/boost]
    if f:eta_candidates.append(Q**2*rho_old**r0*rho_free**(f-1)/boost)
    eta_candidates.append(hyperplane_sum_bound(q,alpha,beta_free,r0,f)
                          /(q**d*base_h**r0*free_h**f*boost))
    eta=min(eta_candidates,key=lambda x:x.b)
    assert 0<eta<=1
    holder_etas={}
    if f or anchor_gram_det is not None:
        old_eta=min((I(1),Q**2*rho_old**(r0-1)/boost,
            hyperplane_sum_bound(q,alpha,alpha,r0,0)/(q**(r0-1)*base_h**r0*boost)),key=lambda x:x.b)
        for L in holder_orders:
            if L*k>n:continue
            free_L=free_moment(q,beta_free,L) if f else I(1)
            candidates=[eta]
            if f:candidates.append(old_eta*free_L**f)
            if anchor_gram_det is not None:
                # Completion-square theta cancels against the exact normalizer.
                # These raw spectral moments must not be clipped or divided by boost.
                hyper_L,full_L=correlated_moments(q,alpha,L,anchor_gram_det,H0)
                candidates.append(hyper_L*free_L**f)
                if f:candidates.append(full_L*free_L**(f-1))
                for profile in diagonal_spectral_profiles(anchor_gram_det,H0):
                    raw=[raw_moment(q,scale*alpha,L) for scale in profile]
                    hs=[theta(iv.pi**2/(scale*alpha)) for scale in profile]
                    product=I(1)
                    for value in raw:product*=value
                    for i in range(r0):
                        candidates.append(hs[i]**L*(product/raw[i])*free_L**f)
                    if f:candidates.append(product*free_L**(f-1))
            holder_etas[L]=min(candidates,key=lambda x:x.b)
    best=None
    for gs in gamma_grid:
        gamma=I(gs);tails=rank_tails(q,n,k,gs)
        # Upper bound in rank's exact tail identity; never assume full rank.
        rank_remainder=(1-eta)*sum((eta**t*tails[t] for t in range(k)),I(0))
        moment=eta**k+rank_remainder
        for L,etaL in holder_etas.items():
            candidate=etaL**k+eta**k*packing_tail(q,n,k,L,gs)+rank_remainder
            moment=min((moment,candidate),key=lambda x:x.b)
        logcap=d*k*iv.log(q)+k*gamma*R2+k*n*iv.log(theta(q*q*gamma))+iv.log(moment)
        if best is None or logcap.b<best[0].b:best=(logcap,gs)
    answer=(iv.exp(best[0]),best[1])
    if n==518:
        # This branch is authorized only for full joint-incidence targets.
        old=completion_details(s,r,h,anchor_size=H0,free_beta=free_beta,
                               anchor_gram_det=anchor_gram_det)
        answer=min((answer,old),key=lambda x:x[0].b)
    _cap_cache[key]=answer
    return answer


def completion_bound(s,r,h,*,anchor_size=None,free_beta=None,coordinate_count=118,anchor_gram_det=None):
    return completion_details(s,r,h,anchor_size=anchor_size,free_beta=free_beta,
                              coordinate_count=coordinate_count,anchor_gram_det=anchor_gram_det)[0]


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
