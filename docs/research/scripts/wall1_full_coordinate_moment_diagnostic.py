"""Full-coordinate r10/H6 moment decomposition; diagnostic, not probability."""
from mpmath import iv
import wall1_anchored_dual_completion as a
iv.dps=55;I=iv.mpf;q=3329;n=518;r=10;k=12;H=6;f=6
R2=I('1.21')*iv.exp(2*(386*iv.log(q)-iv.log(iv.pi**253/iv.factorial(253)))/506)-2
alpha=I(4*518)/(12*R2);beta=I(518)/(2*R2)
Q=a.theta(iv.pi**2/(alpha*q*q));rho=Q/(q*a.theta(iv.pi**2/alpha));rf=a.theta(iv.pi**2/(beta*q*q))/(q*a.theta(iv.pi**2/beta))
eta=min((I(1),Q**2*rho**3*rf**6,Q**2*rho**4*rf**5),key=lambda x:x.b)
eta0=min((I(1),Q**2*rho**3),key=lambda x:x.b)
for gs in ('.25e-6','.3e-6','.35e-6','.4e-6','.5e-6','.75e-6','1e-6'):
 tails=a.rank_tails(q,n,k,gs);rest=(1-eta)*sum((eta**t*tails[t] for t in range(k)),I(0));best=(eta**k+rest,1,eta**k,I(0))
 for L in (2,3,4,5,6,8,10,12,16,24,32,40):
  if L*k>n:continue
  e=min((eta,eta0*a.free_moment(q,beta,L)**f),key=lambda x:x.b)
  p=eta**k*a.packing_tail(q,n,k,L,gs);v=e**k+p+rest
  if v.b<best[0].b:best=(v,L,e**k,p)
 pref=(r-1)*k*iv.log(q)+k*I(gs)*R2+k*n*iv.log(a.theta(q*q*I(gs)))
 print(gs,'L',best[1],'logcap',iv.log10(iv.exp(pref)*best[0]),'parts',*[iv.log10(v) for v in (best[2],best[3],rest)])
