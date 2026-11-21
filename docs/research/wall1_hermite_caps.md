# Finite-dimensional Hermite caps from spherical linear programming

The exact-twin lower radius reaches **34.3753482%** of $0.85G_{406}$ and **44.8425823%** of $0.85G_{506}$, rounding down. The improvement comes from both the spherical polynomial and a finite-dimensional integral check that enlarges the averaging ball. The integral check alone saves 0.478 nats in each target rank.

| Rank | Previous log cap | Certified log cap | Hermite upper bound | Lattice volume-density upper bound |
|---:|---:|---:|---:|---:|
| 406 | 776.598654340 | 775.869497700 | 45.696295350 | $7.017063\times10^{-67}$ |
| 506 | 1020.115234016 | 1019.379685531 | 56.214161971 | $2.850567\times10^{-84}$ |

| Rank | Exact twin radius | Gain as percentage points of $0.85G_b$ | Algorithm 1 radius at 1% slack | Algorithm 1 fraction of $0.85G_b$ |
|---:|---:|---:|---:|---:|
| 406 | 0.126914766 | 0.0939242 | 0.125656155 | 0.340344485 |
| 506 | 0.366057332 | 0.0666848 | 0.362426013 | 0.443977402 |

Selected neighboring upper caps on $(d/2)\log\gamma_d$ are given below. The verifier prints the corresponding rational witness and cap for every integer from 400 through 511.

| Rank | Log cap | Rank | Log cap |
|---:|---:|---:|---:|
|404|771.114716545|507|1021.867149497|
|405|773.491988598|508|1024.355604926|
|407|778.249240917|509|1026.845049936|
|408|780.630215328|510|1029.335482647|
|505|1016.893214922|511|1031.826901190|

## Scope of the finite bounds

Normalize the lattice minimum to one. Write $H_d=(d/2)\log\gamma_d$, $V_d=\pi^{d/2}/\Gamma(1+d/2)$, and $\Delta_d^{\rm lat}=2^{-d}V_d e^{H_d}$. Every reported cap bounds the supremum over all real Euclidean lattices of that rank. The certificate covers each integer rank from 400 through 511. Its polynomial and radius searches establish feasible bounds. Optimality over all LP witnesses or all lattice-specific methods remains open.

* The finite Kabatiansky–Levenshtein construction lifts to a spherical code in one extra dimension. Cohn–Zhao remove the extra dimension for angles at least 60 degrees and show that the Euclidean Cohn–Elkies LP dominates the resulting spherical LP. Levenshtein's direct Euclidean Bessel bound and the finite spherical polynomial bounds are distinct. Sardari–Zargar Table 1 compares them through dimension 120 and also implements an enlarged integration ball. Below we certify the sign on that ball directly in the requested dimensions. Zargar's later asymptotic multiplier $(1+o(1))/e$ supplies no numerical remainder here. [Cohn–Zhao](https://arxiv.org/abs/1212.5966) · [Sardari–Zargar, Table 1 and §3](https://arxiv.org/pdf/2001.00185) · [Zargar](https://arxiv.org/abs/2407.10697)
* The historical MIT table used in Part 82 includes ranks 56, 64 and 72. The November 18, 2026 table cites Kravatskiy [25]. The author identifies unrestricted upper bounds in ranks 4–7, 9–23 and 25–48, lattice-specific upper bounds in 14–23 and 25–48, and a rank-36 packing construction. The separate repository also gives higher-rank results, including unrestricted upper certificates in 57 and 58. Zubrilina gives earlier small-rank lattice upper bounds. The subset of lattice upper bounds and their Mordell propagation used by Part 88 is included in the comparison. No high-rank certificate from Kravatskiy was identified. [MIT density archive](https://dspace.mit.edu/entities/product/d8a88a76-3fa7-4b75-89ef-ea71a0e05b77) · [Kravatskiy’s density certificates](https://github.com/alexlegeartis/SpherePackings) · [Zubrilina](https://arxiv.org/abs/2610.35830) · [Part 82](wall1_small_d_caps.md)
* Poisson summation proves the ordinary Euclidean LP inequality for lattices, and the same auxiliary-function theorem extends to periodic packings. Merely restricting its application to lattices gives the same numerical cap. Modular-form bounds on the first coefficient of a theta series require hypotheses such as even unimodularity. Arbitrary real lattices of determinant one need not have integral squared norms. A modular-form *dual* LP certificate can also lower-bound the best attainable LP upper bound, which is the wrong direction for a Hermite cap. The high-dimensional spinless modular-bootstrap calculations provide numerical evidence for much stronger functions. Neither their numerical roots alone nor an asymptotic density exponent, including the 2026 sharp CE exponent, verifies a finite witness at these ranks. [Cohn–Elkies](https://arxiv.org/abs/math/0110009) · [Cohn–Triantafillou](https://doi.org/10.1090/MCOM/3662) · [Afkhami-Jeddi et al.](https://arxiv.org/abs/2006.02560) · [2026 asymptotic theorem](https://github.com/openai/ten-proofs/blob/main/ComparatorChallenges/A_SpherePacking.lean)

## Spherical polynomial and lattice counting proof

Write $P_j$ for the Gegenbauer basis normalized at one and $h_j$ for harmonic multiplicity in dimension $d$. For a rational threshold $t$ and parity $e\in\{0,1\}$ choose a polynomial $q$ of degree $m-1$. Let $v=(1+x)^e(x-t)q$ and $f=qv$. The code checks that every coefficient of $q$ and $v$ in the spherical basis is nonnegative, using the exact tridiagonal matrix for multiplication by $x$. The addition formula and the Schur product theorem give positive definiteness of $f$ and nonnegative Gegenbauer coefficients. Orthogonality gives $f_0=\sum_j q_jv_j/h_j>0$. Consequently any $N$ unit vectors have pair sum at least $f_0 N^2$, including their diagonal. The ratio $B=f(1)/f_0$ is computed exactly. The free coefficients in the search make the low-degree coefficients of $v$ proportional to $h_j$ and set the out-of-range coefficients of $q$ to zero. The proof uses only the resulting sign and norm checks.

Place a ball of radius $R$ about a uniform point of the lattice torus. For each of the $N$ lattice points in the ball take its direction from the center (defined almost everywhere). The mean of $N$ is $V_d R^d/\det L$. On integrating their pair sum, each diagonal term contributes $f(1)$ per point. For each nonzero displacement the off-diagonal contribution is the integral of $f$ of the angle cosine on the intersection of two radius-$R$ balls, divided by $\det L$, by unfolding. Only finitely many displacements occur. If all these integrals are nonpositive, Jensen's inequality gives $f_0(\mathbb E N)^2\le f(1)\mathbb E N$. Hence
$$H_d\le \log B-\log V_d-d\log R.$$
Set $S=1/[2(1-t)]$ and $R^2=U=S\exp(2g/d)$. At $g=0$ the pair sign holds pointwise. A certified enlargement subtracts exactly $g$ nats from the log cap. This is a finite-dimensional use of the averaging idea in Sardari–Zargar.

## Certificate for every displacement and axial slice

Scale the pair separation to one. Each ball now has radius $s\le\sqrt U<1$. In a slice transverse to the line of centers let $h\ge0$ be the absolute axial offset from the midpoint, $a=1/2+h$, $b'=1/2-h$, and $y$ the transverse radius. Nonempty slices have $b'>0$. With $r_1^2=y^2+a^2$ and $r_2^2=y^2+b'^2$, the angle cosine $x=(y^2-ab')/(r_1r_2)$ increases from $-1$. Equivalently $x=(r_1^2+r_2^2-1)/(2r_1r_2)$ increases in each distance while both are below one. Thus $x\le x_* = 1-1/(2U)$. If the slice reaches $x>t$, then $s^2>S$. Moreover $h<0.02$, since $r_1^2-r_2^2=2h$ and the script checks the cosine with squared distances $U,U-0.04$ is already below $t$.

Extend such a slice to the unique $y_*$ with $x(y_*)=x_*$. Every added integrand is nonnegative. Also $y_*^2\ge s^2-a^2>S-0.52^2$ since the original slice ends at $r_1=s$. Under $w=-(d-1)\log(y/y_*)$ the radial measure $y^{d-2}dy$ is a positive constant times $e^{-w}dw$ with reversed endpoints. Differentiation gives
$$\frac{dx}{d\log y}=(1-x^2)\frac{y^2+ab'}{r_1r_2},\qquad
(r_1r_2)^2=(y^2+ab')^2+y^2(a-b')^2.$$
The derivative lies between zero and one. For $0\le w\le5$, put $Y=(S-0.52^2)e^{-10/(d-1)}$ and $x_{\min}=x_*-5/(d-1)>0$. Then $y^2\ge Y$ and the derivative lies in
$$[L,D]=\left[\frac{1-x_*^2}{\sqrt{1+0.04^2/Y}},\ 1-x_{\min}^2\right].$$
For a bin $[l,r]$ this encloses $x-t$ in $[x_*-t-Dr/(d-1),x_*-t-Ll/(d-1)]$. For $w\ge5$ the cosine is below $t$ by the endpoint check and monotonicity. The remaining 160 bins use the exact exponential masses with outward rounding and Horner evaluation of the rational Taylor expansion $q(t+X)/q(t)$. A negative upper sum proves the required lens inequality uniformly in pair separation, including arbitrarily short slices. The binary search retains only verified positive enlargements.

## Terminal bound

With $n=1023$, $k=n-b$, the exact twin has $\log M_0=k(k+1)H_b/[b(b-1)]$ when using a cap $H_b$. The factor $k-1$ in $\log a$ cancels the denominator in the exponent of $a$. Counting primitive rank-$(k+1)$ extensions as in Part 88 yields
$$\log\rho=\frac{-\log 100-\log K_{k+1}}{n(k+1)}-\frac{k H_b}{b(b-1)}.$$
Each radius holds with Haar probability at least 0.99 per width, simultaneously over qualifying bases. For Algorithm 1 with an exact oracle and 1% slack multiply by $1.01^{-k/(k-1)}$. An implementation using a numerical twin threshold must enforce the stated factor. The comparison and its gain use the unrounded Part 63 definition of $G_b$. [Part 88](wall1_li_walter.md) · [Part 63](wall1_profile_rigidity.md)

## Reproducible certificate

Run the Python block from the repository root with NumPy and mpmath.

```python
from pathlib import Path
from fractions import Fraction as Q
from math import comb
import numpy as np
from mpmath import iv as I
I.dps = 45

def mult(d,j):
    return comb(d+j-1,j) - (comb(d+j-3,j-2) if j>=2 else 0)

def candidates(d,numer):
    # Discovery only. Retain the best plausible witness of each parity.
    t = numer / 10000000
    p = [np.ones_like(t),t]
    for j in range(1,61):
        p.append(((2*j+d-2)*t*p[-1]-j*p[-2])/(j+d-2))
    best = {}
    hsum = psum = altsum = 0
    smallest=[np.full_like(t,np.inf),np.full_like(t,np.inf)]
    for m in range(1,60):
        j = m-1
        smallest[j%2]=np.minimum(smallest[j%2],p[j])
        h = float(mult(d,j))
        hsum += h
        psum = psum + h*p[j]
        altsum += (-1)**j*h
        for e in (0,1):
            a = -1/p[m] if e==0 else -2/(p[m]+p[m+1])
            c = 0 if e==0 else (-1)**m*(-1-a*p[m])
            S = hsum+a*psum+c*altsum
            # With q scaled as below the LP ratio equals S.
            good = ((a>0) & (S>0) & (1+a*smallest[0]+c>=0)
                    & (1+a*smallest[1]-c>=0))
            if e:
                # Top two coefficients of (1+x)(x-t)q.
                qm=1+a*p[m-1]+c*(-1)**(m-1)
                prev=0 if m==1 else (m-1)/(2*(m-1)+d-2)*(1+a*p[m-2]+c*(-1)**(m-2))
                good &= (prev+(1-t)*qm>=0)
            cost = np.log(np.maximum(1,S)) + d/2*np.log(2*(1-t))
            for i in np.argsort(np.where(good,cost,np.inf))[:1]:
                if good[i]:
                    w = (cost[i],int(numer[i]),m,e)
                    if e not in best or w<best[e]: best[e]=w
    return best.values()

def times_x(d,q):
    out = [Q(0)]*(len(q)+1)
    for j,v in enumerate(q):
        out[j+1] += v*(j+d-2)/(2*j+d-2)
        if j: out[j-1] += v*j/(2*j+d-2)
    return out

def enlargement(d,t,q,e):
    # Taylor coefficients in X=x-t, formed exactly before interval evaluation.
    def iv(x): return I.mpf(x.numerator)/x.denominator
    def add(a,b):
        return [(a[j] if j<len(a) else 0)+(b[j] if j<len(b) else 0)
                for j in range(max(len(a),len(b)))]
    prev,cur=[Q(1)],[t,Q(1)]
    poly=[q[0]]
    for j in range(1,len(q)):
        poly=add(poly,[q[j]*z for z in cur])
        shifted=add([t*z for z in cur],[0]+cur)
        nxt=add([(2*j+d-2)*z/(j+d-2) for z in shifted],
                [-j*z/(j+d-2) for z in prev])
        prev,cur=cur,nxt
    assert poly[0]>0
    co=[iv(z/poly[0]) for z in poly]
    T=iv(t)
    S=1/(2*(1-T))
    def works(g):
        U=S*I.exp(2*g/d)
        if not (U<1 and (2*U-I.mpf('.04')-1)/(2*I.sqrt(U*(U-I.mpf('.04'))))<T):
            return False
        Y=(S-I.mpf('.52')**2)*I.exp(-I.mpf(10)/(d-1))
        xmax=1-1/(2*U)
        xmin=xmax-I.mpf(5)/(d-1)
        assert Y>0 and xmin>0
        low=(1-xmax**2)/I.sqrt(1+I.mpf('.04')**2/Y)
        high=1-xmin**2
        excess=xmax-T
        assert excess-low*5/(d-1)<0
        total=I.mpf(0)
        for j in range(160):
            l=I.mpf(5*j)/160
            r=I.mpf(5*(j+1))/160
            X=I.mpf([(excess-high*r/(d-1)).a,(excess-low*l/(d-1)).b])
            val=co[-1]
            for z in reversed(co[:-1]): val=z+X*val
            total+=(I.exp(-l)-I.exp(-r))*X*val**2*(1+T+X)**e
        return total.b<0
    # All gains in the bracket enter the result only after successful verification.
    lo,hi=0,1000
    while hi-lo>1:
        mid=(hi+lo)//2
        if works(I.mpf(mid)/1000): lo=mid
        else: hi=mid
    return lo

def certify(d,T,m,e):
    t=Q(T,10000000)
    assert 0<t<=Q(1,2)
    p=[Q(1),t]
    for j in range(1,m+1):
        p.append(((2*j+d-2)*t*p[-1]-j*p[-2])/(j+d-2))
    a=-1/p[m] if e==0 else -2/(p[m]+p[m+1])
    c=0 if e==0 else (-1)**m*(-1-a*p[m])
    q=[mult(d,j)*(1+a*p[j]+c*(-1)**j) for j in range(m)]
    v=times_x(d,q)
    for j,y in enumerate(q): v[j]-=t*y
    if e:
        w=times_x(d,v)
        for j,y in enumerate(v): w[j]+=y
        v=w
    if min(q)<0 or min(v)<0: return
    f0=sum(q[j]*v[j]/mult(d,j) for j in range(m))
    assert f0>0
    B=sum(q)*sum(v)/f0
    assert B==sum(q)
    def iv(x): return I.mpf(x.numerator)/x.denominator
    H=I.ln(iv(B))+d*I.ln(iv(2*(1-t))/I.pi)/2+I.loggamma(1+I.mpf(d)/2)
    gain=enlargement(d,t,q,e)
    return int((H*10**9).b)+1-gain*10**6,gain

root=Path('docs/research')
source=(root/'wall1_dual_pinning.md').read_text()
exec(source.split('\n```python\n')[1].split('def ceildiv')[0])
for b in range(400,512):
    caps=[(C[b],0,0,0,0)]
    coarse=list(candidates(b,np.arange(3350000,4700001,500)))
    grid=np.unique(np.concatenate([np.arange(T-550,T+551) for _,T,_,_ in coarse]))
    for _,T,m,e in candidates(b,grid):
        cap=certify(b,T,m,e)
        if cap is not None: caps.append((cap[0],T,m,e,cap[1]))
    cap,T,m,e,gain=min(caps)
    assert cap<C[b]
    print(b,cap,T,m,e,gain,flush=True)
    if b not in (406,506): continue
    assert (cap,T,m,e,gain)=={406:(775869497700,4075070,26,0,478),
                             506:(1019379685531,4125869,32,0,478)}[b]
    k=n-b
    H=I.mpf(cap)/M
    logK=A[n]-A[k+1]-A[b-1]-I.ln(2*n)
    G=I.exp((n-2*k-1)*(I.ln(b/(2*I.pi*I.exp(1)))+I.ln(I.pi*b)/b)/(2*(b-1)))
    rho=I.exp((-I.ln(100)-logK)/(n*(k+1))-k*H/(b*(b-1)))
    target=I.mpf('.85')*G
    old=rho*I.exp(k*(H-I.mpf(C[b])/M)/(b*(b-1)))
    for R in (rho,rho*I.exp(-I.ln(I.mpf('1.01'))*k/(k-1))):
        print('radius, fraction x 1e9',int((M*R).a),int((M*R/target).a))
    print('gain fraction x 1e9',int((M*(rho-old)/target).a))
    u=I.mpf(b)/2
    density=I.exp(H+u*I.ln(I.pi)-I.loggamma(1+u)-b*I.ln(2))
    assert density<I.mpf({406:'7.017063e-67',506:'2.850567e-84'}[b])
    print('gamma ceiling x 1e9',int((M*I.exp(2*H/b)).b)+1)
```

## Audit note (Nov 2026)

Independent audit (Codex): CORRECT WITH MINOR ISSUES.

* **Certificate.** The certificate passes at all 112 ranks from 400 through 511. Every winning witness was replayed in Sage
  220-bit interval arithmetic, with the same upward-rounded caps.
* **Proof steps.** These were verified: Gegenbauer nonnegativity in exact rationals, the Schur-product step, the density →
  Hermite conversion Δ = 2^{-d}V_dγ_d^{d/2}, whole-bin interval enclosure of the lens integral, and the monotone tail.
* **Comparison with Part 86.** Every new cap is strictly below its Part 86 C[b]. The smallest improvement is 0.727 nats, at
  rank 404.
* **Propagation into Part 88.** The radius propagation is correct. The 99% guarantee holds per width.
* **Literature.** The 2026 link points to a Comparator challenge statement whose theorem bodies contain `sorry`. The
  formalization to cite is the repository's top-level SpherePacking.lean. Reference [25] in the November 18 revision could
  not be independently confirmed. Neither point affects the finite certificate.
