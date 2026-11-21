# A first moment for BKZ-completable prefixes

Use zero-based GS indices, Haar probability at ambient covolume one, exact primal BKZ including truncated end windows, width $b$, and $k=N-b$. Write $s=\det W$, $T=L/W$ for the orthogonal projection, $q=\lambda_1(T)$ and $R_T=h_b s^{-1/b}$ with $h_d=V_d^{-1/d}$ for unit-ball volume $V_d$. Let $B(c)$ count distinct completable $W$ with $q<cR_T$.

**Finite theorem.** At $N=1023$ the following unconditional first moments hold. All logarithms are natural. The last column counts distinct bad primitive sublattices with only the determinant cap $s\le e^{F}$, where $F=kb d_b$ is the Part 63 comparison scale. The same quotient-relative radius is used on both sides.

| $b$ | certified $c$ | upper bound on $\log\mathbb E B(c)$ | lower bound on log mean with determinant cap alone |
|---:|---:|---:|---:|
|406|0.003540|−773|469686|
|506|0.008497|−948|338925|
|647|0.014130|−864|179435|

Markov gives simultaneous coverage over bases within each width. Part 65 gives slightly larger radii at 99% coverage. Here the expected multiplicity itself is below $2^{-1023}$ per width. The comparison column concerns Haar input. Part 41 also considers a different, discrete planted ensemble. [Part 41](wall1_sublattice_union.md) · [Part 65](wall1_one_sided_terminal.md)

## Split measure and elimination of the lifts

The unoriented primitive incidence measure disintegrates as $NA(N,k)s^{N-1}ds$, times independent Haar probabilities for the unit-covolume shapes $H=s^{-1/k}W$ and $J=s^{1/b}T$, times uniform shear $u\in\mathrm{Hom}(T,W_{\mathbb R}/W)$, up to rotations. Indeed the parabolic stabilizer in adapted coordinates has two special linear diagonal blocks and an additive rectangular upper block. Its integer subgroup gives the two shape quotients and the shear torus. Invariance under translations forces uniform conditional shear. The primitive-sublattice mean fixes the radial normalization. Thus the exact integrand is the expectation over $H,J$ of the shortness indicator times the shear probability of admitting at least one completion. [Split law, Part 46](wall1_haar_prefix_law.md) · [Normalization, Part 5](wall1_sublattice.md) · [Kim's flag mean formula](https://arxiv.org/abs/2005.10874)

For example, $W$ must admit an internally reduced basis, since every truncation of a shortest-head window retains its head. Its last GS length $g_{k-1}$ must satisfy $q\ge\sqrt3 g_{k-1}/2$ by reducing the lift of a shortest quotient generator in the last projected prefix line. Even in rank two the shear matters. With $g_0=1$, $q=0.9$, shear zero gives a shorter lift, while shear $1/2$ passes the test (multiples with coefficient at least two have height at least $1.8$). Uniform rescaling gives covolume one. A universal upper bound can discard lifts by retaining the following coupled shape test.

Put $S_i=\log\det W_i$, $S_0=S_N=0$. If $H_d$ bounds $\log(\lambda_1^d/\det)$ in rank $d$, every window truncation gives
$$
d S_{i+1}\le(d-1)S_i+S_{i+d}+H_d,\qquad 2\le d\le\min(b,N-i).
$$
In particular for $i=k-j$, $1\le j\le\min(k,b-1)$, take $d=j+1$ and substitute $S_{k+1}=\log(sq)$. These inequalities test the last prefix lengths jointly against $q$ for a single ordering of $W$. The projected quotient must admit an HKZ basis beginning with this shortest generator. Using all truncations strengthens the necessary test by eliminating even the unobserved GS lengths, as follows. [Profile-only completion and its limitations, Part 42](wall1_profile_union.md)

Use the envelope $U$ constructed in the script. Its endpoints vanish, and for every $i\ne k$ with an interior successor, the minimizing $d$ satisfies $dU_{i+1}\ge(d-1)U_i+U_{i+d}+H_d$ by upward rounding. At $k$ the script verifies $\log(c h_b)<U_{k+1}-(1-1/b)U_k$. Thus $S\le U$ coordinatewise for a bad completion. Indeed a positive maximum of $S-U$ cannot occur at $k+1$ by shortness. At every other interior maximum the displayed convex average forces the same maximum at the preceding index, contradicting the endpoints.

Choose cuts strictly inside $W$ as listed in the script. Given $s$, the pair test now requires an internal primitive flag in $s^{1/k}H$ satisfying the caps at these cuts, $\log s\le U_k$, and a primitive line in $s^{-1/b}J$ of length at most $e^{U_{k+1}}/s$ and less than $cR_T$. These are checkable by bounded-covolume enumeration. The two existence probabilities factor at fixed $s$. Bound each by its flag or line mean and discard the last relative-length inequality after using it to prove the caps. Each counted $W$ contributes at least one chain, since $k$ itself is retained. Omitting this cut would only certify existence probability.

Explicitly, let $0=e_0<\cdots<e_m=N$ include all internal cuts and both $k,k+1$, with gaps $d_i=e_i-e_{i-1}$. Iterated unfolding gives the resulting integrated upper bound
$$
\frac{2^{1-m}\exp[A_N-\sum_i A_{d_i}+\sum_i d_i(U_{e_{i-1}}+U_{e_i})]}
{\prod_{0<j<m}(e_{j+1}-e_{j-1})}.
$$
Here $A_1=0$, $A_d-A_{d-1}=\log(dV_d/\zeta(d))$. Each denominator integrates one log determinant from minus infinity to its cap. This is the Part 65 flag integral with the distinguished prefix retained. For the opposite comparison the exact mean is $A(N,k)e^{NF}\Pr_J(\lambda_1(J)<c h_b)$, with $A(N,k)=\exp(A_N-A_k-A_b)/(2N)$. Part 46's second moment gives a probability at least $m_0/(1+m_0)$ for $m_0=c^b/(2\zeta(b))$, hence at least $c^b/8$ here. The use of the GSA scale in this comparison is purely a choice of cutoff.

## Proportional width

For $b/N\to a\in(0,1)$ there exists $K_a$ such that
$$
\mathbb E B\big(\exp[-\tfrac14\log^2 N-K_a\log N]\big)\le 2^{-N}
$$
for sufficiently large $N$. To see this, the deterministic chunk argument of Part 66 gives $\log(s)/k\le\log q+D$, $D=\tfrac14\log^2 N+O_a(\log N)$. In detail, the last chunk ending at $k$ has mean at most $\log q+D$ by the harmonic sum there. Deleting its final entry increases that bound by at most $D/(\min(k+1,\lfloor b/2\rfloor)-1)$. Each preceding chunk has all entries bounded by the original last mean plus $O_a(\log N)$ by the successive two-chunk inequality. Averaging proves the claim. Thus badness forces $s\le X=(c h_b e^D)^{kb/N}$. Unfolding gives $\mathbb E B(c)\le A(N,k)X^N c^b/(2\zeta(b))$. The ball-volume formula and Stirling give $|\log A(N,k)|=O(N^2\log N)$ (sum at most $N$ terms of size $O(N\log N)$). Since $kb=\Theta_a(N^2)$, choosing $K_a$ sufficiently large proves the bound. This strengthens the quantifier of the Part 66 squared-log estimate to an unconditional count. [Part 66](wall1_terminal_constant.md)

**Gap.** A fixed positive radius at the three listed dimensions does not establish a dimension-independent radius along any width sequence. The asymptotic cap still pays the endpoint harmonic sum. A polynomial or constant radius would need a stronger estimate, for example an integrable bound on the joint shear acceptance over the surviving internal flags. Multiplying acceptance probabilities for overlapping windows would reuse the same shear coordinates. The argument supplies no such independence or asymptotic radius. [Wall 1 frontier](../PROOF_GAP.md)

## Interval certificate

The packing constants and integer envelope below use the proved Part 65 bounds. The cuts, dents and comparisons certify the two distinct-prefix means above. Run with Python 3 and mpmath.

```python


from math import comb
from fractions import Fraction
from mpmath import iv as I

I.dps = 45
n, M = 1023, 10**9
small = [0, 0, Fraction(4,3), 2, 4, 8, Fraction(64,3), 64, 256]
C, A = [0,0], [0,0]
for d in range(2,n+1):
    u = I.mpf(d)/2
    if d < len(small):
        z = Fraction(small[d])
        H = I.ln(I.mpf(z.numerator)/z.denominator)/2
    else:
        H = u*I.ln(2/I.pi)+I.loggamma(2+u)
    D = d+1
    s = 4/(5*I.sqrt(D))
    a = 1/(D*s)
    c = (2*a-s)/D-s*a*a
    assert c > 0 and 2*a-s > 0 and a*a-2*a*s+I.mpf(3)/(D+2)>0
    P = I.ln((1-s)*(1+a)**2/c)+u*I.ln(2*(1-s)/I.pi)+I.loggamma(1+u)
    bound = P if P < H else H
    for v in (1,2,3,4,5,6):
        # Scaled Gegenbauer recurrence for signs.
        prev, cur = 1,v*(D-2)
        j=1
        while cur>0 and j<150:
            prev,cur=cur,(2*j+D-2)*v*cur-100*j*(D+j-3)*prev
            j+=1
        if cur>0: continue
        deg=j-1
        dim=comb(D+deg-1,deg)+comb(D+deg-2,deg-1)
        t=I.mpf(v)/10
        s=t-2*(1-t)/d
        cand=I.ln((1-s)*dim/(t-s))+u*I.ln(2*(1-s)/I.pi)+I.loggamma(1+u)
        if cand<bound: bound=cand
    C.append(int((M*bound).b)+1)
    assert C[d] > M*bound
    if d<=32:
        partial = sum(I.mpf(j)**(-d) for j in range(1,65))
        lo = partial+I.mpf(65)**(1-d)/(d-1)
        hi = partial+I.mpf(64)**(1-d)/(d-1)
        lz = I.mpf([I.ln(lo).a,I.ln(hi).b])
    else:
        lz = I.mpf([0,(3*I.mpf(2)**(-d)).b])
    A.append(A[-1]+I.ln(2)+u*I.ln(I.pi)-I.loggamma(u)-lz)

def recurrence(b,dent):
    T = [0]*(n+1)
    for i in reversed(range(n-1)):
        ds = range(2,min(b,n-i)+1)
        v = min((C[d]+d-2+T[i+1]-T[i+d])//(d-1) for d in ds)
        T[i] = T[i+1]+v-(dent if i==n-b else 0)
    return T

def envelope(b,dent):
    T = recurrence(b,dent)
    return [I.mpf((n-j)*T[0]-n*T[j])/(n*M) for j in range(n+1)]


for b,dent,inner,r,upper,lower in [
    (406,5987000000,list(range(13,170,13))+[183,197,212],'.003540',-773,469686),
    (506,5100000000,[12],'.008497',-948,338925),
    (647,4582000000,[],'.014130',-864,179435),
]:
    k=n-b
    U=envelope(b,dent)
    ends=[0]+inner+[k,k+1,n]
    L=A[n]-(len(ends)-2)*I.ln(2)
    for p,q in zip(ends,ends[1:]):
        L+=(q-p)*(U[p]+U[q])-A[q-p]
    L-=sum(I.ln(z-x) for x,z in zip(ends,ends[2:]))
    h=I.exp(I.loggamma(1+I.mpf(b)/2)/b)/I.sqrt(I.pi)
    F=k*b*(I.ln(b/(2*I.pi*I.exp(1)))+I.ln(I.pi*b)/b)/(2*(b-1))
    assert I.exp(U[k+1]-(1-I.mpf(1)/b)*U[k])/h>I.mpf(r)
    assert L<upper<-n*I.ln(2)
    assert A[n]-A[k]-A[b]-I.ln(2*n)+n*F+b*I.ln(I.mpf(r))-I.ln(8)>lower
```

## Audit note (independent audit, Nov 2026)

All conditions used are genuinely implied by exact BKZ completability, and the certificate passes (the envelope inequality at
every row i ≠ k was additionally confirmed in exact rationals, minimum margin 0). However the large negative log means are
**not slack**: E B scales like c^{kb} (measured slope d log E B / d log c ≈ 2.5·10⁵ ≈ kb), so the certified radii sit just below a
very steep break-even c* (0.003551 / 0.008528 / 0.014181 at log E B = 0). The result is essentially Part 65's relative bound
recast as a count of distinct completable prefixes. The 'all primitive prefixes' column uses a different determinant cap and is
illustrative only.
