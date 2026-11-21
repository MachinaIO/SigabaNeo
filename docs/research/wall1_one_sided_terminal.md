# One-sided bounds for all BKZ terminal quotients

Let the ambient lattice be Haar unimodular, let $b$ be the exact BKZ width, and index from zero. Put $k=N-b$, $W=\langle b_0,\ldots,b_{k-1}\rangle_\mathbb Z$, $T=\pi_{W^\perp}L$, and $h_b=V_b^{-1/b}$, where $V_b$ is unit ball volume. The quotient's Gaussian-heuristic radius is $h_b\det(T)^{1/b}$. Full BKZ includes all projected windows and truncated end windows, so $g_k=\lambda_1(T)$.

**Finite theorem.** At $N=1023$, for each width separately, with probability greater than 99%, every fully reduced basis satisfies **both** lower bounds in its row. The absolute radius is in ambient covolume-one units. The relative bound is on $g_k/(h_b\det(T)^{1/b})$.

| Width | Previous absolute radius | New absolute radius | New relative bound | Target $0.85G$, approximate | Upper bound on log failure probability |
|---:|---:|---:|---:|---:|---:|
|406|0.005933200|0.00609055|0.00356898|0.369|−5.163|
|506|0.015621412|0.01588487|0.00858457|0.816|−4.781|
|647|0.039603438|0.03996130|0.01424667|1.822|−5.116|
|800|0.140797866|0.14264140|0.03307094|3.413|−4.779|

The gain comes from strengthening the packing constraints before integrating over primitive flags. It does not establish the proposed constant-factor asymptotic. The absolute and relative targets require separate treatment because the determinant of the selected quotient varies. [Previous absolute certificates](wall1_poisson_exponent.md) · [GSA convention](wall1_profile_rigidity.md)

## Crossing conditions and the flag count

For $1\le j\le\min(k,b-1)$, the length-$b$ window at $i=k-j$ contains the projection of column $k$. In particular, in a size-reduced chart,
$$
 g_i^2\le g_k^2+\sum_{i\le l<k}\mu_{kl}^2g_l^2 .
$$
For $j=1$ the best lift has exactly the squared length on the right. At fixed diagonal the allowed fraction of the circle is $1-\min(1,2\sqrt{(1-(g_k/g_i)^2)_+})$. The same column enters the tests at larger $j$, so multiplying their marginal fractions is unjustified. A backward chain using just adjacent tests loses a factor $\sqrt3/2$ at each step. We use instead the determinant consequence of **every truncation** of each crossing window. With $S_i=\log\det W_i$ for the prefix of rank $i$, it is
$$
 d(S_{i+1}-S_i)\le H_d+S_{i+d}-S_i,\qquad 2\le d\le\min(b,N-i).
$$
Indeed the head stays shortest after truncation. Here $H_d$ bounds $\log(\lambda_1^d/\det)$ in rank $d$. These inequalities retain information about the earlier profile even when the terminal minimum is very small. [Torus disintegration](wall1_haar_prefix_law.md) · [Independent lifts at one cut](wall1_poisson_smallball.md)

Count nested primitive prefixes ending at the partition cuts in the script. Each bad full flag, including its $W$ and terminal shortest line, maps to such a chain. It suffices to count the coarser chain once even when it admits many completions. The conditions for an eligible completion imply upper bounds $S_i\le U_i$ proved below. Dropping the remaining completion tests at this point gives a finite first moment, unlike summing over unrestricted terminal prefixes.

To see the caps, use the integer backward recurrence below. Off the special row $i=k$, its minimizing $d$ ensures $d(U_{i+1}-U_i)\ge C_d/M+U_{i+d}-U_i$. The linear term in $U$ cancels. Suppose either the absolute or the quotient-relative lower bound fails. The numerical tests yield respectively
$$
 S_{k+1}-S_k < U_{k+1}-U_k,\qquad\text{or}\qquad
 S_{k+1}-(1-1/b)S_k < U_{k+1}-(1-1/b)U_k .
$$
The second uses $\det T=e^{-S_k}$. A positive maximum of $S-U$ cannot occur at $k+1$ under either condition. At any other interior maximum, the truncation inequality forces the same maximum at its left neighbor by convex averaging with weight $(d-1)/d$ there. Both endpoints have difference zero. This proves the caps for the **union** of the two failures.

For cuts $0=e_0<\cdots<e_h=N$ of consecutive ranks $d_j$, the primitive-chain mean density in the interior log determinants has exponential factor $\exp(\sum_j d_j(S_{e_{j-1}}+S_{e_j}))$. Its normalization is $2^{1-h}\exp(A_N-\sum_j A_{d_j})$, with $A_d$ as in the script (using exact log zeta for the identity). This is the split averaging identity iterated over successive primitive cuts, or the disjoint HKZ partition formula after integrating internal HKZ flags. Each block admits HKZ; its sign-divided internal weight integrates to one under normalized shape measure. Integration up to each cap divides by the positive coefficient $e_{j+1}-e_{j-1}$. Markov bounds existence by this mean. [Partition formula](wall1_volume_svp_weights.md) · [Primitive chain averaging](https://arxiv.org/abs/2610.15265)

## Higher-degree packing constraint

Set $D=d+1$. Write $P_j$ for the zonal Gegenbauer polynomials for the unit sphere in dimension $D$, normalized at one, and $h_j'$ for degree-$j$ harmonic multiplicity. Fix $0<t<1$. Stop at the first $m+1$ with $P_{m+1}(t)\le0$. For $s<t$ a spherical code of maximum inner product $s$ has size at most
$$
 \frac{1-s}{t-s}\left[\binom{D+m-1}{m}+\binom{D+m-2}{m-1}\right].
$$
Indeed take $Q(u)=\sum_{j=0}^m h_j'P_j(t)P_j(u)$. The reproducing-kernel (Christoffel–Darboux) identity expresses $(u-t)Q$ as a positive multiple of $P_m(t)P_{m+1}(u)-P_{m+1}(t)P_m(u)$. Both coefficients are nonnegative. The addition formula makes these zonal kernels positive semidefinite, as is $Q$. Their pointwise products are positive semidefinite by the Schur product theorem. Thus $f=(u-s)Q^2$ contributes at least $(t-s)\sum_j h_j'P_j(t)^2$ per ordered pair on average over a code: subtracting this constant kernel leaves a positive semidefinite kernel. Here the constant coefficient of $Q^2$ follows by harmonic orthogonality, and removing its constant component preserves positive semidefiniteness by orthogonal projection in the tensor-square feature space. Off-diagonal $f\le0$; Cauchy–Schwarz bounds $Q(1)^2\le(\sum h_j')\sum h_j'P_j(t)^2$. Summing the harmonic multiplicities gives the displayed binomials.

Scale the lattice to minimum one and put $r=[2(1-s)]^{-1/2}$. Points in any translated radius-$r$ ball, centered and lifted to the upper hemisphere of the same radius, retain separation at least one. Their number is bounded by the code bound $B$. Averaging the translate gives $V_dr^d/\det\le B$. This supplies the candidate $H_d=\log B-\log(V_dr^d)$, used also on truncations that cross $k$. The script takes the best proved bound, including the previous cubic. It tests the Gegenbauer signs with integers by scaling $P_j(v/10)$ by $10^j(D-2)_j$ (rising factorial). [Packing and spherical codes](https://arxiv.org/abs/1212.5966)

## Asymptotic consequence and gap

For $b/N\to a\in(0,1)$, the crossing constraints give the weaker simultaneous lower bound $g_k/(h_b\det(T)^{1/b})\ge\exp[-O_a(\log^2 N)]$ with failure probability at most $2^{-N}$. To see this, split the index path from 0 to $k$ into at most $\lceil k/(b-1)\rceil$ segments of at most $b-1$ edges. On each segment ending at $v$, write $x_i=\log g_i$, $m_i$ for the mean of $x_i,\ldots,x_v$. The truncation ending at $v$ gives $x_i\le m_{i+1}+H_d/(d-1)$ and $m_i\le m_{i+1}+H_d/[d(d-1)]$, $d=v-i+1$. Minkowski gives $H_d\le d\log(2h_d)=O(d\log(2d))$. Summation back from $m_v=x_v$ costs $O(\log^2 b)$ per segment. Thus $g_k\ge g_0\exp[-O_a(\log^2 N)]$. Siegel's sign-pair bound gives $\lambda_1(L),\lambda_1(L^*)\ge h_N/2$ except on mass at most $2^{-N}$ in total. Since $T^*=L^*\cap W^\perp$, Minkowski gives $\det(T)^{1/b}\le 2h_b/\lambda_1(L^*)=O(1)$ there. Use $g_0\ge\lambda_1(L)$ and $h_N/h_b=\Theta_a(1)$.

This loss grows with dimension. Neither this argument nor the finite flag count establishes a dimension-independent constant at the quotient scale or $0.85G$ in ambient units. The empirical $0.87$ compares the best basis found with typical output at small rank. To reach the proposed absolute radii one still needs a bound on the mass of completable flags in the surviving profile region, including joint avoidance in overlapping windows. [Experiments](wall1_bad_bases_experiment.md) · [Wall 1 frontier](../PROOF_GAP.md)

## Interval certificate

Python 3 and mpmath. All printed table inequalities use outward interval comparisons. The integer dents and cuts are witnesses; reproducing their search is unnecessary.

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


rows = [
 (406,5978871832,list(range(13,170,13))+[183,197,212,618],".00609055",".00356898","-5.163",".369"),
 (506,5089727826,[12,518],".01588487",".00858457","-4.781",".816"),
 (647,4573769958,[377],".03996130",".01424667","-5.116","1.822"),
 (800,3726249289,[224],".14264140",".03307094","-4.779","3.413")]
for b,dent,cuts,absolute,relative,logcap,target in rows:
    k=n-b
    U=envelope(b,dent)
    ends=[0]+cuts+[n]
    L=A[n]-len(cuts)*I.ln(2)
    for p,q in zip(ends,ends[1:]):
        assert 1<=q-p<=b
        L+=(q-p)*(U[p]+U[q])-A[q-p]
    L-=sum(I.ln(z-x) for x,z in zip(ends,ends[2:]))
    gh=I.exp(I.loggamma(1+I.mpf(b)/2)/b)/I.sqrt(I.pi)
    x=U[k+1]-U[k]
    assert I.exp(x)>I.mpf(absolute)
    assert I.exp(x+U[k]/b)/gh>I.mpf(relative)
    assert L<I.mpf(logcap)<-I.ln(100)
    slope=(I.ln(b/(2*I.pi*I.exp(1)))+I.ln(I.pi*b)/b)/(2*(b-1))
    assert abs(I.mpf(".85")*I.exp((n-2*k-1)*slope)-I.mpf(target))<I.mpf(".001")
    print(b, absolute, relative, logcap)
```
