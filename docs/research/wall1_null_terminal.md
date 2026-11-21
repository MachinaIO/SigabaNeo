# A terminal minimum certificate for the null lattice

For 511 independent uniform sample rows, 512 columns and prime modulus 3329, **every exact fully BKZ-1000 basis** of the null lattice has terminal projected minimum greater than $\sqrt{6000}$ with probability at least 0.99. This uses an ambient Gaussian count and 23 steps of deterministic profile propagation. The first GSA crossing is at 506. Both numbers refer to the fixed comparison length $\sqrt{6\beta}$ in physical coordinates. A tail probability for a random projected CBD norm would be an additional input to any joint success probability.

## From an ambient minimum to a terminal minimum

Index GS lengths $g_i$ from zero and put $k=N-\beta$. In the repository's exact BKZ predicate the head of every projected window realizes its minimum, including truncated windows. In particular $\lambda_1(T)=g_k$. Even for an arbitrary projected basis one has $\lambda_1(T)\ge\min_{i\ge k}g_i$, by projecting a nonzero integer combination at its last nonzero coefficient. There is no dimension loss in this inequality. [BKZ definition](../../SigabaNeo/Lib/Lattices/Reduction/BKZ.lean)

Let $C_l\ge(l/2)\log\gamma_l$. Put $P_0=0$ and
$$
 P_j=\min_{2\le l\le\min(j+1,\beta)}
 \frac{C_l+\sum_{v=j-l+1}^{j-1}P_v}{l-1}.
$$
Then $\lambda_1(T)\ge\lambda_1(L)e^{-P_k}$. Indeed Hermite on the first $l$ rows of any window gives $(l-1)\log g_i\le C_l+\sum_{h=1}^{l-1}\log g_{i+h}$. Backward induction bounds $\log(g_i/g_k)$ by $P_{k-i}$, and $g_0\ge\lambda_1(L)$. This is Part 6's ratio bound applied directly to the null lattice. It holds simultaneously for all reduced bases. [Prefix bounds](wall1_prefix.md) · [Part 7](ratio_unique.md)

**Slide.** Write $N=s\beta$, let $h_j=g_{j\beta}$, and let $B_j$ be the covolume of primal block $j$. The squared dual approximation factor is $\rho\ge1$. For $j<s-1$ the shifted block has covolume $B_j h_{j+1}/h_j$ and its last reciprocal basis vector has length $1/h_{j+1}$. The dual condition and Hermite give
$$
 h_{j+1}\ge (B_j h_{j+1}/h_j)^{1/\beta}/\sqrt{\rho\gamma_\beta}.
$$
The primal condition gives $B_j\ge(h_j/\sqrt{\gamma_\beta})^\beta$. Substitution and iteration therefore give
$$
 \lambda_1(T)=h_{s-1}\ge\lambda_1(L)
 (\sqrt\rho\,\gamma_\beta)^{-\beta(s-1)/(\beta-1)} .
$$
The shifted dual checks stop at the head of the final primal block. Imposing an extra dual check on that entire final block, or importing Part 6's overlapping-window cutoff for an arbitrary slide basis, would require an additional hypothesis. The implemented predicate requires divisibility. [Slide conditions](../../SigabaNeo/Lib/Lattices/Reduction/Slide/Conditions.lean)

## Counting in the null ensemble

After deleting a prescribed set of sample coordinates, write $r$ for the number retained, $N=r+512$ and $D=q^r$. Every punctured solution extends by choosing each missing sample in its prescribed residue class. The remaining design is uniform. For $0<R<q$, any nonzero possible lattice point of length at most $R$ has secret part nonzero modulo $q$. Each such candidate belongs with probability $q^{-r}$ by row independence. Count opposite signs together. With $t>0$ and $\theta(t)=\sum_{j\in\mathbb Z}e^{-tj^2}$,
$$
 \Pr(\lambda_1(L)\le R)\le e^{tR^2}\theta(t)^N/(2D).
$$
This follows by majorizing each ball indicator with its exponential weight, then extending the numerator sum to all integer vectors. Poisson summation gives $\theta(t)\le H=\sqrt{\pi/t}(1+2z/(1-z))$ for $z=e^{-\pi^2/t}$ since $j^2\ge j$ for $j\ge1$. The table uses $t=\pi e D^{-2/N}$ and $R^2=(\log(0.02D)-N\log H)/t$. Its 99% event applies to all widths simultaneously for each fixed shape.

| Retained rows | Null rank | Ambient radius (rounded down) | First certified BKZ width | First certified exact slide width | First GSA crossing, widths ≥40 |
|---:|---:|---:|---:|---:|---:|
|511|1023|443.0664|1000|1023|506|
|188|700|56.2165|none|none|none|
|149|661|38.4825|none|none|none|
|134|646|32.8751|none|none|none|

At width 1000 the certified terminal radius exceeds 79.0418, against a target below 77.460. At 999 the same bound is below 75.549, against a target above 77.42. “First certified” minimizes the stated propagated bound. Smaller widths may satisfy the actual inequality. The last two rows retain the sample counts of the Part 39 dimensions 662 and 647. Removing the embedding height lowers each rank by one. Freezing coordinates before reduction is a different experiment from selecting a prefix of the reduced full basis. [Part 39](wall1_projected_reference.md) · [Part 44](wall1_zshape.md)

For GSA the predicted physical length is $G=D^{1/N}\delta^{2\beta-N-1}$, where $\log\delta=[\log(\pi\beta)/\beta+\log(\beta/(2\pi e))]/[2(\beta-1)]$. On the full shape, at 406 this gives 24.962 against a target of 49.356, and at 506 it gives 55.192 against 55.100 (rounded). The missing step from 1000 to 506 is a lower-tail estimate for an adaptively selected quotient. A signed or unsigned GSA exponent alone has no probability content.

## A dual bound valid for every rational prefix

Let $S=L\cap W$, $d=\dim T\ge2$, and $a=\lambda_1(L^*)$. Then
$$
 \lambda_1(T)\ge \frac{\det L}{\det S}
 \left(\frac{a}{\sqrt{\gamma_{d-1}}}\right)^{d-1}.
$$
Indeed $T^*=L^*\cap W^\perp$ by testing inner products before and after projection. For a shortest primitive $v\in T$, the kernel $K$ of evaluation at $v$ in $T^*$ has rank $d-1$ and covolume $\|v\|/\det T$. Evaluation is onto $\mathbb Z$, so adjacent layers are $1/\|v\|$ apart. Hermite on $K$ and $\lambda_1(K)\ge a$ give the inequality. Extending a basis of $S$ gives $\det T=\det L/\det S$. Thus any valid prefix covolume upper bound can be inserted, with the factor raised to dimension $d-1$.

There is no positive uniform lower bound using just ambient determinant and the two ambient minima for unrestricted rational prefixes. In $\mathbb Z^N$ take the line through $(M,1,0,\ldots,0)$. Projection of $e_1$ has length $1/\sqrt{1+M^2}$ although all three ambient invariants equal one. Orthogonally adjoining coordinate axes to the prefix gives every proper positive prefix rank. Reducedness supplies genuinely additional information.

## Haar normalization and HKZ selection

For a unit-covolume Haar lattice in dimension $N$, the expected number of primitive lines up to radius $u$ is $V_N u^N/(2\zeta(N))$, where $V_N=\pi^{N/2}/\Gamma(1+N/2)$. Consequently, with failure at most $\epsilon$, all fully BKZ bases satisfy $\lambda_1(T)>(2\epsilon/V_N)^{1/N}e^{-P_k}$. This also applies to full HKZ prefixes since these satisfy each finite-window head test. At $N=1023$ the ambient 99% radius is greater than 7.7402. A single HKZ projection retains at least $\sqrt3/2$ of this lower radius (greater than 6.70), since a transverse shortest vector lifts with height at most half the first minimum. This is precisely the support restriction in Part 46. For Haar at covolume $D$, multiply lengths by $D^{1/N}$. [Primitive mean value theorem](https://arxiv.org/abs/2310.03459) · [HKZ prefix law](wall1_haar_prefix_law.md)

More generally the exact HKZ failure probability at radius $u$ integrates the Part 46 joint density against the indicator $D_d^{1/d}s_d\le u$ at $d=\beta$, using its physical covolume recursion. Unfolding only the first $k$ steps leaves a Haar shape under the incidence measure weighted by all ancestor shortest-vector tests. Dropping these weights and treating the terminal shape as an independent normalized Haar lattice would change the probability. The ambient-event bound above bypasses that integration. It gives no near-GSA finite-width theorem. No numerical evaluation of the deep selected integral is used here.

## Reproduction

The Python script uses interval arithmetic for transcendental evaluations and integers for the profile. The unrestricted window recurrence gives an optimistic test for smaller widths. Every passing row is checked to have an inactive width cap. At other rows even the relaxed test fails. Upward rounding defines the implemented certificate.

```python
from mpmath import iv as I
from math import ceil
I.dps=50
M=10**12
def profile(n):
    h=[0,0,I.mpf(4)/3,2,4,8,I.mpf(64)/3,64,256]
    C=[0,0]+[I.ln(h[l])/2 if l<9 else l*I.ln(2/I.pi)/2+I.loggamma(2+I.mpf(l)/2) for l in range(2,n+1)]
    # Conservative upward integer quantization defines the certificate itself.
    c=[ceil(float((M*x).b))+1 if l>=2 else 0 for l,x in enumerate(C)]
    assert all(I.mpf(c[l]) >= M*C[l] for l in range(2,n+1))
    p=[0]; S=[0,0]
    for j in range(1,n):
        p.append(min(-(-(c[l]+S[j]-S[j-l+1])//(l-1)) for l in range(2,j+2)))
        S.append(S[-1]+p[-1])
    return p,c
for r in (511,188,149,134):
    n=512+r; a=I.mpf(n)/2; dlog=r*I.ln(3329)
    R=I.exp((dlog+I.loggamma(1+a)-a*I.ln(I.pi)+I.ln(I.mpf(2)/100))/n)-I.sqrt(n)/2
    # Gaussian majorant. Poisson summation and h^2 >= h bound the theta tail.
    t=I.pi*I.exp(1-2*dlog/n)
    z=I.exp(-I.pi**2/t)
    theta=I.sqrt(I.pi/t)*(1+2*z/(1-z))
    R2=I.sqrt((dlog+I.ln(I.mpf(2)/100)-n*I.ln(theta))/t)
    assert R2>R and R2<3329
    R=R2
    p,c=profile(n)
    if r==511:
        assert R*I.exp(-I.mpf(p[23])/M)>I.mpf("79.0418")
        assert R*I.exp(-I.mpf(p[24])/M)<I.mpf("75.549")
        assert I.exp((I.loggamma(1+a)-a*I.ln(I.pi)+I.ln(I.mpf(2)/100))/n)>I.mpf("7.7402")
    cert=[]; gsa=[]; slide=[]
    for b in range(2,n+1):
        j=n-b; t=I.sqrt(6*b); relaxed=R*I.exp(-I.mpf(p[j])/M)
        if relaxed>t:
            assert j+1<=b
            cert.append(b)
        else: assert relaxed<t
        if n%b==0:
            A=I.mpf(2)*c[b]/(M*(b-1))
            if R*I.exp(-(n//b-1)*A)>t: slide.append(b)
        if b>=40:
            logdelta=(I.ln(I.pi*b)/b+I.ln(b/(2*I.pi*I.exp(1))))/(2*(b-1))
            G=I.exp(dlog/n+(2*b-n-1)*logdelta)
            if G>t:gsa.append(b)
            else: assert G<t
    print(r,n,R,min(cert,default=None),min(slide,default=None),min(gsa,default=None))
```
