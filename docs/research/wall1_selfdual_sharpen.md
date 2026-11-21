# Filtering the generalized-slide extension count

At rank 1023 the two-block first moment is essentially saturated. For the audited numerical Hermite factors, even **exactly counting distinct extensions that admit a passing basis** improves the determinant-only radius by a relative factor below $1+4\cdot10^{-12}$ at widths 406 and 506. This is a limitation of Markov applied to that count. It gives no upper bound on the minimum returned by an implementation. Using positive tour slack $10^{-6}$ gives the following 99% lower bounds on the terminal quotient minimum of the exact-oracle algorithm, simultaneously over passing bases at each fixed width. Entries for bounds and ratios round down.

| Width | Blocks | Minimum | Fraction of $0.85G_b$ | Zero-slack certificate (limit) |
|---:|---:|---:|---:|---:|
|406|2|0.12656786|0.342813|0.12656799|
|506|2|0.36551260|0.447758|0.36551297|
|341|3|0.05158655|0.276408|0.05158665|
|256|3|0.01021614|0.186912|0.01021617|
|255|4|0.00997766|0.185807|0.00997769|
|205|4|0.00249714|0.129674|0.00249715|

The shortfalls at 406 and 506 are about 0.24263 and 0.45080 ambient length units. For the propagated certificate below, scanning every three- and four-block width gives the largest target fractions at 341 and 255 respectively. Width and block count change together. The zero-slack column is a supremum in the slack parameter of this determinant certificate. All factors increase monotonically with slack. The stopping theorem needs positive slack, and reducing it increases the tour budget. These statements use the real-arithmetic and Hermite-cap qualifications in [Part 88](wall1_li_walter.md). The Part 64 experiment compared small-rank restart outputs and supplies no rank-1023 probability estimate. [Part 87](wall1_selfdual_extend.md)

## The selected line and the exact incidence integral

Set $k=n-b,r=k+1,m=b-1$. At a primitive extension $P$ of determinant $D$, draw normalized shapes $H=D^{-1/r}P$ and $J=D^{1/m}(L/P)$ independently from Haar measure, and draw the uniform lift homomorphism from the projected quotient to the torus of $P$. This is the unselected primitive incidence law with radial density $nK_r D^{n-1}$, in the normalization of [Part 84](wall1_prefix_level.md). There is no uniformly sampled internal terminal line. Enumerate primitive hyperplanes in $H$ by unoriented primitive normals in $H^*$. A normal of length $t$ gives physical terminal height $g=D^{1/r}/t$. Its kernel in $H$ has determinant $t$. Upon marking the normal, its kernel normalized to determinant one is Haar of rank $k$, by primitive-line unfolding in the dual and dualizing the normalized quotient. This law holds under the sum over normals.

For two blocks let $a$ be the common twin factor. In the unit kernel shape a first primitive line of length $z$ passes the two tests exactly when
$$
 t^{k-1/k}/a^k\le z\le a,\qquad t\le T=a^{k/(k-1)} .
$$
Indeed its physical length is $D^{1/r}t^{1/k}z$, and the primal and shifted dual inequalities are $x\le a(D/g)^{1/k}$ and $D/x\le(ag)^k$. Both are Hermite inequalities on the **named** vectors. They impose no shortest-vector requirement on either internal line. Any such first line extends to a basis of the kernel, and then to $P$ and $L$ by primitivity. Size reduction preserves the heights and projected lattices.

For each eligible normal project the lift homomorphism further to the circle modulo the kernel, with circumference $g$. The exact terminal shortest test is the Part 46 indicator $I_g$ that every nonzero projected competitor $y\in D^{-1/m}J$ satisfies
$$
 |y|^2+g^2\|u_t(y)\|_{\mathbb T}^2\ge g^2 .
$$
Given one marked normal the induced character is uniform by primitivity. Averaging its indicator on the character and $J$ gives precisely $Z_b(g(D/g)^{1/b})$ by scaling to terminal determinant one. This is the selected-line factor in the exact minimum density, not the CDF at a preselected vector. The exact mean of distinct passing extensions is the radial integral of the expectation of the **maximum** of these indicators over normals admitting a first line and $g<\rho$ (empty maximum zero). All normals share the same external shape and lifts. Substituting independent copies of the minimum CDF would change the integral. [Part 46](wall1_haar_prefix_law.md)

Here are rigorous enclosures for that exact law. Put $D_*=(T\rho)^r$. At fixed $D<D_*$ existence implies a normal in $(D^{1/r}/\rho,T]$. Its probability is bounded by one and by its primitive Siegel annulus mean. For every candidate $g\ge D^{1/r}/T$, so a projected competitor shorter than $\sqrt3 D^{1/r}/(2T)$ kills **every** character. Multiply the internal probability upper bound by
$$
 1-F_m(\sqrt3 D^{1/r+1/m}/(2T)).
$$
This exact Haar minimum CDF arises on the independent external shape. For numerical enclosures its survival is at most $1/(1+V_m s^m/(2\zeta(m)))$ at argument $s$, by the Part 46 second moment. Conversely, if the projected quotient has minimum above $\rho$, every internal candidate passes, for every character. Its probability is $1-F_m(\rho D^{1/m})$. These inclusions bracket the shared-character integral without evaluating a high-dimensional void probability by a Poisson approximation.

## How much can exact filtering buy?

Let $R$ solve $K_r(TR)^{nr}=.01$, and $u=10^{-12}$. There is a strict gain over $R$: at its outer determinant endpoint the normal annulus shrinks to zero volume, and the external survival bound is also strictly below one. The same bounds integrated over $D$ vary continuously in the cut. A quantitative lower certificate is $(1+v/8)R$ with $v=e^{-800}$. In the outer layer $D^{1/r}>(1-v)T\rho$ the expected number of eligible normals is at most $r v V_r T^r/2<1/2$. This layer has radial mass fraction $1-(1-v)^{nr}\ge nr v/2$ by Bonferroni. At the proposed cut the mean divided by .01 is therefore at most $\exp(nrv/8)(1-nrv/4)<1$. The reverse estimate below explains why this strict gain disappears at the displayed precision.

Take $\rho=(1+4u)R$ and integrate only through $D_0=[(1+u)TR]^r$. Normals in $[(1-2u)T,(1-u)T]$ automatically give $g<\rho$. In their normalized kernels every primitive line in $[(1-u)a,a]$ works by the displayed twin inequalities. Write $h_1,h_2$ for the respective primitive-pair shell means, equal to shell volume divided by twice the dimension-specific zeta value. For the outer count $N$, Rogers gives $\mathbb E N^2=h_1^2+h_1$. The expected count of normals with a passing kernel is at least $h_1 h_2/(1+h_2)$, by unfolding and the same second moment in the kernel. This filtered count is bounded by $N$, so Cauchy–Schwarz gives existence probability at least
$$
 \frac{h_1}{1+h_1}\left(\frac{h_2}{1+h_2}\right)^2 .
$$
Multiply by $1-F_m(\rho D_0^{1/m})$, independently. The exact Part 46 density with $1-V_m s^m/2\le Z_m(s)\le1$ encloses this last CDF between $h(1-V_m s^m/2)$ and $h$, where $h=V_m s^m/(2\zeta(m))$. The script verifies $h_i>10^{40}$ and the CDF below $10^{-300}$. Thus the exact filtered mean exceeds .01 at this cut, since the integrated unfiltered mass is $.01(1+u)^{nr}$. This proves the claimed enclosure of the optimal Markov radius for this predicate, including the 1% and small positive slack cases. It applies to the explicit cap-based factors; stronger oracle output properties or smaller actual Hermite factors define different counts.

The dominant loss is the frequency of distinct small-determinant extensions in the first moment combined with the permitted twin factor. At the two determinant thresholds the upper ends of the normal and first-line shells already enclose enormous expected counts, while the terminal quotient has almost no competitors on the required scale. At the target the unfiltered mass relative to the 1% budget has log about 676827 and 425786 at zero slack. The lower-bound argument at the slightly raised cut suffices to rule out reaching the target by exact filtering. It does not assert that many passing extensions occur on a typical lattice.

## Additional block boundaries

Write the nonterminal block widths in order $d=b+s,b,\ldots,b$. Let $v$ be the block determinant and $x,y$ its head and the following block head. Write $B,T'$ for the primal and shifted dual log Hermite factors. Then
$$
 x\le e^B v^{1/d},\qquad v\le e^{dT'}x y^{d-1},\qquad
 x\le e^i y,\quad v\le e^{dT'+i}y^d,\quad i=d(B+T')/(d-1).
$$
For ordinary blocks use the Hermite consequences of their two SVP tests. With $H=C_b/[10^9 b(b-1)]$ and $E=\log(1+\epsilon)$, Definition 1 gives $B=T'=(d-1)(H+E/(b-1))$ throughout. Use the sharper unchanged-tour factors of Part 88 for two blocks. Start with $X=U=0$ at terminal head $g$. Moving backwards, add $dX+dT'+i$ to $U$ before adding $i$ to $X$. This multiplies the block determinant bounds and proves $D\le e^U g^r$. Count primitive extensions once. The same external survival bound applies with $T=e^{U/r}$. [Li–Walter, Definition 1 and Algorithm 1](https://eprint.iacr.org/2023/140.pdf)

The multi-block table conservatively drops this factor and uses the scalar consequences of the intermediate exact SVP tests. Optimality of the full multi-block integral, which must retain their internal shortest and reversed-dual shortest indicators, is open here.

## Interval reproduction

Run the Python block at the repository root. It reuses the audited cap and Haar normalization intervals of [Part 86](wall1_dual_pinning.md), based on [Part 82](wall1_small_d_caps.md). The shell checks use $1<\zeta(j)<2$.

```python
from pathlib import Path
src=Path('docs/research/wall1_dual_pinning.md').read_text()
exec(src.split('\n```python\n')[1].split('def ceildiv')[0])
def row(b,eps):
    p,s=divmod(n,b)
    k=n-b
    r=k+1
    H=I.mpf(C[b])/(M*b*(b-1))
    E=I.ln(1+I.mpf(eps))
    widths=[b+s]+[b]*(p-2)
    X=U=I.mpf(0)
    for j,d in reversed(list(enumerate(widths))):
        B=(d-1)*H+(E if j==0 else I.mpf(0))
        T=(d-1)*H+E
        if p>2: B=T=(d-1)*(H+E/(b-1))
        # x<=exp(B) v^(1/d); v<=exp(d*T) x next^(d-1)
        inc=d*(B+T)/(d-1)
        U+=d*X+d*T+inc
        X+=inc
    K=A[n]-A[r]-A[n-r]-I.ln(2*n)
    R=((-I.ln(100)-K)/n-U)/r
    S=(I.ln(b/(2*I.pi*I.exp(1)))+I.ln(I.pi*b)/b)/(2*(b-1))
    tar=I.mpf('.85')*I.exp((2*b-n-1)*S)
    return I.exp(R),I.exp(R)/tar,I.exp(U/r),I.exp((k-1)*H+E)
def ball(d):
    v=I.mpf(d)/2
    return I.exp(v*I.ln(I.pi)-I.loggamma(1+v))
u=I.mpf('1e-12')
for b in (406,506,341,256,255,205):
    for eps in ('0','.000001','.01'):
        R,ratio,T,a=row(b,eps)
        print(b,eps,int((10**8*R).a),int((10**6*ratio).a))
        if n//b!=2: continue
        k=n-b
        r,m=k+1,b-1
        assert r*ball(r)*T**r<I.exp(800)
        h1=ball(r)*T**r*((1-u)**r-(1-2*u)**r)/4
        h2=ball(k)*a**k*(1-(1-u)**k)/4
        assert h1>10**40 and h2>10**40
        D0=((1+u)*T*R)**r
        F=ball(m)*((1+4*u)*R)**m*D0/2
        assert F<I.mpf('1e-300')
        assert (1+u)**(n*r)*(1-F)/(1+1/h1)/(1+1/h2)**2>1
for lo,hi in ((256,341),(205,255)):
    best=row(hi,'.000001')[1]
    assert all(row(b,'.000001')[1]<best for b in range(lo,hi))
```
