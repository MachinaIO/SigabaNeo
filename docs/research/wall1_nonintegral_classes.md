# Nonintegral dual classes in the width-506 block

**Result.** At horizontal rank 505, a verified horizontal minimum of 54.82 bounds the full Gaussian charges at heights 2 and 3 by $10^{-41.86}$ and $10^{-31.74}$, respectively, for every physical projection. A lower bound of 99.25% of each model Gram–Schmidt length also puts height 4 below $10^{-9.71}$. For heights 5 through 30 this note gives an additional, finite test on the projection in the ambient integer coordinates. Every block passing the three conditions in Corollary 2 has nonintegral contribution $R<0.005792$. At the literal GSA lengths the conditional bound improves to $0.00012938$. On the physical zero design, direct evaluation gives $6.4276\cdot10^{-53}<R<6.4277\cdot10^{-53}$.

The projection test uses Gram determinants of integer bases in a specified quadratic form. It avoids enumerating the residue code. The GSA model supplies terminal lengths but leaves those Gram determinants unspecified. Whether a reducer-selected block passes remains open.

## The sum being bounded

Fix a design and horizontal prefix independently of the CBD plant, conditionally on the design. Use $N=1023$, $q=3329$, $d=505$, $F=[A\ I_{511}]$, $L_0=\ker(F\bmod q)\subset\mathbb Z^N$. Write $E$ for the orthogonal complement of the prefix span, $P$ for its orthogonal projector, $H=PL_0$, $J=P\mathbb Z^N$, and $T=E\cap\mathbb Z^N$. All duals are intrinsic to the span. The retained vectors at height $k$ have horizontal component $h+kPX$, $h\in H$. The strict inequalities in the all-heights criterion charge a tie as failure. These conventions agree with the physical embedding and the formal criterion. [AttackLattice](../../SigabaNeo/Lib/Lattices/Research/Wall1/AttackLattice.lean) · [UniquenessCriterion](../../SigabaNeo/Lib/Lattices/Research/Wall1/UniquenessCriterion.lean)

For $w\in E$, pairing with $Pz$ equals pairing with $z$. Thus $J^*=T$ and $H^*=E\cap L_0^*$. Since $q\mathbb Z^N\subset L_0$, every $w\in H^*$ is $u/q$ with $u\in T$. Its pairing with $L_0$ is integral precisely when $u\bmod q\in\operatorname{row}(F)$. Consequently $w\mapsto qw\bmod q$ identifies $H^*/T$ with $(T\bmod q)\cap\operatorname{row}(F)$. Multiplication by any tested height is invertible modulo $q$. The zero residue class is therefore exactly the set with $kw\in\mathbb Z^N$. The Lean minimum of at least one applies to $T$. The other classes are translates of $T$ and can contain shorter vectors. [ProjectionDual](../../SigabaNeo/Lib/Lattices/Research/Wall1/ProjectionDual.lean) · [MarkedIntegerSection](../../SigabaNeo/Lib/Lattices/Research/Wall1/MarkedIntegerSection.lean)

Keep the Part 177 test scale
$$
 a=1.9d,\quad B=1+a=960.5,\quad t=d/(2B),\quad
 \alpha=\pi^2/t,\quad \gamma=3\pi^2,\quad
 b_k=e^{t(B-k^2)}(\pi/t)^{d/2}/\det H .
$$
For independent CBD(3) coordinates the characteristic function at $kw$ is $C_k(w)=\prod_j\cos^6(\pi k w_j)$ by the six half-sign representation. Write
$$
 M_k=b_k\sum_{w\in H^*} e^{-\alpha\|w\|^2}C_k(w),\qquad
 R=\sum_{k=2}^{30} b_k\sum_{w\in H^*\setminus T}e^{-\alpha\|w\|^2} C_k(w).
$$
All summands are nonnegative. On the cap $\|PX\|^2\le a$ a height-$k$ hit contributes at least one to the periodized Gaussian $\sum_{h\in H}\exp(t(B-k^2-\|h+kPX\|^2))$. Its unconditional expectation is $M_k$ by Poisson summation. Hence $\sum M_k$ bounds both $R$ and the full higher-height charge, including the zero frequency. One pays the cap exception only once. The height-one estimate uses the real CBD moment bound. [Part 177 and audit](wall1_aliasing.md) · [Part 175 and audit](wall1_smoothing_uniqueness.md) · [CBDTail](../../SigabaNeo/Lib/Lattices/Research/Wall1/CBDTail.lean)

## A theta bound in the ambient integer coordinates

Write $\Theta_H(u)=\sum_{h\in H}e^{-u\|h\|^2}$ and $\Theta_{\mathbb Z^N}(Q)=\sum_{z\in\mathbb Z^N}e^{-z^TQz}$ for a positive definite matrix $Q$. Define
$$
 D_k=1+3tk^2,\qquad u_k=t/D_k,\qquad v_k=\gamma/D_k,\qquad
 Q_k=\gamma(I-P)+v_kP .
$$

**Theorem 1.** For each tested height,
$$
 M_k\ \le\ e^{t(B-k^2)}D_k^{-d/2}\,\Theta_H(u_k)\,\Theta_{\mathbb Z^N}(Q_k). \tag{1}
$$

*Proof.* For $|x|<1/2$, integrating $\tan s\ge s$ from zero to $\pi |x|$ gives $\cos^6(\pi x)\le e^{-\gamma x^2}$. At the endpoints the left side vanishes. Centering each coordinate modulo one and including the nearest integer in a positive sum gives
$$
 C_k(w)\le e^{-\gamma\operatorname{dist}(kw,\mathbb Z^N)^2}
          \le \sum_{z\in\mathbb Z^N} e^{-\gamma\|kw-z\|^2}.
$$
This step retains every possible integer near $kw$, including integers outside $E$. Put $A_k=\alpha+\gamma k^2=\alpha D_k$. Since $w\in E$, completing the square gives the exact identity
$$
 \alpha\|w\|^2+\gamma\|kw-z\|^2
 =A_k\left\|w-\frac{\gamma k}{A_k}Pz\right\|^2+z^TQ_k z .
$$
For each integer $z$ the shifted Gaussian sum on $H^*$ is at most the centered sum. Indeed its Poisson series has the same nonnegative Gaussian coefficients and phases of modulus one. The centered sum is $\det H\,(\pi/A_k)^{d/2}\Theta_H(\pi^2/A_k)$. Multiplying by $b_k$ cancels the covolume and yields (1), since $\pi^2/A_k=u_k$. All rearrangements involve positive series or absolutely convergent Gaussian Fourier series. [Micciancio and Regev, Lemmas 2.8–2.9](https://cims.nyu.edu/~regev/papers/average.pdf)

### Bounding both factors by finite data

Put $\theta(s)=\sum_{n\in\mathbb Z}e^{-s n^2}$. If a lattice basis has Euclidean Gram–Schmidt lengths $g_i$, then $\Theta_H(u)\le\prod_i\theta(ug_i^2)$. In upper triangular coordinates sum first over the first basis coefficient, with the later ones fixed. Its Gaussian is a translate of the one-dimensional sum and is maximized at integral shift. Repeat on the remaining coordinates. The identical proof in the metric $Q_k$ shows that for any unimodular integer basis $U_k$ of $\mathbb Z^N$,
$$
 \Theta_{\mathbb Z^N}(Q_k)\le\prod_{j=1}^N\theta(p_{kj}),\qquad
 p_{kj}=\frac{\det (U_{k,1:j}^TQ_k U_{k,1:j})}
              {\det (U_{k,1:j-1}^TQ_k U_{k,1:j-1})}.                  \tag{2}
$$
Here $U_{k,1:j}$ consists of the first $j$ columns and the empty determinant is one. These are **squared** Gram–Schmidt lengths. Their product is $\gamma^{N-d}v_k^d$. The actual projector is rational, as is $Q_k/\gamma$. Thus unimodularity and pivot ratios after removing $\gamma$ can be checked in integer and rational arithmetic.

There are also bounds requiring fewer inputs.

1. If $\lambda_1(H)\ge L$, then
   $$
   \Theta_H(u)\le 1+2(d+1)^2\Gamma(1+d/2)\bigl(2/(uL^2)\bigr)^{d/2}.       \tag{3}
   $$
   For $r\ge L$, lift the $L$-separated points of the radius-$r$ ball to the unit sphere in $\mathbb R^{d+1}$ by $x\mapsto (x,\sqrt{r^2-\|x\|^2})/r$. Distances are at least $L/r$. In an open cap of angular radius $\arcsin(L/(\sqrt2 r))$ their components perpendicular to the cap axis have strictly negative pairwise inner products. At most $d+1$ such points fit, since an affine dependence among $d+2$ components would give two equal positive combinations on disjoint supports with negative mutual inner product. The fraction of sphere area in this cap is at least $(L/(\sqrt2 r))^d/(2(d+1))$ by projection onto the equatorial ball and the unit-ball volume inequality $V_{d+1}\le 2 V_d$. Averaging cap occupancy over rotations bounds the count by $2(d+1)^2(\sqrt2 r/L)^d$. The nonzero count vanishes below $L$. Integrating the count against $2ur e^{-ur^2}\,dr$ and extending the upper integrand to $r=0$ gives (3). This uses Part 177's packing estimate over all radii.
2. Uniformly in $P$,
   $$
   \Theta_{\mathbb Z^N}(Q_k)\le\theta(\gamma)^{N-d}\theta(v_k)^d.          \tag{4}
   $$
   In the standard coordinate basis all pivots are between $v_k$ and $\gamma$. Each pivot is the minimum squared $Q_k$-length of the current coordinate vector plus a real combination of earlier ones. The Euclidean squared length there is at least one, and zero earlier coefficients give the upper bound. The product of the pivots is known. Apply the secant inequality for the convex function $x\mapsto\log\theta(e^x)$ between $\log v_k$ and $\log\gamma$, then sum. The two resulting exponents are $d$ and $N-d$.
3. More generally set $m_k=\gamma D_k^{-d/N}$. If some unimodular basis satisfies $m_k/c\le p_{kj}\le c m_k$ for every $j$, $c>1$, then
   $$
   \Theta_{\mathbb Z^N}(Q_k)\le
   [\theta(m_k/c)\theta(c m_k)]^{N/2}.                                \tag{5}
   $$
   The same secant proof works because the mean of the log pivots is $\log m_k$. Different bases may be used at different heights.

For completeness, let $s=e^x$ and give $n\in\mathbb Z$ mass proportional to $e^{-sn^2}$. The second derivative of $\log\theta(e^x)$ is $s^2\operatorname{Var}(n^2)-s\mathbb En^2$. Writing $a=\mathbb En^2$, we have $\operatorname{Var}(n^2)\ge a(1-a)$ since $n^4\ge n^2$. For $s\ge\pi$, $a\le 2\sum_{n\ge1}n^2e^{-\pi n}<1/2$ by $\sum n^2z^n=z(1+z)/(1-z)^3$. This proves convexity on that half-line. The Poisson identity $\theta(s)=\sqrt{\pi/s}\,\theta(\pi^2/s)$ reflects its log graph plus an affine function and gives convexity on the other half-line. The function is smooth at $s=\pi$.

## Width 506 with and without projection data

Use zero-based terminal indices and the audited full-row GSA model
$$
 s=\frac{\log(506/(2\pi e))+\log(506\pi)/506}{1010},\qquad
 g_i^0=q^{511/N}\exp((2d-N-1-2i)s),\quad 0\le i<505 .
$$

**Corollary 2.** Suppose the physical block satisfies all of the following.

* Its verified minimum is at least $54.82$.
* Its supplied horizontal basis has $g_i\ge 0.9925 g_i^0$ at every index.
* For each $5\le k\le30$ it has an integer basis as in (5) with $c=7/5$.

Then $\sum_{k=2}^{30}M_k<0.005792$. With $g_i\ge g_i^0$ the same sum is below $0.00012938$. In particular both conclusions bound $R$ by less than $0.009$. The corresponding Part 94 failure bounds, including the audited cap and height-one terms, are $0.006271$ and $0.000608$, respectively. The exact aliases and the zero mode are already included in $M_k$.

*Numerical proof.* In (1) take the smaller of (3) and $\prod_i\theta(u_k(fg_i^0)^2)$ for $f=0.9925$ or $1$. Use (4) at $k=2,3,4$ and (5) at $5\le k\le30$. The table encloses the base-ten logarithms of the resulting individual upper bounds for the first three heights. The first column uses only (3) and (4).

| $k$ | Minimum alone | Minimum and $f=0.9925$ | Minimum and $f=1$ |
|---:|---:|---:|---:|
| 2 | $(-41.869,-41.868)$ | at most $-41.868$ | at most $-41.868$ |
| 3 | $(-31.746,-31.745)$ | at most $-31.745$ | at most $-31.745$ |
| 4 | $(1.407,1.408)$ | $(-9.713,-9.712)$ | $(-10.657,-10.656)$ |

The resulting sums of upper bounds are in $(0.00579140,0.00579141)$ and $(0.0001293791,0.0001293792)$ in the order stated in the corollary. Add $0.000478351+6.44\cdot10^{-14}$ from the audited Part 177 estimates. This accounts for all heights including ties. [Parts 94 and 171–177](../PROOF_GAP.md)

A block can also be tested directly by (1)–(4) using the actual pivot products, without the factor-$7/5$ hypothesis. The GSA listing alone determines neither the $P$ in $Q_k$ nor the integer bases in (2). The interval for $f=1$ evaluates a sufficient condition at the model lengths. No physical model-profile witness with those pivot data is supplied. Part 177's example within 0.75% of the model has a minimum below 1.837 and therefore falls outside the corollary.

## The physical zero design

Take $A=0$ and the Part 175 prefix of all 512 secret unit axes and six $q$-scaled error axes. Then $E$ retains 505 coordinate axes, $H=q\mathbb Z^d$, $H^*=q^{-1}\mathbb Z^d$, $T=\mathbb Z^d$, and $\lambda_1(H)=3329$. Using $g_i=q$ and (4) in (1) gives $\sum M_k<2.377\cdot10^{-47}$ without testing (5).

One can also enclose $R$ itself. Put $p_j=\binom6{3+j}/64$, $-3\le j\le3$. Separability of the original periodized Gaussian gives the exact formula
$$
 R=\sum_{k=2}^{30}\left\{
 e^{t(B-k^2)}
 \left[\sum_{j=-3}^3p_j\sum_{n\in\mathbb Z}e^{-t(qn+kj)^2}\right]^d
 -b_k\theta(\alpha)^d\right\}.                                      \tag{6}
$$
The subtraction removes every integral frequency including zero. In the bracket retain $n=0$ for a lower bound. An upper bound adds $2z/(1-z)$, $z=e^{-t(q-90)^2}$, since $|qn+kj|\ge |n|(q-90)$ for nonzero $n$. Formula (6) gives $-52.1920<\log_{10}R<-52.1919$ and the tighter decimal enclosure in the opening paragraph. In this example the actual higher-height collision probability on the cap is zero. The positive Gaussian first moment measures the slack in the test.

## Reproduction and remaining gap

The numerical enclosures use 65-decimal outward intervals. To reproduce the theta calculations, use reciprocal transformation when $s<\pi$. Otherwise sum $|n|\le4$ and add an interval from zero to $2e^{-25s}/(1-e^{-11s})$, since consecutive squared indices in the tail differ by at least 11. In the following pseudocode all noninteger constants are exact decimals or interval evaluations of the formulas above.

```text
for k = 2,...,30:
    pref = exp(t*(B-k^2)) / D_k^(d/2)
    pack = 1 + 2*(d+1)^2 * Gamma(1+d/2) * (2/(u_k*54.82^2))^(d/2)
    ambient = theta(gamma)^(N-d) * theta(v_k)^d
    if k >= 5:
        ambient = (theta(m_k/(7/5))*theta(m_k*(7/5)))^(N/2)
    for f in {0.9925, 1}:
        intrinsic = product(theta(u_k*(f*g_i^0)^2), i=0,...,504)
        total[f] += pref * min(pack,intrinsic) * ambient
```

As an exact small check, take the primitive prefix $(1,8)$ in its two-dimensional graph kernel modulo 13. The orthogonal line is spanned by $b=(-8,1)$, $P=bb^T/65$, and $H^*=\mathbb Z b/13$ since the projected kernel has unit-line spacing $13/\sqrt{65}$. At $k=2$, with unit coefficients $\alpha=\gamma=1$ for this algebra check, $Q=I-4P/5$. Its standard-basis pivots are $69/325$ and $65/69$, of product $1/5$. Substitution of $w=jb/13$ for $-13\le j\le13$ and every $z\in\{-3,\ldots,3\}^2$ gives equality of the two completed-square expressions in all 1,323 comparisons in exact rational arithmetic. The exact-alias test agrees with $13\mid j$ in every case.

The open physical question is whether an actual reducer output near the model profile satisfies the full higher-height bound. The minimum resolves heights 2 and 3 here, and the lower profile also resolves height 4. Heights 5–30 require additional evidence on such a block. Parts 172–174 and 176 concern dual exits, marked averages, or the law of a selected prefix. They give no verified pivot data for (2) or occurrence probability for Corollary 2. A successful fixed-block check conditions on that block. A frequency statement over reducer outputs would require a design and selection law. All new bounds here are paper proofs.

## Audit

**Verdict — MINOR CAVEATS.** Corollary 2 gives the stated bounds for every fixed, plant-independent block satisfying its three hypotheses. The qualification concerns height one. Part 177 bounds the failure event on the cap, while Lean charges the full theta sum. Equation (3) supplies a bound on that sum and preserves both numerical conclusions.

**Gaussian and class accounting.** Since $qH^*\subset T$ and every tested $k$ is coprime to $q$, $kw$ is integral exactly when $w\in T$. All CBD characteristic-function weights are nonnegative sixth powers, so deleting the integral slice gives $R\le\sum_k M_k$. Centering each coordinate gives the nearest-integer Gaussian upper bound, which is at most the sum over all ambient integers, including those outside $E$. Completing the square leaves coefficients $\gamma$ on $E^\perp$ and $\alpha\gamma/A_k=v_k$ on $E$. Poisson summation on the intrinsic lattice $H^*$ bounds the shifted theta by the centered theta. Its $\det H$ cancels the reciprocal covolume in $b_k$, and the remaining normalization is $D_k^{-d/2}$. Every dual vector enters the original charge once. The sum over ambient integers majorizes its weight without assuming any bound on class multiplicities.

**Finite projection test.** At each of the 26 heights from 5 through 30, the witness is an ordered integer matrix $U_k$ with determinant $\pm1$. Every successive Gram determinant ratio must belong to $[m_k/c,c m_k]$, where $c=7/5$. For the rational form $Q_k/\gamma$, write $x=p_{kj}/\gamma$. The pivot comparisons are exactly $D_k^d(cx)^N\ge1$ and $D_k^d(x/c)^N\le1$, so supplied witnesses can be checked even at equality. Existence also admits a finite search in principle. Size-reducing a witness in the $Q_k$ metric preserves its pivots and bounds each earlier Gram–Schmidt coefficient in absolute value by $1/2$. Since $Q_k\succeq v_k I$, each resulting column has squared Euclidean norm at most $(1+(N-1)/4)c m_k/v_k$.

Successively summing over the integer basis coefficients gives the product of one-dimensional thetas at **squared** pivots. Their product of arguments is fixed by unimodularity. For the log-theta convexity argument, writing $\mu=\mathbb E[n^2]$ gives $s(1-\mu)>1$ on $s\ge\pi$ because $\mu<1/2$ there. Poisson reflection supplies the other half-line. The secant weights therefore sum to $d$ at $v_k$ and $N-d$ at $\gamma$ in (4), and to $N/2$ at each endpoint in (5). For (3), lifting preserves the lower bound $L/r$ on chord distances. The open cap gives strictly negative perpendicular inner products. Integrating the resulting nonzero point count produces the stated gamma factor. These estimates justify using the minimum alone at heights 2 and 3 and the lower GS profile at height 4.

**Independent arithmetic.** I used 320-bit outward-rounded MPFI intervals, a factorial expression for the half-integer gamma value, and reciprocal theta transformation followed by summation through $|n|=8$. For $r=e^{-s}$ the omitted two-sided tail is at most $2r^{81}/(1-r)$. The first eight rows below enclose values of the *upper bounds*.

| Quantity | Independent enclosure |
|---|---|
| Minimum only, base-ten log at height 2 | $(-41.868436,-41.868435)$ |
| Minimum only, base-ten log at height 3 | $(-31.745795,-31.745794)$ |
| Minimum only, base-ten log at height 4 | $(1.407934,1.407935)$ |
| Height 4, base-ten log with $f=0.9925$ | $(-9.712169,-9.712168)$ |
| Height 4, base-ten log with $f=1$ | $(-10.656106,-10.656105)$ |
| Sum of upper bounds, $f=0.9925$ | $(0.00579140400996,0.00579140400997)$ |
| Sum of upper bounds, $f=1$ | $(0.00012937915540,0.00012937915541)$ |
| Zero-design upper bound from (1) and (4) | $(2.37661031,2.37661032)\cdot10^{-47}$ |
| Zero-design $R$ from (6) | $(6.42762872902,6.42762872903)\cdot10^{-53}$ |

In (6), coordinate independence gives the $d$th power. The integral slice contributes exactly $b_k\theta(\alpha)^d$ since $C_k(w)=1$ on that slice. Enclosing both terms before subtraction gives the last row. Exact rational arithmetic reproduced the two pivots and all 1,323 completed-square equalities for the stated example. Using both primitive lines from Part 177 and both coefficient triples $(k,\alpha,\gamma)=(2,1,1),(3,2/3,7/5)$ gave 5,292 equalities in total. Integrality of $kw$ agreed with $13\mid j$ throughout.

**Lean contract and height-one correction.** Here $3d/2<a$, $\sqrt{1+a}<54.82$, and the upper index of the Lean sum is 30. For each tested higher height, the exponential majorizes the closed-ball indicator for each lattice point, including ties. Averaging over the original plant gives `highCharge` $\le$ `ballMoment` $\le M_k$. The two-shell expression in Part 177 lies in $(6.44042091,6.44042092)\cdot10^{-14}$, so quoting that expression as strictly below $6.44\cdot10^{-14}$ rounds downward. It also bounds the capped event, while `oneCharge` here equals the minimum of one and $\Theta_H(1/12)-1$. Applying (3) at $u=1/12$ bounds this full difference by $3.635\cdot10^{-26}$. With the cap charge in $(0.00047835048013,0.00047835048014)$, this gives `smoothError` below $0.006269755$ and $0.000607730$ in profile order. Lean proves `failure_le_smoothError`. The Gaussian comparison and numerical inequalities are paper proofs. [FixedBlockCount](../../SigabaNeo/Lib/Lattices/Research/Wall1/FixedBlockCount.lean) · [FixedBlockChernoff](../../SigabaNeo/Lib/Lattices/Research/Wall1/FixedBlockChernoff.lean)

**Scope.** The probability is over the CBD plant conditional on the design and its plant-independent prefix. The $f=1$ evaluation retains the minimum and projection hypotheses. The zero design uses its own coordinate projection. Existence of a reducer-selected block near GSA passing all three tests and its frequency under a selection law both remain open. Part 171's determinant obstruction concerns its earlier uniform-floor test.
