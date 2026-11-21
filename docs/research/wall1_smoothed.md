# Smoothing an exact block trajectory

Uniform tie-breaking removes the axis discrepancy in the three-dimensional example of [Part 14](wall1_dynamics.md). It fails one step later in dimension four. A single generic metric also need not restore a covolume-only transition, even when conditioning on the exact perturbed covolume. The two examples below use iid binary checks.

## Fresh uniform choices at each insertion

Take the kernel in integers of a uniform binary row $(a,b,c,d)$. Use consecutive coordinate blocks of size two, starting from a basis adapted to the coordinate flag. Insert a uniformly chosen shortest line at each step, using fresh coins. Complete the insertion within its block. Consider the histories $H_{12},H_{13}$ that first select axis 1 and then select projected axis 2 or 3, respectively. The third block is the projection of the full lattice off the two selected axes. Here and below an axis selection in these histories means selecting its **unit** generator.

In each history both deleted coefficients vanish. Thus the last block is a plane parity kernel. Write $r$ for its remaining coefficient among the first three. Its area is two exactly when $(r,d)\ne(0,0)$, and its squared minimum is two exactly when $(r,d)=(1,1)$. Indeed the latter kernel excludes both unit axes and contains a diagonal. The likelihoods of the histories given the input are

| History | Required zeros | Remaining coefficient | Likelihood at zero | Likelihood at one |
|---|---|---|---:|---:|
| $H_{12}$ | $a=b=0$ | $c$ | $1/4$ | $1/2$ |
| $H_{13}$ | $a=c=0$ | $b$ | $1/4$ | $1$ |

To check the table, when all three coefficients vanish each visited plane has two shortest axes. For $(a,b,c)=(0,0,1)$ only the first decision is tied. For $(0,1,0)$ both decisions are forced. Projection after the first unit selection drops its coordinate, so this calculation is independent of the within-block completion. If the two likelihoods are $s,t$, the desired conditional probability given area two is $t/(s+2t)$ by summing the three nonzero pairs. The answers are **2/5 and 4/9**, a gap of $2/45$. This also covers independent uniform choices among primitive lines of length at most $h\lambda_1$ for every $1\le h<\sqrt2$. On a plane with a unit vector, every longer vector has length at least $\sqrt2$. A unit selection is impossible when its coefficient is nonzero.

## One continuous metric for both queries

Return to the three-dimensional binary row $(a,b,c)$ and the two overlapping blocks of Part 14. Fix $0<e<1/100$. Sample a symmetric matrix $B$ uniformly in the Frobenius ball of radius $e/10$ about $\mathrm{diag}(1,1+e,1)$, independently of the check. Use the squared norm matrix $G=S B$, with $\log S$ independent and uniform on $[0,10e]$. This full-dimensional perturbation tends uniformly to the identity. The anisotropy of its center is intentional.

Write $X,Y$ for first selecting unit axes 1 and 2. The eigenvalues of $B$ lie in $[1-e/10,1+1.1e]$. Thus a Euclidean squared length at least two loses to any available unit, and $B_{11}<B_{22}$ forces axis 1 when both are available. Consequently $X$ means $a=0$, and $Y$ means $a=1,b=0$. When both coefficients are one neither unit is possible. These histories depend only on the row.

For selected unit $i$, let $k$ be the index of the residual binary plane kernel (one or two). In coordinates modulo that unit the quotient metric is the Schur complement of $G_{ii}$. Its covolume is
$$
 D=k S C_i,\qquad C_i=\sqrt{\det B/B_{ii}}.
$$
Indeed the residual integer coordinates range over precisely that plane kernel. The quotient quadratic form for $B$ is the minimum over real lifts of the squared norm, so it obeys the same two spectral bounds as $B$. Hence $1-e/10\le C_i\le1+1.1e$ by taking the square root of its two-dimensional determinant.

Consider the interval $J=2[\exp(2e),\exp(8e)]$. Index one cannot reach it since $\exp(10e)(1+1.1e)<2$. For index two, every possible $C_i$ gives the same density $1/(10eD)$ throughout $J$, by the log-uniform scale and $-2e<\log C_i<2e$. Thus conditioning on the *measured* area at almost every $D\in J$ leaves the relative weights of all index-two rows within either history unchanged. This interval has positive probability. The event that the perturbed terminal squared minimum exceeds $3/2$ distinguishes residual row $(1,1)$ exactly. Its minimum is at least $2(1-e/10)$ there, and an available unit elsewhere has squared norm at most $\exp(10e)(1+1.1e)<3/2$.

Given $X$, the possible index-two residual rows are $(0,1),(1,0),(1,1)$ with equal weights. Given $Y$ they are $(1,0),(1,1)$ with equal weights. The conditional tail probabilities are therefore **1/3 and 1/2** on the same interval of perturbed areas. Any common area-dependent prediction incurs absolute error at least $1/12$ on one history at almost every such area. This disproves sufficiency under generic smoothing in general. It leaves open more restrictive perturbation laws, including orthogonally invariant noise centered at the identity.

## What genericity gives for an adaptive prefix

Fix a full-rank lattice and draw a metric with a density on positive definite forms. Almost surely every projected lattice block with lattice-generated prefix has a unique shortest unoriented line simultaneously. For a fixed prefix choose real coordinates adapted to its span. Squared lengths of quotient classes are rational functions of the metric entries by the Schur complement formula, with positive denominator. Equality for two classes distinct up to sign gives a nonzero polynomial after clearing denominators. Indeed one may choose a block diagonal metric with arbitrary positive quotient form, and the two rank-one outer products differ. The polynomial zero set is null (induct on the number of variables using the univariate root bound and Fubini). There are only countably many lattice-generated prefixes and pairs of classes. This argument applies conditional on each discrete lattice input when the noise has a conditional density.

For a fixed finite schedule of exact shortest-line queries and a metric-independent completion rule given the selected coefficients, the discrete transcript is locally constant at each such tie-free metric. For one fixed block the quotient lattice is discrete, since the prefix is spanned by part of a lattice basis. On a sufficiently small metric neighborhood, all quotient squared norms stay between one half and twice their center values by minimization over lifts. Only the finitely many classes within four times the center squared minimum can then compete. Strict comparisons against the other lines persist locally, and induction applies to the finite schedule. Averaging hence weights transcripts by the noise mass of their decision regions. For atomic rational perturbations the null-set argument alone supplies no probability estimate.

Neither uniqueness nor local stability identifies the minimizing line with a marked plant. A fixed prefix also preserves the divisibility of the plant class under a change of quotient metric. The missing random-input estimate concerns the joint probability that the selected quotient contains a nonzero primitive plant class and every competing line has larger minimum. These examples give no block-size or running-time bound for the planted ensemble.


## Independent audit (Nov 2026)

Verdict: **correct**. (1) re-enumerated (2/5 vs 4/9); (2) generic uniqueness (nonzero tie polynomial, countable union of null
sets) and local stability (quotient forms within factor 2, finitely many competitors) are valid for metric-independent
completions; (3) checked by hand and by Monte Carlo (e = 0.009, 200k samples: ≈ 0.331 vs 0.501). Nit: lattice-generated
prefixes suffice for discreteness (primitivity not needed). Cross-reference: the audit of wall1_coupling.md found that in the
4-dimensional example conditioning on the full in-block profile removes the discrepancy; whether the same holds for the
anisotropic example of (3) is being examined in docs/research/wall1_profile.md.

## Small linear perturbations of the rank-1023 null family

Let $m=511$, $n=512$, $N=m+n$, $q=3329$, and $L=q^{-m/N}L_0$ for the graph kernel of Part 52. Work on the determinant-one space $X_N$ with Haar probability $\mu$. Write $k=N-\beta$ with zero-based GS indices. At this finite rank there is a quantitative obstruction to mixing by a near-identity perturbation, even after averaging over **all** graphs.

**A common-vector test.** Every graph kernel contains $q\mathbb Z^N$. In particular $v=q^{n/N}e_1$ belongs to every normalized lattice and has length $c=57.92666\ldots$. Let $T$ be any determinant-one perturbation, possibly input-dependent, and $P$ the law of $TL$. If $\Pr(\|(T-I)e_1\|\le u)\ge1-\delta$, then
$$
 d_{\rm TV}(P,\mu)\ge 1-\delta-V_N(cu)^N,\qquad
 V_N=\pi^{N/2}/\Gamma(1+N/2).
$$
Indeed use the event of a nonzero lattice point in the ball centered at $v$ of radius $cu$. The point $Tv$ witnesses it under the coupling. Under Haar its probability is at most the expected nonzero count, exactly the ball volume by Siegel's formula. The argument applies to the full Hecke family of this Smith type as well. [Siegel mean value formula](https://www.sciencedirect.com/science/article/abs/pii/S0022314X22000117) · [Hecke family](wall1_hecke_transfer.md)

Here $V_N^{-1/N}/c=0.1341332\ldots$, so at $u=0.10$ the volume is below $10^{-130}$. For a law supported in $\|T-I\|_{\rm op}\le u$, even TV distance $0.01$ requires $u\ge0.99^{1/N}V_N^{-1/N}/c$. This is a necessary radius, with no sufficiency assertion above it. A walk with many small steps obeys the same obstruction whenever its **product** stays near the identity. Mixing estimates for escaping products alone give no control of their final distortion. Part 52's fixed-rank convergence takes $q$ to infinity. Its finite sharp-cutoff power $q^{-511/1023^2}\simeq0.996$ supplies no small error here. The common-vector test uses orientation. A terminal event is rotation invariant and can have small discrepancy even at TV distance near one.

**Transport of a marked basis.** Suppose $a\le s_{\min}(T)\le s_{\max}(T)\le b$, $a>0$, and set $K=b/a$. For every prefix span $W$ and vector $x$,
$$
 a\,d(x,W)\le d(Tx,TW)\le b\,d(x,W).
$$
Take the infimum of the singular-value inequalities for $x-w$ over $w\in W$. This simultaneously bounds every GS length of the transported basis and every projected competitor in every full or truncated window. Thus an exactly reduced basis becomes $K$-approximate in the block-head length tests. For exact transport it suffices that the least competing length on a different line divided by the head length exceed $K$ in every window. This is Part 25's squared-length margin after centering the log metric by a scalar. Earlier-column integer size reduction can be redone without changing any projected window lattice or GS length. Preserving an implementation's entire sequence of branch decisions requires its other margins as well. The standard basis of the cubic lattice has a tied first window and an arbitrarily small diagonal stretch of the head breaks that test. There is no positive uniform exact radius over reduced bases of arbitrary inputs. Part 64 measures terminal lengths after search at ranks up to 60 and provides no lower quantile for these margins at 1023. [Part 25](wall1_stability.md) · [Part 64](wall1_bad_bases_experiment.md)

For $A=I+\sigma G$ with iid standard normal entries, on $t=\sigma\|G\|_{\rm op}<1$ the determinant is positive by continuity along the segment from $I$. The raw singular values lie in $[1-t,1+t]$. For $T=A/(\det A)^{1/N}$ one may take $a=(1-t)/(1+t)$, $b=1/a$, while the actual condition number is at most $(1+t)/(1-t)$. Also $\|T-I\|_{\rm op}\le 2t/(1-t)$ by expanding around the scalar identity. On the exceptional event one may use absolute determinant normalization for the lattice or resample, accounting for its probability. For an elementary explicit tail take two $1/4$-nets of the unit sphere of size at most $9^N$ (disjoint-ball packing). Approximating the two maximizing vectors costs at most half the operator norm, and each fixed bilinear test is standard normal. Hence except with probability $\delta$,
$$
 \|G\|_{\rm op}\le 2\sqrt{2\log(2\cdot9^{2N}/\delta)}.
$$
This gives $1+O(\sigma\sqrt{N+\log(1/\delta)})$ multiplicative GS distortion in the small-noise regime. For example at $\delta=0.01$, $\sigma=0.00024$ gives $t<0.046$, so the normalized law has TV distance at least $0.99-10^{-130}$ (using the displayed bounds on the good event). The net bound is conservative.

**What transfers.** Let $E_\beta(r)$ mean that some exactly reduced basis has $g_k<r$. Part 82 certifies $\mu(E_\beta(r))<0.01$ per width, with determinant-one radii conservatively rounded down as follows.

| $\beta$ | 406 | 506 | 647 | 800 |
|---|---:|---:|---:|---:|
| $r$ | 0.00654 | 0.01696 | 0.04255 | 0.15090 |

If $P(E_\beta(r))\le\mu(E_\beta(r))+\epsilon$, a fresh exact reducer on $TL$ has $g_k\ge r$ with probability at least $0.99-\epsilon$. For a selected exact basis on $L$, if its transport passes all exact tests and $s_{\max}(T)\le b$ except on mass $\eta$, its original $g_k\ge r/b$ with probability at least $0.99-\epsilon-\eta$. To quantify over all original bases via this implication requires simultaneous transport or control of a measurable bad witness. Approximate transport alone would require a Haar bound for approximate heads. Part 46's shortest-line disintegration includes avoidance and selection weights, and an arbitrary finite-width output needs its own selector. Conditioning on a trajectory can amplify discrepancy by the inverse probability of the conditioning event. [Part 82 certificates](wall1_small_d_caps.md) · [Part 46 disintegration](wall1_haar_prefix_law.md)

One unconditional smoothed bound is available directly. Part 48 gives a physical ambient minimum exceeding 443.0664 with probability at least 0.99 (using its stated threshold). Its deterministic propagation applies anew to **every exact output on the perturbed lattice**. With the Part 48 coefficients $P_k$, this gives $g_k(TL)\ge a\,443.0664\,q^{-m/N}e^{-P_k}$ on mass at least $0.99-\Pr(s_{\min}(T)<a)$. This uses no continuity of a basis selector. It inherits the ambient propagation loss. [Part 48](wall1_null_terminal.md)

**Randomize, round, then reduce.** For a physical column basis $B$, use grid spacing $h$ and integer input $C=\operatorname{round}(TB/h)$ entrywise. Then $hC=(I+F)TB$ with $F=(hC-TB)(TB)^{-1}$ and $\|F\|_{\rm op}\le z=hN\|(TB)^{-1}\|_{\rm op}/2$ by the Frobenius bound. Choose $h$ for $z<1$. Any unimodular output change $U$ on $C$ yields the original basis $BU$. In physical length units every GS length of $hCU$ lies between $(1-z)a$ and $(1+z)b$ times its counterpart in $BU$, uniformly even for adaptively selected $U$. Exact heads on $C$ give at most $K(1+z)/(1-z)$-approximate heads on $B$. In the other direction, a strict margin exceeding $(1+z)/(1-z)$ suffices to retain an exact head when passing from $TB$ to $hC$. Mesh choice must account for basis conditioning. Rounded normalized inputs have countable support and TV distance one from Haar. Eventwise comparison before rounding plus a decision-boundary estimate, or a direct analysis of rounded inputs, is needed. The integer coefficients map back exactly, but a target vector's primitivity, survival in the chosen quotient, and competition there must still be checked for any recovery claim.

**Gap at rank 1023.** Genuinely small near-identity motions fail the proposed full-space mixing test. No proved width-specific margin law and event-specific discrepancy bound identify a compatible $\sigma$ outside that obstruction. Small condition number by itself allows large rotations, and failure of the oriented TV test supplies no lower bound on terminal-event discrepancy. Neither a near-GSA lower quantile nor an impossibility theorem for every noise scale or selector follows. Randomizing first removes the need to preserve the original reducer's transcript for a guarantee on the new input, but leaves the law of its selected terminal block and the accuracy of pullback to be established.

### Audit note for the appended section (Nov 2026)

Independent audit (Codex): CORRECT WITH MINOR ISSUES.

* **Common-vector TV bound.** Verified. V_1023(0.1c)^1023 ≈ 3.391·10⁻¹³¹, and t < 0.04554 at the stated Gaussian parameters.
* **Transport and strict margins.** Verified, including adaptive U.
* **Correction.** "A terminal event is rotation invariant" holds for the existential event E_β(r). For a particular selector's
  returned length, it additionally needs the selector to be rotation-equivariant, or its output law to be invariant.
