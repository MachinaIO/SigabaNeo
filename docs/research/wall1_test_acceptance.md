# Acceptance of the width-506 terminal-block certificate

**The projection test (iii) rejects every output of the Part 108 forward pass.** One frozen coordinate axis suffices to prove this for all designs, even allowing a different unimodular witness at each height. Under a separate comparison model, a uniformly oriented 505-plane in 1023 dimensions passes (iii) with probability below $10^{-178}$. The minimum test (i) has a smaller but material cost. At the full-row model determinant, its exact physical floor rejects 13.7319% of fresh Haar lattices, rounded. Rounding the ratio to 0.998 changes that figure to 16.6336%. The coordinatewise profile test (ii) also disagrees with a determinant-matched HKZ tail model.

A fixed-block alternative is to count nonzero horizontal competitors in the capped, shifted balls. At the budget below, every accepted block has terminal failure probability below **0.000607731**. Its rejection probability is below $4.193\cdot10^{-122}$ for a fresh Haar horizontal lattice at the model determinant, for *any* fixed orientation. For physical reducer outputs the count, its lower tail of acceptance across designs, and the prefix lift require separate evidence. All new results here are on paper. [Part 180 and audit](wall1_nonintegral_classes.md) · [Frontier](../PROOF_GAP.md)

## 1. The projection obstruction on the actual first pass

Use Part 180's $N=1023$, $d=505$, $a=1.9d$, $B=1+a=960.5$, $t=d/(2B)$, $D_k=1+3tk^2$, $\gamma=3\pi^2$, $v_k=\gamma/D_k$ and $m_k=\gamma D_k^{-d/N}$. Let $P$ be the physical orthogonal projector onto the retained space $E$. Condition (iii) asks for **squared** pivots in $[m_k/c,c m_k]$ for $Q_k=\gamma(I-P)+v_kP$ with $c=7/5$.

If a unimodular basis has squared pivots in $[l,u]$ for a positive form $Q$, then
$$
 \min_{0\ne z\in\mathbb Z^N} z^TQz\ge l,\qquad
 \min_{0\ne z\in\mathbb Z^N} z^TQ^{-1}z\ge 1/u .
$$
For the first inequality, the last nonzero basis coefficient contributes at least its squared pivot. For the second, take the reversed dual basis, whose squared pivots are the reciprocals in reverse order. Unimodularity makes it a basis of the full integer dual. Consequently:

* If $e_j\in E^\perp$, its squared dual length is $1/\gamma$. This violates the upper-pivot requirement whenever $cm_k<\gamma$.
* If $e_j\in E$, its squared primal length is $v_k$. This violates the lower-pivot requirement whenever $v_k<m_k/c$.

Both strict inequalities hold already at $k=5$ and persist through $k=30$. In the horizontal-first, no-lookahead Part 108 pass the very first full window consists of 506 of the 511 orthogonal $q$-axes. Every exact shortest vector is a signed coordinate axis times $q$. Its direction stays frozen through the terminal projection. Thus **the fraction passing (iii) is exactly zero and the original joint rejection probability is one** for this reducer. This does not require Part 117's high-probability result on the *next* graph appends. The Part 180 zero-design example likewise succeeds by the unrestricted theta bound while failing the balanced-pivot condition. A new tour that revisits the first prefix, or global preprocessing that changes the first window, changes the argument's hypothesis. [Part 108](wall1_first_tour.md) · [Part 117](wall1_idea_round2.md) · [Part 180, equations (2), (4), (5)](wall1_nonintegral_classes.md)

**Uniform orientation benchmark.** Even with no exact frozen axis, (iii) is restrictive. At $k=30$ put $D=D_{30}$ and $b=cD^{-d/N}$. The first column $z$ of any witness must satisfy
$$
 j=\|z\|^2\le bD<38.916,\qquad
 \|(I-P)z\|^2/j\le x_j=(b/j-D^{-1})/(1-D^{-1}).
$$
For a uniform Grassmannian plane and fixed $z$, the fraction on the left has law $X/(X+Y)$ for independent chi-squares with $N-d$ and $d$ degrees of freedom. Put $p=(N-d)/N$. For $0<x<p$, its lower-tail probability is at most $\exp[-N D_{\rm Ber}(p\Vert x)/2]$. This follows by applying the exponential Markov bound to $(1-x)X-xY\le0$ at tilt $(p-x)/(2x(1-x))$. Each integer vector of squared norm $j$ is a sum of exactly $j$ signed unit steps, by padding its shortest such expression with opposite pairs. There are at most $\binom{2N+j-1}{j}$ multisets of these steps. Summing the product of this bound and the beta-tail bound at $x_j$ over $1\le j\le38$ gives a base-ten logarithm in $(-178.281,-178.280)$. This upper bound permits **every** integer first column and uses just one of 26 heights. It is a reference probability for a real plane. For a general multi-tour q-ary reducer the fraction is unknown.

## 2. The minimum, with and without rounding

Let $h=(\det H/V_d)^{1/d}$, where $V_d$ is the unit-ball volume. For a fresh Haar lattice scaled to the specified determinant, the ball of radius $rh$ has normalized volume $r^d$. Counting one representative per sign pair gives mean $m=r^d/2$. The finite-rank enclosures below are for the **probability** of $\lambda_1<rh$. Boundaries have zero Haar mass by Siegel integration.

| Radius input | Finite-rank lower bound | Finite-rank upper bound |
|---|---:|---:|
| $r=0.998$ | 0.1663364761842 | 0.1663364761850 |
| $r=54.82/h$, full-row model $h=54.95252663536\ldots$ | 0.1373186911450 | 0.1373186911452 |
| $r=0.95$ | $2.81443\cdot10^{-12}$ | $2.81444\cdot10^{-12}$ |

For reproducibility, apply Bonferroni to the nonzero half-ball count through orders 8 and 9. In Kim's Proposition 1 the ordered factorial moment of order $j$ lies between $m^j$ and $m^j+e_j$, where, with $u=\lfloor j^2/4\rfloor$,
$$
 e_j=\big[2\,3^u(\sqrt3/2)^d+21\,5^u2^{-d}\big]\,(1+m)^j .
$$
The rank condition $d\ge u+3$ holds. Subtract $\sum_{j=1}^9 e_j/j!$ from the eighth Poisson partial sum for a lower bound and add it to the ninth for an upper bound. The Poisson volume heuristic $1-e^{-r^d/2}$ explains why rounding the radius matters. At a fixed nonextreme quantile the relative fluctuation is of order $1/d$, since $\log(\lambda_1/h)$ is the log volume coordinate divided by $d$. [Kim, Proposition 1](https://arxiv.org/pdf/1410.2005) · [Södergren, volume-process limit](https://arxiv.org/abs/1001.3623) · [Part 107](wall1_lit_random_bases.md)

Part 136's $1.372\cdot10^{-5}$ is for reselecting a suitable primitive line from a Haar **parent** at ratio 0.954. Part 105 treats a single selected quotient. Part 151 splits a penultimate physical event, Part 161's 0.990 cutoff is on a *candidate's* radius, and Part 162 additionally imposes shortestness and both gates. None gives the marginal CDF in the table for a selected q-ary terminal lattice. Its physical determinant also varies. Part 114 gives a first-pass GH lower bound of 28.8095 and a zero-log-error comparison of 35.178. Both differ substantially from the full-row GSA value used to convert 54.82. The marked last-draw law in Part 120, the conditional drift and dual-cusp results in Parts 139/142, and the later selected-count recursions leave this distinction in effect. [Restart audit](wall1_restart_certificate.md) · [Selection law](wall1_selection_law.md) · [Determinant drift](wall1_idea_drift.md) · [Band count and audit](wall1_band_plane_hits.md) · [Upper-band quotient](wall1_upper_band_quotient.md)

**Sensitivity of the actual Part 180 inequality.** Replace only its physical minimum by $L=52.20$ ($0.94991083h$ rounded at the model determinant). Keep $g_i\ge0.9925g_i^0$ and the original pivot hypothesis. Applying Part 180 (3) at $u=1/12$ bounds $\Theta_H(1/12)-1$ by $2.001\cdot10^{-15}$. Height zero is excluded since $L^2>B$. In (1), take the smaller of the packing and GS upper bounds on the intrinsic theta as in Corollary 2. For heights 2, 3 and 4 the base-ten logs of the resulting upper bounds lie in $(-31.128,-31.127)$, $(-21.006,-21.005)$ and $(-9.713,-9.712)$. The full heights 2–30 sum is below $0.0057914040100$. Including the audited cap $0.00047835048014$ gives **terminal failure below 0.006269755**, at the original error precision. The lower minimum alone costs essentially nothing in this conditional bound. The zero acceptance in §1 still applies if (iii) is kept. [Part 180, inequalities (1)–(5) and audit](wall1_nonintegral_classes.md)

## 3. What the coordinatewise GS test asks of a tail

Bai–Stehlé–Wen measured head concavity, including a BKZ-45 example at tour 50. A quantitative comparison for the *tail* can be made without extrapolating that head measurement. The Chen–Nguyen 45-dimensional unit-covolume HKZ tail table gives final log-base-two length $-0.886666930030433$. Write $s$ for the Part 180 slope parameter, so successive GSA lengths have ratio $e^{-2s}$. At equal last-45 determinant the GSA last length is $e^{-44s}$ in geometric-mean units. The modeled final ratio is $2^{-0.886666930030433}e^{44s}\in(0.62729,0.62731)$. To meet even the last coordinate of (ii) with that tail shape would require the last-45 **geometric mean** to be over 1.5821 times its GSA counterpart. [Bai–Stehlé–Wen, slides 8–9](https://asiacrypt.iacr.org/2018/files/SLIDES/MONDAY/514/1330-1445/Bai_slides.pdf) · [fpylll, Chen–Nguyen tail constants and normalization](https://raw.githubusercontent.com/fplll/fpylll/master/src/fpylll/tools/bkz_simulator.py)

Alternatively match the whole rank-505 determinant. In a *model* of a full HKZ suffix, start at $S=\log\det H_{\rm GSA}$, assign log length $u_j=(S-\log V_j)/j$ at rank $j$, and update $S\gets S-u_j$ down through rank 46. Append the 45-dimensional table scaled by $e^{S/45}$. The ratios to the corresponding Part 180 coordinates are 1.0024, 1.2355, 1.3489, 0.8392 and 0.4734 at remaining ranks 505, 400, 250, 100 and 46. The last ratio is **0.1977**. These are normalized shape calculations. They give neither simultaneous confidence intervals nor a width-506 experimental frequency. Part 177 also exhibits a physical block with profile inside the 0.75% tolerance and minimum below 1.837. A profile alone does not distinguish the relevant events. [Part 177 and audit](wall1_aliasing.md)

## 4. A basis-independent replacement with a reference acceptance bound

For a fixed physical block $(E,H)$ let $y=PX$ for a fresh CBD(3) vector and $Z=\|y\|^2$. Define the following score using the **known distribution**, independently of the true plant:
$$
 C(E,H)=\mathbb E_X\!\left[
 {\bf1}_{Z\le a}\sum_{k=0}^{30}
 \#\{0\ne h'\in H:\ \|h'+ky\|^2+k^2\le1+Z\}\right].
$$
**Accept when $C(E,H)\le0.00012938$**, or when a certified upper bound meets this value. This uses Part 180's tighter reported charge as the allowance. There is no GS profile or balanced-pivot condition. The score is finite for a rational physical block: the CBD support is finite, the squared comparisons are rational and, on the cap, $\|h'\|\le30\sqrt a+\sqrt B$. Feasibility of exact evaluation at rank 505 is open. One may use the existing fixed-block estimates as upper bounds where they succeed. [Part 177, finite primal test](wall1_aliasing.md) · [Part 180, conditional bounds](wall1_nonintegral_classes.md)

**Fixed-block guarantee.** On the cap, a competing vector can be signed to have nonnegative height at most 30. A vector with zero horizontal coefficient is either zero, the designated line at height one, or a longer multiple of it. Every competitor therefore contributes to the displayed count, including a competitor tied in length. Markov's inequality and the Part 180 cap bound give terminal failure $\le 0.00047835048014+C(E,H)<0.000607731$ on acceptance. The cap is paid once. The same proof at allowance $0.005791405$ gives failure below $0.006269756$ and contains every block satisfying the lowered-floor sufficient conditions of §2: height zero contributes nothing, the expected number at height one is bounded by the per-vector CBD sum $\Theta_H(1/12)-1$, and the higher counts by Part 180 (1). On the physical zero design with the Part 180 prefix, $H=q\mathbb Z^{505}$ and $q>30\sqrt a+\sqrt B$, so $C=0$. This also occurs on the Part 108 pass at $A=0$: after the initial $q$-axis phase each new graph column is a unit axis and is selected.

The omitted origin matters when computing a comparison mean. A capped ball enlarged to radius $\sqrt{B-k^2}$ can include the origin at high heights even though that multiple is longer than the plant. The current Lean definition of `ballMoment` counts the origin in such an enlarged ball. The score above has a direct paper proof and would need its own comparison lemma for the formal restart chain. [FixedBlockCount](../../SigabaNeo/Lib/Lattices/Research/Wall1/FixedBlockCount.lean) · [FixedBlockRestart](../../SigabaNeo/Lib/Lattices/Research/Wall1/FixedBlockRestart.lean)

**Reference acceptance theorem.** Fix any $E$ and any covolume $\Delta$. Sample $H$ in $E$ with scaled intrinsic Haar law, independently of $X$. For fixed $y,k$ on the cap, the mean nonzero count in a translated ball is its volume divided by $\Delta$, by Siegel integration. Averaging the finite sum and enlarging the radii gives
$$
 \mathbb E_H C(E,H)\le S(h)=\sum_{k=0}^{30}
 \left(\frac{\sqrt{B-k^2}}{h}\right)^{505},
 \qquad h=(\Delta/V_{505})^{1/505}.
$$
Thus the reference rejection probability is at most $\min(1,S(h)/0.00012938)$. At the full-row model determinant $S(h)<5.425\cdot10^{-126}$ and rejection is below $4.193\cdot10^{-122}$. Even at the separate comparison value $h=35.178$, rejection is below $2.814\cdot10^{-24}$. At $h=28.8095$ the bound on probability is one. This theorem allows coordinate-aligned $E$ and arbitrary choices of basis for $H$. Plausibility for a BKZ output is **conjectural**: its embedded $H=P L_0(A)$ and $P$ come from the same design, whereas the reference proof averages intrinsic shapes conditional on the plane. Part 163 in particular rules out an unrestricted density comparison for the discrete selection law. [Siegel mean value formula, Theorem 1](https://arxiv.org/pdf/1410.2005) · [Part 163](wall1_restart_haar_ratio.md)

## 5. The remaining reducer statement and checks

Specify the input order, preprocessing, tours or stopping rule, oracle and ties, and distribution of independent trial coins $\omega$. For design $A_i$ define $G_i$ to be the event that the selected block meets the score budget and that the **same output prefix** meets the chosen Part 47 lift allowance $\ell$. If using a sufficient upper bound in place of the exact score, $G_i$ must include successful certification by that bound. Define $\delta_i=\Pr_{A_i,\omega}(G_i^c)$ and $\alpha(A)=\Pr_\omega(G\mid A)$. With $\epsilon=0.000607731$, sufficient statements for 99% end-to-end success are
$$
 \prod_i\delta_i\le0.01-\epsilon-\ell
 \quad\text{(independent disjoint blocks)},\qquad
 \mathbb E_A(1-\alpha(A))^T\le0.01-\epsilon-\ell
 \quad\text{(conditionally iid shared-design trials)}.
$$
For two equal block bounds this permits $\delta_i\le\sqrt{0.01-\epsilon-\ell}$, about 0.09691 before the lift charge. With the looser conditional bound 0.006269756 it permits only about 0.06108 before that charge. Disjoint blocks drawn from a total of 511 rows use their **own** ambient dimensions and determinants. Two independent copies of the full-row GSA calculation do not describe that split. For a shared design, $\alpha\ge1/T$ on 98% of designs alone is insufficient: the other 2% can have zero acceptance, and the passing group can still exhaust with probability $(1-1/T)^T$. An explicit sufficient quantile statement is $\Pr(\alpha<x)+(1-x)^T\le0.01-\epsilon-\ell$. No selected-output bound of either required size is proved here. [Part 136, Theorems 1–2 and audit](wall1_restart_certificate.md) · [Disjoint-block contract](../../SigabaNeo/Lib/Lattices/Research/Wall1/FixedBlockRestart.lean)

**Arithmetic checks.** Calculations used 65–70 decimal digit outward intervals in scratch space. For §2 use $V_0=1$, $V_1=2$, $V_j=2\pi V_{j-2}/j$ or the half-integer factorial formula. For the lowered-floor calculation use the Part 180 numerical proof with $L=52.20$, reflecting theta arguments below $\pi$ and truncating at $|n|=8$ with two-sided tail at most $2e^{-81s}/(1-e^{-19s})$. For §1 the finite sum has 38 terms. In an exact small check, all 360 unimodular two-by-two matrices with entries in $[-4,4]$ for $Q=\operatorname{diag}(25,1)$ had a squared pivot at least 25 and one at most 1. For the count check, take the unit line $(3,4)/5$, horizontal spacing 3, $a=4$, and two independent CBD(3) coordinates. In units of $1/4096$, the cap exception was 378, capped failure mass 490, and capped expected competitor count 670. Replacing $1+Z$ by $1+a$ inside the count increased it to 2804. The enumeration used exact rational squared distances and the binomial CBD masses.

## Audit

**Verdict — MINOR CAVEATS.** The deterministic obstruction and both fixed-block failure budgets hold. Two qualifications matter when using the revised test. The Haar rejection bound applies to the exact score predicate. An implementation using a looser upper bound can reject more often. The score supplies the terminal probability hypothesis used in a restart proof on paper. The current Lean theorem requires a different acceptance predicate.

**First pass.** In Part 108 the span of the frozen directions grows at every step. Every shortest vector of the initial cubic window is a signed $q e_j$, so the terminal plane satisfies $Pe_j=0$ for at least one integer unit vector, for every design and every tie choice. For a witness $U$, the columns of $U^{-T}$ in reverse order span the integer dual and have squared pivots at least $1/(c m_k)$ in the inverse form. The last nonzero coefficient of any integer combination gives the same lower bound on its squared length. But $e_j^T Q_k^{-1} e_j=1/\gamma$, and $c m_5/\gamma\in(0.31357084,0.31357085)$. Height 5 alone rules out every witness. The acceptance probability for (iii) on this pass is exactly zero. For the separate uniform-plane comparison I obtain $-178.280160<\log_{10}(\text{union bound})<-178.280159$.

**Independent numerical checks.** I used 320-bit outward-rounded MPFI intervals, reconstructed the determinant from the 505 model lengths, and computed the ball volumes by the two-step recurrence. Kim’s ordered factorial moments count distinct points in a half-ball. Dividing by $j!$ gives the binomial moments needed for the order-8 and order-9 Bonferroni bounds. The following are probability enclosures at $h=54.952526635359789\ldots$. [Kim, Proposition 1](https://arxiv.org/pdf/1410.2005)

| Minimum floor | Haar rejection probability |
|---|---|
| $54.82$ | $(0.13731869114505,\ 0.13731869114515)$ |
| $0.998h$ | $(0.16633647618429,\ 0.16633647618490)$ |
| $52.20$ | $(2.68412648,\ 2.68412649)\cdot10^{-12}$ |

For $L=52.20$ I recomputed the packing and profile bounds using theta reflection and a direct sum through $|n|=6$, with omitted tail at most $2e^{-49s}/(1-e^{-s})$ at the reflected argument $s\ge\pi$. The height-one upper bound is below $2.000193\cdot10^{-15}$. The heights 2–30 sum of upper bounds lies in $(0.0057914040099622,0.0057914040099623)$. Including the cap gives a total below $0.006269754490097$, under the retained profile and pivot hypotheses.

**Tail model.** The fpylll table records mean base-two log *lengths* at unit covolume. Its last entry gives a last-length ratio in $(0.62729944,0.62729945)$ when the two rank-45 tails have equal covolume, and a required geometric-mean multiplier in $(1.58217899,1.58217900)$. Matching the whole rank-505 determinant and applying the stated suffix recursion instead gives $(0.19771238,0.19771239)$ for the last ratio. These are comparisons of model profiles. A frequency for condition (ii) on width-506 outputs would require their joint profile law. [Chen–Nguyen constants in fpylll](https://raw.githubusercontent.com/fplll/fpylll/master/src/fpylll/tools/bkz_simulator.py)

**Revised score and Haar rejection.** On the cap, sign selection covers all heights through 30. At $h'=0$ the squared length is $k^2(1+Z)$, so excluding that term removes only the zero vector, the signed plant and its longer multiples. The closed-ball count therefore dominates the indicator of every capped Part 94 failure, including ties. For a fixed plant-independent block, adding the Chernoff cap once to the score allowance gives an upper bound in $(0.0006077304801320,0.0006077304801321)$. For each fixed plane, Siegel integration applies to each translated ball with its center held fixed during the lattice average. At the model determinant I obtain $S(h)\in(5.42403872,5.42403873)\cdot10^{-126}$ and $S(h)/0.00012938\in(4.19233167,4.19233169)\cdot10^{-122}$. This bounds $\Pr_H[C>0.00012938]$. For a verifier using $U\ge C$, its rejection event $U>0.00012938$ can be strictly larger. The stated Haar estimate for such a verifier would require control of that additional rejection probability. The exact toy counts in §5 also reproduce. [Siegel formula, Theorem 1](https://arxiv.org/pdf/1410.2005)

**Lean and reducer scope.** Lean's `countAccept` requires `MinFloor L`, `smoothError a L ≤ ε`, and the lift sum on the returned prefix. Its higher-height `ballMoment` averages an enlarged ball over all plants and includes the origin when eligible. A proof that $1-\mathrm{success}\le\mathrm{normChernoff}+C$ would give the terminal estimate for a score-based instance of the generic restart inequality. It would not establish an upper bound on `smoothError` itself. The existing `restartCount_lwe` consequently cannot be invoked from score acceptance alone. For independent disjoint row blocks the product formula uses rejection of the actual joint score-and-lift test. For repeated trials on a shared design the exhaustion term is the stated conditional-iid moment. In both cases selection must remain plant-independent. The probability that the specified reducer and verifier meet both budgets on the same output prefix remains open. [FixedBlockChernoff](../../SigabaNeo/Lib/Lattices/Research/Wall1/FixedBlockChernoff.lean) · [FixedBlockRestart](../../SigabaNeo/Lib/Lattices/Research/Wall1/FixedBlockRestart.lean) · [RestartReduction](../../SigabaNeo/Lib/Lattices/Research/Wall1/RestartReduction.lean)
