# What a dual minimum can certify about a selected plane

At the original Part 142 radii, the probability that **any** of the 408 raw dual floors fails is less than $8.147\cdot10^{-14}$ in the marginal restart. The exit fits the budget. The obstruction is the implication on its complement. A small plane forces a short vector in a complementary dual section, with an exponent equal to the **codimension of the plane**. Here that exponent is 503. There are rank-506 Euclidean lattices satisfying the determinant, upper band, both shortest-line comparisons and both numerical gates even with dual minimum greater than $1/2$. Their role is to test a deterministic implication. Their probability under the finite restart is unknown.

## Which lattice carries the plane?

Use $q=3329,\ b=506,\ d=505,\ c=477/500$, and write $V_j$ for the Euclidean unit ball volume in dimension $j$. Immediately before draw 406, the old lattice $M$ has rank $d$ and covolume $D$. The unit-height window $W=(M,0)+\mathbb Z(\widetilde U,1)$ has rank $b$ and covolume $D$. Its designated shortest generator $v$ has length $s=\rho g$, where $g=(D/V_b)^{1/b}$. Set
$$
 L=P_{v^\perp}W,\quad \Delta=D/s,\quad h=(\Delta/V_d)^{1/d},\quad
 x=\text{designated shortest generator of }L,\quad t=|x|,\quad Q=P_{x^\perp}L .
$$
The gates are $1<t\le r(h)=\sqrt{1+c^2h^2}$ and $\lambda_1(Q)<u=ch\,t^{-1/d}$. A primitive line of length $p<u$ in $Q$ gives a saturated plane of area $tp<tu$ through $x$ in $L$, or a saturated rank-three lattice in $W$ of covolume $stp$. The upper-band mass $P$ also requires nonzero fresh height, $g<203.888$, and $0.990<\rho\le1.097193$. The inherited mass $p_a$ requires horizontal lifts of the two winners and a witness. It includes the near-lift and shrunken-lift cases and has no upper-band restriction. Both selections use the same mark at 406. The independent CBD(3) plant and draw 407 do not enter. [Part 161](wall1_band_plane_hits.md) · [Witness correspondence](wall1_upper_band_quotient.md) · [Inherited event and audit](wall1_shrunken_lifts.md) · [Part 168 definitions](wall1_subset_ustat.md)

For a projection onto a subspace $E$, the metric dual in $E$ is the section of the original dual by $E$. For an append and projection, a dual vector has the form $(\xi,j-\langle\xi,\widetilde U\rangle)$ perpendicular to the winner, with $\xi\in M^*$ and $j\in\mathbb Z$. If $\xi=0$, a nonzero such vector has length at least one and the winner is horizontal. Thus every floor $R\le1$ propagates, irrespective of ties. For a vertical winner the full old minimum propagates. At a horizontal step only monotonicity of the minimum truncated at one is guaranteed. The integral mark-annihilator has minimum at least one, but is a **subgroup** of the retained dual. Short vectors with nonzero labels are precisely the issue below one. These statements use the Lean declarations named `metricDual_projectedModule`, `lattice_retained_dual_minimum`, `graph_markLabel_ker` and `integerSection_minimum`. The new estimates below are paper results. [ProjectionDual](../../SigabaNeo/Lib/Lattices/Research/Wall1/ProjectionDual.lean) · [AppendDual](../../SigabaNeo/Lib/Lattices/Research/Wall1/AppendDual.lean) · [MarkedIntegerSection](../../SigabaNeo/Lib/Lattices/Research/Wall1/MarkedIntegerSection.lean)

## A deterministic area floor and a witness count

**Proposition 1.** Let $K$ be a full Euclidean lattice of rank $n\ge3$, covolume $\delta$, and dual minimum at least $R>0$. Let $x$ be any shortest generator of length $t$, and $\alpha=\sqrt3/2$. Every plane lattice $B\subset K$ containing $x$ satisfies
$$
 \det B\ \ge\ \max\left\{\alpha t^2,\ \delta
                  (R/\sqrt{\gamma_{n-2}})^{n-2}\right\}.                 \tag{1}
$$
Here $\gamma_m=\sup_J \lambda_1(J)^2/(\det J)^{2/m}$. The same floor with $t$ replaced by a specified lower bound on the winner length holds uniformly over winners. A closed cutoff $A$ strictly below the floor excludes every plane. An open cutoff equal to the floor also excludes every plane.

*Proof.* Saturate $B$ in $K$, which can only decrease its area. The shortest vector $x$ is primitive and extends to a basis $x,w$ of the saturated plane. Reduce $w$ by a nearest multiple of $x$. Its component along $x$ has length at most $t/2$, while its norm is at least $t$. Hence its perpendicular length is at least $\alpha t$. Multiplication by $t$ gives the first term.

More generally, for a saturated rank-$k$ sublattice $B$, extend its basis to one of $K$. The projected remaining basis has covolume $\delta/\det B$ in $(\operatorname{span} B)^\perp$, by block triangularity. A vector there pairs integrally with the projected basis exactly when it pairs integrally with $K$. The complementary dual section $J=K^*\cap(\operatorname{span} B)^\perp$ consequently has rank $m=n-k$, covolume $\det B/\delta$, and minimum at least $R$. For $m>0$, the definition of $\gamma_m$ gives
$$
 R\le\lambda_1(J)\le\sqrt{\gamma_m}\,(\det B/\delta)^{1/m}.              \tag{2}
$$
Taking $k=2$ proves (1). The Hermite coefficient in (2) is optimal using only the rank and covolume of $J$. Any $J$ can occur as such a section by adjoining a perpendicular primal plane to $J^*$. This optimality statement concerns the section estimate. Attaining both terms in (1) together for prescribed data is a separate extremal problem. ∎

**Counting form.** Set $\ell=\max\{\alpha t,\delta(R/\sqrt{\gamma_{n-2}})^{n-2}/t\}$ and $a=A/t$. Distinct saturated planes correspond to unoriented primitive lines of $P_{x^\perp}K$ of length at most $a$, by taking inverse images. The quotient minimum is at least $\ell$. If the counted lines span dimension $j$, their number $N$ satisfies
$$
 2N+1\le(1+2a/\ell)^j .
$$
Indeed the disjoint open $\ell/2$-balls about zero and both generators of each counted line fit in the $(a+\ell/2)$-ball in their span. To bound $j$ further, $i$ independent such lines give a saturated rank-$(i+1)$ sublattice with determinant at most $t a^i$, by lifting and Hadamard's inequality. Thus $j<i$ whenever $1\le i<n-1$ and $t a^i<\delta(R/\sqrt{\gamma_{n-i-1}})^{n-i-1}$. For $i=n-1$ the test is $t a^{n-1}<\delta$. Even a bound of one witness per selected history would permit hit probability one.

Ordinary successive-minimum transference gives $\lambda_m(Q)\le m/R$ when $m=\operatorname{rank}Q$ and $\lambda_1(Q^*)\ge R$. The complementary-index lower product gives $\lambda_m(Q^*)\ge1/\lambda_1(Q)$. A short first primal vector can require a **long last dual vector**. Equation (2) obtains a short first dual vector using additional determinant information. A Gaussian formulation retains additional shape information as well. For any $\sigma>0$, Poisson summation gives
$$
 1+2N\sum_{k\ge1} e^{-\pi k^2a^2/\sigma^2}
 \ \le\ \sum_{z\in Q}e^{-\pi |z|^2/\sigma^2}
 \ =\ \frac{\sigma^m}{\det Q}\sum_{\xi\in Q^*}e^{-\pi\sigma^2|\xi|^2}.
$$
The inequality counts all nonzero multiples on the $N$ distinct primitive lines in the closed $a$-ball of $Q$. The dual floor removes terms from a ball about zero. An estimate using only that floor must still hold for the example below. [Banaszczyk, *New bounds in some transference theorems in the geometry of numbers*](https://doi.org/10.1007/BF01445125)

## Sharpening the exit in Theorem C

**Proposition 2.** At index $j=0,\ldots,407$ put $n'=105+j,\ N=400+n'$. For $0<R<1$ the probability of a nonzero raw dual vector shorter than $R$ is at most
$$
 e_j(R)=q^{-n'} V_N\big((qR)^2+N/4\big)^{N/2}.                         \tag{3}
$$
The same bound holds for any data-dependent retained section. In particular, with the **original** Part 142 radii
$$
 R_0(j)=q^{-1}\left[(q^{n'}/(408000 V_N))^{1/N}-\sqrt N/2\right],
 \qquad \sum_{j=0}^{407}e_j(R_0(j))<8.147\cdot10^{-14}.                \tag{4}
$$

*Proof.* A nonzero raw dual vector below one has the form $(a,b)/q$ with $a\not\equiv0\bmod q$. Otherwise both blocks are divisible by $q$ and its norm is at least one. For each eligible integer pair the probability of its $n'$ graph congruences is $q^{-n'}$, by independence of columns over the prime field. Opposite signs give the same hit, so the probability bound is half the expected signed count.

For each integer point $y$ in the ball of radius $qR$, take the half of its centered unit cube given by offsets $z$ with $\langle y,z\rangle\le0$ (take either half at zero). Each half has volume $1/2$, their interiors are disjoint, and $|y+z|^2\le(qR)^2+N/4$. Hence the full integer count is at most twice the ball volume in (3). The factors of two cancel. The retained dual is contained in the corresponding raw dual by the projection identity, for every history. Sum (3) over the 408 indices to obtain (4). This uses the inward-half-cube observation also used for a primal count in Part 169. [Part 142, Theorems A and C and audit](wall1_dual_cusp.md) · [Part 169 and audit](wall1_finite_chain.md)

For an exit allowance $\delta_j$, inversion of (3) gives
$$
 R_{\rm in}(j,\delta_j)=q^{-1}\sqrt{(q^{n'}\delta_j/V_N)^{2/N}-N/4}
$$
whenever this radius is real and lies in $(0,1)$. Monotonicity carries the initial $R_0(0)\in(0.00528473,0.00528475)$ through the pass. The stronger late floor comes from the longer **raw** graph at that index. The event defining $P$ has already been decided before index 407.

| Index $j$ | $R_0(j)$ | Upper bound on $e_j(R_0(j))$ | $R_{\rm in}(j,10^{-4}/408)$ | $R_{\rm in}(j,10^{-4})$, single index |
|---:|---:|---:|---:|---:|
| 405 | 0.199994580 | $4.339\cdot10^{-15}$ | 0.203958223 | 0.205310653 |
| 406 | 0.200909156 | $4.592\cdot10^{-15}$ | 0.204873709 | 0.206230708 |
| 407 | 0.201825944 | $4.859\cdot10^{-15}$ | 0.205791403 | 0.207152976 |

Radii in the table are rounded down. Even with the original full-cube count, counting both signs gives a single-index exit of at most $1/816000$ at $R_0(j)$. Part 159 already uses this at 405 for its large-$g$ exit. Equation (4) bounds a single union of raw events in the marginal restart. ∎

## Required floor at the plane cutoff

Apply (2) to $L$ with $A=tu$. On a hit, the dual minimum of $L$ is **strictly below**
$$
 R_{\rm plane}(h,t)=\sqrt{\gamma_{503}}
          \left(\frac{t u}{V_{505}h^{505}}\right)^{1/503}.               \tag{5}
$$
A floor at or above this threshold suffices to rule out the hit. The rank-three lift in $W$ gives the same threshold since $st u/D=t u/\Delta$. For $p_a$ there is another test. All three independent lifts are in $M$. Saturating in $M$ gives determinant strictly below $st u$. The corresponding threshold for the dual of $M$ is $\sqrt{\gamma_{502}}(st u/D)^{1/502}$. This test uses the index-405 floor. The rank-503 test on $L$ applies to either class. Neither test requires an independence assumption about the chosen plane.

For a fixed scale check inside the audited range take $g=40,\ \rho=199/200,\ s=39.8,\ t=0.90s=35.82$. Then $39.82692<h<39.82694$, $38.00804<r(h)<38.00805$, and $37.72660<u<37.72661$. The threshold (5) lies between **0.75670 and 1.08198**, and the old rank-502 threshold between **0.75298 and 1.07669**. Even the larger single-index floors in the table fall below the lower endpoints. These brackets apply to the thresholds of the section test. Whether a history attains these scalars is a separate issue.

For the brackets we used $V_m^{-1/m}\le\sqrt{\gamma_m}\le\sqrt{2}((1+m/2)/V_m)^{1/m}$, $m\ge2$. For the lower bound, Siegel's mean for the signed nonzero count of a ball in a determinant-one Haar lattice is its volume. At volume less than one some lattice misses the ball. Let the volume increase to one. For the upper bound, normalize the minimum to one. At any point consider the $k\ge1$ lattice points within $1/\sqrt 2$, with displacement vectors $z_i$. Pairwise distances at least one give $k\sum |z_i|^2\ge\sum_{i<j}|z_i-z_j|^2\ge k(k-1)/2$. Consequently the sum of translates of $(1-2|z|^2)_+$ is at most one. Integrating on a fundamental domain gives $\det J\ge V_m2^{-m/2}/(1+m/2)$, as required. [Siegel, *A mean value theorem in geometry of numbers*](https://doi.org/10.2307/1969027)

## A counterexample with the two shortest lines selected

**Proposition 3.** At the scale in the preceding paragraph there exists a rank-506 Euclidean lattice $W$ of determinant $D=V_{506}40^{506}$, with $\lambda_1(W^*)>1/2$, whose first two successive shortest-line selections are unique up to sign, have lengths $s,t$, and pass the strict plane gate. Thus the band, the determinant, and both shortestness conditions can all be included when testing the proposed geometric implication.

*Proof.* Fix a three-dimensional lattice $B$ with basis
$$
 b_1=(s,0,0),\qquad b_2=(s/2,t,0),\qquad b_3=(0,t/2,p_0),
 \qquad p_0=0.91s=36.218.
$$
Its unique shortest line is $b_1$. For coefficient $\pm1$ of $b_3$, the squared length is at least $p_0^2+t^2/4>s^2$, and coefficients of larger magnitude suffice by the third coordinate. Without $b_3$, a coefficient $\pm1$ of $b_2$ gives at least $t^2+s^2/4>s^2$, and magnitude two or more suffices by the second coordinate. After projection off $b_1$, the unique shortest line in the projected $B$ comes from $b_2$, since $p_0>t$. Projecting again gives a witness of length $p_0<u$.

To preserve the selections and obtain the claimed dual floor, take a Haar lattice $C$ of rank 503 and determinant $d_C=D/(stp_0)$. Conditional on $C$, choose $\phi\in\operatorname{Hom}(C,\mathbb R^3/B)$ with Haar probability, and set
$$
 W=\{(y,z): z\in C,\ y\bmod B=\phi(z)\}.
$$
Lifting a basis of $C$ gives $\det W=\det B\,d_C=D$. For any nonzero $z\in C$, $\phi(z)$ is uniform on the torus, by surjectivity of evaluation (integer multiplication on a torus is onto). Integrating a fiber count over that torus divides its cross-sectional volume by $\det B$. Applying Siegel to $C$ and integrating the slices of the ball shows that the expected signed count outside $B$ of norm at most $s$ is $V_{506}s^{506}/D<0.079156$. Projection off $b_1$ sends the torus onto the torus of the projected $B$, whose covolume is $\det B/s$. The same calculation for this projection gives expected signed count outside the projected $B$ of norm at most $t$ equal to $V_{505}t^{505}/(D/s)<5.549\cdot10^{-24}$.

Put $R=1/2$. In the dual, the first component belongs to $B^*$. At first component zero the remaining lattice is $C^*$, whose nonzero mean count in the $R$-ball equals $d_C V_{503}R^{503}$ by dual invariance of Haar probability under inverse transpose. For each fixed nonzero $\eta\in B^*$ the remaining fiber is a uniform translate of $C^*$ conditional on $C$. Indeed each independent basis image under $\phi$, paired with the nonzero torus character $\eta$, gives an independent uniform phase modulo one. Integrating this translate bounds its expected count by the same quantity. The number of eligible $\eta$, including zero, is at most $(1+4Rs)^3$, since each integer $\langle\eta,b_i\rangle$ has absolute value at most $2Rs$ and the three integers determine $\eta$. Hence the expected signed nonzero dual count is at most
$$
 (1+4Rs)^3\,d_C V_{503}R^{503}<1.656\cdot10^{-85}.
$$
The sum of the three expected unwanted counts is less than one. Some $W$ has all three counts zero, so the designated shortest lines survive both comparisons, the witness remains, and the closed dual $R$-ball contains only zero. Dual floors also hold in both projected lattices by the section identity. This auxiliary Euclidean ensemble tests universal deterministic assertions. Graph reachability, a horizontal mark and a prescribed fresh height are additional hypotheses absent from this construction. ∎

## Arithmetic checks and remaining probability

Two small checks use only integers or rational numbers.

* Take $K=A_2\oplus\mathbb Z$ with the two planar basis vectors of norm one and inner product $1/2$, and choose the first as winner. Its dual minimum is one (the planar dual has squared minimum $4/3$). Squared quotient lengths are $3b^2/4+c'^2$. Enumerating primitive pairs with the first nonzero coordinate positive gives respectively $1,2,4$ distinct planes at closed squared-area cutoffs $3/4,1,7/4$. The box $|b|,|c'|\le2$ suffices by the quadratic form. At the first cutoff both terms of (1) are exact, because $\det K=\sqrt3/2$ and $\gamma_1=1$.
* For one output, two columns, $q=5$, enumerate the 25 pairs of column residues. Count signed integer triples $(a,b_1,b_2)$ with $0<a^2+b_1^2+b_2^2<6,\ a\not\equiv0\bmod5$ satisfying the dual congruences. There are 36 eligible triples in $[-2,2]^3$. Across designs the counts are zero on 12 designs, two on eight and four on five. The mean $36/25$ verifies the raw first-moment identity, and the hit probability $13/25$ is below its signed-pair bound $18/25$.

The numerical enclosures used 75-decimal outward interval arithmetic, integer factorials, $V_{2k}=\pi^k/k!$, and $V_{2k+1}=2^{2k+1}k!\pi^k/(2k+1)!$. To reproduce (4), for each integer $j=0,\ldots,407$ form $X=\exp((n'\log q-\log408000-\log V_N)/N)-\sqrt N/2$, then sum $V_N(X^2+N/4)^{N/2}/q^{n'}$. The sum lies in $(8.14649,8.14650)\cdot10^{-14}$. The counts for Proposition 3 use the three displayed volume formulas with rational $g,\rho,t/s,p_0/s,R$, with no sampling.

**Remaining conjecture (Parts 161 and 164).** $P+p_a\le0.00019770868$ in the specified marginal restart. Let $I_P,I_a$ be the two event indicators, and $E$ the raw-dual exit at index 406 at the original $R_0(406)$. Their first winners have incompatible heights, so $I_P+I_a\le1$. Thus
$$
 P+p_a=\mathbb E[(I_P+I_a)\mathbf1_{E^c}]
        +\mathbb E[(I_P+I_a)\mathbf1_E],\qquad
 \mathbb E[(I_P+I_a)\mathbf1_E]<4.592\cdot10^{-15}.
$$
Under this allocation it suffices to bound the first term by $0.000197708679995408$. Charging the full $10^{-4}$ at its larger single-index radius would leave $0.00009770868$. The outstanding term averages the fraction of passing designs at each prefix. The selected tests use the *one* mark at draw 406 and include the old-lift requirement for $p_a$. The raw event $E^c$ is evaluated on the design, including the new raw column. The Hermite and Gaussian identities give restrictions on individual lattices. Proposition 3 rules out deducing zero hits from the scalar data for general Euclidean lattices. A bound on how often these geometries occur, or a stronger deterministic property specific to reachable graph sections, is still missing. [Part 161 budget and audit](wall1_band_plane_hits.md) · [Part 164 selected fraction and audit](wall1_selected_hit_direct.md) · [Part 169 terminal identities](wall1_finite_chain.md)

## Audit

**Verdict — MINOR CAVEATS.** Propositions 1–3 and the probability accounting are sound. One scope correction concerns the exact determinant of the example.

**Reachability at the example’s scale.** At every finite restart prefix the window has a basis with rational entries in the original ambient coordinates. The initial graph is integral, each append has a rational lift, and projection off a rational winner has rational matrix $I-vv^\top/(v^\top v)$. Thus the squared covolume, a Gram determinant, is rational. At exactly $g=40$, Proposition 3 prescribes $D^2=(40^{506}/253!)^2\pi^{506}$, which is transcendental. The restart probability at this exact determinant is zero. What remains open is the mass of reachable windows passing the stated inequalities and height tests as $g$ varies. The example establishes the claimed obstruction to a universal implication for Euclidean lattices. [Part 169, rational representation](wall1_finite_chain.md)

**Raw exit.** For $R<1$ every nonzero eligible point has a nonzero first block modulo $q$. Each sign pair therefore imposes the same $n'$ independent uniform scalar congruences, with probability $q^{-n'}$ for the pair. The inward half of each centered cube has volume $1/2$ and lies in the enlarged ball by the squared-norm identity. Different cubes overlap only on null boundaries. Thus the number of eligible pairs is at most the enlarged ball volume, including when the larger integer count used in the argument includes zero. Inclusion of each retained dual in its raw dual holds pointwise, and the union bound needs no independence across prefixes. An independent 85-decimal outward interval calculation used $V_0=1$, $V_1=2$, $V_n=2\pi V_{n-2}/n$ and the unrounded original radii. It gave
$$
 8.14649452211672\cdot10^{-14}<\sum_{j=0}^{407}e_j(R_0(j))<8.14649452211673\cdot10^{-14},
 \qquad
 4.59193101731569\cdot10^{-15}<e_{406}(R_0(406))<4.59193101731570\cdot10^{-15}.
$$
These enclose the upper-bound expressions. The simultaneous guarantee improves Part 142's $10^{-3}$ by a factor exceeding $1.2275\cdot10^{10}$ in the marginal restart. [Part 142, Theorem C and Audit](wall1_dual_cusp.md)

**Area and selection.** Completing a basis of the saturated plane gives projected covolume $\delta/\det B$. Dualizing gives complementary covolume $\det B/\delta$ in rank $505-2=503$. Hermite's inequality has the direction in (2), and reducing the other planar basis vector along $x$ supplies the independent $\sqrt3\,t^2/2$ floor. For Proposition 3 the internal comparisons are strict: $p_0^2+t^2/4>s^2$, $t^2+s^2/4>s^2$, and $t<p_0<u$ with $t<r(h)$. Projection preserves the complementary coordinate in $C$, so the two outside counts exclude all competing lines, including ties. Evaluation at any nonzero $z\in C$ is onto the torus even for imprimitive $z$. In the dual calculation a nonzero character of the torus is onto the circle, giving the uniform translate on each nonzero fiber. The zero fiber uses the nonzero Siegel mean for $C^*$. The independently evaluated three means or majorants are below $0.079156$, $5.549\cdot10^{-24}$, and $1.656\cdot10^{-85}$ respectively. Their sum below one forces simultaneous avoidance without independence. The two small enumerations also reproduce the stated counts.

**Budget and formal scope.** The first winner has incompatible heights on the two events, so their combined contribution on the draw-406 raw exit is at most that single exit probability. Exact subtraction gives $0.00019770868-4.592\cdot10^{-15}=0.000197708679995408$. This is a sufficient ceiling on the *joint mass* of hits and the draw-406 good event. Both selections use the same mark, and the inherited event keeps its horizontal-lift tests. A bound on this joint mass is still missing. `AppendDual.lean` typechecked independently, with only `propext`, `Classical.choice`, and `Quot.sound` in its six axiom reports. Its minimum theorem gives the truncated floor for every nonzero window vector and the full old floor for nonzero fresh height. The numerical and probabilistic propositions above remain paper results. [Part 164, selected fraction](wall1_selected_hit_direct.md) · [AppendDual](../../SigabaNeo/Lib/Lattices/Research/Wall1/AppendDual.lean)
