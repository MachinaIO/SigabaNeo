# The cost of forgetting the signed frame

The factor four of the rank-four graph can grow to **1,048,576** in a rank-22 graph with the same normalized upper band, both quotient gates and a uniform fresh mark. The law here is uniform on one reflection orbit of parents. More generally the loss can be exactly $2^r$ for arbitrarily many reflected old axes, even if the observer knows the isometry class of the parent and every labelled mark coset. The latter construction uses a Euclidean orthogonal summand. Neither example measures the mass of such orbits under the width-506 restart.

## The sharp inequality for a given parent law

Let $\mu$ be a finite parent law, restricted to its positive support, $b(S)\ge0$ a mark-averaged observable, and $I(S)$ the observation. Examples of $I$, in decreasing detail, are the isometry class of a marked inclusion $M\subset K$ with fixed coset labels, the isometry class of $M$, and the ordinary theta series of $M$. Write $C$ for a nonempty observation fiber and $m_C=\max_{S\in C} b(S)$.

**Proposition 1.** The pointwise least $I$-measurable majorant is $b^I(S)=m_{I^{-1}(I(S))}$. The best constant, valid for *all* nonnegative observables under this law, is
$$
 \mathbb E b^I\le L_I\mathbb E b,\qquad
 L_I=\max_C\frac{\mu(C)}{\min_{S\in C}\mu(S)}.
$$
For a particular $b$, each positive fiber mean has the exact multiplier $m_C/\mathbb E[b\mid C]$. The overall multiplier is their average weighted by $\mu(C)\mathbb E[b\mid C]$, normalized by $\mathbb E b>0$.

*Proof.* A majorant constant on $C$ must reach its maximum there, and this choice suffices. The contribution to $\mathbb E b$ from a maximizing atom is at least $m_C\min_{S\in C}\mu(S)$. Sum over fibers for the inequality. Take the indicator of a minimum-mass atom in a fiber realizing $L_I$ for equality. The formula for a particular observable follows by grouping the two expectations by fiber. ∎

For the orbits of a finite group acting on parents **and preserving their law**, the conditional mass is uniform on each orbit, so $L_I=\max_C|C|\le |G|$. A two-element fiber with conditional masses $\varepsilon,1-\varepsilon$ already costs $1/\varepsilon$ on the indicator of the rare atom. Even an invariant law for a frame group gives the orbit bound only for its orbit partition. A theta fiber can be a union of such orbits. Finally, averaging over a random frame preserves a mean under an invariant law, whereas a pointwise majorant takes a maximum. This distinction also explains the factor two in Part 167, where the orbits are of *ordered triples*, before averaging the last mark. [Random order and audit](wall1_random_order.md) · [Order-invariant majorants and audit](wall1_new_tools.md)

## A reflection orbit with one winning parent

For $r\ge2$, take independent uniform signs $a_1,\ldots,a_r$, and independently $j\in\mathbb F_{17}$ uniform. In coordinates $(z,y_1,\ldots,y_r,k)$ the window is
$$
 W_{a,j}=\{(z,y,k)\in\mathbb Z^{r+2}:z\equiv a\cdot y+jk\pmod {17}\}.
$$
The parent $M_a$ is its height-zero graph, and mark $j$ labels $M_a+j e_z$. We may insert an orthogonal Euclidean lattice $B$ among the old coordinates, between the $y$'s and $k$, taking its component of every mark zero. Assume $B=0$ or $\lambda_1(B)>\sqrt2$. Write $n$ for total window rank, $d=n-1$, $D=17\det B$ with the convention $\det 0=1$, $V_n$ for unit ball volume and $c=477/500$. Use the signed key $(\|v\|^2,\min_{\rm lex}(v,-v))$ at both selections. The test requires a nonhorizontal first winner, its length $s$ in $0.990g<s\le1.097193g$ for $g=(D/V_n)^{1/n}$, and
$$
 1<t\le\sqrt{1+c^2h^2},\qquad p<ch\,t^{-1/d},\qquad
 h=(D/(sV_d))^{1/d},
$$
where $t,p$ are the first and second projected minima. As in the rank-four toy, we omit the width-specific restriction on $g$.

**Theorem 2.** Suppose $s=1$ lies below the normalized band and the three lengths $(s^2,t^2,p^2)=(2,3/2,4/3)$ pass its band and gates. Then the selected fraction is
$$
 b(a)=\frac2{17}\,\mathbf 1_{\{a=(-1,\ldots,-1)\}}.
$$
The least isometry-invariant and theta-determined majorants on this support both have constant value $2/17$. Their expectation is $2^r\mathbb E b$.

*Proof.* At $j=0$ the fresh unit is shortest. Otherwise there are no units in the graph. Its old roots of squared length two include a vector with $z=-1$, one for each old input $i$, with that input equal to $-a_i$. A new root with $z=-1$ and fresh support exists exactly for $j=\pm1$, with $k=-j$. All roots without $z$-support lose the signed comparison against a root starting with $-1$. If any old $a_i=1$, the first such old index wins by its negative coordinate. If all old $a_i=-1$, the fresh candidate, whenever present, precedes every old candidate because the latter has a positive entry before the fresh axis. These comparisons exhaust all squared-length-two vectors with first coordinate $-1$, and $B$ supplies no competitor at this length.

On a winning mark, flipping signs transforms the graph to $\sum_i w_i\equiv0\pmod{17}$, and the chosen line to a difference of two axes. Projection averages those two coordinates. The squared norm of a projected graph point is $A^2/2+\sum_i z_i^2$, with $A+\sum_i z_i\equiv0\pmod{17}$. Every such tuple occurs, since one can distribute $A$ among the two integer coordinates. With all remaining entries zero, nonzero $A$ has magnitude at least 17. With exactly one entry $\pm1$, the minimum is $1+1/2$, realized only at $A=\mp1$. All other nonzero remaining tuples have squared norm at least two. Thus **every** projected minimizer is a projected root connecting that pair to a third axis. Projecting off it averages the three coordinates, because the two removed lines span the sum-zero plane on the triple. The same computation gives $1+1/3$, attained because at least one axis remains. The orthogonal summand stays intact in both projections. This proves the two quotient values regardless of the signed second tie.

Reflecting the $r$ old input axes independently acts transitively on the distinct parents, fixes $e_z$ and $B$, and preserves each individual mark label. Consequently the entire support lies in one class even with all labelled coset length spectra observed. Its maximum is $2/17$ and exactly one of $2^r$ equally probable parents attains it. Proposition 1 gives the result. ∎

**An unpadded example.** For $r=20$, $B=0$, the ratio $s/g$ at $s=\sqrt2$ lies between $0.994$ and $0.996$, and both quotient gates pass. Thus the factor is $2^{20}$ in an integer graph. Here the signs define the parent sampling law. If these parents are instead embedded into a uniform full-alphabet experiment, the calculation gives the multiplier *conditional on their orbit*. Other orbits can contribute to the unconditional denominator.

**Arbitrarily large factors with the same gates.** For each even $r\ge2$ set $k_0=r+2$, append a summand of rank $m$, and set $n=m+k_0$. Take $g_*=71/50$ and require $\det B=\delta=V_n g_*^n/17$. For fixed $r$ and sufficiently large $m$ a lattice of this determinant with minimum strictly above $R=\sqrt2$ exists. Indeed
$$
 \frac{V_m R^m}{\delta}
 =17g_*^{-k_0}(R/g_*)^m\pi^{-k_0/2}
   \prod_{i=1}^{k_0/2}(m/2+i)\longrightarrow0.
$$
Here the volume ratio follows by iterating $V_\ell=2\pi V_{\ell-2}/\ell$.

For completeness, whenever $m\ge2$ and this ratio is below one, take a large prime $l$ and the integer preimage of the kernel of a uniform nonzero linear form on $\mathbb F_l^m$. Scale this index-$l$ lattice by $u=(\delta/l)^{1/m}$. No nonzero multiple of $l$ in every coordinate is in the scaled $R$-ball once $lu>R$. Each other integer vector occurs with probability $(l^{m-1}-1)/(l^m-1)<1/l$. The number of integer points in the ball of radius $R/u$ is at most $V_m(R/u+\sqrt m/2)^m$, by disjoint unit cubes. Dividing by $l$ tends to $V_m R^m/\delta<1$. The expected number of nonzero points in the closed ball is therefore below one for large $l$. Some choice has none, and its scaled determinant is exactly $\delta$.

Now $g=g_*$, so the unit lies below the band and $0.990<\sqrt2/g_*<1.097193$. At the root length,
$h/g_*=(g_*V_n/(\sqrt2 V_{n-1}))^{1/(n-1)}\to1$. To see this, slice the unit ball by its last coordinate. The volume ratio is at most 2 and at least $2n^{-1/2}(1-1/n)^{(n-1)/2}$ by the slice $|x|\le1/\sqrt n$. Both gates eventually hold strictly because $1<3/2<1+c^2 g_*^2$, $4/3<c^2 g_*^2$, and $t^{-1/d}\to1$. Theorem 2 applies. This shows unbounded loss as the width varies. It asserts exponential growth in the number of reflected axes, without asserting an exponential rate in the padded rank.

**Exact small checks.** Scratch enumeration of the unpadded sign parents for $r=2,3,4,5,6$, using both signs of all vectors of squared length one or two, gave exactly two nonhorizontal squared-length-two winners in each experiment, out of 68, 136, 272, 544 and 1,088 designs respectively. This checks the signed selection at these ranks. For $r=2,14,20$, exact rational comparisons separately checked the numerical gates. In detail, enclose $V_0=1,V_1=2,V_i=2\pi V_{i-2}/i$ using $333/106<\pi<355/113$. At $D=17$, compare $(s/g)^{2n}=2^n(V_n/17)^2$ with the band endpoints raised to $2n$. Compare $(1/2)^d$ and $(4/3)^d(3/2)$ with $c^{2d}17^2/(2V_d^2)$. All comparisons are strict. An independent loop over the full $17^3$ rank-four designs, retaining signed vectors through squared length three and projecting with integer numerators, found just $(16,16,1),(16,16,16)$. Completeness of that cutoff follows by rounding a lift along each removed generator. Writing $C=c^2 h^2<1.84$, a passing first image has a lift of squared norm at most $1+C+2/4<4$. A passing second witness has one below $C+(1+C)/4+2/4<4$. [Rank-four transfer calculation](wall1_transfer_operator.md)

In that full rank-four experiment the theta fiber of the winning parent has exactly four members. Its parent graph is the kernel of a row $(1,-a_1,-a_2)$ modulo 17. With no unit vector, all three coefficients are nonzero. Each pair of axes supplies at most one sign pair of squared length two, and supplies one exactly when the two coefficients agree up to sign. Thus zero units and six vectors of squared length two pick out precisely $(a_1,a_2)\in\{\pm1\}^2$. Reflections identify all four even with coset labels fixed. The full-law majorant mean is consequently $8/4913$, while the selected mean is $2/4913$.

## What first moments control at width 506

Use the unconditioned plain LWE $(511,512,3329)$ restart, independently of the CBD(3) plant. Write $S$ for the framed parent after 405 appends, $q=3329$, $Q=q^{400}$, and $N(S)$ for the number of raw prefixes reaching it, out of $Q^{510}$. Given $S$, the next uniform column maps onto $H=K/M$ with equally large kernel cosets. The two deterministic indicators $f_S(u),a_S(u)$ of Part 169 use the *same* mark. The former includes $32.18553<g<203.888$ and a positive first height, the latter requires the horizontal lifts and has no band restriction. Their first heights are incompatible. Hence for $b(S)=|H|^{-1}\sum_{u\in H}(f_S(u)+a_S(u))$,
$$
 P+p_a=\sum_S N(S)Q^{-510} b(S),\qquad
 \mathbb E b^I=Q^{-510}\sum_C\left(\sum_{S\in C}N(S)\right)\max_{S\in C} b(S).
$$
This follows by counting equally likely prefixes and applying Proposition 1. The embedded inverse of Part 176 retains $N(S)$ as a multiplicity. Bijecting raw inputs by processing-order permutations preserves their uniform law, but need not carry their *selected output* to the reflected output under the old frame. For instance, on first-step rank loss the signed comparison of the $q$-axes selects the first horizontal axis, as Part 169 proves. Thus input exchangeability alone does not establish uniformity on terminal isometry fibers. [First-tour law](wall1_first_tour.md) · [Finite chain and audit](wall1_finite_chain.md) · [Inverse branch and audit](wall1_inverse_branch.md)

**Proposition 3 (loss localized to ambiguous marks).** For the physical observable before any raw-dual exit is removed, let $I$ retain the isometry class of $M\subset K$. At a given mark allow every shortest first sign pair and, for each, every shortest second sign pair. Evaluate the two original geometric tests on each such flag, including the first height, the horizontal-lift tests and the witness existence test. Write $\eta(S)$ for the fraction of marks on which some flags pass the union of the tests and others fail. Then
$$
 0\le \mathbb E b^I-(P+p_a)\le\mathbb E\eta.
$$

*Proof.* For each mark take the minimum and the maximum of its binary test over these flags, then average each over marks to get $b_-(S),b_+(S)$. An isometry of the inclusion induces a bijection of marks and extends by the identity on the fresh real coordinate. It carries the full window, both sets of shortest lines, and the old sublattices after each projection to their counterparts. It preserves every test once the flag is specified. Thus $b_-$ and $b_+$ are constant on each marked isometry class. Every signed choice lies between them, so $b_-\le b\le b^I\le b_+$ and $b_+-b_-=\eta$. Averaging proves the claim. ∎

This bound counts a tie only when it can change the test. If every shortest flag has the same outcome for each mark in a class, the signed observable is already constant there. For the ordinary theta series of $M$, different marked inclusions may occur within a single fiber, so this proof does not bound the additional loss. No estimate of $\mathbb E\eta$ at width 506 is supplied by the orbit sizes.

**A uniform upper bound on the envelope itself.** The zero mark excludes both hits at every parent. Its window is $M\oplus\mathbb Z$, with a fresh unit. A nonhorizontal winner then has length at most one, below the physical band. If the first winner is horizontal, the fresh unit survives the first projection, so $t\le1$ fails the strict lower gate. Hence $b(S)\le1-1/|H(S)|\le1-q^{-400}$. This constant bounds $\mathbb E b^I$ even for the ordinary theta observation. Its distance from one is far too small to meet the allowance.

**Which counts could improve the bound?** If nonnegative statistics $T_i(C)$ are functions of the chosen observation and $\alpha_0+\sum_i\alpha_i T_i(I(S))\ge b(S)$ for *every reachable* $S$, with $\alpha_i\ge0$, then
$$
 \mathbb E b^I\le\alpha_0+\sum_i\alpha_i\mathbb E T_i.
$$
Indeed the same inequality holds at a maximizing member of each class, and one can sum over the classes. A non-invariant count that bounds $b(S)$ pointwise only gives this argument after replacing the count by its class maximum, unless a different invariant bound is proved. Three distinctions matter for the proposed inputs.

1. **The dual-floor exit.** Let $E$ be the draw-406 raw-dual exit of Part 172 and $Y=f_S(U)+a_S(U)\in\{0,1\}$. Its audited bound gives $\mathbb E[Y\mathbf1_E]\le\Pr(E)<4.592\cdot10^{-15}$. The simultaneous exit over all 408 indices is below $8.147\cdot10^{-14}$. To use the smaller exit in an invariant certificate for the *original target*, first take $b_{\rm good}(S)=\mathbb E[Y\mathbf1_{E^c}\mid S]$, averaging over the actual raw prefixes and final column conditional on $S$. It suffices to show $\mathbb E b_{\rm good}^I\le0.000197708679995408$. The original exit probability need not bound the exit's own class maximum. In a single class containing one positive-mass exceptional atom, the envelope of its indicator is identically one. The Euclidean counterexample in Part 172 has two unique successive shortest lines, a strict plane hit and dual minimum greater than $1/2$. Hence the scalar floor alone does not exclude the geometry even when ties disappear. The example supplies no lower bound on restart mass. [Dual transference and audit](wall1_transference.md)
2. **The annihilator theta bound.** The marked lattice has $H^\perp=K^*$. For the stated cubic restart the Lean inequality controls $\theta_{K^*}(s)\le\theta_{\mathbb Z}(s)^{505+h_t}$ for $s>0$, where $h_t$ counts horizontal wins. This observable depends on the inclusion $M\subset K$. For instance, with $M=\mathbb Z^2$ the two extensions by $(1/q,0)$ and $(1/q,1/q)$ have the same index, whereas their duals have respectively two and zero squared-length-one vectors, by integral pairing. Thus the marked theta observable does not in general descend to the ordinary parent isometry class. Even with the marked inclusion observed, the inequality gives an upper bound on a Gaussian sum. Using it to bound the majorant requires a pointwise implication from a passing fraction to a sufficiently large count. Part 173's capped Gaussian weight can equal one on every eligible candidate with small dual theta. [Part 142](wall1_dual_cusp.md) · [MarkedTheta.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/MarkedTheta.lean) · [Gated theta and audit](wall1_gated_theta.md)
3. **The positive-height first moment.** For an interval $J\subset(0,q)$ of physical lengths the exact conditional mean of the count before selection is
$$
 T_J(M,K)=\frac1{|K/M|}\#\{(y,k)\in K\times\mathbb Z_{>0}:\|(y,k)\|\in J\}.
$$
Indeed $1\le k<q$ and the congruence $[y]=kU$ specifies one mark. The sum counts all these incidences by linearity. This statistic is invariant for the marked inclusion. On the upper-band good set the first moment for the *full* upper band majorizes the positive-height fraction, but already its inner shell $1.004g<\|(y,k)\|<1.097g$ contributes more than $74.85561$ on **every** such parent by Part 161. Capping that conditional full-band mean at one gives exactly one there. This obstruction applies to the raw vector count, and leaves open a count retaining shortestness and the gates. Part 147 bounds other terms, including short-line horizontal charge and positive-height plane multiplicity on horizontal wins. Those charges concern different witness conditions. Neither estimate covers all of the inherited residual. [Upper-shell bound and audit](wall1_band_plane_hits.md) · [Uncovered lines and audit](wall1_uncovered_lines.md) · [Inherited event](wall1_inherited_witness.md)

**Remaining conjecture.** For the specified width-506 restart, $P+p_a\le0.00019770868$. A sufficient, stronger assertion for the invariant-majorant approach is the displayed bound on $\mathbb E b_{\rm good}^I$ for a specified observation $I$. A small bound on the ratio $\mathbb E b^I/\mathbb E b$, even if established at this width, would still require an absolute estimate. The orbit examples invalidate a width-independent factor based solely on signed ties and the two normalized gates. The width-506 law might concentrate on quite different fibers. Neither their weighted maxima nor a first moment majorizing those maxima at the required scale is evaluated by the available estimates. [Parts 161–176](../PROOF_GAP.md)

## Audit

**Verdict — SOUND.** The multiplier is exact on the stated uniform reflection orbit, including when every mark coset retains its label. No corrections are required.

**Orbit and projections.** The parents are distinct since the congruence on a single old input recovers its sign. Each old-axis reflection fixes $e_z$, so it carries the coset at $j$ to the coset at the same $j$. For $j\ne0$ the signed minimum starts with $z=-1$. An old root with a negative input coordinate precedes every fresh root. When all old signs are negative, the old roots starting with $-1$ have a positive input coordinate, and the fresh root precedes all of them precisely at $j=\pm1$. At $j=0$ the fresh unit misses the band. After sign changes on a winning mark, projection averages a pair of coordinates. Each shortest image joins that pair to a third axis, so removing any such line averages the triple. A fourth axis remains for $r\ge2$. This gives $t^2=3/2$ and $p^2=4/3$ for every second tie choice. The class maximum is $2/17$ and the orbit mean is $2/(17\cdot2^r)$. In the padded construction $\sqrt2/g_*<1$ makes the ball-volume ratio tend to zero for each fixed even $r$. The finite-field first moment then gives a summand of the required determinant with no nonzero point in the closed $\sqrt2$-ball. The unbounded factors follow as the width varies.

**Exact gate and enumeration checks.** Independent scratch arithmetic bounded $\pi$ by alternating rational partial sums in Machin's formula. With $C=c^2h^2$, $n=22$ and $s^2=2$, rational comparisons after raising to powers $44$ and $21$ respectively gave
$$
0.99461<s/g<0.99462,\qquad 102755.26<C^{21}<102755.27.
$$
The unit's normalized length is below $0.990$. At the root, $t>1$ and the powered left sides for the two gates are $2^{-21}$ and $(4/3)^{21}(3/2)=2199023255552/3486784401$. Both are below $C^{21}$. Thus the unpadded rank-22 graph realizes $2^{20}=1{,}048{,}576$. In rank four, the same calculation isolates $s^2=2$ in the band and gives $C<1.84$, validating the rounded-lift cutoff. Enumerating all $4913$ designs with both vector signs through squared norm four and using integer projection numerators gave 1150 designated nonhorizontal winners in the band, 430 through the first gate, and exactly $(16,16,1)$ and $(16,16,16)$ through both. The four sign parents are precisely those with zero units and six norm-squared-two vectors. This recovers the full rank-four means $2/4913$ and $8/4913$ from Part 178. Part 167's factor two uses permutations of ordered triples before mark averaging.

**Excess and scope.** An isometry of $M\subset K$ induces a bijection of $K/M$. Extending it by the identity on fresh height carries every shortest flag and every horizontal lift to its counterpart. Thus the mark-averaged flag minimum and maximum are constant across each observation fiber. They enclose both the signed mean and its fiber maximum, and their difference is exactly the fraction of marks admitting both outcomes. This proves Proposition 3 for the physical observable before the raw-dual exit. The probability is over the actual parent and its uniform mark, with existence of two disagreeing flags at that mark. The proof supplies no numerical estimate of this probability or of the restart mass of the reflected examples. The width-506 target $P+p_a\le0.00019770868$ remains open.
