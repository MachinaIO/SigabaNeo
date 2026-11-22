# What can column order tell us about a selected hit?

Two exact one-append families have the same pattern. Half of the selected hits lie on constant column triples, which win in every order. The other half lie on orbits of size three, on which exactly one order wins. This gives a sharp test of how much information about the selected event survives when the column order is erased. It also supplies counterexamples to four possible probability estimates.

## Finite experiment and certificate

Let the three chronological columns be independent uniform elements of an alphabet of size $Q=q^m$. Write $S=(C_1,C_2)$ and $U=C_3$. Let $F$ be the indicator that the designated first line has nonzero last coordinate, lies in the Part 162 upper band, and passes both quotient gates. The width-specific restriction on the incoming history is omitted in these toys. In particular $F$ counts hits per design, including the signed tie rule. The last column has $Q$ equiprobable possibilities at every prefix. [Part 108](wall1_first_tour.md) · [Part 158](wall1_selected_scaling.md) · [Part 162](wall1_upper_band_quotient.md) · [Part 164](wall1_selected_hit_direct.md)

Let $B=\{-e_i:1\le i\le m\}$ in the column alphabet and $r=|B|$. In **each of the two enumerated families**, the complete support of $F$ is
$$
\{(a,a,a),(a,a,-a):a\in B\}.
\tag{1}
$$

| $(m,q)$ | Designs | Band candidates | Length passes | Candidates passing both gates | Selected designs | Winning prefixes |
|---|---:|---:|---:|---:|---:|---:|
| $(1,17)$ | 4,913 | 1,734 | 816 | 24 | 2 | $(-1,-1)$ |
| $(2,5)$ | 15,625 | 5,000 | 3,168 | 48 | 4 | $(a,a)$ for $a=(0,-1),(-1,0)$ |

**Verification of (1).** I reran the finite Part 162 enumeration with the ordered graph columns emitted at each selected hit. For reproduction, enumerate the three columns in lexicographic order. Form the sign pairs of nonzero integer vectors of squared norm at most three satisfying all graph rows. The squared band contains only the integer two. For each band candidate $v$ with nonzero last coordinate, project the list along $v$, choose the smallest nonzero image $x$ by squared norm and then signed tuple, and apply the length gate. Project the list again along $x$ and test the strict witness cutoff. Record the three columns if both gates pass and $v$ also has the smallest original key. Integer projection numerators and a common denominator preserve ties. The gate comparisons used rational squared norms and 75-decimal interval arithmetic for the thresholds. The rounded-lift bounds in the Part 162 audit certify that squared norms through three suffice in both rows. The counts agree with the audited aggregate counts. Equation (1) specifies the recorded triples modulo each prime. [Part 162, exact graph checks and audit](wall1_upper_band_quotient.md)

The four tests below concern the actual terminal bit in (1). Put $p=\Pr(F=1)=2r/Q^3$. All logarithms are natural.

## Four proposed estimates and their counterexamples

1. **Average information as a multiplicative bias factor.** Test the proposed inequality $\Pr(F=1\mid S=s)\le p\exp I(S;F)$ on positive-mass prefixes. On $s=(a,a)$ the ratio of posterior to prior is $Q^2/r$, equal to 289 and $625/2$ respectively. Yet $I(S;F)\le H(F)=h(p)<\log 2$, since $0<p<1/2$. Thus even a factor of two would fail on both examples. The forward mark entropy is exactly $\log Q$ everywhere. The experiment distinguishes the average information from the pointwise likelihood ratio even for a two-valued statistic. Earlier entropy arguments in this series use average bounds. [Information and the terminal observable](wall1_information.md) · [Part 117](wall1_idea_round2.md)

2. **Reverse exposure with a diffuse predecessor.** Expose the last column $u$ first. For reversing the selected event, test the weak claim $H(S\mid U=u,F=1)\ge\log 2$ whenever $u$ has positive selected mass. Before conditioning on $F$, this entropy is $2\log Q$. After conditioning, $u$ fixes the unique axis in (1) and hence fixes $S=(a,a)$; the entropy is zero for every supported $u$. For example, at $q=5$, either $(0,1)$ or $(0,-1)$ leaves precisely the predecessor $((0,-1),(0,-1))$. This rules out even two equally likely reverse predecessors as a consequence of the forward equal-fiber law. Reversing an unconditioned independent column sequence remains valid.

3. **Decay of reveal-martingale increments.** Write $M_k=\mathbb E[F\mid C_1,\ldots,C_k]$ and $D_k=\mathbb E[(M_k-M_{k-1})^2]$. Test the proposed late-reveal estimate $D_3\le D_2$ under equal-size fresh alphabets. Equation (1) gives $M_1=2/Q^2$ on $C_1\in B$ and $M_2=2/Q$ on the $r$ winning prefixes, with zero elsewhere in each case. Consequently
   $$
   \mathbb E M_1^2=4r/Q^5,\qquad
   \mathbb E M_2^2=4r/Q^4,\qquad
   \mathbb E M_3^2=2r/Q^3.
   $$
   Orthogonality gives $D_k=\mathbb E M_k^2-\mathbb E M_{k-1}^2$. Hence $D_3/D_2=Q(Q-2)/(2(Q-1))$, exactly $255/32$ and $575/48$. Both terminal increments carry more variance than the preceding increment. The calculation tests the martingale of the weight itself.

4. **Representing the weight by interactions of at most two columns.** Test whether arbitrary functions of the three pairs can sum to $F$, even allowing signed coefficients and no restrictions on their magnitudes. On the cube $\{0,a\}^3$, for any $a\in B$, only $(a,a,a)$ wins. The alternating sum over the eight corners, with sign $+1$ on $(a,a,a)$, is one. For each pair function the sum vanishes by cancellation across the omitted coordinate. Thus any such approximation has uniform absolute error at least $1/8$ on each toy. This tests a representation of the terminal bit on individual designs. It does not rule out one-sided bounds in expectation.

## Surviving identity for column-order averaging

Let a finite group $\Gamma$ act by measure-preserving bijections on a finite probability space of full support. For an indicator $f$ define $Af(x)=|\Gamma|^{-1}\sum_{\sigma\in\Gamma}f(\sigma x)$, and let $O(x)$ be its orbit. The following three quantities distinguish randomizing order, predicting from an unordered input, and bounding the ordered event on every input.

* $Af(x)$ is the fraction of points of $O(x)$ at which $f=1$. Randomizing by an independent uniform group element preserves the marginal probability $\mathbb E f$.
* Among all real predictors $g$ constant on each orbit, $Af$ uniquely minimizes mean squared error. The minimum is $\mathbb E[Af(1-Af)]$.
* Among all orbit-constant pointwise majorants, the smallest is $\mathbf1_{Af>0}$. Its mean is the mass of all orbits meeting the event.

**Proof.** Each point in $O(x)$ has the same number of preimages under $\sigma\mapsto\sigma x$, namely the size of the stabilizer of $x$. The conditional input law given its orbit is uniform by invariance. Thus $Af=\mathbb E[f\mid O]$, proving preservation of the mean. Squaring $f-g=(f-Af)+(Af-g)$ and conditioning on $O$ kills the cross term. The conditional mean square of the first term is the variance of a Bernoulli variable with parameter $Af$. Finally, a constant dominating $f$ on one orbit must be at least its maximum there, which is one exactly when that orbit contains a hit. This also proves sharpness. The mean-preservation statement for reducer symmetrization already appears in Part 135. [Part 135, Proposition 3.2](wall1_plant_symmetry.md)

Apply this result with $\Gamma=S_3$ permuting the input positions, using chronological coordinates for the tie rule after each permutation. Equation (1) gives $r$ singleton winning orbits and $r$ mixed orbits of size three. Each mixed orbit contains just one hit. An exhaustive permutation of the recorded triples gives the following counts of **ordered inputs**, including duplicate columns with their correct multiplicities.

| $(m,q)$ | $Af=0$ | $Af=1/3$ | $Af=1$ | Minimum mean squared error | Least invariant majorant mean |
|---|---:|---:|---:|---:|---:|
| $(1,17)$ | 4,909 | 3 | 1 | $2/14739$ | $4/4913$ |
| $(2,5)$ | 15,617 | 6 | 2 | $4/46875$ | $8/15625$ |

In both families the optimal squared error is $p/3$ and the least pointwise majorant has mean $2p$. In particular, the candidate estimate $Af\le1/3$ on every unordered input fails on the constant triples. Permutation symmetry also leaves the *unframed* lattice isometry class unchanged within each mixed orbit, by permuting its input coordinate axes. Thus even its entire ordinary theta series takes the same value on the winning and losing orders of that orbit. This gives a concrete limitation on reconstructing an ordered event using that series alone.

## Remaining gap

The positive result determines exactly which part of the toy event an unordered observer can predict. An independent permutation of exchangeable columns preserves the mean of any fixed chronological rule, including when its intermediate choices depend on previous columns. The numerical orbit counts and the support formula (1) are finite-family results. They give no estimate of orbit frequencies or selected mark fractions at width 506. The frontier's shared inequality $P+p_a\le0.00019770868$, including its separate inherited residual, remains open. [Part 164, audit](wall1_selected_hit_direct.md) · [Wall 1 frontier](../PROOF_GAP.md)

## Audit

**Verdict — SOUND.** The counts, four counterexamples and orbit identities hold as stated. No correction is needed.

An independent scratch enumeration visited every ordered design in both graph families. It included all raw sign pairs through squared norm four, used exact signed lexicographic ties before and after the first projection, and tested the strict witness cutoff by rational comparison. With $T=t^2$, $Z$ the squared witness length and $C=(477/500)^2h^2$, the final comparison is $Z^dT<C^d$. Rational bounds on $\pi$ separated every tested value from the uncertain gate endpoints. The rounded-lift bounds in Part 162 ensure the list is complete. The counts below are per candidate through the third count and per design in the last column. The entries in each triple are in processing order. [Part 162 and audit](wall1_upper_band_quotient.md)

| Designs | Band candidates | Length passes | Both gates | All selected triples |
|---:|---:|---:|---:|---|
| 4,913 | 1,734 | 816 | 24 | $(-1,-1,-1),\ (-1,-1,1)$ |
| 15,625 | 5,000 | 3,168 | 48 | $(a,a,a),\ (a,a,-a),\ (b,b,b),\ (b,b,-b)$ with $a=(-1,0),\ b=(0,-1)$ |

The posterior-to-prior ratios at the winning prefixes are $289$ and $625/2$, while $\exp I(S;F)\le\exp H(F)<2$. Every supported final column has exactly one predecessor prefix conditional on a hit, giving conditional entropy zero. Computing the conditional second moments from the enumerated support gives $D_3/D_2=255/32$ and $575/48$, both greater than one. On each stated cube the third alternating difference of $F$ is one. Every sum of pair functions has difference zero, and the eight errors can contribute at most eight times the uniform error. This proves the $1/8$ lower bound for the stated approximation problem.

On each mixed orbit, one of three distinct ordered triples wins, equivalently two of six permutations when the equal columns are labeled. The constant orbits contribute one of the two hits in the first family and two of the four in the second. Closing the event under all permutations therefore gives masses $4/4913$ and $8/15625$, exactly $2p$. The half split, $2p$ and the prediction error $p/3$ depend on these toy orbits. In general the least invariant pointwise majorant is the indicator of the union of hit orbits. Randomizing the order preserves the mean for exchangeable columns with the same chronological rule, including its signed tie priorities. Keeping the original coordinate priorities gives a different experiment. [Random order and audit](wall1_random_order.md)

The width-506 sufficient allowance $P+p_a\le0.00019770868$ remains open. Its $P$ is the unconditional history average of the winning-mark fraction times the good-history indicator, and $p_a$ is a separate inherited residual. Neither the toy orbit counts nor the Haar benchmark bounds that sum. [Part 164 and audit](wall1_selected_hit_direct.md) · [Parts 158 and 162–165](../PROOF_GAP.md)
