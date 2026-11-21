# Selecting a terminal quotient by its prefix determinant

A determinant test can certify the **actual quotient minimum** on ordinary Haar input. At final width 506 the test below gives a simultaneous 0.9·GH lower bound for every rank-505 quotient whose prefix passes an explicit cutoff, outside a Haar event of probability 0.005. The unresolved algorithmic quantity is the probability of producing even one passing prefix. There is also a dual terminal rule with a 0.9885·GH guarantee on a fresh Haar parent. Its output is a hyperplane section, and using it as a projected terminal block requires a separate geometric step.

Write $N=1023$, $d$ for horizontal output rank, $k=N-d$, $V_j$ for unit ball volume and $h_j=V_j^{-1/j}$. Own GH means $h_d(\det H)^{1/d}$. A horizontal-only block of width β has $d=β$. For the final call including the extra height coordinate, $d=β-1$. The physical benchmark at β=506 is 27.4538 for the latter convention, a necessary height-zero floor for 99% conditional success. Height one also involves the plant's position in the Voronoi cell. [Parts 94 and 103](wall1_width_scan.md)

## A determinant test with a quantified search target

Normalize the parent to determinant one. Given a primitive prefix $P$, write $D=\det P$ and $H=\pi_{P^\perp}L$, so $\det H=1/D$. For Haar input the expected number of primitive unoriented rank-$k$ prefixes of determinant at most $T$ is $M=aT^N$, where
$$
 a={1\over N}{N\choose k}\prod_{i=1}^k
 {V_{N-i+1}\zeta(i)\over V_i\zeta(N-i+1)},\qquad \zeta(1):=1
$$
in this product only. In the integral over marked prefixes, conditional on $D$, the normalized quotient shape has Haar law. The expected number of prefixes under the cap whose quotient contains a primitive sign pair shorter than $c$ times own GH is at most $M c^d/(2\zeta(d))$. Indeed, count *all* such pairs per prefix and apply primitive Siegel in the quotient. Equivalently each pair specifies a primitive extension $P\subset E$ with $det E=\det P\,|v|$. Thus with failure probability at most this expectation the bound holds for every eligible quotient at once, regardless of the subsequent choice of basis. No independence between candidate windows enters. [Split integral in Part 51](wall1_random_block_reducer.md) · [Kim's mean value formulas](https://arxiv.org/abs/2005.10874)

Fix $c=0.9$ and $T=(0.01c^{-d}/a)^{1/N}$. The following outward intervals use natural logarithms. The last column rescales unit-covolume Haar lengths by $s=3329^{511/1023}$ for comparison with physical units. It encloses the **lower certificate** $sc h_d T^{-1/d}$, conditional in the logical sense that the prefix passes on the simultaneous good event. Conditioning the probability measure on passing can change the failure probability.

| β | $d$ | $\log T$ | scaled lower certificate |
|---:|---:|---:|---:|
|406|405|[523.5490, 523.5496]|[69.7561, 69.7563]|
|406|406|[524.0041, 524.0047]|[69.9851, 69.9853]|
|506|505|[547.8318, 547.8324]|[95.7470, 95.7472]|
|506|506|[547.8577, 547.8583]|[96.0414, 96.0416]|

For reproduction, evaluate the displayed product with 45-decimal interval arithmetic, $V_j=\pi^{j/2}/\Gamma(1+j/2)$, and bracket each zeta for $j>1$ between $1+2^{-j}$ and $1+2^{-j}(1+2/(j-1))$. At rank 505 the allowed mean count is about $1.28\times10^{21}$. Even this large mean gives no upper bound on the void probability. The cutoff is only a factor $M^{1/N}$ above the mean-one cutoff in determinant, about 1.049 at rank 505. The scaled 95.747 is a Haar implication. Transferring it to the graph ensemble requires a marked graph count and a search bound there.

**Implementable variant.** Start with the supplied basis. Make $m=N$ independent column permutations, including the identity as an additional candidate. For each run the Part 88 terminating generalized slide routine at horizontal width $d$ with 1% twin slack and its LLL preprocessing. Keep the rank-$k$ prefix with smallest determinant, ties by candidate order. Complete it with its own suffix and insert an exact quotient shortest vector at the terminal head. Report whether $D\le T$. On integral inputs there are $N+1$ slide runs of polynomial oracle cost in dimension and input bit length (for Haar reals Part 88 gives termination in exact arithmetic) and one rank-$d$ SVP. Comparisons use Gram determinants. On a miss the selected run still supplies its slide certificate because its quotient survives. For Haar input the unconditional probability of falling below 0.9·GH is bounded by
$$
 0.005+\Pr(\min_i D_i>T).
$$
Estimating the second term by a power of a marginal miss probability is invalid. Given the parent and its presentation, the random restarts are independent, so their joint miss probability is the *mean of a power* of the conditional miss probability, with the identity miss indicator inside that mean. This specifies a measurable output rule and isolates a single scalar probability to estimate. For comparison, the Part 88 deterministic cap $D\le h^{kd}$ with $h=(1.01^2\gamma_d)^{1/(2(d-1))}$ gives a log cap above 1000 at $d=506$ when evaluated with the Part 98 upper bound 56.2142. The marked calculation requires a much shorter prefix. Neither Parts 86–101 nor the marked formula above gives the needed 0.005 miss bound. Selecting the largest **projected quotient** determinant implements exactly this same rule.

The baseline already controls a minimum: exact terminal SVP identifies the head with that minimum. At horizontal widths 406/506 Part 88 gives unconditional 99% Haar radii 0.12531/0.36188 in input determinant-one units. Those absolute radii do not specify fractions of the random own GH. On the graph ensemble the stronger Part 101/103 certificate at final width 506 is about 8.088 physical, roughly 3.4 times below the necessary floor. The simultaneous passing-basis estimates survive restart selection when the retained output satisfies their hypotheses. Standard BKZ-β controls overlapping projected windows and has first-vector and prefix bounds. The restart procedure returns a slide basis with a terminal SVP, with no proof of all the standard BKZ window conditions. [Parts 86–103](../PROOF_GAP.md) · [Finite-width BKZ guarantees](wall1_lit_random_bases.md)

## Global determinant extremes and finite completions

The ideal rule minimizes $D$ over all primitive rank-$k$ sublattices (break ties in supplied basis coordinates), then performs the same terminal SVP. Bounded sets of their primitive exterior products are finite, so the minimum exists. The displayed miss term becomes precisely the ordinary Haar void probability for this Rankin problem. This is an existence benchmark: exhaustive exterior-vector enumeration hides a global search outside the polynomial-work width-β model. Counting one final SVP would misstate its cost. Maximizing the *prefix* determinant has no solution globally: replace one coordinate prefix vector by $e_1+t e_N$ in a basis, retaining $e_2,\ldots,e_k$. The resulting primitive determinants diverge. In a finite list this objective shrinks the quotient determinant.

Even globally maximizing the quotient determinant has no worst-case positive own-GH fraction. On a diagonal lattice take $k$ lengths $u^2$, then one length $u$, then $d-1$ lengths one, with $0<u<1$. By Cauchy–Binet every nonzero integral rank-$k$ minor contributes at least $u^{4k}$ to the squared determinant and equality singles out the short coordinate plane for a primitive minimizer. The optimal quotient has ratio $u^{1-1/d}/h_d\to0$. Common rescaling preserves the ratio. This addresses both widths and shows why a distributional existence argument matters.

A concrete graph restart has an exactly computable, poor output law. Present the lattice as $(qz+Ax,x)$ with 512 free $x$ coordinates. Randomly retain $d$ of those coordinates and project off the span of all remaining coordinate axes, using the primitive intersection with the lattice as prefix (compute by integer kernel and completion). The intersection spans that coordinate space since the lattice contains $q\mathbb Z^N$. Every retained integer tuple lifts, so the terminal quotient is exactly $\mathbb Z^d$ for every design and every restart. One rank-$d$ SVP suffices, and maximizing determinant across polynomially many such completions changes nothing. At $d=405,406$ the ratios are in [0.2032,0.2036], and at $d=505,506$ in [0.1823,0.1826], from $1/h_d$. The physical minimum is one. This gives an explicit fresh-completion law without the adaptive append or void-conditioning assumptions obstructed in Parts 108–112. General primitive completions have no uniform probability law; Part 104 even constructs selectors with arbitrarily small terminal physical quantiles. [One-pass selector analysis](wall1_markov_reducer.md)

## A shortest-dual terminal step

In a presented rank-$b=β$ parent $W$, compute a primitive shortest $w\in W^*$, break sign and ties by basis coordinates, and compute the integer kernel $S=W\cap w^\perp$. Reduce $S$ internally by one exact SVP to expose its minimum. Cost is two calls of ranks $b,b-1$ plus integer linear algebra. On a determinant-one Haar parent the dual is marginally Haar too. With probability at least 0.99 both
$$
 \lambda_1(W)\ge .01^{1/b}h_b,\qquad
 |w|\le399^{1/b}h_b
$$
hold: the primal primitive first moment bounds the first failure by 0.005, and the dual second-moment void bound is $1/(1+399/(2\zeta(b)))<0.005$ at both widths. No joint shape assumption is required. Since $S\subset W$ and $\det S=|w|$ (the complementary height is $1/|w|$), the section satisfies
$$
 {\lambda_1(S)\over h_{b-1}(\det S)^{1/(b-1)}}\ge
 {.01^{1/b}h_b\over h_{b-1}(399^{1/b}h_b)^{1/(b-1)}} .
$$
The right side exceeds 0.9859/0.9885 respectively. Scale invariance extends this to a Haar-shaped parent of any scale. A concrete sufficient physical scale at 506 is $(\det W)^{1/506}>27.454/(.01^{1/506}h_{506})$, using inheritance of the primal minimum directly. [Part 107 moment bounds](wall1_lit_random_bases.md)

A section occurs as the *first* $b-1$ vectors of a basis adapted to the pairing with $w$. Its dual equals the projection of $W^*$ off $w$. Neither identity makes the section a terminal projection of $W$. Even splitting off a lift with pairing one generally projects the section obliquely in the resulting metric (orthogonally off the lift), shortening some lengths. Running this rule on a tail larger than β also exceeds the oracle budget. If an actual rank-β Haar parent is supplied, the **primal** global SVP followed by projection is implementable and Part 105 gives $0.925$ times own GH at rank β−1 with failure below 0.000234/0.000063. On an inherited tail its input-law hypothesis remains open. At rank 505 even a 0.9 own-GH guarantee needs determinant root about 5.57 physical to reach 27.454 by that bound. Neither terminal operation proves this scale and shape for a BKZ-selected tail. [Part 105](wall1_selection_law.md) · [Part 106](wall1_chain_law.md)

The determinant restart yields a test on the correct projected object within budget. The next mathematical question is whether its minimum observed prefix determinant has a sufficiently small upper tail. A theorem for the ideal Rankin minimizer alone would still leave that algorithmic question open.

## Audit note (Nov 2026)

Independent audit (Codex): CORRECT WITH MINOR ISSUES.

* **Simultaneous Haar flag bound.** The normalization is correct, via Kim's unfolded flag integral: the expected flag count is
  aT^N·c^d/(2ζ(d)) = 0.005/ζ(d). The bound holds for every passing prefix (det K ≤ T) on the same parent, with
  log T ∈ [547.83201620, 547.83202089].
* **Reducer miss probability.** Open. About 1.28·10²¹ passing prefixes are allowed on average, so the mean says nothing about
  existence.
* **Dual-section constants.** 0.98600 (406) and 0.98854 (506) hold in the section metric only. They do not transfer to a
  projected block without a further metric argument.
* **Coordinate restart.** It gives exactly Z^d, with physical minimum 1.
* **Rounding.** 27.4538 is rounded to nearest. The downward value is 27.4537.
