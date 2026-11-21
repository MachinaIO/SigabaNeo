# Random near-shortest block selection

Write $a=1+\varepsilon$. A block query samples a nonzero projected vector of norm at most $a\lambda_1$. For $1\le a<2$ all candidates are primitive, since dividing a nonprimitive candidate by its multiplicity would beat the minimum. Sampling signed vectors thus samples unoriented lines uniformly. For larger factors restrict to primitive vectors if the result must extend to a basis. Fix lift and unimodular completion rules as part of the algorithm. Computing the exact radius and sampling this finite set are oracle operations here.

## Profile of the returned basis

Suppose every maximal overlapping projected block in the **final basis** has first Gram–Schmidt length at most $a$ times its minimum. This condition passes to right truncations because restriction can only increase the minimum. Put $S_j=\sum_{i<j}\log g_i$ after normalizing the lattice to determinant one. Hermite's inequality in a truncated block of length $l$ gives
$$
l(S_{i+1}-S_i)\le S_{i+l}-S_i+l c'_l,\qquad c'_l=\tfrac12\log\gamma_l+\log a.
$$
In particular the entire Part 6 upper envelope is obtained by running its recurrence with $c'_l$. Explicitly put $w_n=w_{n-1}=0$ and, backwards for $j=n-1,\ldots,1$, set
$$
w_{j-1}=\max_{2\le l\le\min(\beta,n-j+1)}
 (l w_j-w_{j+l-1}-l c'_l)/(l-1).
$$
Then $S_j\le w_j-(1-j/n)w_0$. The right side has zero endpoints and satisfies every inequality with one equality at each interior index. At a positive leftmost maximum of the difference, that equality bounds the difference by a convex combination of its left neighbor and a right neighbor, a contradiction. Restore the scale by multiplying the prefix determinant bound by $\det(L)^{j/n}$. In the coarser repository first-vector bound the replacement multiplies the length guarantee by $a^{1+(n-1)/(\beta-1)}$. [Part 6](wall1_prefix.md), [profile theorem](../PROOF_GAP.md)

An existence construction for this profile is to sample the first vector from the entire projected suffix, recursively in the quotient. This takes $n$ queries and delivers the displayed overlapping-block conditions by restriction, at the cost of an initial dimension-$n$ oracle. The displayed inequalities alone certify only a checked output of a width-limited overlapping tour.

For slide there is a width-limited terminating variant on the repository's equal blocks ($n=t\beta$, $\beta>1$). In each aligned block insert a random near-minimum first. These updates preserve all aligned boundary lattices and the projected lattices of the other aligned blocks. Test each once-shifted reciprocal block. If its last reciprocal GS test vector (the dual row orthogonal to all preceding primal block rows) has norm greater than $b\lambda_1^*$, with $b\ge a$, choose a reciprocal near-minimum within factor $a$ and use it as last dual basis row by unimodular completion. Restart the primal pass after this update. On a clean scan all primal and dual tests hold simultaneously. In an integral ambient lattice this terminates: the product of squared covolumes of proper aligned boundary prefixes is a positive integer. Primal updates preserve it. A shifted dual update changes only the one boundary just before its last row. In the quotient by the fixed initial prefix the covolume of the first $\beta-1$ rows equals the full block covolume times the norm of their primitive reciprocal normal (height times base equals volume). Thus the affected boundary covolume strictly decreases. The same proof works after a common integral rescaling. This is an oracle variant, without a tour complexity estimate. [Slide conditions](../../SigabaNeo/Lib/Lattices/Reduction/Slide/Conditions.lean)

Here is its Hermite bound. Let $x_j$ and $V_j$ be the initial GS length and determinant of aligned block $j$, starting at zero. Put $H=a\sqrt{\gamma_\beta}$ and $K=b\sqrt{\gamma_\beta}$. The shifted determinant is $V_j x_{j+1}/x_j$, so primal and reciprocal Hermite give
$$
x_j\le H V_j^{1/\beta},\qquad
1/x_{j+1}\le K(V_j x_{j+1}/x_j)^{-1/\beta}.
$$
Consequently $x_j\le C x_{j+1}$ for $C=(HK)^{\beta/(\beta-1)}$. Multiplying $V_j\ge(x_0 C^{-j}/H)^\beta$ yields $x_0\le H C^{(t-1)/2}\det(L)^{1/n}$. This controls slide boundaries. It does not imply Part 6 at every index. An untruncated discrete Gaussian has positive probability of zero and of arbitrarily long vectors at every finite positive parameter. A smoothing estimate alone supplies neither profile test. Conditioning on the primitive ball restores the length guarantee with nonuniform weights.

## What a coupling would have to bound

At a matched history let $S,T$ be the two finite candidate sets in common coordinates. Uniform selection has exactly
$$
d_{\rm TV}=1-|S\cap T|/\max(|S|,|T|),
$$
by summing the smaller atom masses. Deleting just one of $N$ lines costs $1/N$ **if the remaining set is identical**. Even nested lattices need not give nested candidate sets at their respective relative radii. A block need not contain the projected plant at all.

In the embedding $L_A=L_0+\mathbb Z u$, where $L_0$ is the height-zero kernel. Removing all nonzero multiples of $u$ leaves a set that fails closure: $v+u$ and $-v$ remain for horizontal $v\ne0$. Taking their generated lattice restores $u$. Passing to $L_0$ deletes every nonzero-height coset. Imposing a single congruence instead can delete almost every near-minimal candidate: in $\mathbb Z^r$ mark $e_1$, take $1\le a<\sqrt2$, and impose $\sum_{i<r}z_i=0\bmod 2$ (indices $1,\ldots,r$). Both minima are one. Only $e_r$ survives among the $r$ axis lines, so TV is $1-1/r$, whereas direct mark selection has probability $1/r$. Conditional on missing the mark, TV from the reference is still $1-1/(r-1)$ for $r\ge2$. Dimension alone gives no lower bound on candidate abundance either: a rectangular block with spacings $1,M,\ldots,M$, $M>a$, has one primitive candidate line.

For the same-design null comparison replace the syndrome target $As+e$ by independent uniform $b'$. Given $u$, membership of $u$ has probability $q^{-m}$ in the null law and one in the planted law. In fact the planted joint input law is precisely the null law conditioned on membership, hence input TV is $1-q^{-m}$. This is an obstruction to an input-agreement coupling, **not** a lower bound on output TV.

For a valid trajectory comparison condition each experiment on its own transcript. If the next full observable transition kernels at each common history have TV $\delta_i(h)$, couple maximally until first disagreement, padding stopped paths with a stop symbol. The probability of disagreement by step $T$ is at most $\sum_{i\le T}\mathbb E_{\rm real}\delta_i(H_{i-1})$, by summing disjoint first disagreements and dropping the agreement indicator. Include stopping decisions, completions if observable, and the terminal marked test as needed. Infinite sums follow by monotone convergence. Candidate overlap computes one transition only given the blocks; latent blocks need their own conditional coupling. Even exact agreement of output planes cannot compare a marked event evaluated on different lattices. [Earlier trajectory calculation](wall1_coupling.md)

For a finite uniform candidate kernel, the information about $A$ released by a line $X$ conditional on $U$ and prior transcript $H$ is $H_2(X\mid U,H)-\mathbb E\log_2|S|$ when $S$ is determined by $(A,U,H)$ (here $H_2$ denotes Shannon entropy in bits). Large sets can encode the whole design index if their supports are disjoint. The identical argument with the plant as index precludes an entropy bound based solely on the denominator. For Part 38 the reference resamples $A$ independently given $U$ and keeps the conditional plane marginal; it is still a planted experiment. TV to a different null selector does not directly bound this KL divergence. The terminal failure includes capture, nonprimitivity and ties. Part 34 requires the selected competitor count and primitivity probability; Parts 31 and 37 explain why basis or isometry randomization cannot replace that calculation. [Selection inequality](wall1_analyzable_reducer.md), [selected moments](wall1_second_moment.md), [exchangeability](wall1_exchangeable.md), [random scales](wall1_random_scale.md)

## CBD(3), 511 samples, 512 secret coordinates, modulus 3329

The ambient dimension is 1024. The general shell comparison yields only the upper bound **one** on terminal failure at all three widths; no lower bound on selected shell overlap has been established. The following distinctions quantify the obstruction.

| Width | Full-input prefix rank | Available comparison |
|---:|---:|---|
| 406 | 618 | Every plane fixed independently of both plant and design has terminal success below $2^{-678.61}$ (Part 40). |
| 512 | 512 | At maximal syndrome rank 511 a fixed plane projects the lattice onto the entire projected integer lattice. Only one signed pair can pass the uniqueness test. |
| 647 | 377 | Deleting 377 predetermined sample coordinates gives failure at most 0.00483352 (Part 39). In the resulting 647-dimensional input the terminal prefix is empty. |

In particular at 406 data processing against the product of the plane marginal and the joint input marginal gives $I((A,U);P)\ge s\,678.61-1$ bits for actual terminal success $s$. At 99% this exceeds 670 bits. This conclusion concerns the sum $I(U;P)+I(A;P\mid U)$; Part 40 exhibits a plant-informed selector with zero second term. At 512 a numerical fixed-plane upper bound follows from the same rank calculation: the chance that the plant residue belongs to the plane modulo $q$ is at most $(5/16)^{511}$. Otherwise the random residual matrix has one more column than rows, giving rank-defect probability at most $1/[3329(3329-1)]$. On maximal rank, hitting either preassigned shortest vector requires at least 511 CBD pivots, hence contributes at most $2(5/16)^{511}$ unconditionally. Total fixed-plane success is below $9.03\cdot10^{-8}$. Neither fixed-plane estimate applies to an adaptive output. [Part 40](wall1_finite_family.md)

At 647 the reported number concerns exact shortest-pair uniqueness. For the punctured integral lattice one can even ensure the same pair is the entire sampling shell on that event: $R^2\le 1+646\cdot9=5815$, and every longer squared norm is at least $R^2+1$. Thus $a<\sqrt{1+1/5815}$ suffices. With this positive slack there is **one** candidate line with probability at least 0.99516648 in the prescribed terminal block. It supplies no abundance estimate in earlier adaptive blocks. Parts 41–43 likewise count admissible prefixes or witnesses without assigning trajectory probabilities. No heuristic shell populations, new recovery probabilities for the full-input reducer, or runtime bounds enter these conclusions. [Part 39](wall1_projected_reference.md), [bounded covolume](wall1_sublattice_union.md), [profile filter](wall1_profile_union.md), [filtered moment](wall1_filtered_moment.md)
