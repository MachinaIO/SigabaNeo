# Wall 1 · What survives a deferred reveal?

At final width 506, reserving 505 graph columns gives an exactly cubic horizontal quotient. Reserving 466 through 504 also fails the physical height-zero test, for **every** old prefix of the required rank. The obstruction is a collision among subset sums of the unread columns. In the middle range, deferred revelation gives an exact conditional counting law. It leaves a lower-dimensional old minimum and a count in an explicit old superlattice. I do not obtain a 99% bound there.

Use the plain independent graph with 511 sample axes, 512 secret axes and prime modulus 3329. Write its generators as the sample vectors scaled by q and the graph vectors (A_j,e_j), absorbing a harmless sign in A. Put d = β−1. At β = 506 the prefix rank is 518 and the horizontal output rank is 505. The physical floor from [Part 103](wall1_width_scan.md) lies strictly between 27.45 and 27.46. These rational endpoints follow by squaring twice in the formula √(1+3d/2−√(9d/198)). This is a necessary test for 99% conditional uniqueness. The height-one Voronoi test and the higher-height distances still apply. Projection can also lose the information needed to lift a successful terminal answer. [Part 94](wall1_threshold.md) · [Part 47](wall1_decoupled.md)

## A. Deferred graph columns

Read t columns, reserve f = 512−t, and choose a primitive prefix K in the old lattice using only the old input and independent coins. Condition on this whole history. Write Q for orthogonal projection off span K and G for the projection of the old lattice. Its rank is a = d−f, so t ≥ 7 at width 506. Only the new **secret axes** are orthogonal to K. The sample components of the corresponding generators generally project nontrivially. In the orthogonal coordinates (old quotient space, fresh axes), the final horizontal lattice is exactly

$$H=\{(g+\textstyle\sum_j z_j v_j,z):g\in G,\ z\in\mathbb Z^f\},\qquad v_j=Q(A_j,0).$$

In particular det H = det G. This is a rank-β final problem, provided preprocessing uses block calls of width at most β. A single exact call on the entire old lattice would exceed budget even at t = 7.

Let B = G + Q(ℤ⁵¹¹ × 0) in the old space and U = B/G. Since qB ⊂ G, U has order at most qᵃ. The displacements modulo G are independent uniforms on U by the homomorphism theorem. This is the graph-chart version of deferred revelation. Applying the uniform Grassmannian law of [Part 118](wall1_lit_projections.md) directly to all of H would discard the old constraints.

For a closed ball of radius R < q, conditional failure of the minimum test is certain if G contains a nonzero point in that ball. Otherwise an upper bound is the following first moment, capped at one:

$$\frac1{2|U|}\sum_{0<\|z\|\le R}\#\{b\in B:\|b\|^2\le R^2-\|z\|^2\}.$$

Here z runs over integer vectors. Each such z has a nonzero residue coefficient, hence its displacement is uniform on U. Each b belongs to exactly one coset, and negation pairs the witnesses. There is no independence assumption between different z. The old layer costs an indicator, not a term divided by the number of fresh shifts. For a threshold relative to own GH, substitute the radius computed from det G conditional on the history.

**A deterministic exclusion.** Map the binary cube of fresh coefficient vectors into U by their displacements. Whenever 2ᶠ > qᵃ, two images agree. Subtract and cancel the old displacement with an element of G. This gives a nonzero vector (0,z) with squared norm at most f. At width 506 the inequality holds for a ≤ 39: the endpoint check is the exact integer comparison 2⁴⁶⁶ > 3329³⁹. It reverses at a = 40 since 2⁴⁶⁵ < 3329⁴⁰. Throughout the excluded range √f ≤ √505 < 23, strictly below the necessary floor. At a = 0 the whole lattice is ℤ⁵⁰⁵. At t = 256 the ranks are a = 249 and f = 256. Neither layer can then be dismissed by rank alone. With f = 1 the old rank is already 504. At β = 406 the same check gives failure for a ≤ 31 (2³⁷⁴ > 3329³¹), with √f < 21 and the Cantelli floor above 24. The general rank rule is t ≥ 513−β. Thus the proposed dichotomy is rigorous at the cubic end, while old-rank dominance alone proves no middle-range impossibility.

## B. Random deletion after reduction

An independent random row mask, applied to the original coordinates with the old reduced basis discarded, gives exactly the punctured graph. Conditional on the mask and plant, a candidate with nonzero secret discrepancy meets r retained row equations with probability q⁻ʳ. The dimension is 513+r, already seven over budget at r = 0. The established 99% certificate uses r = 134, hence width 647. [Part 39](wall1_projected_reference.md)

If the old reduced span is used too, independence of the mask from the matrix says nothing about independence of that span from the retained rows. For example a stored first entry of each row reveals its retained entries even after independent masking. Choosing the span on deleted rows alone restores fresh retained rows, with the compatibility issue in C. Deleting secret coordinates also changes the equations: each eliminated independent secret column removes one modular constraint until their column space exhausts the retained row space. At width 506 a coordinate deletion retaining r rows must eliminate r+7 secret axes. The eliminated r by (r+7) matrix has full row rank except with probability at most (qʳ−1)q⁻⁽ʳ⁺⁷⁾/(q−1), by counting projective left null lines. On full rank the projected horizontal lattice is cubic. This bound assumes an independent mask.

## C. Two disjoint sets of sample rows

Keeping the fresh 255 or 256 rows with all secret coordinates gives widths 768 or 769, exceeding 506 by 262 or 263. Either half supplies the 134 rows used at 647. Halving the sample count alone therefore costs no width for the existing certificate. To fit 506, a further prefix must remove exactly the excess above. A training prefix supported on sample axes of the discarded half removes none of these remaining dimensions.

More generally embed a training prefix by zero-padding its fresh sample coordinates. If its secret residues span rank s, each fresh row must annihilate that span for the prefix generators to be lattice members. Conditional probability is exactly q⁻ʳˢ for r fresh rows. Filling in the missing sample coordinates using those rows restores membership but makes the Euclidean projector depend on the holdout. Alternatively one can project a fresh lattice along the trained rational *space* without requiring these generators to belong: conditional on training this is just a prescribed-plane experiment, with the actual prefix equal to the intersection. One must recompute its determinant and metric. This distinction rules out transferring the training prefix determinant to the fresh quotient.

## D. Dual selection

A dual graph vector can be written (u/q,w−Aᵀu/q) with integral u,w. For a prescribed old dual vector with nonzero sample residue, zero-padding its fresh entries is compatible with probability q⁻ᶠ. For several vectors with residue span s this becomes q⁻ᶠˢ. For f = 256 and s = 1 this is already below 2⁻²⁸¹⁶ since q > 2048. Sample numerators divisible by q impose no fresh constraint. Completing fractional entries gives an exact fresh modular law, but the completed dual space then depends on the same fresh columns. Moreover the dual of a projected lattice is a section. A certificate for a short-vector minimum in the section does not transfer through inversion of the Gram matrix. At width 506 the relevant dual section must have rank 505; switching sides saves zero ranks. [Part 115](wall1_idea_variants.md)

## E. Independent pilot and a smaller proof obligation

Train a rational plane on an independent pilot matrix of the same shape and apply it, unchanged, to the target graph. Conditional on the pilot, Part 118 applies literally through the graph-chart comparison: in the uniform-code model, conditional on image dimension s, each represented residue line is hit with probability (qˢ−1)/(qᵈ−1). A point of qF in the test ball is deterministic, where F is the projection of the ambient integer lattice. For the full independent graph one can bound the joint bad event before charging the inverse chart probability. Choosing pilot prefix rank 518 fits final width 506. This removes the history average for the target. It also removes the correlation that made the pilot prefix short in the first place. The prescribed-plane obstruction in Parts 40–41 of the [gap summary](../PROOF_GAP.md) is relevant; averaging over independent pilot planes cannot exceed a uniform upper bound for fixed planes.

The intermediate split in A gives the most direct remaining proof question. For example, at t = 256 one needs a joint bound on the rank-249 minimum event and the truncated rank-249 ball counts in B divided by [B:G], averaged over training. These two quantities suffice for a horizontal first-moment bound at any prescribed physical radius; conditioning further on G alone need not determine B. This avoids propagating selected flags through the 256 fresh columns. It gives no bound on the old event itself. Nor does the determinant guarantee of Part 114 for the original greedy tour transfer to this modified reducer. The binary-cube exclusion and the conditional moment are finite statements about the modified quotient. A width-506 terminal uniqueness or recovery certificate remains open.

## Audit note (Nov 2026)

Independent audit (Codex): CORRECT WITH MINOR ISSUES.

* **Collision obstruction (466 ≤ f ≤ 505).** Verified: 2^466 > 3329^39. The collision gives a nonzero vector (0, z) in the final
  horizontal block with ‖z‖² ≤ f ≤ 505 < 23². This rules out 99% conditional uniqueness for every such design.
* **Conditional first moment at f = 256.** Exact for R < q. An exhaustive toy check agrees.
* **Triage of (B)–(E).** Verified.

Wording corrections:

* The fresh secret axes are guaranteed orthogonal to K. Particular old axes may also be orthogonal.
* "At any prescribed physical radius" must keep R < q. At R = q, q·e_j has deterministic zero displacement.
