# One isotropic metric for a forward sweep

An orthogonally invariant perturbation can erase the axis discrepancy of Part 18 in three dimensions and still fail to give a covolume-only law one insertion later. The cause is a reversal of the ordering of two coordinate lengths upon projection. The following probability gap is strictly positive at every fixed noise radius. It need not stay bounded away from zero as the noise vanishes.

## Four-dimensional binary example

Take the integer kernel of one uniform binary row in dimension four. Use the forward width-two sweep and coordinate-adapted basis of [Part 18](wall1_smoothed.md). Choose one metric for the entire sweep. Put
\[
 G=S B,\qquad B=I+E,\qquad 0<\epsilon<1/100,
\]
where E is uniform in the Frobenius ball of radius ε in real symmetric four-by-four matrices, and log S is independently uniform on [−4ε,4ε]. Both draws are independent of the row. This full-dimensional law is invariant under orthogonal conjugation. A deterministic scalar normalization could also make its mean exactly the identity, rescaling all measured areas and squared lengths together.

Write H₂ and H₃ for selection of unit axis 1 followed by the projected unit axis 2 or 3, respectively. After either unit deletion the residual integer coordinates are exactly the kernel of the residual row, since the deleted check coefficient is zero. An adapted basis visits the first two remaining coordinates, irrespective of the completion inside the preceding block. All projected metrics for B have spectrum in [1−ε,1+ε], by minimizing the quadratic form over real lifts. Thus any available unit beats all integer vectors of Euclidean squared norm at least two. Ties have probability zero by the density and polynomial argument of Part 18.

When the first three bits vanish, let p be the likelihood of H₂. Axis 1 must win the first comparison, an event of probability 1/2. The likelihood of H₃ is therefore 1/2−p. With
\[
 T_j=B_{jj}-B_{1j}^2/B_{11},\quad j=2,3,
\]
the second choice on these histories compares T₂ and T₃. When B₁₁ is smallest among the first three diagonals, exchanging indices 2 and 3 preserves that event and interchanges the two second choices. Hence
\[
 p=1/6+\delta,\qquad
 \delta=\Pr[B_{33}<B_{11}<B_{22},\ T_2<T_3].
\]
This term survives isotropic averaging. For explicit constants take h=ε/4 and the symmetric center with B₁₁=1, B₂₂=1+h²/4, B₃₃=1−h²/4, B₄₄=1, B₁₂=B₂₁=h and remaining off-diagonals zero. The Frobenius ball of radius ρ=h²/100 about this center lies inside the sampling ball by the triangle inequality. Each entry changes by at most ρ, preserving the two strict diagonal inequalities. Throughout the ball,
\[
 B_{22}-B_{33}\le h^2/2+2\rho
 < ((h-\rho)^2-\rho^2)/(1+\rho)
 \le (B_{12}^2-B_{13}^2)/B_{11}.
\]
Thus δ ≥ (ρ/ε)¹⁰ = (ε/1600)¹⁰ by the volume ratio in dimension ten.

## Conditioning on the exact terminal area

For each history let r be the surviving bit among the first three and d the fourth bit. The two deleted bits must vanish. With r=0 the history likelihoods are p and 1/2−p. With r=1 they are respectively 1/2 and 1. Indeed row prefix 001 ties the two available units in the Euclidean first plane, resolved by the sign of B₁₁−B₂₂, and then forces axis 2. Prefix 010 forces both choices for H₃. None of these decisions uses d or S.

The terminal area is D=kSC where k=1 for (r,d)=(0,0) and k=2 otherwise, and C is the square root of the determinant of the terminal Schur complement of B. Its spectral bounds give |log C|<2ε. On the interval J=2[exp(−2ε),exp(2ε)] only index two contributes, since exp(4ε)(1+ε)<2 exp(−2ε). Every index-two realization of the row and B has the same conditional density 1/(8εD) throughout the interior of J. Consequently conditioning on the measured D there introduces no further relative weighting of those realizations. Each history has positive probability in that interval.

The event F that the terminal squared minimum exceeds 3/2 detects (r,d)=(1,1) exactly. In this case every nonzero integer vector in the kernel has Euclidean squared norm at least two and 2 exp(−4ε)(1−ε)>3/2. Otherwise a unit survives and exp(4ε)(1+ε)<3/2. Summing the three equally likely nonzero bit pairs with their history likelihoods gives, almost everywhere on J,
\[
 \Pr(F\mid H_2,D)=1/(2+2p),\qquad
 \Pr(F\mid H_3,D)=1/(5/2-p).
\]
The second exceeds the first by 3δ/[(2+2p)(5/2−p)] ≥ 2δ/5, since p≤1/2. Any common area-dependent prediction therefore incurs absolute error at least (ε/1600)¹⁰/5 on one history. Conditioning the row to be nonzero preserves these formulas, since index two already implies that condition.

By comparison, the two three-dimensional unit-axis histories of Part 18 are interchanged by a coordinate transposition under isotropic noise and the iid row law. Their joint measures with the terminal area and minimum agree. In four dimensions a calculation that merely orders the original diagonal entries would give p=1/6 and identical tails. The Schur correction is essential even for the sign of the discrepancy.

This is an obstruction for a single forward sweep on an unmarked modular kernel. It rules out exact area sufficiency under isotropic smoothing in general. It leaves open quantitative approximation at small noise and conditioning on a richer state. For the planted ensemble, changing the metric with a prefix fixed leaves divisibility in the quotient group unchanged. Estimating recovery for a fully reduced basis or the verified slide output still requires the joint selected-prefix probability of a nonzero primitive plant class and strict separation from other lines. The example supplies no block-size improvement or planted failure rate.


## Independent audit (Nov 2026)

Verdict: **correct** (explicit ball checked exactly at ε = 1/100, 1/1000, 10⁻⁶; final formulas verified). The lower bound on δ is valid but extremely weak: Monte Carlo at ε = 0.009 gives δ ≈ 1.6·10⁻⁷ versus the proved bound 3·10⁻⁵³.
