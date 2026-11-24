# Correlated canonical anchor moments

This analytic argument concerns the certified H6/H7 canonical Gaussian kernels.
It does not prove the adaptive BKZ selected-history law.

Let M=G⁻¹, G=I+AAᵀ, τ=π²/(q²α), and
H(x)=Σ_z exp(−τ(x+qz)ᵀM(x+qz)). Completion-square cancellation bounds
the normalized canonical anchor by H. Let λ bound the largest eigenvalue of G.

Expand H(x)^L. Set y=x+qz₁, w₁=0, wᵢ=zᵢ−z₁, and w̄=L⁻¹Σᵢwᵢ.
The exact energy identity is

    Σᵢ ||y+qwᵢ||²_M
      = L||y+qw̄||²_M + q²(Σᵢ||wᵢ||²_M − L||w̄||²_M).

Cauchy–Schwarz on the L−1 nonzero difference variables bounds the second
parenthesis below by L⁻¹Σᵢ≥2||wᵢ||²_M, hence by
(Lλ)⁻¹Σᵢ≥2||wᵢ||². No fractional center is rounded.
Poisson positivity bounds each shifted lattice theta by its centered value.
Consequently, with C_L=theta(τq²/(Lλ))^{r₀(L−1)}, the uniform full mean is

    E_x H(x)^L ≤ C_L Θ_Z^r₀(LτM)/q^r₀.

For the affine hyperplane Σxᵢ=s modulo q, y ranges over a coset of
Λ={y∈Z^r₀ : Σyᵢ=0 modulo q}. The same shifted-theta bound removes this
coset and the real shift qw̄. Write E=[e₁−e_r,…,e_(r−1)−e_r].
Decompose Λ into layers Σyᵢ=qj and complete the square at the real center
qj G1/(1ᵀG1). Each layer's remaining lattice is a translate of E Z^(r₀−1).
Since Aᵀ1=(1,1), 1ᵀG1=H₀=r₀+2. Thus, uniformly in s,

    E_{Σx=s} H(x)^L
      ≤ C_L Θ_Z^(r₀−1)(Lτ EᵀME) theta(Lτq²/H₀)/q^(r₀−1).

For any positive definite rational matrix, successive completion of squares
bounds its integer theta above by the product of scalar thetas at its LDL
pivots. The determinant is retained in the product of the pivots. Every
certified chart must be checked; profiles are maximized within a family,
not assumed identical merely because determinants agree.

Multiply the hyperplane bound by the normalized free-coordinate moment to
the power f. Alternatively, if f>0, solve for one free coordinate, use its
normalized supremum one, and multiply the full-mean bound by the remaining
f−1 moments. Retain previous bounds by minimization. Neither the new raw
bounds nor their factors are clipped individually or divided by a Gram boost.

## H5 D15 extension (Part 441)

The six c3/H5 exceptional codes admit bases (s,3,4), s in {0,1,2}.
Their omitted columns have integer entries, sum one, norm squared three,
and inner product −1. Up to exchanging the last two rows, A has rows
(1,1),(1,−1),(−1,1). Exact LDL pivots are (1/3,3/5,1/3) for G⁻¹
and (14/15,5/14) for the root Gram; λ=5. This uses a separate H0=5
scope: D15 alone does not distinguish H5 and H7. The cache and profile dispatch
now include the anchor size.

The integration captures the isotropic one term before weighted D23 and
reconstruct its filtered determinant counts using fixed_four_plane(D/4)^N.
It captures bad6 before the weighted ball replacement. With pref=exp(5βR²)/q^(3m),
the split is pref*bad_count/Q*bad_bound^N and pref*(safe_one+none_power).
Here bad_count=6 only for overlap2, removed by exclude_five_fifteen; Q=q³.
The completed candidate has choices*q³*freecost^(r−3)/(r−2), no extra half.
See [H5 normalizer](wall1_five_point_normalizer.md) for the implemented split,
independent chart enumeration, and validation. Part440 numbers precede this extension.
