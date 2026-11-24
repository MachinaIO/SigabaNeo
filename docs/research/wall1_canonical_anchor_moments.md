# Canonical anchor moments by completion of squares

This paper-level bound applies only to the certified H6 two-four charts
(Gram determinant 12 or 16) and H7 shared-four charts (determinant 15).
It is not a new Lean theorem or a proof of adaptive BKZ selection.

Write A for the two omitted columns, H=I+AᵀA, G=I+AAᵀ,
and τ=π²/(q²α). For y=x+qz,

    ||y+Ab||²+||b||²
      = yᵀG⁻¹y + (b+H⁻¹Aᵀy)ᵀH(b+H⁻¹Aᵀy).

Poisson positivity bounds every shifted H-theta by its centered value C.
The exact anchor normalizer ψ(0) is at least C from the z=0 terms.
Consequently the normalized anchor f₀ satisfies

    f₀(x) ≤ Σ_z exp(−τ(x+qz)ᵀG⁻¹(x+qz))
          ≤ Π_i φ_{λα}(x_i),

where φ_β(x)=Σ_z exp(−π²(x+qz)²/(q²β)). The spectral upper bounds
λ are 6, 4, and 5 for determinants 12, 16, and 15 respectively.
There is no additional division by the earlier Gram normalizer boost.

Let R_L=q⁻¹Σ_x φ_{λα}(x)^L, h=φ_{λα}(0), and let ρ_L bound
the normalized free-coordinate moment. On the affine hyperplane, solve
for one old coordinate, or one free coordinate if present. With r₀ old
coordinates and f free coordinates this gives

    η_L ≤ h^L R_L^(r₀−1) ρ_L^f,
    η_L ≤ R_L^r₀ ρ_L^(f−1)       (f>0).

Both bounds may be minimized with previous valid moment bounds.
The first remains valid for f=0. R_L is unnormalized and must not be
clipped at one. The scalar centered-alias binomial bound used for free
moments also bounds R_L before normalization and clipping.

Implementation retains all previous completion candidates. The exact
rational test checks 3,645 completion-square and spectral residual
identities across the three canonical charts, plus a regression where
raw moments exceed one. These finite checks supplement the general
algebraic argument; they do not replace it.

## Weighted diagonal refinement (Part 439)

For positive weights w, set d_i=G_ii+Σ_(j≠i)|G_ij|w_j/w_i.
The matrix diag(d)−G is positive semidefinite because its quadratic form is
Σ_(i<j)|G_ij|w_iw_j(x_i/w_i−sign(G_ij)x_j/w_j)².
Consequently distinct scalar widths d_i α can replace λα. The hyperplane
bound minimizes over the coordinate removed; its maximum factor is h_i^L.

Weights one on shared rows and t on other rows yield profiles
(5+2t,5+2t,2+2/t,2+2/t) for D12 and
(3+4t,3+1/t,3+1/t,3+1/t,3+1/t) for D15. The grid t=1,3/2,2,3
is retained alongside the scalar bound. Every chart has the stated profile
up to permutation. All 27 charts and 19,116 weighted-square identities pass.
The D16 family retains its scalar profile.

The isolated refinement gave a through24 envelope below0.007831; through17
remained below3.219e-17. This is still above the3.01e-12 target. Logs are
`/tmp/wall1_diagonal_cumulants.log` and `/tmp/wall1_diagonal_frontier.log`.
The subsequent [correlated moments](wall1_correlated_anchor_moments.md)
retain the full rational Gram matrix and are minimized against these bounds.
