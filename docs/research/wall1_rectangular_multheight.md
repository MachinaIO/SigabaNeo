# Multiple heights certify contraction in the 400-marked rectangle

For the fixed rectangular state of `wall1_lattice_radial_profile.md`, the
actual next capped void potential contracts in expectation. This resolves
that example's previously open one-step transition; it does not prove the
selected-history estimate for general reachable states.

Use q=3329,m=400,g=550 and the same ell,c defined there:
M=ell Z^400 plus c Z^105, K=(ell/q) Z^400 plus c Z^105.
The incoming radius is R²=605²−1. All graph lattices contain an unmarked
horizontal vector of length c, so the actual shortest winner satisfies s<=c,
regardless of the fresh mark U. Thus its outgoing radius is at least

    B²=605² c^(−2/506)−1.

The actual projection can only decrease the norm of a candidate lift. No
law or independence for the winner is assumed.

## Fixed-state shared-mark moment bound

Put X(v)=center(v)^2/q² and fix J={−16,...,16}, theta=1/10.
If an outgoing mark v is missed, every lift at height j in J is missed even
before projection. Each such lift has squared norm

    ell² Σ_(i=1)^m X(v_i+j u_i)+j².

Multiplying the exponential upper bounds on these indicators gives a
simultaneous miss upper bound. Averaging v coordinatewise gives

    P'_u <= exp[(theta/ell²)(Σ_j j²−|J|B²)] Π_i K(u_i),
    K(u)=q⁻¹ Σ_v exp[theta Σ_(j in J) X(v+ju)].

This may exceed one; no unsupported clipping is applied inside the product.
The coordinates of a fresh uniform U in this fixed marked group are independent.
Raise the preceding bound to24 before averaging U. This yields

    E_U[(P'_U)^24]
      <= exp[(24theta/ell²)(Σ_j j²−|J|B²)]
         * (q⁻¹ Σ_u K(u)^24)^400.                        (1)

The same scalar u is shared across the24 auxiliary marks inside K(u)^24.
Replacing it with independent copies would give a different, invalid bound.
All residues and periodic wraparound are included exactly.

## Integer finite-sum certification

There are q²=11082241 pairs (u,v). Compute
S(u,v)=Σ_j center(v+ju)^2 in int64, exactly. For x=S/(10q²),
0<=x<=33/40. With Q=2^24 and degree16, set T_0=Q and

    T_d=ceil(T_(d−1) S/(10q²d)).

Induction gives T_d>=Q x^d/d!. The exponential tail is at most
(33/40)^17/[17! (1−33/40)], whose product with Q is below one.
Therefore (Σ_(d=0)^16 T_d+1)/Q bounds exp(x). Explicit integer inequalities
protect every product, sum, and row sum from overflow. The24th powers and
final sum of row bounds use Python arbitrary-precision integers. Their
average is an exact rational upper bound for the parenthesized factor in(1).
Only the geometry and final logarithms use outward interval arithmetic.

The certified results are

    E_U[(P'_U)^24] < 2.753e−40,
    E_U[min(1,(P'_U/.280)^24)] < 5.105e−27.                (2)

These are upper bounds, not measured probabilities or estimates of the actual
values. An independent implementation audit checked normalization, int64
ranges, the Taylor remainder, and the shared-mark law. Nine small finite
cases independently check the factorization and indicator bound with exact
rational weights and detect the independent-u substitution error.

## Strict expected contraction

The incoming mark has squared distance ell²Σ_i X_i with iid uniform residues.
Use the same Berry–Esseen input as the original radial-profile note:
[Shevtsova, Corollary1](https://arxiv.org/pdf/1111.6554v1), constant0.4748.
Its assumptions hold because the centered finite-support variables are iid,
have positive variance, and have finite third absolute moment. The left-CDF
convention transfers to the right-CDF and strict tail by limits. Exact finite
moments and an alternating-series interval for the normal tail at z=1.3 give

    0.06412030525 < P < 0.12948066393 < .280.

Consequently the incoming capped potential is larger than4.326e−16, while
(2) bounds its outgoing expectation. The conditional expected increment is
strictly negative for this fixed state. It can therefore be assigned zero
nonnegative drift charge in the capped-potential argument.

This result does not imply that all subsequent states stay rectangular, or
that actual selected histories have this fixed geometry. That is the remaining
barrier to using it in the complete BKZ proof. The earlier shell obstruction
at a conservative radius remains mathematically valid: it omitted the joint
coverage supplied by many heights and the stronger available winner cap.

Run `OPENBLAS_NUM_THREADS=1 python3 docs/research/scripts/wall1_rectangular_multheight.py`.
Log: `/tmp/wall1_rectangular_multheight.log`. Run the independent checks with
`python3 docs/research/scripts/wall1_rectangular_multheight_checks.py`.
