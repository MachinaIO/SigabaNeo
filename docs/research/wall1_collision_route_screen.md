# Screening two routes to the production collision estimate

The actual selected-history collision bound remains open. Two independent
research checks identify losses that must be avoided before scaling the
[pair evaluator](wall1_selected_pair_collision.md) to dimension 505.
Neither calculation below bounds actual BKZ failure from below.

## The enclosing ball loses the axial restriction

For S=K intersect B_rho, the multiplicity of a difference v is the number
of K points in B_rho intersect (B_rho−v). Completing the square gives

    B_rho intersect (B_rho−v)
        subset B_sqrt(rho²−||v||²/4)(−v/2).

Replacing each lens by this enclosing ball loses substantial mass before
any lattice discrepancy or selected-history issue is considered. In the
continuum, with d=505 and b=d/2,

    integral V_d (rho²−||v||²/4)_+^b dv
       = (V_d rho^d)² C_d,
    C_d=2^d Gamma(b+1)²/Gamma(2b+1)=28.17867867058... .

This follows by radial integration and the substitution
x=||v||²/(4rho²), whose normalized density is Beta(b,b+1).
In contrast, the integral of the exact lens volume is (V_d rho^d)² by
Fubini applied to the convolution of two ball indicators.

The old-minimum gate removes differences ||v||<=r where rho²=r²−2 and
r=1.1g. On the entire current scalar range, r²/(4rho²)<.251.
For X with the beta density above, its mean is b/(2b+1) and variance
b(b+1)/((2b+1)²(2b+2)). Cantelli therefore gives

    C_d P(X>.251) > 27.95458043.

Even substituting ideal continuum densities 1/det(K) for candidate points
and 1/det(M) for differences into this particular majorant leaves the
normalized collision ratio above 27.95. The resulting Cauchy–Schwarz void
certificate is greater than .96422, failing the existing .126 or .1795
ceilings. This is a benchmark for a relaxation, not an assertion that
selected differences have continuum density or that true variance is large.

The precise information to retain is axial. Write y=x+v/2, ell=||v||,
and t=<y,v>/ell. The exact lens condition is

    ||y_perp||²+(|t|+ell/2)² <= rho².

Its continuum volume is

    2 V_(d−1) integral_0^(rho−ell/2)
        [rho²−(t+ell/2)²]^((d−1)/2) dt.

A lattice-slice estimate preserving this axial restriction avoids the
built-in factor-28 loss. Its discrepancy and the selected radial weights
are still unproved; the continuum normalization alone does not bound them.
The [lens/shell decomposition](wall1_lens_shell_identity.md) separates those
two errors exactly and identifies which part the old-minimum gate controls.

## Independent randomized deletion has a rank cost

Let V be the frozen graph-input residue span in F_q^k, of dimension t,
and let a canonical witness input residue v lie outside V. Choose a
uniform nonzero functional H independently of the random matrix. Exactly
q^(k−t−1)(q−1) functionals satisfy HV=0 and Hv!=0. Thus

    p_t=P_H(HV=0,Hv!=0)=q^(k−t−1)(q−1)/(q^k−1).

For every nonnegative canonical weight W(A), on a fixed-t stratum,

    E_A W = p_t^(-1) E_(A,H)[W 1_{HV=0,Hv!=0}].

This preserves the actual selection weights and avoids enumerating all
flags. For each independently fixed H the
[congruence-section agreement argument](wall1_generalized_deletion.md)
allows the hidden map to be exposed before imposing agreement. However,
the reciprocal cost is at least q^t (equality only at t=0).

For the frozen graph section, t=f−400+d_F: the kernel of the syndrome
map on the f-dimensional primitive integer section has this dimension,
and its input projection is injective. The conservative live table in
[the integrality bound](wall1_integrality_bound.md) gives d_F>=115 at
f=405 outside its stated exceptional event. Consequently t>=120 and

    log10(p_t^(-1)) >=120 log10(3329)>422.6776554.

This estimate is deliberately tied to that table and its exception.
Witnesses with v in V are undetected and need separate treatment.
Choosing H from the annihilator after observing V would remove this
counting cost, but would make H matrix-dependent; the independent hidden-map
law could no longer be used without proving its conditional distribution.

Finally, dropping agreement is safe for a nonnegative collision weight,
but not for a signed centered correction. Bounding only the positive term
throws away the cancellation against the squared mean needed by the
variance target. A useful deletion argument must preserve that cancellation
and agreement, or pay the displayed cost with a stronger estimate.

## Validation and remaining task

`python3 docs/research/scripts/wall1_collision_route_screen.py` verifies the
lens constants by outward interval arithmetic and checks the mask identity
by complete enumeration in 30 finite cases. Independent agents derived the
two routes; parent verification checked the formulas, constants and source
scope of the conservative rank bound.

These checks direct the next research toward exact axial lens counts and
agreement-preserving centered deletion estimates. They do not supply the
production collision bound, a new BKZ failure probability, or a Lean theorem.
