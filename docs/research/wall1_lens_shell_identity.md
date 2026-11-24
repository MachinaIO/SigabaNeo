# Separate radial and discrete lens errors without enclosing-ball loss

This reorganizes the existing exact collision identity from
[the dual-cusp analysis](wall1_dual_cusp.md) and
[the full-family variance note](wall1_full_family_variance.md).
It retains the exact axial lens geometry, avoiding the factor-28 relaxation
identified in the [route screen](wall1_collision_route_screen.md).
It does not yet supply bounds for the two resulting discrepancy terms.

## Pointwise decomposition on the old-minimum gate

Let K have rank d and M subset K have index h>1 and determinant D.
Write rho²=r²−2 and suppose lambda_1(M)>r>rho. Use all nonzero candidates
S=(K intersect B_rho) minus {0}, with A=|S|>0, m=h−1 and nu=A/m.
For nonzero v in M set w(v)=#{x in S:x+v in S}.
The multiplicity square sum over nonzero marks is

    B=A+sum_(v in M, v!=0) w(v).

Since ||v||>rho, neither zero nor −v is in the lens. Thus removing the
origin from S does not alter any off-diagonal lens count. Define its
continuum volume and positive radial derivative by

    ell(t)=2 V_(d−1) integral_(t/2)^rho
                    (rho²−u²)^((d−1)/2) du,
    k(t)=−ell'(t)=V_(d−1)(rho²−t²/4)^((d−1)/2),  0<t<2rho.

Let N_M(t) count nonzero M points of norm at most t. Set

    J=integral_0^(2rho) [N_M(t)−V_d t^d/D] k(t) dt,
    E=sum_(v in M, 0<||v||<=2rho)
             [w(v)−ell(||v||)/det(K)].

The endpoint <=2rho is essential: tangent lenses have zero volume but can
contain a lattice point. E retains these contributions.
Stieltjes integration by parts gives sum ell(||v||)=integral N_M(t)k(t)dt.
Convolution gives integral (V_d t^d/D)k(t)dt=(V_d rho^d)²/D.
Therefore, with a=V_d rho^d/det(K), the exact identity is

    B=A+a²/h+J/det(K)+E.

Put delta=A/a−1. The variance over the h−1 nonzero fresh marks satisfies

    R=Var(Z)/nu²=m B/A²−1
     =1/nu + (m/h)/(1+delta)²−1
       + m/A² [J/det(K)+E].

This includes the diagonal term, origin exclusion and finite-h correction.
It holds separately at each actual entry history. Subsequent averaging must
retain all its state-dependent factors; ratios of expectations cannot replace
the expectations of these ratios. The relevant void upper bound is R/(1+R).

## What the minimum gate controls in this integral

The normalized continuum reference integrand (V_d t^d/D)k(t)dt has total
(V_d rho^d)²/D. Under x=t²/(4rho²), its normalized density is
Beta((d+1)/2,(d+1)/2). At d=505 this is Beta(253,253).
The old-minimum gate sets N_M(t)=0 for t<=r. Throughout the current
production scalar range, r²/(4rho²)<.251. The normalized reference weight
in that guaranteed-empty interval is less than

    I_.251(253,253)
     =sum_(j=253)^505 binom(505,j)(251/1000)^j(749/1000)^(505−j)
     <1.704e-33.

Thus the part of J directly fixed by N_M(t)=0 has an extremely small
reference weight. Most of the radial integral is around t=sqrt(2)rho,
beyond the old-minimum cutoff. This statement concerns the cumulative-count
kernel only. It is not the distribution of distances of two uniform ball
points, and it does not control N_M(t) above r or the whole value of J.

## Remaining analytic work and verification

J measures the selected old lattice's radial discrepancy; E measures the
projected grid's discrete lens discrepancy. Delta measures its candidate
count normalization. A valid bound must control their displayed combination
under the actual selected histories. Replacing J or E by zero would assume
the missing result. Bounding their absolute values separately can also
discard useful cancellation.

`python3 docs/research/scripts/wall1_lens_shell_identity.py` verifies the full
identity in 80 exact rational one-dimensional lattice examples, including
positive and negative E. It checks the continuum normalization at dimensions
1,3,505 with interval arithmetic, and the beta-tail bound using exact rational
arithmetic. Independent review confirmed the general decomposition and the
need to include tangent-lens boundary points. These checks identify the
remaining estimates; they do not improve the proved production probability
or complete the BKZ theorem.
