# Optimizing a square against the actual mixed moments

Part 273 uses a Charlier kernel chosen for a Poisson reference. The selected tail
objective instead weights the competitor count Z by a nonnegative collision
polynomial g(J), together with saturation. Its best fixed-degree square can be
computed directly from those mixed moments, without a reference distribution.
This note gives an exact algebraic certificate of that optimality. It does not
evaluate the needed moments for the width-506 restart.

## Weighted Gram matrix

Fix the proposed flag, the collision polynomial g, and degree t. Work conditional
on containment, and let S be saturation. Put phi_h(z)=(z)_h, h=0,...,t, and

\[
 M_{ij}=E[g(J)1_S\phi_i(Z)\phi_j(Z)\mid\mathrm{contain}].
\]

This matrix is positive semidefinite: for any real vector c,
c^T M c=E[g(J)1_S(sum_i c_i phi_i(Z))^2 | contain]>=0. Define the weighted
subset moments A_h(g) as in Part 273. Then its entries are exactly

\[
 M_{ij}=\sum_{v=0}^{\min(i,j)}{i\choose v}{j\choose v}v!
                             (i+j-v)! A_{i+j-v}(g).           \tag{1}
\]

Only subset degrees through 2t and collision degrees through two are needed
when g is quadratic. The same grouped rank sums therefore supply the data.

Since phi_0(0)=1 and phi_i(0)=0 for i>0, the normalization p(0)=1 is just c_0=1.
The finite optimization is

\[
                    \min_{c_0=1} c^T M c.                    \tag{2}
\]

This optimizes over all degree-at-most-t squares with that normalization, for
the specified g and actual mixed law. It does not optimize g, the radius, or
the flag family, and does not claim optimality among every nonnegative polynomial.

## Exact certificate, including singular matrices

Partition M as [[M_00,b^T],[b,A]]. Solve A x=-b and put c=(1,x). The implementation
uses rational elimination, sets free variables to zero, and checks (Mc)_i=0 for
every i>0. For every other normalized coefficient vector d, write h=d-c. Then
h_0=0 and

\[
                  d^T M d-c^T M c=h^T M h\ge0.               \tag{3}
\]

Thus the checked stationarity equation and PSD condition prove global optimality.
No matrix inverse or positive-definiteness assumption is needed. For completeness,
PSD implies b is orthogonal to ker A: otherwise the quadratic form on (1,uv)
for v in ker A becomes negative for one sufficiently large signed u. Symmetry
then makes the linear system consistent. Rational elimination produces a rational
solution when the moment entries are rational.

The PSD check uses exact Schur complements. A positive diagonal pivot removes
one square and leaves its Schur complement. A zero diagonal pivot requires all
remaining entries in its row to vanish; otherwise its quadratic form can have
either sign by varying that coordinate. Negative pivots or a nonzero such row
are rejected. This permits zero and singular Gram matrices and uses no tolerance.

The pointwise inequality from Part 273 remains unchanged:

\[
 g(J)1_S1_{Z=0}\le g(J)1_S p(Z)^2.
\]

For g(J)=(J-collision_center)^2, divide (2)'s value by the positive tail
denominator (tau-collision_center)^2 to obtain a selected tail bound. The
optimizer is deterministic data attached to the fixed flag's moment law;
coefficients are not chosen after observing the particular conditioned design.

## Verified implementation and limits

The follow-up [joint tail square](wall1_joint_tail_square.md) enlarges the class
to squares of polynomials affine in J and degree at most t in Z. It uses the
same mixed moment orders and retains a direct pointwise selected-tail certificate.

`scripts/optimal_void_square.py` constructs (1), validates PSD, solves the
stationarity equations and returns the coefficients and exact objective value.
It rejects incomplete moment ranges and invalid matrices. PSD is only an algebraic
consistency test: it does not certify that supplied numbers equal the actual
mixed moments, or account for an omitted high-dimensional remainder.

`scripts/wall1_optimal_void_square.py` checks 324 finite weighted laws, including
singular cases, against direct polynomial evaluation. At degree three on support
{0,1,2,3}, the computed optimum equals exactly the weight at zero, as a cubic can
vanish at the three positive support points. Invalid PSD inputs and incomplete
moment lists are rejected.

The actual-design test in `scripts/wall1_selected_flag_3d.py` uses the conditional
rank formulas to build M, then compares the objective with a separate enumeration
of g(J)p(Z)^2 over every conditioned matrix. All 288 degree/flag/radius cases pass.
Every optimized value is at most the same-degree Charlier mixed value, as (3)
requires; 245 are strictly smaller. The selected-tail inequalities also pass.
These are improvements to the finite test bounds, not to the unresolved width-506
probability estimate. No aggregate bound for draws 14--404 is obtained here.
