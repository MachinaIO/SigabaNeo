# A joint competitor/collision square certificate

Part 274 optimizes a product (J-c)^2 p(Z)^2. The same mixed moment data allow
a larger class: a polynomial affine in J and of degree at most t in Z, squared
only after the two variables are combined. This can improve the bound without
requesting higher competitor or collision moments.

## Pointwise tail condition

Let T be the least attainable parity-compatible integer above the collision
threshold tau. Use the falling-factorial basis and set

\[
 P(Z,J)=1+a(J-T)+\sum_{h=1}^t (b_h+c_hJ)(Z)_h,\qquad a\ge0.  \tag{1}
\]

When Z=0 and J>=T, P(Z,J)>=1. On all outcomes P(Z,J)^2>=0. Hence, conditional
on a fixed flag's containment equations, with S its saturation event,

\[
 \Pr(S,Z=0,J>\tau\mid\mathrm{contain})
                   \le E[1_S P(Z,J)^2\mid\mathrm{contain}]. \tag{2}
\]

No relation between J and Z other than the selected-event implication is needed.
The polynomial is fixed before drawing the conditioned matrix. The same argument
works with any deterministic T such that the target event implies J>=T.

## Gram matrix and exact optimization

Take the basis 1, J-T, (Z)_1, J(Z)_1, ..., (Z)_t, J(Z)_t and its conditional
Gram matrix M, weighted by 1_S. It is positive semidefinite. All its entries use
the existing subset moments A_(h,p), with h<=2t and p<=2: multiply falling
factorials using Part 273's identity, multiply powers of J, and replace
E[1_S J^p (Z)_h | contain] by h! A_(h,p).

The coefficient optimization is

\[
                  \min_{c_0=1,\ c_1\ge0} c^T M c.           \tag{3}
\]

The matrix has size 2t+2 rather than t+1, but the input moment orders do not
increase. This optimizes within the normalized class (1), not over all conceivable
nonnegative bivariate polynomials or all certificates exploiting integer J.

First solve the unconstrained normalized-square problem of Part 274. If its
chosen minimizer has c_1>=0, it solves (3). Otherwise solve the boundary c_1=0
by deleting that row and column. This boundary solution is optimal: the segment
from any feasible positive-slope point to the unconstrained negative-slope
minimizer crosses the boundary, where convexity gives a value no greater than
at the feasible endpoint. This also handles nonunique unconstrained minimizers.

The implementation additionally checks an exact optimality certificate. Writing
v=M c, it verifies

\[
 c_0=1,\quad c_1\ge0,\quad v_1\ge0,\quad c_1v_1=0,
 \qquad v_i=0\ (i\ge2).
\]

For any feasible d, put h=d-c. Then

\[
 d^T M d-c^T M c=h^T M h+2h^T v=h^T M h+2d_1v_1\ge0.     \tag{4}
\]

Thus PSD and the displayed equations certify global optimality even for singular
M. All arithmetic in the checker is rational; no numerical tolerance is used.

Every optimized product from Part 274, divided by (T-collision_center)^2 with
collision_center<T, is feasible in this class: take
P=(J-collision_center) p(Z)/(T-collision_center), where p(0)=1.
Therefore the optimum in (3) cannot be worse than that product at the same T.
This does not imply domination of the separate parity polynomial, which need
not be a square. Taking the minimum of valid certificates remains safe.

## Verification and unresolved scope

`scripts/joint_tail_square.py` constructs M, solves (3), and checks (4)'s
conditions. `scripts/wall1_joint_tail_square.py` tests 243 finite joint laws,
including cases where the slope constraint is active, and four boundary/singular
fixtures. It independently evaluates the polynomial and its tail domination.

The actual-design test in `scripts/wall1_selected_flag_3d.py` uses conditional
graph rank sums for M, and separately enumerates each conditioned matrix to
evaluate P(Z,J)^2. All 288 cases agree and give valid selected tail bounds;
94 strictly improve on the optimized product at the same integer threshold.
The complete finite first-selection sum is also checked. The example q=5,R^2=1
improves the combined upper bound to 11/15, while its actual exit probability
is 9/25: the result is still not an exact failure calculation in general.

As in Part 274, PSD validation alone cannot prove that the supplied moments
are the actual moments. For width 506, those moment entries and their aggregate
over selected flags remain unbounded. This note gives no new draw-14--404
probability guarantee and does not complete the BKZ proof. It is a paper proof
with exact finite checks, not a Lean formalization.
