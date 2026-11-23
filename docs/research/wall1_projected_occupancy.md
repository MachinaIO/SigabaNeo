# Projection-aware occupancy certificate for a positive-height branch

Follow-up: [whole-flag occupancy](wall1_flag_occupancy.md) removes the positive-height
and coprimality restrictions from the occupancy reduction by retaining the exact
multiplicity of raw labels lost under projection. Its selected-history probability
estimate is still open.

This note combines the already proved geometry of [Part 176](wall1_inverse_branch.md)
with a finite occupancy bound. It does not prove the Part 246 exceptional-history
estimate. The new output is an explicit sufficient statistic retaining the projection
saving discarded in the two-radius estimate of [Part 230](wall1_inductive_typicality.md).
The projection and finite-point identification below are paper proofs. The finite
occupancy inequality and its history union bound are now formalized in
[CosetOccupancy.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/CosetOccupancy.lean),
without additional axioms. The accompanying rational checks are finite examples,
not a width-506 computation.

## Exact finite count after selecting the winner

Fix an incoming state with full lattices M contained in K in a d-dimensional Euclidean
space, qK contained in M, and H = K/M. Fix the fresh mark u, its lift u0, and the
selected primitive winner w = (x,a) in W = (M,0) + Z(u0,1). Orient w so a > 0,
and assume gcd(a,q) = 1. Write s squared = ||x|| squared + a squared and
m0 = x - a u0 in M. Define

\[
 R=M+\mathbb Z(m_0/a),\qquad T=K+R,\qquad
 G=I-xx^\top/s^2,\qquad E_b=\{y:y^\top Gy\le b^2\}.
\]

Here b is any nonnegative radius, including the branch-dependent radius used by a
later gate. Part 176 proves [R:M] = a and R intersect K = M. Consequently the natural
map K/M to T/R is a bijection; put h = |H| = [T:R]. There is no assumption that R is
contained in K. In general it is not.

Let Q project orthogonally off w. For z in K,

\[
 \operatorname{dist}(Q(z,0),QW)^2
   =\min_{r\in R}(z+r)^\top G(z+r).                 \tag{1}
\]

To check (1), subtract (j/a)w from (z+m+ju0,j). This leaves
(z+m-jm0/a,0), with the same projection. These vectors range over z+R.
The squared norm of Q(y,0) is y transpose G y. The eigenvalues of G are 1
on x perpendicular and a squared / s squared on its span (G = I when x = 0).
Thus it is positive definite and the minimum exists.

For c in T/R set

\[
 n_c=\#(E_b\cap c),\qquad N=\#(E_b\cap T),\qquad
 J=\#\{(y,z)\in(E_b\cap T)^2:y-z\in R\}.
\]

All these sets are finite. Equation (1) identifies the exact next void fraction as

\[
 p'=h^{-1}\#\{c:n_c=0\},\quad
 \sum_c n_c=N,\quad \sum_c n_c^2=J.                \tag{2}
\]

This uses uniform *fresh marks* conditional on the selected branch. It makes no
uniformity assertion about the winner or the incoming history.

## A sufficient statistic and its limits

For N > 0, Cauchy--Schwarz on the occupied classes gives

\[
 p'\le 1-\frac{N^2}{hJ}
       =\frac{v}{\mu^2+v},\qquad
 \mu=N/h,\quad v=J/h-(N/h)^2.                    \tag{3}
\]

Equality holds precisely when all nonzero n_c are equal. Thus the second-moment
bound is optimal among unrestricted occupancy vectors with that equality pattern.
For 0 < rho < 1, a sufficient condition for p' <= rho is

\[
 hJ\le\frac{N^2}{1-\rho}.
\]

In particular rho = 273/1000 gives the integer certificate

\[
                         727hJ\le1000N^2.       \tag{4}
\]

The count J is ordered and includes the diagonal. An equivalent form is

\[
 J=\sum_{r\in R}\#\bigl(T\cap E_b\cap(E_b-r)\bigr).       \tag{5}
\]

Only r in E_b-E_b can contribute. Formula (5) retains the actual selected
quadratic form and all congruence collisions. Replacing J by N would incorrectly
treat different representatives of one covered class as independent hits.

For completeness, if f(c)=n_c and normalized Fourier coefficients on T/R are used,
finite Parseval gives v = sum over nontrivial characters of |f-hat| squared.
These are coefficients of the *occupancy count*, not the void indicator used in
Part 230. A bound for one is not automatically a bound for the other.

The geometric identities det(G) = a squared / s squared and det(T) = det(K)/a
imply

\[
 \frac{\operatorname{vol}(E_b)}{\det T}
       =\frac{s V_d b^d}{\det K}.
\]

This volume ratio is not N and does not prove (4). The height cancels in this
volume expression while it remains in the discrete set T and in its collisions.
The occupancy ratio in (3) is invariant under a common rescaling of all n_c;
a larger count alone therefore gives no automatic improvement.

## Relation to the history exit event

On each positive-height coprime branch, use the actual radius defining the desired
next void observable. By (4), an exit p' > 273/1000 forces failure of that certificate.
For a whole history, a union bound can therefore charge such certificate failures,
plus all branches not covered by the hypotheses. Horizontal winners (a = 0) must be
handled separately. Heights divisible by q also require separate treatment. Indexing
must match the observable: Part 246's smaller-radius b_i is not automatically the
next moving-threshold height-one void of Part 230.

This is only a reduction. Neither a bound on J conditional on N nor a probability
bound for certificate failure under the selected-history law has been obtained.
In particular it supplies no numerical improvement on the requested
3.64 times 10^-12 exception allowance. It avoids a loss of projection information,
but does not remove selection bias or replace the unresolved history estimate.

## Exact finite verification

Run `python3 docs/research/scripts/wall1_projected_occupancy.py`.
The checker enumerates all 17 marks for M = 17Z contained in K = Z, selects actual
shortest vectors with signed lexicographic ties, and checks (1)--(4) at four squared
radii using rational arithmetic. It independently computes projected distances
from the two generators of QW. Winners have heights 1, 2 and 3; the test therefore
includes nontrivial R/M. These checks validate finite examples, not the general
paper proof or the high-dimensional probability estimate.

## Formalized scope

`support_bound` proves N² <= (h - emptyCount) J. `void_ceiling` proves the integer
certificate for every rational threshold, with `void_ceiling_273` and
`void_ceiling_280` as specializations. `history_exit_count_of` transfers certificate
failures to an exit-count bound over finite histories, allowing the label type to
depend on both time and history and requiring no independence between draws.
Compilation and the printed axiom audits use only `propext`, `Classical.choice`,
and `Quot.sound`. The geometric identification with this note's projected lattice,
and the needed bound on certificate failures, remain outside these Lean theorems.
