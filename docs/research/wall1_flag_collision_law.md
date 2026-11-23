# Conditional collision law for a fixed flag

The whole-flag certificate of [Part 263](wall1_flag_occupancy.md) uses a candidate
cylinder depending on the selected flag. Fixing that flag before averaging makes
the cylinder deterministic, but changes the matrix law. The following exact
first and second moments retain this change. They apply to any finite candidate
set, including the half-open cylinder. They do not condition on shortestness.

## Remaining random map

Let A be uniform in F_q^(m by d), for prime q. A fixed list of flag lifts has
output columns X and input columns Y. Its containment event is AY=X. It is
possible precisely when ker Y is contained in ker X. Put t=rank Y and assume
this consistency condition. On V=im Y there is a well-defined map B with BY=X.
The containment event has probability q^(-mt): extend a basis of V to the input
space and specify the m coordinates of its t images. The images of the remaining
d-t basis vectors stay independent and uniform under containment.

Choose one such complement once, writing y=y_V+y_W. In these coordinates the
remaining matrix is a uniform map T: F_q^(d-t) -> F_q^m. For an ordered pair of
integer candidates z=(x,y), z'=(x',y'), put

\[
 v=(y-y')_W,\qquad u=x-x'-B(y-y')_V.
\]

Its collision equation is Tv=u. It is forced if v=u=0, impossible if v=0,u!=0,
and has probability p=q^(-m) otherwise. All reductions here are modulo q.
The choice of complement changes these coordinates but not the moments below.

## Exact variance with repeated and incompatible equations

Let F count the ordered pairs with v=u=0. For v!=0 normalize (v,u) by dividing
both by the first nonzero coordinate of v. Denote the resulting normalized
input direction by ell and output by a. Let w_(ell,a) be the number of ordered
pairs giving that normalized equation, and W_ell=sum_a w_(ell,a). Then the
ordered collision count in Part 263 is

\[
 J=F+\sum_{\ell,a}w_{\ell,a}\,1_{T\ell=a},\qquad
 E[J\mid AY=X]=F+p\sum_\ell W_\ell.                         \tag{1}
\]

For a fixed ell, exactly one output is realized; outputs with zero weight may
also occur. Consequently its weighted contribution has second moment
p sum_a w_(ell,a)^2. Distinct normalized directions are linearly independent
in pairs, so their images under uniform T are independent. Therefore

\[
 \operatorname{Var}(J\mid AY=X)=
 \sum_\ell\left(p\sum_a w_{\ell,a}^2-p^2W_\ell^2\right).    \tag{2}
\]

This formula includes both repeated equations and the negative covariance of
incompatible equations with the same input direction. Assigning independent
Bernoulli variables to all ordered pairs would give a different variance.
If t=d there are no free directions and J=F deterministically.

## A flag-weighted sufficient bound

For a fixed candidate set of size N, the 0.280 occupancy certificate fails when
J>tau, where tau=25 N^2/(18 q^m). Let mu_J and sigma_J^2 be (1)--(2). If
a=tau-mu_J>0, then

\[
 \Pr(J>\tau\mid AY=X)\le
 \frac{\sigma_J^2}{\sigma_J^2+a^2}.                           \tag{3}
\]

To prove this without a distributional assumption, put Z=J-mu_J. For every c>=0,
on Z>=a one has (Z+c)^2>=(a+c)^2. Thus the probability is at most
(sigma_J^2+c^2)/(a+c)^2; choose c=sigma_J^2/a. The strict-tail event in (3)
is contained in that event. A zero variance gives zero in (3). If tau<=mu_J,
use the bound one instead unless the deterministic count resolves the event.

Now enumerate a deterministic finite family of possible canonical selected
flags at a specified draw, with a radius determined by each flag. Canonical raw
lifts can be chosen by reduction along earlier flag vectors, so irrelevant
choices of lifts are not distinct entries. Every selected flag must obey AY=X.
On its selection event, Part 263 identifies the projected void and the candidate
occupancies. Dropping the selection and saturation tests gives the valid bound

\[
 \Pr(b_i>0.280)\le
 \sum_{\text{consistent flags }f}q^{-m t_f}
       \Pr(J_f>\tau_f\mid AY_f=X_f).                         \tag{4}
\]

The family must cover all reachable flags and radii at the draw. The same formula
can be summed over draws; a family with a restricted geometric range needs a
separate term for its complement. Containment does not itself ensure saturation
or shortestness, but (4) only uses the occupancy identity on the actual selection
event. On the larger containment event J_f is still a well-defined finite count.
No independence across flags or draws is asserted.

The numerical problem is now to bound the weighted sum (4), retaining selection
tests if dropping them is too costly. Neither (2) nor (3) shows that the sum is
small at width 506. In particular, this note does not improve the outstanding
3.922e-12 allowance. It provides computable conditional quantities rather than
using an unconditional q^(-400) collision factor after fixing a flag.

## Verification

[ConditionalGraphProbability.lean](../../SigabaNeo/Lib/Lattices/Research/Wall1/ConditionalGraphProbability.lean)
formalizes the conditional rank-increment probability used here. A row restriction
of the full test matrix specifies the conditioning equations. The theorem assumes
those equations are consistent and separately proves that their probability is
positive. The additional system has conditional probability q^(-m times the rank
increment) if consistent, and zero otherwise. Restriction cannot increase rank,
so the natural-number subtraction in the exponent is justified. An explicit
corollary gives q^(-m) for one additional independent direction.

This uses `AffineGraphMoments.system_probability` on the two nested systems and
their probability ratio. It does not assume that the tests are independent and
does not condition on shortestness. The geometric construction of the fixed flag,
the RREF program, the saturated law, and the numerical selected-history sum are
outside this new module's formalized scope.

[Saturation weights](wall1_flag_saturation.md) refine this containment-only law
by computing joint saturation and collision probabilities, hence the mean and
variance under saturation as well. Shortestness is still not conditioned on.

`python3 docs/research/scripts/wall1_flag_collision_law.py` enumerates all residual
maps for finite examples, checks the exact mean, variance, and the one-sided bound,
and includes full-rank constraints with no remaining randomness. The argument
above is a paper proof; it has not been independently audited or Lean-formalized.
