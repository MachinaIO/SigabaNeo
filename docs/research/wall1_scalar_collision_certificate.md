# A multiplicity-aware scalar-orbit collision certificate

This connects [scalar-orbit expansion](wall1_scalar_orbit_expansion.md) to
unweighted candidate counts. It avoids random reciprocal multiplicity weights.
The certificate is deterministic; bounding its failure over actual selected
histories remains open.

## Apply the operator to candidate multiplicities

Let H be a nontrivial F_q-vector space of size h, q an odd prime. Fix a finite
multiset of genuine candidate points of norm at most R in K, labeled in the
actual marked quotient H=K/M. Discard candidates with zero label. Write n_v
for the remaining multiplicity at v, and define

    N=sum_(v!=0) n_v,
    J=sum_(v!=0) n_v^2,
    C_sc=sum_(projective lines L) (sum_(v in L minus {0}) n_v)^2.

Equivalently C_sc counts ordered candidate pairs and nonzero scalars t such
that label(y)=t*label(x), with both labels nonzero. Each collinear pair has
exactly one such scalar. Diagonal candidate pairs are included.

Let k be the number of heights used, and let r be the certified squared
nonconstant multiplier bound on F_q^*/{+1,-1} for heights1,...,k. Use the
sign-averaged operator

    T_pm n(v)=(1/(2k))*sum_(j=1)^k [n_(jv)+n_(-jv)].

This is necessary if candidate multiplicities are not symmetric. It first
replaces n by n_even(v)=(n_v+n_-v)/2, preserving N and C_sc and decreasing
J. Its support consists of labels with a candidate at some signed height.
All such candidates are legitimate: if a candidate labels j*v, use height j;
if it labels -j*v, use height -j.

The mean over nonzero marks is N/(h-1). On each projective line, the constant
part of n has its mean preserved; the remaining modes contract by at most r
in squared norm. Therefore

    E_(v!=0) (T_pm n(v))^2
      <= [r*J+(1-r)*C_sc/(q-1)]/(h-1).

If N>0, Cauchy--Schwarz on the support proves the nonzero-mark coverage bound

    B=(q-1)*N^2 /
      [(h-1)*(r*(q-1)*J+(1-r)*C_sc)].                    (1)

Set B=0 when N=0. The inequality C_sc<=(q-1)*J follows by applying
Cauchy--Schwarz to each line. Hence (1) is at least the ordinary occupancy
bound N^2/((h-1)*J). Duplicating every candidate by the same integer factor
leaves (1) unchanged: N scales linearly and J,C_sc scale quadratically.

If R^2+k^2<c^2 and c>1, all covered marks have actual graph winner length
below c; the zero mark has the fresh unit competitor. Thus

    Pr(S_U>=c) <= ((h-1)/h)*(1-B)                       (2)

for a fresh uniform U conditional on the incoming state. For a desired
nonzero-mark coverage beta, the sufficient certificate is the polynomial
inequality

    (q-1)*N^2 >= beta*(h-1)*(r*(q-1)*J+(1-r)*C_sc).

This is an event to control under the selected-history law. Replacing its
random counts by expectations, or taking a ratio of expectations, is not
justified by the deterministic certificate.

## Retain selection through mixed moments

Fix a stratum with constant h,q,r and a valid fixed witness construction,
as in the [fixed quotient law](wall1_fixed_quotient_law.md). Let alpha(T)
be the actual selection likelihood inside it, and put

    D=r*(q-1)*J+(1-r)*C_sc,
    a=E alpha,  n=E[alpha*N],  d=E[alpha*D].

All expectations here are under the unselected, conditioned stratum law.
If d>0, weighted Cauchy--Schwarz proves

    E[alpha*B] >= (q-1)*n^2/((h-1)*d) =: L.            (5)

Indeed apply it to sqrt(alpha)*N/sqrt(D) and sqrt(alpha*D), taking zero
on D=0; N=0 there. This is a one-sided bound, not an equality replacing
an expected ratio by a ratio of expectations. If d=0 then N=0 on the
selection-weighted support and set L=0.

Provided the next unused mark is uniform conditional on the full history,
and the witness radius condition holds throughout the selected stratum,
the joint selected contribution to its next winner tail is bounded by

    Pr(Sel and S_next>=c | stratum)
      <= ((h-1)/h)*(a-L).                              (6)

The bracket is nonnegative, since L<=E[alpha*B]<=a. Multiply by the exact
stratum probability for its contribution under the original law. If a>0,
divide (6) by a for a conditional selected bound. If geometry or candidate
data are not determined by T in the chosen setup, retain that additional
state and the selection indicator in the weighted expectations instead.
Uniformity conditional merely on a coarse state is not assumed.

Thus the necessary inputs are a lower bound on E[alpha*N], upper bounds
on E[alpha*J] and E[alpha*C_sc], and a compatible bound on selection mass.
The full function alpha need not be recovered, but its correlations with
the counts cannot be discarded. The positive-covariance example in the
fixed quotient note rules out replacing these by products of unselected
means without a separate proof.

On that exact example the r=0 mixed-moment bound for selected conditional
witness coverage is128/71045, below its exact mean127/69952. The checker
also validates r=1/4 and r=1 relaxations using the same actual selection
likelihood. This tests (5), not the production mixed moments needed by (6).
The weighted argument received independent mathematical review.

[Quotient selected incidence](wall1_quotient_selected_incidence.md) implements
the joint terms needed for those mixed moments, distinguishing full competitor
membership from quotient-only collision equations. It provides exact terms
and valid truncation directions, not an evaluated production sum.

## Exact label identities and the importance of multiplicity

For a nonzero label set A, with line-density second moment nu as in the
expansion note,

    (h-1)*(q-1)*nu = sum_(t!=0) |A intersect t^(-1) A|.  (3)

If A is the nonzero support of a candidate multiset, the right side also
equals the sum of 1/(n_label(x)*n_label(y)) over collinear ordered candidate
pairs. Omitting these reciprocal weights overcounts (3). Formula (1)
avoids this problem by applying the spectral argument to n itself, rather
than incorrectly identifying the unweighted count with an indicator moment.
An incomplete candidate set certifies its own support; it need not enumerate
all short points to give a valid lower bound on actual coverage.

## Fixed-candidate scalar collision probabilities

After consistent fixed containment equations, the existing
[conditional collision law](wall1_flag_collision_law.md) leaves a uniform
linear map T:F_q^d -> F_q^m. For fixed residual candidate data (u,v), write
its label as lambda=u-Tv. For a second candidate (u',v') and t!=0,

    Pr(lambda'=t*lambda, lambda!=0)
      = Pr(T(v'-t*v)=u'-t*u)
        - Pr(T(v'-t*v)=u'-t*u, Tv=u).                   (4)

The subtraction removes the zero label exactly. A fixed linear system has
probability q^(-m*rank) when consistent, and zero otherwise. If v'-t*v and v
are independent, (4) is p-p^2, p=q^(-m). Degeneracies cannot be replaced by
that value: for identical candidates and t=1 the first equation is forced
and the answer is1-Pr(Tv=u). The formula for N uses1-Pr(Tv=u); summing (4)
at t=1 gives the conditional mean of J, and summing over all t!=0 gives
the mean of C_sc for this fixed candidate set.

These statements concern the labels represented by this fixed residual map.
After a rank-dropping projection, two raw syndromes can represent the same
actual mark. The scalar-collision condition is then equality in the quotient,
not equality of the raw syndromes. One must identify that quotient and retain
the equations and events defining it before using a residual-map law.
Likewise, selected candidate geometry cannot be treated as fixed independently
of T. Formula (4) does not remove either conditioning issue.

The [fixed quotient law](wall1_fixed_quotient_law.md) resolves the first issue
on each fixed frozen-kernel and syndrome-image stratum: its quotient map
remains uniform subject to the frozen-space equations, with an exact outer
weight. Actual shortest-selection conditions remain coupled to that map.

## Verification scope

Run `python3 docs/research/scripts/wall1_scalar_line_collisions.py` for exact
small-field rank/consistency probabilities, indicator line identities and
candidate-multiplicity checks. The general counting and spectral proofs
received independent mathematical review. There is no new width506
probability estimate or Lean formalization here.

The completed checker passes1638 residual-system probability checks across
input dimensions0,1,2, including864 rank-two cases. It checks all256 subsets
of the nonzero labels in F_3^2, including explicit zero-label exclusions and
reciprocal multiplicity identities. The multiplicity certificate and uniform
duplication invariance pass on the same256 subsets;254 nonempty cases strictly
improve the ordinary occupancy bound. A further64 subsets of F_7^* test
the nontrivial exact spectral constant r=1/4 for signed heights1,2. These
examples test finite identities and do not model selected width506 histories.
