# Recovering the raw misses by selected projection

The[draw15 raw-void bound](wall1_draw15_incidence_transfer.md) shows that the
fixed raw family misses mean fraction greater than0.00006469. This note
identifies the extra information needed to recover those labels by projection.
It proves no new bound on the selected-history void.

## Same raw labels, including quotient-rank losses

For each raw matrix use H=Z^N/L and the canonical cylinder C from
[whole-flag occupancy](wall1_flag_occupancy.md). Its radius B may depend on
the selected history, but require B>=R, the fixed raw radius. Let Z(c) be
the centered raw fiber-hit count and let Y(c) count the points z in C
with raw norm greater than R and label c. All expectations below use the
original matrix law and an independent uniform raw label c.

If Z(c)>0, its raw witness projects inside the radius B ball, so the
projected class is covered. If Z(c)=0, every cylinder representative of
that class has norm greater than R: a shorter integral representative can
be reduced coordinatewise modulo q, preserving its label because qZ^N
is contained in L and decreasing its norm, to produce a centered raw hit.
Consequently, for the complete cylinder count,

    {projected miss}={Z=0,Y=0}.

Uniform pushforward from H handles lost quotient labels exactly. This
identity does not condition the matrix or the selected flag on a raw miss.
Using only a subset of the long cylinder representatives gives an upper
event for projected misses, which is still sufficient below.

## Restricted occupancy and its limitation

Write p=Pr(Z=0), a=E[1_(Z=0)Y], b=E[1_(Z=0)Y^2]. If b>0, Cauchy--Schwarz
on the recovered raw labels gives

    Pr(projected miss)<=p-a^2/b.

These are joint expectations over matrix and label. Statewise ratios can
also be averaged, but ratios of separately averaged state counts cannot
replace them without a proof such as this joint Cauchy--Schwarz argument.

Unrestricted moments alone can lose the needed correlation. For a fixed
matrix, let n(c) count all cylinder points, with mean mu and variance V.
For its raw-miss set A of density p, covariance gives

    E_c[1_A n]>=max(0,p*mu-sqrt(p*(1-p)*V)).

The abstract occupancy n=0 on A and n=mu/(1-p) on its complement has
V/mu^2=p/(1-p) and recovers no raw misses. This is an obstruction to a
moment-only inference, not a claimed realizable selected lattice. The
global raw-void lower bound is not a lower bound on p for every matrix.

## A finite-degree mixed-moment target

Use the degree10 Q with Q(0)=1 from[the lower-witness construction](wall1_draw15_lower_witness.md).
For every real lambda, the polynomial

    Q(Z)^2*(1-lambda*Y)^2

is nonnegative everywhere and equals1 on{Z=0,Y=0}. This is an instance
of the existing square-moment method, now with raw and selected-cylinder
features together. Put T=E Q(Z)^2, A=E[Q(Z)^2 Y], B2=E[Q(Z)^2 Y^2].
For B2>0, optimizing lambda=A/B2 proves

    Pr(projected miss)<=min(1,T-A^2/B2).

If B2=0, use min(1,T). A certified upper bound on T, lower bound on A
and positive upper bound on B2 give the safe replacement
min(1,T_upper-max(0,A_lower)^2/B2_upper). No independence is used.
The needed total degrees are20,21,22 respectively. The raw-only pipeline
can address T; it does not bound the mixed selected quantities A or B2.
Their selected geometry and shared raw matrix must be retained. Replacing
the selected flag by a fixed or independent one is not licensed here.

This gives a concrete target for projection-aware counting while preserving
the proved raw-void obstruction. It is not a completed drift estimate or
a replacement for the other score, horizontal and prefix obligations.

## Certified raw square baseline and the mean-direction issue

Write Q(z)^2=sum_(j=0)^20 d_j (z)_j and let
F_Q(u)=sum_j d_j u^j. Exact rational arithmetic verifies
|d_j|<=|a_j| for j=2,...,20, where a_j are the factorial coefficients
of the existing lower witness (1-z)Q(z)^2. The zeroth and first factorial
moments match their Poisson reference exactly. Consequently the already
certified absolute factorial discrepancy below1e-25 also bounds
|T-F_Q(mu)|. This does not require rerunning the incidence cover.

On each of40 equal subintervals of[0,9.287185], the21 exact Bernstein
coefficients of F_Q lie above0.00020014984 and at most1. Therefore the
original, ungated draw15 law satisfies

    0.00020014983 < T < 1+1e-25.

This closes the raw-only term with a weak but rigorous uniform bound.
In particular F_Q(9.287185)<0.00020015 is NOT a valid upper bound for T
from the mean upper bound alone: F_Q(0)=1. A deterministic zero count
already disproves that mean-only inference (it is not claimed to be the
production law). A tighter production baseline needs a tighter mean
interval or a different certificate. The proof and all840 Bernstein
coefficients are checked by `scripts/wall1_raw_square_baseline.py`.

### Using the available centered-ball lower count

The existing `candidate_lower` bound does provide a nontrivial lower mean
when evaluated at this same draw15 radius (rather than the draw14 radius):

    4.5740608 < mu < 9.287185.

The lower interval endpoint before rounding is4.5740608011071165394... .
Here mu=|S|/q^400 exactly: each centered candidate satisfies the affine
syndrome equation with probability q^(-400). Counting by input fibers
gives the same mean, since at most one centered output in a given fiber
can have that syndrome. Thus the centered-ball lower count applies to Z.
The lower count subtracts the coordinate caps outside the centered cube;
it does not assume all integer ball points are centered.

Repeating the exact Bernstein calculation on this smaller interval gives
F_Q(mu)<0.015595757074. Including the existing discrepancy below1e-25,

    0.00020014983 < T < 0.015595758.

This improves the earlier uniform upper certificate by a factor exceeding64.
It is an ungated original-law bound and therefore also upper-bounds the
unnormalized gated raw-square term t_i at this geometry. It is NOT a bound
on a conditional expectation after division by a survival probability,
nor a bound for another draw or radius. The selected terms A and B2 remain
unbounded; no actual history probability improvement is claimed.

## From label averages to a first-exit event

Let p_i(history) be the projected void fraction and fix delta>0. Let G_i
be the event that the execution is alive and no earlier p_j reached delta.
This gate depends on the actual history but not on the independent auxiliary
uniform raw label. Also let D_i be the history event B_i>=R_i required
by the raw-witness implication. Define joint, unnormalized gated moments

    t_i=E[1_(G_i and D_i) Q_i(Z_i)^2],
    a_i=E[1_(G_i and D_i) Q_i(Z_i)^2 Y_i],
    b_i=E[1_(G_i and D_i) Q_i(Z_i)^2 Y_i^2].

The pointwise square bound, followed by minimization over a deterministic
scalar for each i, gives

    E[1_(G_i and D_i) p_i] <= t_i-a_i^2/b_i

when b_i>0; use t_i when b_i=0. Markov and the disjoint first-hit events
therefore imply the sufficient bound

    Pr(any alive exit p_i>=delta)
      <= sum_i Pr(G_i and not D_i)
         + (1/delta) sum_i (t_i-a_i^2/b_i).

One may cap each summand by its gate mass. This is a direct first-exit
alternative, not an additional charge to add on top of a stopped-drift
bound for the same event. The square coefficients and any estimates must
use this same gated law; neither ungated mixed moments nor ratios of
separately normalized gates can be substituted. Nonnegativity does allow
t_i<=T_i, but gives no corresponding lower bound on a_i from ungated A_i.
In particular the new raw baseline does not establish these mixed inputs,
radius-gate probabilities, or the production exit budget. For an index
where B_i>=R_i is already established, its radius-gate charge is zero.

## Containment cannot replace selection in a lower mixed moment

The fixed-flag collision formulas condition on containment, not on the
flag being selected. The distinction has the wrong direction for the
required lower bound on A. It persists even when saturation is automatic.
For an explicit graph-lattice example take

    L_(a,b)={(x,y,z) in Z^3 : x=a*y+b*z mod3}, w=(0,0,-1).

Use signed lexicographic shortest selection as in
[the three-dimensional selected-flag fixture](wall1_selected_flag_moments.md).
Containment of w is b=0, leaving a uniform in{0,1,2}. The flag is saturated
for all three values. At raw radius R=0 and projected radius B=1 the long
canonical cylinder consists of +/-e1 and +/-e2. For a=0 their counts at
labels0,1,2 are(2,1,1), and the actual winner is(0,-1,0). For a=1,2 the
counts are(0,2,2), and w is selected. These are global shortest winners:
their norm is1, and every nonzero integer vector has norm at least1;
the sign and tie convention choose the displayed vectors.

Z is1 at label0 and0 elsewhere. With h=Q(1)^2, exact averaging gives

    E[1_selected Q(Z)^2 Y | b=0]=8/9,
    E[Q(Z)^2 Y | b=0]=(10+2h)/9 > 8/9.

For the present Q, h=0.10104883578993319... . Thus dropping selection
would overstate the lower-moment input by0.2446775190644296... . Multiplying
both sides by the containment probability1/3 does not repair the error.
This is an exact small lattice counterexample to that inference, not a
production obstruction. Selection exclusions must remain in A: for example
odd weighted Bonferroni truncations can lower-bound the selected term,
but their weighted competitor incidences still require evaluation. The
existing containment upper bounds alone do not provide this missing input.
