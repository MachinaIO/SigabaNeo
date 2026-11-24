# Multiple-height coverage from scalar-orbit expansion

This bounds the union of several height witnesses on the same fresh mark,
without treating them as independent. It introduces a second moment of
coverage across projective lines. That moment is not yet controlled under
the selected-history law, so this is not a completed width506 tail bound.

## A finite averaging operator

Let q be an odd prime and G=F_q^*/{+1,-1}, of order N=(q-1)/2. Fix
1<=J<q/2 and let D consist of the distinct classes of1,...,J. Define

    T f(x)=(1/J)*sum_(j=1)^J f(j*x),
    r=max_(nontrivial characters chi of G) |(1/J)*sum_j chi(j)|^2.

For the trivial group G at q=3 define r=0.

For a subset A of G of density a, the support of T1_A is exactly
union_(j=1)^J j^(-1) A. If its density is b, normalized Parseval and
Cauchy--Schwarz give

    E(T1_A)^2 <= a^2+r*a*(1-a),
    b >= a/[a+r*(1-a)]                                  (1)

when a>0; for a=0 the support is empty. Parseval bounds every nonconstant
Fourier mode by r. Cauchy--Schwarz applied on the support uses E T1_A=a.
No self-adjointness of T is needed: r is a squared singular-value bound.

## Apply to the actual shared scalar orbit

Fix the full incoming lattice state M subset K and H=K/M, with qH=0.
Assume the next mark U is uniform on H conditional on this full history,
as for the fresh unused column in the restart filtration.
Let d(v) be its nearest marked distance and s the old lattice minimum.
For 1<c<=s choose R>=0 with R^2+J^2<c^2. On each projective line L in
H, the symmetric set

    A_L={v in L minus {0}:d(v)<=R}

descends to a subset of G after choosing a generator of L. Its density
a_L is unchanged by that choice or by passing to sign classes. If j*U
belongs to A_L for some1<=j<=J, its nearest representative at height j
is a graph vector of squared length at most R^2+J^2<c^2. Consequently
the actual winner has length below c. Formula (1) lower-bounds the
fraction of nonzero marks on that line that supply such a competitor.

All these events involve the same U. Their dependence is precisely what
the averaging operator retains. The sign quotient is legitimate because
d(v)=d(-v). Strict margin in the radius condition avoids all winner ties.

## The line-occupancy second moment

Assume H is nontrivial, and average uniformly over its projective lines.
Put mu=E_L a_L and nu=E_L a_L^2. Lines all contain q-1 nonzero marks, so
this is also the natural decomposition of a uniform nonzero mark. The
averaging operator preserves the mean separately on every line. Thus

    E_(U!=0) (T1_A)^2 <= nu+r*(mu-nu).

For mu>0 another Cauchy--Schwarz bound gives

    Pr_(U!=0)(some height1..J competitor below c)
      >= mu^2/[r*mu+(1-r)*nu] =: B.                     (2)

Set B=0 when mu=0. For c>1 the zero mark also has the height1 unit
competitor. Hence the actual inclusive upper tail satisfies

    Pr(S_U>=c) <= ((|H|-1)/|H|)*(1-B).                 (3)

If H is trivial, S_U<=1 and this tail is zero. As in the existing
[phase-tail connection](wall1_phase_winner_tails.md), (3) can constrain
winner-bin masses while retaining shared convolution budgets.

For signed label counts n_L=|A_L| and ell=#projective lines,

    mu=(sum_L n_L)/(ell*(q-1)),
    nu=(sum_L n_L^2)/(ell*(q-1)^2).

There is no extra factor of two: both numerator and denominator change
together when passing to sign classes. The inequalities mu^2<=nu<=mu
show that (2) is at least the trivial coverage mu, and is strictly stronger
when r<1 and nu<mu. If every line is completely full or empty, nu=mu
and no expansion is certified. Indeed scalar multiplication cannot move
a mark between projective lines. Thus a global radial count or the fact
that the short marks span H does not supply the needed concentration bound.

The single-line right side of (1) is concave in a for0<r<1. Jensen gives
the wrong direction for lower-bounding its line average from mu alone.
Equation (2) retains the missing second moment instead. It makes no
assumption that different projective lines are statistically independent.

## Verification and remaining work

The general operator and coverage arguments are paper proofs, not Lean
formalizations. The checker `scripts/wall1_scalar_orbit_spectrum.py`
certifies the finite scalar-operator constants at q3329 using outward
interval arithmetic and checks small groups exhaustively. These constants
are independent of the history; mu and nu are not. To obtain a production
bound one still needs estimates for the actual selected-state line counts
at the smaller radius R. In particular the radius cost of increasing J
cannot be ignored. No new numerical full-history bound is asserted.

At q3329 the checker verifies that3 generates all1664 sign classes. It
encloses every nontrivial character multiplier with40-digit interval
arithmetic and compares its endpoints to rational caps exactly. The
certified upper bounds on r are:

    J=2:  1
    J=3:  0.99717678
    J=8:  0.87647451
    J=16: 0.66336619
    J=24: 0.39272107
    J=32: 0.33130614
    J=64: 0.14458391

These are operator bounds, not failure probabilities. For q7,11,13 the
checker exhausts312 subsets of the sign quotients across the tested height
sets. It also checks15552 pairs of arbitrary line subsets in H=F_q^2,
leaving its other lines empty, to verify the global second-moment bound
and the full/empty-line obstruction. All exact checks pass. Independent
mathematical review approved the single-line and global arguments, including
the zero mark and sign normalization.

The [multiplicity-aware collision certificate](wall1_scalar_collision_certificate.md)
applies the same operator directly to candidate counts. It replaces
reciprocal occupancy weights by ordinary and scalar-collinearity collision
counts, with explicit sign symmetrization. Fixed-candidate congruence
probabilities are available for those counts; the actual marked quotient
and the selected geometry must still be retained.
