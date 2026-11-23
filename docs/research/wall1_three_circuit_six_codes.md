# Rare planes on a prescribed three-circuit and three new positions

After Part321, the leading size16 rank8/girth3 terms have c=3,t=3 and
old overlap1 or2. Refine their one-norm-four branch directly, without
assuming girth four or excluding three-point relations.

Fix the first three-support C={0,1,2}, the new positions {3,4,5}, and
prescribe the old overlap A={0,...,a-1}, a=1 or2. Enumerate every balanced
norm-four line u on six positions and every balanced line v of squared
norm six or eight. For norm six this includes the three-support
(2,-1,-1) shape; it must not be omitted in the girth-three family.

The new three columns of the two-row matrix must have rank one, so that
a nonzero combination vanishes on all new positions. Form that combination
and require its old support to be exactly C. Next annihilate the first
old coordinate outside A and require the resulting combination's support
to be exactly A union the three new positions. This tests the prescribed
supports, including all required nonzero coefficients.

Normalize the first relation at coordinate0. Normalize the second at
coordinate3, subtracting its coordinate0 multiple of the first relation.
The resulting pair is a canonical key for the modular plane. It gives
one normalized coefficient assignment for the prescribed supports.

The exhaustive counts are the same for each a:

| Gram determinant | Norm-six witnesses after code deduplication | Additional norm-eight codes |
| --- | ---: | ---: |
| 20 | 3 | 0 |
| 23 | 6 | 0 |

The norm-eight enumeration gives exactly the same determinant23 key set
as the norm-six enumeration. This equality is checked, not inferred
from equal cardinalities. Counts and unit-minor assertions pass at
q=7,17,3329. Each eligible pair has a unit minor and therefore spans a
primitive integer plane. Its first squared height is four and its second
is D/4. There cannot be two independent norm-four lines in such a plane:
their squared area would be at most16, smaller than the squared covolume
D>=20. Thus these belong to the intended one-norm-four family.

Let Q be the full coefficient-count bound and Q4 the existing count of
codes with a norm-four line. In the aggregate one-short-line term use

    (3/Q)*J(4,5)^N + (6/Q)*J(4,23/4)^N + (Q4/Q)*J(4,9)^N.

Here J includes the long Gaussian tail and all periodic layers, as in
the earlier fixed-four-plane bound. Codes without an independent
norm-six or norm-eight line retain the squared second-height bound nine:
after reduction against the primitive norm-four vector, a shorter height
would give an independent integer line of norm below ten. The affine
condition makes short squared norms even. No exceptional family is
discarded, and using Q4 for the residual family only overcounts.

Take the minimum with the former bound. No other c,t stratum or no-four
branch changes. The positive plane-sum envelope is connected to the
general two-relation evaluator, so both the full and restricted component
covers use it. This is exact finite counting plus the existing analytic
bound, not Lean formalization or a completed BKZ proof.

## Verified outcome

The three-modulus enumeration and full cumulant probe pass, including
2106 exact transfer/connected-support checks. Transfer through fifteen
stays below5.295e-13; the sufficient remaining allocation2.4793e-12 is
unchanged and remains unproved.

Size16's full weighted residual log10 is -2.4681074718. The rank8/girth3
term is now -5.5360339823 and no longer dominates. The largest strata
are rank7/girth4 at -2.5855673479, rank4/girth4 at -3.3751772138, and
rank8/girth4 at -3.4179345089. The through24 envelope is about3.34e232,
still ineffective. These are upper bounds, not actual failure rates.
No complete draw14 exit or adaptive BKZ theorem has been established.
