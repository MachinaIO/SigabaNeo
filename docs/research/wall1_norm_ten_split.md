# Selected-cover diagnosis and the next norm stratum

The size17 rank9/girth4 diagnostic reconstructs every complete candidate
cover and checks interval overlap with the production selection. The
selected cover excludes the seven-position determinant23 anchors as well
as the earlier short families. Its remaining two-relation part dominates;
the additional anchor charges do not explain the residual gap.

Splitting the c=4,t=7,a=3 term further shows that the one-norm-four part
dominates. The no-four part is smaller by over18 decimal orders in this
term after the previous geometry refinement. This corrects the tentative
no-four diagnosis: improving that part cannot remove the dominant loss.
Diagnostic logs: `/tmp/wall1_selected_cover.log` and
`/tmp/wall1_anchor_parts.log`.

Fix the unique balanced norm-four line on C, with seven new positions.
Consider an independent affine integer row of squared norm ten. It must
be nonzero on all seven new positions. If it also meets C, it has at
least eight nonzero coordinates. Any coefficient of absolute value two
would force squared norm at least4+7=11. Therefore all coefficients are
unit, on exactly ten positions, with three old and seven new entries.

A row supported only on the seven new positions cannot occur in this
two-dimensional code: together with the first row it would make every
word's old support empty or all of C, contradicting the prescribed proper
nonempty old overlap of the second circuit.

The inner product with the first row is odd, of absolute value one or
three. In the latter case subtracting the appropriately signed first row
gives squared norm10+4-6=8. That plane is already covered by the norm-eight
family. In the remaining case the Gram determinant is39 and the second
squared height is39/4. An old-exclusive and a new coordinate give a unit
minor, so this is the primitive-plane height.

There are at most3*4*126=1512 witness pairs: three first lines, four old
triples and126 balanced norm-ten lines on each ten-position support.
This deliberately overcounts planes and prescribed overlaps, which is
safe for an upper bound. The exact enumeration checks all1512 witnesses,
including the cases already covered at norm eight.

If there is no independent row of squared norm at most ten, a reduced
second basis row has squared norm at least twelve. Gauss reduction against
the norm-four first row gives inner product of absolute value at most two,
so the second squared height is at least12-4/4=11. The improved one-four
bound is the sum of the existing exact determinant31 family, at most1512
complete determinant39 kernels, and the full old coefficient count times
the complete height11 kernel. All old cutoff40 tails and periodic layers
remain in every summand. Take the minimum with the previous complete bound.

This is a component refinement, not the full BKZ or adaptive-history proof,
and it is not Lean formalized.

The completed probe passes all1512 norm-ten checks and2106 cumulant
regressions. Size17's weighted residual log10 is6.2490005872; rank9/girth4
is no longer in the five largest strata. The largest is now rank8/girth3
at5.8605637659, followed by rank8/girth6 and rank8/girth4. Through sixteen
remains below9.583e-13 (actual about8.78532707643e-13), and through24
still has an ineffective envelope about1.61354e232. Thus the targeted
term is improved, but the remaining allocation2.0505e-12 is not proved.
Logs: `/tmp/wall1_norm_ten.log`, `/tmp/wall1_norm_ten_cumulants.log`, and
`/tmp/wall1_norm_ten_checks.log`.
