# Six-point theta envelopes for anchored dual completion

The anchored completion multiplier applies to a common-weight Gaussian theta
sum. The selected production anchor minimum can also contain direct-ball or
anisotropic estimates, which cannot be multiplied by that lemma. This update
retains sharper six-point theta bounds without changing the original selected
anchor estimates.

## Audited six-point paths

For c=3,t=3, both overlap values have a final `power_bound` consisting entirely
of common-beta theta powers. The exact norm-six pair classifications and the
one-norm-four six-point split use that same beta. Weighted five/seven-point
branches and direct double-four branches are inactive; `bad_count` is zero.
The final power is therefore a valid theta snapshot for either original or
restricted coefficient families.

For c=4,t=2,overlap=3, the same conclusion holds. The one-four list has Gram
determinants28,31,32, so no weighted determinant24 replacement is used. The
double-four count is zero, and the direct double-four branch requires overlap2.

For c=4,t=2,overlap=2, the unrestricted final minimum is not theta-safe:
it can use a differently weighted determinant24 kernel and direct two-four
ball counts. The additional snapshot instead uses the complete decomposition

    bad_count/coefficient_count * bad_bound^N
      + sum_(D,count) count/coefficient_count * fixed_four_plane(D/4)^N
      + one_count/coefficient_count * fixed_four_plane(9)^N
      + none_power.

Here N=518. The one-four list is (24,12),(31,24),(32,8), with determinant24
removed when its exclusion flag is active. Every kernel in this expression
uses the original common beta, including all its tails and periodic terms.
The three parts cover two, one and zero independent norm-four directions.
It is not obtained by dropping the bad family or by assuming a weighted bound
also controls the unweighted theta.

When both `exclude_six_d24` and `exclude_double_short_anchors` hold, the two
unsafe families are absent, and the final `power_bound` itself is theta-safe.
The implementation handles that case explicitly. In every case the new
common-theta value is minimized against the previously stored common-theta
value. The selected original `anchors` value is unchanged.

## Integration and scope

The common prefactor exp(6*beta*R^2)/q^(4m) is restored before storing the
snapshot. The existing completed candidates then use this snapshot with the
same-weight or separately weighted free-point factors and the anchored dual
cap. Chart counts, basis-witness division and symmetry factors are untouched.

The proof paths and their numerical snapshot values were independently
examined with private AST captures before this integration. The source changes
passed a read-only integration audit and full cumulant/frontier checks.
The result concerns component envelopes, not a proof of the actual selected
history law or the complete BKZ theorem.

## Part 423 validation checkpoint

The cumulant run `/tmp/wall1_h6_theta_dual_cumulants.log` passes all 240
Poisson/cumulant and 1866 connected-support checks. The interval upper endpoint
through order 17 is below 2.666e-13. Through order 24 it is below 1.034e140;
this is still an ineffective upper envelope, not a failure probability.
The required full transfer target remains 3.01e-12 and is not established.

The diagnostic `/tmp/wall1_h6_theta_dual_frontier.log` completes all 18
selected-cover/remainder interval comparisons. Weighted total base-ten logs
at sizes 18, 19, 24 are approximately 10.9437934667, 34.3037813670,
140.0144676088. At size 24 the leader remains rank 9/girth 3, but its
leading anchor is now t=4, overlap=2 (seven points), with four independent
basis extensions. Sizes 18 and 19 are led by rank 8/girth 4 under the
D23-seven cover. These replace the Part 422 frontier identification.

A separate read-only audit identified further common-weight snapshots:
c3 H8/H10/H11 final powers are safe for all overlaps. For c3 H7 overlap 2,
the weighted D27 contribution must first be reconstructed with the original
common beta. For c4 H8/H9, weighted short-pair contributions likewise need
isotropic counterparts before any direct-ball minimum. These are candidates
for subsequent work, not improvements included in this checkpoint.

No new Lean theorem or selected-history bound is claimed.

## Two-four determinant split

The unrestricted H6 c4/overlap2 common-theta snapshot previously charged
all nine two-four codes with the same `bad_bound`. The classification has
five triangular codes (Gram determinant12) and four orthogonal codes
(Gram determinant16). Retain `square_bound^N` before its direct-ball minimum,
and replace the common-theta bad contribution by

    [n_triangle * bad_bound^N
      + n_square * min(bad_bound^N, square_bound^N)] / coefficient_count.

The counts are 5 and4 with the existing exclusions applied: triangular
exclusion removes the former, double-short exclusion removes both. The
original common-beta normalization and complete one-four/no-four terms
are unchanged. The selected original anchor remains unchanged.

This is a refinement of an existing Gaussian estimate, not a new result
about the selected-history distribution. For the unrestricted family,
improving only the square term leaves five triangular terms unchanged;
relative to the previous nine identical bad terms, its isolated gain is
at most9/5. Thus this edit alone cannot close the high-order residual.
## Part 426 validation

Independent branch audit approved the split and the exclusion flags. Both
full runs terminated with exit0: `/tmp/wall1_two_four_theta_cumulants.log`
and `/tmp/wall1_two_four_theta_frontier.log`. All2106 exact cumulant checks
and18 frontier interval comparisons pass. Through17 is below1.526e-14;
through24 is below4.557e133, still ineffective against the3.01e-12 full
transfer target. No probability interpretation is assigned to this envelope.
The size24 leader remains rank8/girth4, t2/overlap2, with4 free extensions.

## Why sharpening only the triangular Gaussian is insufficient

Take the relation matrix with rows (1,1,-1,-1,0,0) and
(1,1,0,0,-1,-1). A unit minor makes its integer row lattice primitive;
the Gram determinant is12. Its rank4 integer kernel has covolume sqrt(12).
Poisson summation on that kernel gives the exact lower bound

    sum_(x in integer kernel) exp(-beta ||x||^2)
      >= (pi/beta)^2 / sqrt(12).

The modular Gaussian includes this zero layer, so it satisfies the same
lower bound. This is a lower bound on the Gaussian surrogate, not on a
ball-event probability. The existing theta product has precisely this
continuous leading term. A new upper bound for the same anchor Gaussian
cannot eliminate that leading term. Improving the complete bound therefore
requires exploiting joint completion constraints, changing the majorant,
or a cover whose exceptional addbacks are also controlled. This does not
prove that the full completion bound or BKZ theorem is impossible.
