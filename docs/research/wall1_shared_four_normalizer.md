# Seven-point shared-four chart normalizer

Fix C=0123 and new positions456. For overlap1, the common point s is C∩D;
for overlap3, it is C\D. The second norm-four support is {s,4,5,6}.
Choose e=max(C\{s}) and6 as omitted positions, with the other five as basis.
For the two balanced norm-four rows a,b, the e/6 minor is diagonal +/-1.
Thus the chart is integral, affine and canonical for every sign pattern.

The two chart columns each have squared norm3 and overlap in only the
coordinate s. Therefore I+A^T A has diagonal4 and offdiagonal +/-1, giving
determinant15. At overlap3 the prescribed six-circuit is
b_s a-a_s b, supported on(C\{s}) union456. This is a unimodular change of
relation rows, so it defines the same integer relation lattice.

The zero-layer Poisson argument gives

    psi_A(0)>=max(h_old^5,q^2 alpha/(pi sqrt(15))).

The count is nine codes for overlap1 and overlap3, and zero for overlap2.
Only exclude_double_short_anchors removes this bad family;
exclude_triangular_anchors does not. An eventual split must apply the D15
normalizer only to bad_count/Q*bad_bound^N, with the original common
prefactor. The remainder four_seven_theta_one+none_power keeps the generic
cap. Neither shared_power nor its direct-ball minimum is a common-theta
reference. No extra basis multiplier is needed with the canonical chart.

An independent read-only proof audit approved this construction. Eighteen
exact chart/six-circuit cases pass in `scripts/wall1_shared_four_normalizer.py`. The split candidate is now implemented; its validation checkpoint follows below.

## Production integration

The helper admits exactly(H6,D12/16) and(H7,D15), uses h_old^(H0-2) in
the boost, and carries the determinant through the cache and118-coordinate
fallback. The D15 flag is not valid for other H values or general anchors.
Production saves a common-theta bad mass and a separate isotropic remainder
for each overlap before shared/direct replacements. For overlaps1 and3,
complete the bad mass with the D15 cap, complete the remainder with the
generic cap, and sum them before minimizing with old candidates. Both
same-weight and free-weight candidates are retained.

The chart count q^(3+overlap), free-point factor and/(f+1) witness factor
remain. No additional1/2 is applied to this family. The frontier captures
the new dictionaries and reconstructs the candidate independently. The
actual implementation received a read-only audit covering counts, guards,
cache propagation, zero free points and zero dependent points.

## Part 437 validation checkpoint

The full runs both exit0: `/tmp/wall1_shared_four_normalized_cumulants.log`
and `/tmp/wall1_shared_four_normalized_frontier.log`. All2106 exact cumulant
checks and18 frontier interval reconstructions pass. Eighteen exact chart
checks and six H7 scalar completion/cache cases also pass. Independent
implementation review approved the family split and its normalizers.

Through17 stays below3.219e-17; through24 is below5.627e5 and remains
ineffective against the3.01e-12 target. This is an upper envelope, not a
failure probability. The size24 leader is now rank10/girth4, H6 t2/overlap2
with6 independent extensions; rank11/girth4 is also substantial. The H7
t3/overlap1,3 terms in the rank10 stratum are smaller. This supersedes the
Part436 H7 leader. The next question is whether higher moments of the
canonical anchor itself can retain more information than f0^L<=f0.
Selected histories and the complete BKZ theorem remain unproved.
