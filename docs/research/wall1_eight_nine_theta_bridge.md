# Common-weight snapshots for c4 eight/nine-point anchors

The selected H8/H9 one-four estimate can use weighted D28/D31 kernels and
later direct-ball counts. The dual completion lemma cannot multiply those
selected minima as if they were common-beta theta sums. Keep an independent
common-weight envelope instead.

At entry to c4,t>=4, save the unweighted one_power. Also retain the initial
rare_split before weighted refinements. After applying the existing
coefficient exclusions, form

    iso_short = sum_(D,count) count/Q * fixed_four_plane(D/4)^N,
    iso_split = iso_short + one_count/Q * fixed_four_plane(9)^N.

Here N=518 and Q is the coefficient count. For H8 the lists are
{(28,12),(31,48)}, {(20,16),(24,14),(32,13)},
{(24,42),(28,12),(31,48)} for overlaps1,2,3. For H9 they are
{(23,30)}, {(31,50)}, {(23,30),(31,150)}. Apply the existing D20/D23/D24
filters only; H10/H11-specific flags do not remove H8/H9 terms.

The kernel fixed_four_plane keeps max(one_height,D/4), the full Gaussian
tail and the periodic correction. For H9 also retain
iso_short+ten_part+remainder, using the existing isotropic norm-ten and
higher-norm terms. The weighted short_part is never used in this envelope.

Both families have bad_count=0 and a common-beta none_power. Before direct_one,
store the minimum of the old common-theta snapshot and

    exp(H beta R^2) * (theta_one+none_power) / q^(m(H-2)).

The selected original anchor and all existing completed candidates remain.
The proof of this branch scope and the actual implementation received
independent read-only audits. No new result about actual selected histories
is inferred. The numerical checkpoints below record validation.

## Extension to the complete c4 H8..24 range

The same saved theta_one now covers all c4,t>=4. H10 reconstructs both
filtered norm-eight and norm-ten determinant lists using fixed_four_plane,
then includes the norm>=12 remainder. H11 has a later weighted D31 branch:
the safe counterpart instead uses iso_short, the1512 determinant39 witnesses,
and the norm>=12 remainder. Neither weighted replacement enters theta_one.
For H>=12, one_power is common-beta immediately before direct_one, and is
saved there. The final snapshot is placed after H14/H15's later isotropic
none_power improvements. All target branches have bad_count=0.

Independent branch and implementation reviews approved the entire range,
including guard equivalence, exclusion filters, full tails, and preservation
of the original selected anchor. Earlier H8/H9 and H13 snapshots remain as
safe redundant minima. They are not multiplied together.

## Intermediate H8/H9 validation

Before the larger-range extension, both full runs exited0 and passed2106
cumulant checks and18 frontier comparisons:
`/tmp/wall1_c4h8h9_theta_cumulants.log` and
`/tmp/wall1_c4h8h9_theta_frontier.log`. The through24 upper envelope was
below1.803e17, still ineffective, with a rank8/girth5 size24 leader. The
complete-range result will be recorded separately after its runs finish.

## Full c4 validation and extension to c>=5

The complete c4 range passes both full runs with exit0 and all2106 cumulant
checks/18 frontier comparisons:
`/tmp/wall1_all_c4_theta_cumulants.log` and
`/tmp/wall1_all_c4_theta_frontier.log`. Through24 was below1.539e17, still
ineffective. These are intermediate results, before the c>=5 integration.

Independent scope and implementation reviews also approve the following
complete catalogue for c>=5. Every final power is common-beta except
c6,H10, where the D32 kernel can be weighted. For this exception, retain

    theta_two = min(original_two_term,
        sum_(D,count) count/Q * six_plane(6,D/6,long_tail)^N),

using the existing LARGE_COUNTS[10][overlap] after its exact D32 exclusion.
The final one_term and none_term remain common-beta. Their sum with
theta_two gives a complete isotropic power. All other c>=5 branches can
retain final power_bound directly, including the c7/c8 GS refinements.

Each complete common power receives exp(H beta R^2)/q^(m(H-2)) and is
minimized against the existing theta snapshot. No weighted final power is
fed into the c6,H10 exception. This preserves the selected old anchors,
all exclusions, infinite Gaussian tails and periodic corrections. The
c>=5 numerical checkpoint follows below.

## Part 435: complete audited snapshot checkpoint

The final combined runs exit0: `/tmp/wall1_all_theta_cumulants.log` and
`/tmp/wall1_all_theta_frontier.log`. All2106 exact cumulant checks and18
frontier interval reconstructions pass. Through17 remains below3.219e-17;
through24 is below2.170e16, still ineffective against the3.01e-12 target.
These upper envelopes are not failure probabilities.

The size24 leader is rank9/girth4 under the original cover. Its leading
terms are H7,t3/overlap3 and H7,t3/overlap1, each with4 independent
extensions. The H6 two-four term is smaller but remains present. Thus the
snapshot-connection work has exposed a seven-point shared-four family;
the special H6 normalizer must not be reused for it without a new chart
proof and a complete family split. The full transfer target and actual
selected-history estimates remain open.
