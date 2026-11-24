# Seven-point common-weight bridge

For c=3, H=7, the selected no-four estimate can use a differently weighted
D27 kernel. That minimum cannot be multiplied by the anchored common-theta
completion lemma. Retain a separate isotropic counterpart instead.

For overlap 1 the exact six/six Gram counts are {(32,4)}; for overlap 2 they
are {(27,18),(32,4),(35,24),(36,18)}. With Q the coefficient count and N=518,
set

    T2 = min(previous_two_six,
             sum_(D,count) count/Q * no_four_plane(6,D/6,six_tail)^N).
    T0 = min(previous_none, one_six_term + T2 + no_six_power).

Both minima compare complete bounds for the same coefficient family, at the
original beta. The periodic terms and infinite Gaussian tails are retained.
The complete seven-point power is

    bad_count/Q * bad_bound^N + one_power + T0.

Restore exp(7 beta R^2)/q^(5m), then minimize against the previous stored
common-theta anchor. The selected original anchor remains unchanged. For
c3 H8,H10,H11, the final power has no differently weighted or direct-ball
replacement, so it can be retained directly with its own common prefactor.

The code deliberately does not feed the weighted D27 minimum into T0.
Free-point factors, rank-tail moments, basis multiplicities and cover addbacks
are unchanged. This is an improvement to component upper envelopes; it does
not establish the actual BKZ selected-history distribution.

## Part 424 validation

Independent read-only review approved the actual integration: all selected
branches retain common beta and the prefactor, and no direct-ball minimum
flows into the stored theta bound. In H7, one_count and bad_count are zero;
keeping the full decomposition explicitly preserves its intended scope.

Both full runs terminated successfully:
`/tmp/wall1_h7_theta_dual_cumulants.log` and
`/tmp/wall1_h7_theta_dual_frontier.log`. The former passes 240 exact
Poisson/cumulant checks and 1866 connected-support checks. The latter passes
all 18 selected-cover/remainder interval comparisons and return-capture checks.
Through order 17 the interval upper endpoint is below 2.666e-13; through
order 24 it is below 2.258e136. This remains an ineffective upper envelope,
not a failure probability, and does not establish the 3.01e-12 full target.

The size24 leader is now rank8/girth4 under the original cover, with a
seven-point anchor t3/overlap3 and three independent extensions. Thus the
next unresolved snapshot family is c4 H7, including its shared direct-ball
branch. Weighted total base-ten logs at sizes18,19,24 are approximately
10.9437902251, 34.3037813636, 136.3535839666. The first two retain rank8/girth4
leaders under the D23-seven cover. No new Lean formalization is claimed.

## Four-circuit extension: common-weight decomposition

For c4 H7, retain the one-four estimate before the weighted D28 replacement.
Minimize it with its isotropic refined split:

    rare_six_count/Q * fixed_four_plane(23/4)^N
    + sum_(D,count) count/Q * fixed_four_plane(D/4)^N
    + one_count/Q * fixed_four_plane(9)^N.

The eight-row determinant lists are empty at overlap1, {(28,18),(31,10),
(32,18)} at overlap2, and {(31,30),(32,54)} at overlap3. The six-row count
is respectively 0,14,42, or zero under its existing exclusion flag. All
terms use the original beta and retain periodic/tail factors. The complete
power adds bad_count/Q * bad_bound^N and none_power before the shared-four
Gaussian/direct-ball replacement. No bad family is removed unless the
corresponding exclusion flag already requires that removal.

Restore exp(7 beta R^2)/q^(5m) and minimize against the existing common-theta
snapshot. This supplies another valid completed candidate; it does not
reinterpret the selected weighted or ball-count anchor as a theta kernel.
Independent read-only review approved the implementation. Both full runs
terminated with exit 0: `/tmp/wall1_c4h7_theta_cumulants.log` and
`/tmp/wall1_c4h7_theta_frontier.log`. All2106 exact cumulant checks and18
frontier interval comparisons pass.

## Part 425 checkpoint

Through17 is below2.665e-13; through24 is below8.203e133. The latter remains
an ineffective envelope against the3.01e-12 full transfer target, and is
not a failure probability. Weighted total base-ten logs at sizes18,19,24
are approximately10.9437840594,32.4450940287,133.9139232846.

The size24 leader remains rank8/girth4, but the leading anchor has returned
to t2/overlap2 (six points), with4 independent extensions. Its weighted
term has log10 approximately133.7453360630, while the t3/overlap3 term
is now approximately115.9825981239. The unresolved six-point two-four
family, rather than the newly connected seven-point family, determines
the next frontier. More snapshots of larger anchors alone cannot remove
that term. A sharper complete two-four theta bound or a stronger cover
that includes its addback is required. Selected-history estimates and
full BKZ remain open; no new Lean theorem is claimed.

## Complete c3 common-theta snapshot scope

Independent read-only audit extends the final-power snapshot to every
c3 family with8<=H<=24. H9's counted-six/eight term uses only the original
common beta, and H12 onward uses the same isotropic minimum classification.
Weighted/direct replacements occur only in other branches. H7 retains its
separate reconstruction; it is not replaced by its selected weighted minimum.
The implementation now covers the entire audited range, including H9.
All existing completed candidates remain available. Numerical results are
recorded after the corresponding full runs complete.

## Part 433 checkpoint

Both full runs exited0: `/tmp/wall1_all_c3_theta_cumulants.log` and
`/tmp/wall1_all_c3_theta_frontier.log`. All2106 exact cumulant checks and18
frontier interval comparisons pass. Through17 remains below3.219e-17;
through24 is below1.438e27, still ineffective against the3.01e-12 target.
The size24 leader is now rank9/girth4, t2/overlap2 (six points), with5
independent extensions. Its t4/overlap3 eight-point term is also significant.
The original cover wins. This supersedes Part432's girth-three H9 leader.

The canonical two-four normalizer is the next candidate for the six-point
family, but it must be applied to its own triangle/square theta masses,
leaving the one/no-four remainder under the generic cap. The design has
been independently audited and is recorded in `wall1_two_four_normalizer.md`;
it is not included in these numerical results. Selected histories and
full BKZ remain open.
