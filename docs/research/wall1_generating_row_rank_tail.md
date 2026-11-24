# Auxiliary rank tails from actual generating rows

Let B be a k-by-n matrix over Fq, with independent entries and each entry's
maximum atom at most M in[0,1]. Assume0<=t<k<=n. Then

    Pr(rank B <= t) <= binom(k,t) M^((n-t)(k-t)).

If rank B<=t, some t rows span every row: choose a row basis and pad it
with other rows. For a fixed subset S of t rows, condition on those rows.
Their span has dimension s<=t. A random vector with independent coordinates
and maximum atom M belongs to a fixed s-dimensional subspace with
probability at most M^(n-s): choose s free coordinates and condition on
them; each of the remaining n-s pivot coordinates must have a specified
value. The remaining k-t rows are mutually independent after conditioning,
so the probability they all lie in the span is at most
M^((n-t)(k-t)). Union over the binom(k,t) fixed subsets S.

This does not condition on an adaptively selected random basis. The union
is taken over fixed row subsets first. Rank below t is covered by padding;
t=0 gives the all-zero matrix bound M^(nk). No uniform-mod-q assumption is
needed. For the bare Gaussian frequency law,

    tau = pi^2/(q^2 gamma),
    M = theta(q^2 tau)/theta(tau).

These are the same independent auxiliary entries used by the existing
rank-tail bound. No statement of independence for BKZ selected history
is inferred. The production helper now minimizes this estimate with1 and
the old Gaussian-binomial estimate. All deficient ranks are still included
in the rank-moment identity, and the Holder packing candidates remain.

Independent mathematical audit approved the conditioning and row selection.
The exact finite tests in `scripts/wall1_dual_frequency_rank.py` now check
both rank bounds under uniform and nonuniform laws over F2 and F3. The
helper's previous single-value regression is a non-worsening bound because
its full-anchor cap also receives the stronger rank estimate. Full runs
and implementation audit determine the numerical checkpoint below.

## Part 430 validation checkpoint

Independent mathematical and implementation audits approved the bound.
Twenty-eight exact finite weighted-rank cases pass, and the helper passes
154 cached full-anchor cases, including the updated non-worsening check.
Both full runs terminated with exit0: `/tmp/wall1_row_tail_cumulants.log`
and `/tmp/wall1_row_tail_frontier.log`. All2106 exact cumulant checks and
18 selected-cover/remainder interval comparisons pass.

The interval upper endpoint through17 is below3.389e-17. Through24 is
below7.427e73, still ineffective against the3.01e-12 full transfer target.
This is an upper envelope, not a failure probability. Size18,19,24 weighted
total base-ten logarithms are approximately-6.3397853110,5.7420825421,
73.8707671109. The size24 leader is now rank12/girth4 with a six-point
t2/overlap2 anchor and8 independent extensions under the original cover.
The previous rank8 leader identification is superseded.

At the former rank8 case, the diagnostic log
`/tmp/wall1_row_tail_bottleneck.log` selects gamma.75e-6 and now bounds
each deficient-rank term below the rank-only full-rank term. This confirms
that the previously identified rank-tail loss was addressed. It does not
identify the limiting term at the new rank12 leader; that needs separate
diagnosis. Actual selected histories and the complete BKZ theorem remain
open. No new Lean theorem is claimed.
