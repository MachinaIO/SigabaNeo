# Remaining completion and history obligations after the all-rank cover

The all-rank D32 cover has been integrated and its complete numerical pipeline
checked. This does not close the size18–24 cumulant transfer or the selected
history law. The following deductions narrow the missing mathematics; none
is a lower bound on BKZ failure or an impossibility theorem for the goal.

## Connected-incidence completion

The current dominant size19/rank11/c4 and size24/rank12/c5 branches contain
full-rank anchors with no remaining free basis points. Their dependent
completions are bounded uniformly by affine-slice occupancy. The exact
extremal occupancy theorem in `wall1_uniform_completion_obstruction.md`
shows that improving only this uniform cap cannot close the displayed terms.
Coordinate planes attain the extremal count, so sharper volume or theta
estimates of that same universal quantity cannot supply the missing gain.

The girth-four completion lemma in
`wall1_girth_four_completion_obstruction.md` further shows that connectivity
is automatic after a connected spanning anchor, and girth-four exclusions
remove at most a secant-line union at each step. A concrete large-occupancy
anchor is given, without claiming membership in every restricted residual.

A viable replacement must instead control occupancy under actual
anchor-incidence weights, restrict the realizable anchor geometry, improve
the joint-incidence estimate, or use a different complete witness cover.
The weighted completion and collision-energy notes remain relevant, but
conditioning on an entire full-rank anchor leaves no random containing plane.
The distribution of anchors themselves must enter any averaging argument.

## Adaptive histories

The smoothed potential gives a correct scale-loss bound, but an abstract
nested-overlap process shows that the two existing transition inequalities
alone do not cancel that loss. Two further geometric checks sharpen this:

- `wall1_initial_small_radius_obstruction.md` proves that the raw restart
  small-radius void is almost one for every initial matrix. Initializing
  the fixed-radius smoothed estimate there gives a trivial bound. This
  does not transfer to later projected states.
- `wall1_lattice_radial_profile.md` gives torus scaling inequalities and an
  actual rectangular marked lattice violating the desired shell premise at
  the conservative cap radius. This example is not shown reachable by the
  algorithm and allows a stronger actual winner cap. Consequently it
  excludes a premise based only on dimension, determinant, marking and
  that conservative cap; it does not exclude using selected-prefix
  arithmetic or the coupled actual winner and projection.

The remaining useful target is a quantitative projection gain under the
actual selected-prefix law, or an initial moment at a later selected state
proved under that law. A small design-radius void moment cannot simply be
reused at a smaller physical radius.

## Verification and scope

The uniform-completion theorem and its three numerical expression barriers
were independently audited; source snapshots match the full production
frontier. The raw-initial-state interval calculation was rerun from the
note. The rectangular-lattice script was rerun independently; its
Berry–Esseen input is explicitly sourced in its note. An independent audit
confirmed the marked-lattice construction, the normal-series enclosure,
the torus coupling and the limited scope of the obstruction. None of these new
results is claimed Lean-formalized. Production security assumptions and
cost claims are not strengthened by these obstruction results.

## Additional conditional tools (Parts 417–418)

`wall1_multi_height_drift.md` replaces the two-layer-only estimate with an
optimized second-moment bound over many heights. `wall1_overlap_energy_drift.md`
retains the exact cross additive energy and sharply converts its variance
to a power moment. Both need actual-history radial or energy estimates.
`wall1_winner_projection_gain.md` proves contraction with the actual winner
in a planar marked subclass, without asserting its premises generically.

For completion, `wall1_independent_map_energy.md` derives independent-map
energy without Jensen and a direct nineteen-point mixed-fiber alternative.
The latter stays within twenty-four input positions, but its asymmetric
input/output Gaussian kernel and coefficient charts remain to be bounded.
The exact finite checks and independent audits validate these reductions;
they do not establish their high-dimensional selected-history premises.
