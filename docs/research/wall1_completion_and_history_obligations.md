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

## Concrete mixed-kernel accounting (Part 419)

The coefficient sum must stay outside the118th coordinate power. Exact
small examples refute normalized independent-coordinate replacements.
A universal Gaussian pivot bound can be globally optimized at the actual
radius, but still loses to the existing volume cap. Thus it is not
integrated. Matrix-dependent coordinate multiplicities can improve a
fixed span; their distribution under actual anchor weights is unknown.

The Gram-kernel formulation now retains both integer theta corrections
and modular aliases through an explicit Schur complement. This avoids
the false suppression obtained by treating a large integer lift of a
modular coefficient as a genuinely long coefficient. The remaining task
is a sufficiently sharp bound on the coupled coefficient sum, including
these alias factors, or a justified restriction on actual anchor geometry.
See `wall1_mixed_chart_sum.md`, `wall1_mixed_gram_kernel.md`,
`wall1_mixed_completion_temperature.md` and `wall1_mixed_kernel_fixture.md`.

## Integrated anchored candidates (Parts 420–421)

The anchor-preserving dual pivot bound now supplies an additional completed
common-Gaussian candidate. It covers both full anchors and independent basis
extensions at the original anchor temperature. All2106 exact checks and18
frontier reconstructions pass. The through24 envelope is still ineffective.
The dominant size24 term has a small girth-three anchor and9 free basis
points; optimizing their weight separately needs a new anisotropic argument.
The selected direct-ball/anisotropic anchor minima are still used only in
the old completed candidate. See `wall1_anchored_dual_completion.md` and
`wall1_extended_dual_completion.md` for the proof and precise scope.

## Separate free-point weights (Part 422)

The explicitly anisotropic extension is now proved, implemented and independently
audited. It retains the original anchor kernel, uses a separate Gaussian
weight for free basis points, and adjusts the hyperplane eta bound accordingly.
All2106 exact cumulant checks and18 reconstructions pass. The remaining size24
leader is rank9/girth3 with a six-point anchor and5 free basis points. The
upper envelope remains ineffective; see `wall1_anisotropic_dual_completion.md`.
