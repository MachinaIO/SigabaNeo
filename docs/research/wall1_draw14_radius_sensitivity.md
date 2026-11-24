# Radius sensitivity of the draw14 reference certificate

The completed draw14 bound is tied to its original physical radius. It
cannot be transferred to a smaller radius by monotonicity in the needed
direction. This check quantifies the sensitivity of its degree12 reference
term, without rerunning or asserting any changed-radius cumulant certificate.

At N=518 let R be the radius in wall1_draw14_frontier.py and let mu(f) be
the existing candidate_lower(518,f*R)/3329^400. The reference term is

    beta(f)=1 / (.280 * sum_(k=0)^12 mu(f)^k/k!).

At f=1 the interval evaluation reproduces beta<9.131e-13. At f=.99976,

    beta(.99976)>3.92763524e-12>3.922e-12.

Thus a0.024% shrink already exhausts the entire history allocation in this
term alone, before adding any nonnegative transfer/error majorants. At
f=.99977 the reference term is below3.697e-12; this does NOT certify the
full bound there, since its radius-dependent transfer terms were not computed.
At f=.9995 the reference term exceeds1.8969e-11.

These are statements about this specific sufficient upper-bound formula
and its existing lower count, not lower bounds on actual failure. A sharper
count, a different polynomial degree, or a projection-aware argument may
perform differently. Nor does the calculation claim that an actual next
radius has one of these values: relating the actual radius to selected
winner length remains part of the history problem.

The existing raw-ball obstruction at draw16 is stronger in a different
sense: even exact counting of that particular deterministic raw ball leaves
more than .292912 of the raw cosets uncovered for every matrix. That result
in wall1_affine_void_moments.md rules out relying solely on that raw ball
for a .280 ceiling, regardless of polynomial degree. Neither observation
rules out the actual projected void, which can be smaller.

Run scripts/wall1_draw14_radius_sensitivity.py. It extracts the production
candidate_lower function by AST, evaluates it with80-digit outward interval
arithmetic, and checks the budget comparisons. The production function's
domain assertions hold at every tested radius. It does not execute or modify
the original module's unrelated long-running incidence checks.
