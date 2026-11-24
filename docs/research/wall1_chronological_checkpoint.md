# Auxiliary-function and chronological collision checkpoint

The full BKZ theorem remains unproved. This checkpoint extends the prior
selected-pair/lens checkpoint; it neither closes the selected-history charge
nor changes the production failure guarantee.

The Gaussian-polynomial analysis supplies an exact matching-width exclusion
through degree six, and a valid broader-width continuum lens majorant. The
latter requires a normalized dual minimum near 24.9931 and its upper
certificate exceeds 10^116.99675 throughout the tested actual-radius interval.
It is therefore ineffective. Existing residual-corridor dual floors leave
only draws 34–39 potentially applicable. These are limitations of this
candidate and available proof inputs, not evidence of poor BKZ performance.
See [the auxiliary-function analysis](wall1_primal_dual_auxiliary.md).

The [multiple-height evaluator](wall1_selected_height_gram.md) retains actual
mixed gates, nonzero-mark anchor subtractions, occurrence multiplicities and
cross moments between unequal-radius candidate families. Reusing the existing
exact affine-square optimizer permits signed weights and singular Gram
matrices. Small algebraic checks and complete geometric one-step examples
verify these identities and the winner-tail implication.

The [chronological experiment](wall1_chronological_height_gram.md) then selects
an actual shortest vector, projects, and appends a fresh uniform column. Its
width-four mode starts with all 625 matrices over F_5, keeps 46 nonsingleton
winner strata, and checks 9000 surviving old/fresh cases. Exact selected rank
moments agree with direct enumeration. This retains residual old-matrix
uncertainty after selection, but only for one selection/append at fixed radius.
No dimension-independent moment bound or repeated-history estimate follows.

Validation is recorded in `wall1_chronological_checkpoint_checks.json`: five
command invocations covering four new checker sources, source and dependency
digests, complete outputs, and log hashes. The default chronological fixture
is a regression check; the residual mode is a distinct experiment. Independent
mathematical audits checked the auxiliary signs and scaling, signed square
optimization, geometric enumeration, and chronological normalization.
No Lean declarations were added, and no Lean build or axiom audit was run.
The literature note also records the scope of two recently checked sources;
it makes no exhaustive literature claim.
