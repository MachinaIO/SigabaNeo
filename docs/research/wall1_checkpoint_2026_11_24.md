# BKZ research checkpoint, 2026-11-24

The complete BKZ proof remains open. This checkpoint preserves the Wall1
research accumulated since the previous committed snapshot, including exact
finite classifications, paper proofs, numerical upper bounds, diagnostic
limitations, and six previously uncommitted Lean modules. It does not assert
that the new numerical work has been formalized in Lean.

## Current quantitative frontier

The full-incidence cumulant contribution through size17 is bounded by
1.077e-12; the outward-interval evaluation is about1.076402696610603e-12.
The independent reference/error allocation is9.131e-13. A conservative
remaining allocation of1.9318e-12 for sizes18--24 and subsequent bad histories
would give a total below3.922e-12, but that remaining estimate is unproved.
The evaluated through24 upper envelope is about3.818709584e223 and is
ineffective; this is neither an observed probability nor evidence of a large
actual failure probability.

The main progress log is `../PROOF_GAP.md`, Parts250--399. The current
production evaluator is `scripts/wall1_larger_triangular_components.py`;
`scripts/wall1_factorial_cumulants.py` performs the exact regressions and
outward-interval transfer calculations. Earlier research notes retain their
dated intermediate numerical values; use the current evaluator and the
latest progress entry for the present frontier.

## Reproduction and validation scope

Run from the repository root:

```
python3 docs/research/scripts/wall1_factorial_cumulants.py
python3 docs/research/scripts/wall1_larger_triangular_components.py
python3 docs/research/scripts/wall1_ball_slice_completion.py
python3 docs/research/scripts/wall1_six_d24_anchor.py
```

The first command passed240 exact Poisson/difference checks and1866 exact
connected/cumulant checks, including the new through17 assertion. The two
local checkers passed1164 affine-pivot checks and73 short representatives
plus180 balanced anchor witnesses. Independent paper audits are recorded in
`wall1_parts391_393_audit.md` and `wall1_ball_slice_d24_audit.md`.

The six Lean modules in this checkpoint concern affine graph moments,
conditional graph probability, coset occupancy, linear remainders, selected
Bonferroni bounds, and selected collision certificates. They are limited
lemmas; they do not establish the complete selected-history estimate or a
heuristic-quality BKZ cost theorem. No declarations in those modules were
changed during preparation of this checkpoint.
All six modules passed a combined `lake build` during checkpoint preparation.
All 143 included Python scripts passed syntax parsing; this is not a claim
that every historical numerical experiment was rerun.

The latest high-order diagnostic records a Part396 snapshot. Its subsequent
compatibility changes are syntax-checked, but its expensive full numerical
run has not been repeated against Parts397--398. That boundary is explicit
in `wall1_high_order_frontier.md`.

## Outstanding work

- Bound the size18--24 terms under the actual weighted anchor/basis law.
- Prove the required selected-history probabilities for adaptive BKZ blocks.
- Connect the probability estimates to the complete algorithm and cost theorem.
- Formalize and audit the new paper-level arguments in Lean.

The old440-bit comparison to heuristic BKZ was invalid after enforcing
block-size constraints and has been removed. No finite certified cost gap
from the estimator is currently supplied by this proof route.

An active weighted-completion research script is intentionally excluded
from this checkpoint; its argument and independent review are not finished.
