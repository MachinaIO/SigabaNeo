# Selected-history and lens research checkpoint

This checkpoint follows b5fa123d and records Parts 472–476 and subsequent
selected-pair and lens work. The full BKZ proof remains unproved. No new
production security bound or finite gap to heuristic BKZ costs is asserted.

The existing Fourier minorant extends to radius squared 1.21g²−2 over all
407 scalar floors, proving candidate density above 1.67866e16. This is
stronger than the alternative elementary rounding count. An old-minimum
gate makes the nonzero-mark first moment exact; it does not make labels
independent. The existing requirement of 100 long winners for a small-g
crossing permits an expected-count bound without independence across draws.

The selected-pair evaluator retains full and quotient exclusions separately,
including zero-anchor subtraction when a gate is incomplete. Partial-gate
certificates use nonnegative weighted remainder bounds. An optimal integer
second-moment void bound closes the small fixture's relaxation gap, but its
possible correction at mean >=1e16 is below 2.501e-33. Actual selected-history
collision estimates remain missing.

Geometric screening shows that replacing a lens by its enclosing ball loses
a factor above 27.95 even in the continuum density benchmark. Independent
random deletion masks have a conservative late-stage cost above 10^422.
The exact lens/shell decomposition avoids the enclosing-ball loss and
separates radial, discrete lens and candidate-normalization discrepancies.
None of those production discrepancies is bounded here. The long-winner
crossing and capped-void exit are kept as different events.

All 14 new executable Python checkers passed and parsed. Their source hashes,
log hashes, exit codes and complete outputs are preserved in
`wall1_selected_lens_checkpoint_checks.json`. The boundary audit adds 48
nontrivial-image cases covering positive full/quotient constraints, zero and
repeated candidate residues, and several centers; malformed dimensions and
zero-label hypotheses are rejected. `git diff --check` passed.

Independent mathematical reviews checked the main derivations. No new Lean
declaration was added, and no full-repository Lean build or axiom audit was
run for this checkpoint. The finite examples are not substitutes for
production selected-history bounds.

The next substantive mathematical task is to control the signed radial and
discrete-lens error combination under the actual selected histories, or to
replace that route with a proved agreement-preserving concentration argument.
See `wall1_lens_shell_identity.md`, `wall1_partial_pair_certificate.md`, and
`wall1_completion_and_history_obligations.md` for the exact obligations.
