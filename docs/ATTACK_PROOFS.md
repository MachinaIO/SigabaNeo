# Lean proofs of the lattice estimator's attacks: status

The goal is a Lean proof, without `sorry` or `axiom`, of every LWE attack the lattice estimator
considers, and of close variants. Each proof is an explicit algorithm with a proven success
probability and operation count. This page tracks progress per attack. Details and bit gaps are
in [PROOF_GAP.md](PROOF_GAP.md); the cost models are in [LWE_ESTIMATOR.md](LWE_ESTIMATOR.md).

Status marks:

* **proved**: a Lean theorem whose remaining premises are only standard facts that are also
  proved;
* **proved given H**: a Lean theorem with the explicit hypotheses `H` as premises;
* **paper**: an audited paper proof, not yet in Lean;
* **open**: no proof.

| Estimator attack | What a proof needs | Status |
| --- | --- | --- |
| `exhaustive_search` | enumerate the secret's support, check `b − As` short; uniqueness w.h.p. | **proved** (`Attacks/Guess/Collision.lean`). `Guess.ambiguity_probability`: for prime `q`, `n > 0`, a secret in a support of size `S` and any fixed error in `[−B, B]^m`, the scan fails to return exactly the secret with probability `≤ (S−1)(2B+1)^m/q^m` over uniform `A`. `Guess.scan_singleton_iff` identifies the failure event. `Guess.scanMultiplications_eq` counts exactly `S·m·n` ring multiplications; additions and tests are not counted |
| `mitm` | split the secret, hash or round `A₁s₁`, collision search | correctness **proved**: `Mitm.matches_eq_scan`, so the join returns the scan's candidates and inherits the bound above. Cost: `Mitm.balanced_tableOperations` counts `k(1+|E|)` modelled table operations. `Mitm.integerBox_card`: the error box has exactly `(2B+1)^m` guesses. A verified indexed table and its comparison count (for the `√S` runtime) are open |
| `arora-gb` | Arora–Ge linearization: full rank of the linearized system w.h.p. (the Gröbner variant needs semi-regularity, Fröberg's open conjecture) | components: `AroraGe.boundedErrorEquation`; `AroraGe.homogeneous_not_injective` shows the homogeneous form keeping the constant monomial is never injective, so the constant must move to the right-hand side; that rank question, success and cost are open. **Counterexample to the naive full-rank claim** (`AroraGe/Rank.lean`): with `s = 0`, `e = 0`, `n = 1`, `B = 1`, `q = 5`, the sample polynomial is odd (`aX − a³X³`), so every linearized matrix has a kernel (`fullRankCount_mod_five`: 0 of `5^m`). Shifting the secret does not help either (`AroraGe/Shifted.lean`, `shiftedFullRankCount`: with all errors zero, 0 matrix–secret pairs have full rank, kernel witness `(0, 1, 3s)`). The degeneracy comes from the constant error law; the next attempt takes errors random with full support on `[−B, B]`. Gröbner: open |
| `bkw` (coded) | plain BKW with fresh samples: bias of summed errors, Chernoff test; coded/LMS variants | components: `Bkw.blockDifference` (subtraction zeroes a block), `Bkw.ErrorTree.residual_bounds` (`|e| ≤ 2^a B`), `Bkw.errorMean_norm` (Fourier bias of a depth-`a` tree is exactly `β^{2^a}` for a finite base law). `Bkw.matchedMass_conditional` (one fresh pair conditioned on a block match factors into a uniform remaining difference and the difference of two independent errors), `errorMean_difference_re` (after one difference the real character mean is `|mean|² ≥ 0`), `zeroStage_negative_mean` (at depth 0 the cosine mean can be −1, so test after ≥ 1 difference). Batch independence, iteration, the test bound and the counts are open |
| `dual`, `dual_hybrid` | Pouly–Shen-style rigorous dual distinguisher; generating the dual vectors needs walls 1 and 2 | components: `DualMoments.moment_score`, `moment_score_sq`, `repeated_score_variance`. Finding ([research/provable_dual.md](research/provable_dual.md)): shortness and dual membership alone give no advantage (zero vectors, repetition), so the input hypothesis must be Pouly–Shen's independent discrete-Gaussian dual samples. **Counterexample to the stated hypothesis** (`Dual/Identity.lean`): discrete-Gaussian samples from the dual kernel can all lie in `qZ^m` (`m = n = 1`, `A = [1]`), making the score constant (`identityKernel_score`, `identityKernel_mean`). The uniform mean equals the number of entries `≡ 0 mod q`, so the samples must be restricted to `w ≢ 0 mod q`, or follow Pouly–Shen's scaled dual exactly. **Proved given fresh samples and a signed Fourier bias** (`Dual/FreshMoments.lean`): `fresh_dual_test`, with fresh independent dual directions and right-hand sides and signed bias `≥ ε > 0`, the threshold test has acceptance gap `≥ 1 − 2δ` once `N ≥ 8 log(1/δ)/ε²`. Also `uniform_character_mean`, `kernel_phase`, `signed_score_mean`, `fresh_variance`, `dot_product_multiplications` (`N·m`). The sign matters (`negative_binary_phase`). Open: deriving the bias for conditioned discrete Gaussians, the cost of generating the directions (walls 1 and 2), and a shared right-hand side |
| `usvp`, `bdd`, hybrids | uniqueness (stage 2) + a solver for the planted shortest vector | uniqueness **proved** (`Planted.badMatrices_probability`); solver: see below |
| — full-dimension sieve on the embedding (the route around walls 1 and 2) | sieve correctness (T1) + the static statistics S1–S3′ for the planted lattice at polynomial `q` | T1 **proved given S1–S4, S3′ and `IdealUniformLeaves`** (`Sieve.prescribedScan_T1`); statistics: paper for random `q`-ary lattices (T4/T4b, audited), obstruction at thin shells and `q = 3329`, wide-shell redesign in progress |
| — BKZ-based (estimator's cheapest) | wall 1 (average BKZ profile) and wall 2 (sieve on BKZ blocks) | open. Parts 1–3 of wall 1 gave an exact pre-BKZ law and two obstructions; part 4 (Gaussian selection) in progress. Worst-case BKZ gives no cost for Kyber |
| sieving cost `2^{0.292β}` itself | assumption (B) | random lattices: T1 in Lean given the static hypotheses; `0.2925` on paper (P′ + audited GFH) |

Machine-checked building blocks, all with axioms `propext`, `Classical.choice`, `Quot.sound` only:
`BKZ.*` (GSA-free BKZ bounds, Hermite constants up to Blichfeldt), `QAry.*` (exact `q`-ary
mean-value formulas, rank-defect counting), `Rerand.*`, `RevMink.*`, `Sieve.*`, `Search.*`,
`Planted.*`, `AvgBKZ.*`, `PolyQ.*`.
