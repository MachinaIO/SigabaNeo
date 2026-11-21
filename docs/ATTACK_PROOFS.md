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
| `exhaustive_search` | enumerate the secret's support, check `b − As` short; uniqueness w.h.p. | in progress (`Attacks/Guess.lean`) |
| `mitm` | split the secret, hash or round `A₁s₁`, collision search | in progress |
| `arora-gb` | Arora–Ge linearization: full rank of the Macaulay/linearized system w.h.p. (the Gröbner variant needs semi-regularity, Fröberg's open conjecture) | linearization in progress; Gröbner open |
| `bkw` (coded) | plain BKW with fresh samples: bias of summed errors, Chernoff test; coded/LMS variants | in progress (`Attacks/Bkw.lean`) |
| `dual`, `dual_hybrid` | Pouly–Shen-style rigorous dual distinguisher given short dual vectors; generating the dual vectors needs walls 1 and 2 | in progress (`Attacks/Dual.lean`) |
| `usvp`, `bdd`, hybrids | uniqueness (stage 2) + a solver for the planted shortest vector | uniqueness **proved** (`Planted.badMatrices_probability`); solver: see below |
| — full-dimension sieve on the embedding (the route around walls 1 and 2) | sieve correctness (T1) + the static statistics S1–S3′ for the planted lattice at polynomial `q` | T1 **proved given S1–S4, S3′ and `IdealUniformLeaves`** (`Sieve.prescribedScan_T1`); statistics: paper for random `q`-ary lattices (T4/T4b, audited), obstruction at thin shells and `q = 3329`, wide-shell redesign in progress |
| — BKZ-based (estimator's cheapest) | wall 1 (average BKZ profile) and wall 2 (sieve on BKZ blocks) | open. Parts 1–3 of wall 1 gave an exact pre-BKZ law and two obstructions; part 4 (Gaussian selection) in progress. Worst-case BKZ gives no cost for Kyber |
| sieving cost `2^{0.292β}` itself | assumption (B) | random lattices: T1 in Lean given the static hypotheses; `0.2925` on paper (P′ + audited GFH) |

Machine-checked building blocks, all with axioms `propext`, `Classical.choice`, `Quot.sound` only:
`BKZ.*` (GSA-free BKZ bounds, Hermite constants up to Blichfeldt), `QAry.*` (exact `q`-ary
mean-value formulas, rank-defect counting), `Rerand.*`, `RevMink.*`, `Sieve.*`, `Search.*`,
`Planted.*`, `AvgBKZ.*`, `PolyQ.*`.
