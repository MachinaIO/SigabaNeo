# Provable cost of the Part 39 SVP call: what the literature gives

Research note, 2026-11-22. Literature and arithmetic only; no Lean or Python in the repository is touched.

**Setting.** Plain LWE (n, m, q) = (511 samples, 512 secrets, 3329), CBD(3) secret and error. Part 39 (Lean:
`Attacks/Primal/SampleDeletion*.lean`) proves that one exact SVP call on the punctured primal embedding lattice
L ⊆ Z^D, with D = 647, returns ±(e, s, 1) with probability ≥ 99.51664% (D = 662 for 1 − 2^-64). Part 131 replaces it
by two independent calls in dimension 646, which succeed with probability > 99.409%. This note asks what is
*proven* about the cost of those calls. The parameters are not re-optimized here.

Convention: "bits" means log₂ of the operation count. "Explicit" means every constant is a number. An `o(D)`,
`Θ(·)`, `Ω(·)` or `Õ(·)` statement gives **no** number at a fixed D such as 647. It holds only for all sufficiently
large D, with unstated thresholds and constants.

## 0. Verdict

1. **Why the prescribed sieve fails** (§1). [DL26]'s theorem is an average-case statement about Haar-random
   lattices. Its static hypotheses S1 (shell populations match volume) and S2 (quenched lens counts) fail on these
   integral lattices, as recorded in the repository. Part 39's lattices also form a countable set, which has
   Haar measure zero. So even an unconditional [DL26] theorem would say nothing about them.
2. **Algorithms proven for every lattice apply unconditionally** (§2). These are the worst-case algorithms: MV
   Voronoi, ADRS/ASD discrete-Gaussian sieving, Kannan enumeration and the AKS-type sieves. Each takes an
   arbitrary rational (here integral) basis and needs no distributional hypothesis. The integrality that defeats
   [DL26] is harmless to them.
3. **The best asymptotic bound is ADRS / Aggarwal–Stephens-Davidowitz.** It is randomized, with time and space
   2^{D+o(D)} ([ASD18] Thm D.1: list size M = 2^{D+Θ(log² D)}). With the hidden constant set to 1 this would be
   about 2^{734.2} at D = 647, but no paper fixes that constant. **Its value at D = 647 is not determined by any
   published theorem.**
4. **The best deterministic bound with an explicit exponent is Micciancio–Voulgaris** ([MV13] Thm 5.4 /
   Cor 5.5): 2^{2D}·D^{c}·poly(log q), where the polylog exponent c is unspecified. At 647 that is
   **2^{1294}·D^{c}**. Two calls at 646 give 2^{1293}·D^{c}.
5. **Fully explicit bound (new here).** I know of no lattice algorithm with explicit constants whose bound at
   D = 647 beats exhaustive search. Likelihood-ordered enumeration of the 512 secret coordinates, verified
   against all 511 samples, recovers s with probability ≥ 99% after **≤ 2^{1234.40} candidate checks** (§4).
   Each check costs at most 2^{19} word operations, so the total is ≈ 2^{1253.4}. This is the best fully
   numeric, fully rigorous cost bound available today. It does not use Part 39.
6. **BKZ** (§3). Terminating BKZ variants with rigorous tour bounds exist: [HPS11] Thm 1 (non-explicit C),
   Li–Nguyen (JoC 2024) and Li–Walter (2023). Their provable output quality is far too weak to certify recovery at
   any β < D, so for the recorded attack they contribute nothing beyond the single call (β = D).

## 1. Which assumption of the prescribed sieve fails

The prescribed provable sieve is Doulgerakis–Laarhoven [DL26] (claimed, 2026 preprint;
[provable_sieving.md](provable_sieving.md)). Its theorem is: *for L Haar-random in X_D = SL_D(R)/SL_D(Z)*, with
probability 1 − e^{−Ω(D/log D)} over L and the coins, exact SVP is solved in time (3/2)^{D/2+o(D)}. Correctness
rests on static hypotheses about the fixed lattice: S1 (each prescribed thin shell holds (1 ± θ)·vol/covol
lattice points), S2 (quenched lens degree bounds for every shell point, from [Laa26]) and S3 (coverage).
[DL26] establishes these only with high probability over the Haar measure.

What fails on the Part 39 lattices:

* **S1 by emptiness (integer height).** L ⊆ Z^D, so every squared norm is an integer. The prescribed terminal
  shell at D = 647 is [1956.928, 1956.947], and at every D = 647..662 it contains no integer. So the terminal shell
  is empty for every design and plant, and the last merge aborts ([planted_qary_sieve.md](planted_qary_sieve.md)).
* **S1 by overpopulation and S2 by arithmetic (irrational height).** With squared height h ∈ [1.02076213,
  1.02076215] the terminal shell is populated, about 12× the Siegel prediction. But the source shell's heights
  are {9, 30}, only height-0 differences reach the terminal shell, parity excludes every such pair, and terminal
  heights all lie in 17Z. So acceptance is zero, and the height-1 plant is never a terminal point
  ([planted_sieve_scaled.md](planted_sieve_scaled.md)).
* **Root cause.** The theorem is quantified over Haar measure. The integral q-ary lattices of any fixed
  dimension form a countable set, which has Haar measure zero. No average-case theorem transfers to them without
  a separate argument, and the two items above show the hypotheses really fail rather than merely being unproven.
  Any shell-based sieve with shells of relative width O(D^{-2}) at radius² ≈ 2000 meets the same integrality
  obstruction ([reverse_minkowski_blocks.md](reverse_minkowski_blocks.md) has the Z^n analogue).

Worst-case algorithms (§2) make no such hypothesis. Their guarantees hold for every input basis.

## 2. Algorithms proven for every lattice

All of these take a basis of an arbitrary lattice (rational, or integral after scaling). None assumes randomness of
the lattice, so all apply unconditionally to the Part 39 lattice, whose basis is integral with entries ≤ q.

| Algorithm | Statement (verified source text unless marked) | Bits at D = 647 | 646 ×2 | 662 |
| --- | --- | --- | --- | --- |
| Micciancio–Voulgaris, Voronoi cell [MV13] | **Thm 5.4**: "deterministic Õ(2^{2n})-time and Õ(2^n)-space algorithm that on input an n-dimensional lattice Λ with basis B, outputs the relevant vectors of Λ". **Cor 5.5**: deterministic Õ(2^{2n})-time SVP. Õ(g) means ≤ log^c g · g "for some constant c and all sufficiently large n"; the input is assumed integral with poly(n)-bit entries, otherwise there is a polynomial factor in the entry size M and the ambient dimension d (§2, "For simplicity…"). The simpler Thm 4.10 / Cor 4.11 gives Õ(2^{3.5n}). | 1294 + c·log₂(1294) | 1293 + … | 1324 + … |
| Aggarwal–Dadush–Regev–Stephens-Davidowitz [ADRS15] | Abstract / informal Thm 1.1: "randomized 2^{n+o(n)}-time and space algorithm for solving SVP" (formal Cor 4.5, not re-read here). The o(n) comes from a 2^{O(n/log n)} sublattice step, Gaussian-mass bounds and a combiner tower; no closed form is given. | 647 + o(647) | 647 + o | 662 + o |
| Aggarwal–Stephens-Davidowitz "Just take the average!" [ASD18] | **Thm D.1**: "For any lattice ℒ ⊂ ℝⁿ, the output of Procedure 3 on input ℒ will be a shortest non-zero vector in ℒ except with probability at most exp(−Ω(n))". Procedure 3: M = 2^{n+Θ(log² n)} list vectors, ℓ = Θ(log n) averaging rounds, 200n outer radii. Running time is stated as 2^{n+o(n)}; no constant is given. | ≈ 647 + Θ(87.2) | ≈ 646 + Θ(87.0) + 1 | ≈ 662 + Θ(87.8) |
| Pujol–Stehlé, ListSieve-Birthday [PS09] | 2^{2.465n+o(n)} time, 2^{1.233n+o(n)} space, randomized (from the repository table in [provable_sieving.md](provable_sieving.md); theorem number not re-checked) | 1594.9 + o | 1593.4 + o | 1631.8 + o |
| Kannan enumeration, Hanrot–Stehlé analysis [HS07] | **Thm 2** (arXiv v2 numbering; "Theorem 3.1" in some renderings): on a quasi-HKZ basis with A = ‖b₁‖², enumeration takes ≤ P(log B)·2^{O(d)}·d^{d/(2e)} loop iterations; HKZ reduction (hence SVP) in deterministic time P(log B, n)·d^{d/(2e)+o(d)}. Input: an integral basis. The authors say the o(d) constants "are improvable", but they made no effort to fix them. | 1111.3 + o(647) | 1109.3 + o + 1 | 1141.1 + o |

Here log₂²(647) = 87.19, log₂²(646) = 87.0 and log₂²(662) = 87.8. "Θ(87.2)" means a constant times that,
with the constant not published.

**What is explicit.** Only the leading exponents (2, 1, 2.465, 1/(2e)) are numbers. Every algorithm also has a
prefactor whose constant is unpublished (log^c, 2^{O(d)}, 2^{Θ(log² n)}, o(n)). For the randomized ones the failure
probability exp(−Ω(n)) has no constant either, so even the constant-probability statement is asymptotic. For
the record, repetition works: k independent runs of [ASD18], keeping the shortest output, fail with probability
≤ (single-run failure)^k, because a run that succeeds returns a true shortest vector.

**An explicit enumeration bound (derived here, from [HS07] §4.1).** HS07 eq. (1), which is fully explicit, gives
the number of integer points in level i's ellipsoid as N_i ≤ (4e(1+√π))^d · ∏_{j≥i} max(1, √A/(√d‖b*_j‖)).
Their Thm 3 for an HKZ basis is also fully explicit: ‖b₁‖^{|I|}/∏_{i∈I}‖b*_i‖ ≤ (√d)^{|I|(1+ln(d/|I|))} ≤ (√d)^{d/e+|I|}.
Together these bound the final enumeration on an HKZ basis by d·(4e(1+√π))^d·d^{d/(2e)} points, times poly.
At d = 647 that is 2^{9.3 + 3179.3 + 1111.3} = **2^{4300}**, since log₂(4e(1+√π)) = 4.914. Kannan's recursion
to produce the (quasi-)HKZ basis is not included. So with the constants made explicit, enumeration is far worse
than MV here. Even the bare leading term d^{d/(2e)} = 2^{1111} beats 4^d only for d < 2^{4e} ≈ 1876, and the
2^{O(d)} factor erases that advantage.

**Approximate SVP does not apply to the recorded dimensions.** Three results are candidates:

* the 2^{0.802n+o(n)}-time, 2^{0.401n}-space algorithm for "some large constant" factor γ (Liu–Wang–Xu–Zheng 2011,
  Wei–Liu–Wang 2015, as cited in [ADRS15] and [ALNS20] Table 1);
* ALNS20's n^c-SVP in 2^{0.802n/(2c)} for c ∈ [1/2, 1] and 2^{0.802n/(c+1)} for c ≥ 1 (informal Thms 1.1–1.2;
  Cors 3.4 and 4.4, not re-read);
* ADRS15's 2^{n/2+o(n)} 1.93-approximate *decision* SVP.

A γ-approximate SVP oracle returns ±v only if λ₂ > γ·λ₁ (unique-SVP with gap γ). Part 39 certifies only that no
other pair has norm ≤ ‖v‖, which is gap > 1. The certificate's failure probability rises steeply with the radius:
at 647, replacing ‖v‖² by γ²‖v‖² multiplies the volume term by γ^{647}. So no γ > 1 is certified at 647, and the
large-constant γ of the 0.802 algorithm is not even specified. Deciding the dimension at which a gap-γ
certificate holds would be a parameter optimization, which is out of scope. [ACKS21] (arXiv:2002.07955) gives
exact SVP in 2^{1.669n+o(n)} time and 2^{0.5n+o(n)} space (Thm 1.4), which is worse than ADRS in time.

## 3. BKZ: termination and tour counts

* **[HPS11] Thm 1** (verified from the PDF). "There exists C > 0 such that … if terminated after
  τ_BKZ := C·(n³/β²)·(log n + log log max_i ‖b_i*‖/(det L)^{1/n}) calls to an HKZ-reduction (or SVP solver) in
  dimension β", the modified BKZ' outputs a basis with ‖c₁‖ ≤ 2·ν_β^{(n−1)/(2(β−1)) + 3/2}·(det L)^{1/n}, where
  ν_β is the maximum Hermite constant in dimensions ≤ β. "If L ⊆ Qⁿ, then the overall cost is
  ≤ Poly(n, size(B))·C_HKZ(β)." Footnote 4: "C is used to absorb lower-order terms in n, and could be taken
  small". It is not given numerically. Lemma 11 has the (1 + ε) variant, with log(n/ε) in place of log n.
  Appendix A shows that the *original* BKZ with LLL parameter δ < 1 terminates after O(β)^n SVP calls, via the
  potential ∏‖b_i*‖^{⌈3β/log(1/δ)⌉^{n−i+1}}. (Gama–Nguyen are credited with an (nβ)^n claim.)
* *(Removed after audit: an "integral termination" claim for BKZ via the LLL potential was false; see Audit item 1. No polynomial tour bound is known for original BKZ.)*
* **Li–Nguyen**, "A complete analysis of the BKZ lattice reduction algorithm", JoC 2024 (ePrint 2020/1237):
  Thm 2 bounds every normalized prefix determinant after O((d/β)² log d) GBKZ tours, for exact or approximate
  oracles. Its use in this repository is in [wall1_literature2.md](wall1_literature2.md). The PDF was
  unreachable this session (403), so the theorem was not re-read.
* **Li–Walter 2023** (generalized slide): Thm 7 gives N = O((k/b)² log(k/t)) inner tours, with constants hidden
  in the O. [wall1_li_walter.md](wall1_li_walter.md) records that the algorithm provably terminates.

**What this gives here: nothing for the recorded attack.** The attack is a single SVP call (β = D). For β < D, the
only provable guarantee is a Hermite-type bound such as HPS's. Recovery would need ‖c₁‖ < λ₂, and λ₂ is heuristically (not certifiably) about
GH(L) ≈ √(D/(2πe))·det^{1/D} ≈ 6.15·det^{1/D} at D = 647. HPS guarantees only 2·ν_β^{≥2}·det^{1/D}. Since
ν_β ≥ γ_β ≳ β/(2πe) by Minkowski–Hlawka, this is ≈ 2·35^{2.04} ≈ 2800·det^{1/D} at β = 600: about 450×
too large under that heuristic (recovery is in any case uncertified). Wall 1 (Parts 30–46) rules out reducedness-only arguments in general. So rigorous tour counts bound
the cost of running BKZ-β, but certify no success probability for any β < 647.

## 4. A fully explicit rigorous baseline: likelihood-ordered secret search

This section is new and self-contained. It is the yardstick that any explicit lattice-route bound must beat.

**Algorithm.** Enumerate y ∈ {−3..3}^{512} in non-increasing CBD(3) probability p(y), breaking ties arbitrarily.
For each y, compute c = b − A·y mod q (centered) and accept the first y with c ∈ {−3..3}^{511}.

**Correctness.** Condition on (s, e). For each candidate y ≠ s, y − s is a nonzero vector mod q (entries in
[−6, 6]), so A(s − y) is uniform on Z_q^{511} over uniform A. Hence Pr[y accepted] = (7/q)^{511} = 2^{−4544.59}.
The true s is accepted. The candidate order does not depend on A. If s has rank R(s), a union bound over the
R(s) − 1 earlier candidates gives Pr[wrong output] ≤ R(s)·2^{−4544.59}.

**Rank.** R(s) ≤ G(s) := #{y : p(y) ≥ p(s)}, which counts the whole tie class adversarially. G(s) depends only
on the type (n₀, n₁, n₂, n₃) of |s_i|. The probabilities are p(0) = 20/64, p(±1) = 15/64, p(±2) = 6/64 and
p(±3) = 1/64. A type has 512!/(n₀!n₁!n₂!n₃!)·2^{512−n₀} members. Sorting all 22,632,705 types by p and
accumulating counts gives:

| Quantity | Bits |
| --- | --- |
| Shannon entropy of CBD(3)^{512} | 1194.68 |
| 99% quantile of log₂ G(s) | **1234.40** |
| 99% quantile of −log₂ p(s) (cruder: G ≤ 1/p) | 1243.31 |
| (1 − 2^{−20}) quantile of log₂ G(s) | 1277.30 |
| Rényi-½ entropy (Arıkan bound on E[R]) | 1286.95 |

These were computed in double precision with log-gamma, then sorted with a cumulative log-sum (scratch script,
not committed). For a certificate, redo them in exact integer arithmetic. That is an easy computation, and the
margins are many bits.

**Cost.** With probability ≥ 99% over s, at most 2^{1234.40} candidates are tested. Each needs a 511×512
mat-vec mod q, under 2^{19} word operations without incremental tricks. The total is **≈ 2^{1253.4} operations,
with every constant explicit**. The wrong-output probability is ≤ 2^{1234.4−4544.59}. This beats MV at 647
(2^{1294} times an unspecified polynomial) and every other explicit bound in §2. It loses only to the
non-numeric ADRS/ASD 2^{D+o(D)}.

**Consequence.** With explicit constants, the rigorous lattice route (Part 39 plus a provable SVP solver) does
not beat brute force on these parameters today. ASD18 has a budget of 1234.4 − 647 ≈ 587 bits for its
2^{Θ(log² D)}, poly and repetition factors before brute force wins. That makes an explicit re-analysis of
ASD18 at D = 647 the most promising single step (§6).

## 5. Formalization in Lean: feasibility and effort

Rough person-time, assuming the repository's existing CBD and uniform-matrix infrastructure. Running time
needs a cost model, and the repository's Lean code proves probabilities, not operation counts. So "formalizing
a cost" below means proving an explicit count of a stated quantity: candidates, list operations, or nodes.

| Item | What would be proved | Effort | Value |
| --- | --- | --- | --- |
| §4 brute-force baseline | the (7/q)^{511} false-accept bound (a finite uniform-matrix lemma close to Part 39's), the rank bound G ≤ #{p ≥ p(s)}, and the numeric quantile by `decide +kernel` over 22,632,705 types (heavy; it may need the 1/p bound or a coarser type grouping) | 2–4 weeks | gives the only fully explicit rigorous cost today |
| HS07 counting layer | eq. (1), the θ-function point count, plus the HKZ geometry Thm 3 (several pages; induction with convexity) | 1–2 months | explicit, but gives 2^{4300}, so useless here |
| Kannan recursion | correctness and cost recursion of HKZ reduction | 2–4 months on top of the above | low |
| MV Voronoi algorithm | Voronoi relevant-vector characterization (Voronoi's theorem, Horváth's boundary lemma), CVPP iterative slicer, rank reduction; making Õ explicit means re-deriving the poly factors | 4–8 months | gives 2^{2D}·explicit poly, but brute force already wins |
| ADRS/ASD18 | discrete Gaussian on lattices, smoothing and Banaszczyk-type tail bounds, the pair-and-average lemma, the BLP+13/GPV initial sampler; the constants must also be fixed first, which is research and not just transcription | 6–12 months, after an explicit paper analysis | the only route that could beat brute force (by up to ~587 bits) |
| HPS11 dynamical-system BKZ | affine-system tour bound | 1–2 months | none for success (§3) |

## 6. What remains unproven

* **No numeric cost at D = 647 (or 646 ×2) for any lattice algorithm better than 2^{1294}·D^{c}** with c
  unspecified. The ADRS/ASD 2^{D+o(D)} bound is asymptotic. Fixing its constants and its exp(−Ω(D)) failure
  constant at D = 647 is open, and is the most valuable next step (≈ 587 bits of slack versus brute force).
* **No provable sieve with exponent < 1 for exact SVP applies to these lattices.** [DL26]'s 0.2925 (and the
  repository's T1 at 0.415) are average-case over Haar measure, and their hypotheses fail here (§1). The
  heuristic 2^{0.2925·647} ≈ 2^{189} remains a cost model.
* **Approximate-SVP speedups (0.802 and below) need a gap-γ uniqueness certificate.** None exists at the recorded
  dimensions, and the 0.802 algorithm's γ is unspecified.
* **BKZ with β < 647 has rigorous tour counts but no rigorous success** (wall 1).
* **Not re-verified this session:** the MV13 SIAM journal numbering (the theorems above are from ECCC TR10-014
  Revision 1), the ADRS15 formal Cor 4.5, the PS09 theorem number, the Li–Nguyen Thm 2 text (403), and ALNS20
  Cors 3.4/4.4. The §4 quantiles were computed in floating point only.

## References

* [ADRS15] D. Aggarwal, D. Dadush, O. Regev, N. Stephens-Davidowitz. Solving the Shortest Vector Problem in 2^n
  Time via Discrete Gaussian Sampling. STOC 2015. arXiv:1412.7994 (abstract, Thm 1.1).
* [ASD18] D. Aggarwal, N. Stephens-Davidowitz. Just take the average! An embarrassingly simple 2^n-time algorithm
  for SVP (and CVP). SOSA 2018. arXiv:1709.01535 (Thm 1.1, Procedure 3, Thm D.1).
* [ACKS21] D. Aggarwal, Y. Chen, R. Kumar, Y. Shen. Improved (Provable) Algorithms for the Shortest Vector Problem
  via Bounded Distance Decoding. STACS 2021. arXiv:2002.07955 (Thms 1.2, 1.4, 1.5).
* [ALNS20] D. Aggarwal, J. Li, P. Q. Nguyen, N. Stephens-Davidowitz. Slide Reduction, Revisited. CRYPTO 2020.
  arXiv:1908.03724 (Table 1, Thms 1.1–1.2).
* [DL26] Doulgerakis, Laarhoven. arXiv:2609.37482 (claimed; see [provable_sieving.md](provable_sieving.md)).
* [HPS11] G. Hanrot, X. Pujol, D. Stehlé. Analyzing Blockwise Lattice Algorithms using Dynamical Systems.
  CRYPTO 2011 (Thm 1, Lemma 11, Appendix A).
* [HS07] G. Hanrot, D. Stehlé. Improved Analysis of Kannan's Shortest Lattice Vector Algorithm. CRYPTO 2007;
  arXiv:0705.0965 / INRIA RR-6186 (Thm 2, Thm 3, eq. (1)).
* Li, Nguyen. A Complete Analysis of the BKZ Lattice Reduction Algorithm. J. Cryptology 2024; ePrint 2020/1237.
* Li, Walter. Improving convergence and practicality of slide-type reductions. Inf. Comput. 2023; ePrint 2023/140.
* [MV13] D. Micciancio, P. Voulgaris. A Deterministic Single Exponential Time Algorithm for Most Lattice Problems
  Based on Voronoi Cell Computations. SIAM J. Comput. 42(3), 2013; ECCC TR10-014 Rev. 1 (Thm 4.10, Cor 4.11,
  Thm 5.4, Cors 5.5–5.6).
* [PS09] X. Pujol, D. Stehlé. Solving the Shortest Lattice Vector Problem in Time 2^{2.465n}. ePrint 2009/605.

## Audit

Independent audit, 2026-11-22. I re-read the note against the repository cross-references
(planted_qary_sieve.md, planted_sieve_scaled.md, PROOF_GAP.md), the primary sources I could download
(ASD18 arXiv:1709.01535, ADRS15 arXiv:1412.7994, HS07 arXiv:0705.0965, ACKS21 arXiv:2002.07955,
MV ECCC TR10-014 Rev. 1), and recomputed §4 with my own scratch script (not committed). The script uses exact
integer arithmetic for the decisive quantities. PS09 (ePrint 2009/605) and HPS11 (ePrint 2011/198, HAL) were
unreachable (403 / bot wall), so I could not check those statements.

**Verdict: MINOR CAVEATS.** The main conclusions hold: [DL26] does not apply, the worst-case algorithms apply
but give no numeric bound at D = 647, and §4's brute-force baseline is correct (I confirmed it exactly). One
peripheral mathematical claim in §3 is false (issue 1). It does not affect any conclusion. The rest are small
corrections or places where the wording claims more rigor than the argument has.

**Confirmed.**
* §1: the terminal interval (1956.928, 1956.948) at 647 and its emptiness of integers, the irrational-height
  window, the source heights {9, 30} (differences {0, 18, 21, 39, 60}), the terminal heights in 17Z, and the
  "≈ 12× Siegel" figure (PROOF_GAP.md) all match the repository. The Haar-measure-zero argument is correct.
  After rescaling to covolume 1, the Part 39 lattices form a countable set, and the Part 39 distribution is
  supported on a finite set, so it is singular with respect to Haar measure. No statement that holds with
  probability 1 − ε, or even 1, over Haar says anything about such a set.
* MV: Thm 5.4 and Cor 5.5 (Õ(2^{2n}), deterministic), Thm 4.10 and Cor 4.11 (Õ(2^{3.5n})), the definition
  "f(n) ≤ log^c g(n)·g(n) for some constant c and all sufficiently large n", and the integral-input caveat are
  all quoted correctly.
* ASD18: Thm D.1 is quoted verbatim. Procedure 3 has M = 2^{n+Θ(log² n)}, ℓ = Θ(log n), u = Θ(n) and 200n
  radii. The proof says only "The running time is clear", with no constants.
* ADRS15: the abstract gives a randomized 2^{n+o(n)} time and space SVP algorithm, 1.93-approximate SVP in
  2^{n/2+o(n)}, and the 2^{0.802n} large-constant-γ citation. All confirmed.
* HS07: Thm 2 (P(log B)·2^{O(d)}·d^{d/(2e)} loop iterations; HKZ in P(log B, n)·d^{d/(2e)+o(d)}), Thm 3
  (‖b₁‖^{|I|}/∏‖b*_i‖ ≤ (√d)^{|I|(1+log(d/|I|))} ≤ (√d)^{d/e+|I|}), eq. (1) with constant 4e(1+√π), and the
  "improvable … no effort was made" remark are all confirmed. (The PDF's eq. (1) has a typo, b*_i for b*_j;
  the note's j is the intended index.) The derived explicit bound d·(4e(1+√π))^d·d^{d/(2e)} ≈ 2^{4300} and the
  crossover d < 2^{4e} ≈ 1876 recompute correctly.
* ACKS21: 2^{1.669n+o(n)} time and 2^{0.5n+o(n)} space appear in the abstract (theorem number not checked).
* Arithmetic: 2.465·647 = 1594.9, (647/2e)·log₂647 = 1111.3, log₂²647 = 87.19, and the §3 figures
  (exponent 2.039, 2·35.1^{2.04} ≈ 2840, GH factor 6.155) all recompute.
* §4, recomputed. There are 22,632,705 types. The 2-, 3- and 5-adic exponents (2n₀+n₂, n₁+n₂, n₀+n₁) of
  20^{n₀}15^{n₁}6^{n₂} determine the type, because the linear system has determinant −3. So distinct types
  never tie in probability, and ties occur only within a type. The float ordering has margins of at least
  5.2·10⁻⁵ bits on either side of the cut, far above rounding error, so the set of types at or above the cut is
  determined exactly. Exact big-integer sums give: mass of the top set = 0.9900018… (≥ 0.99, and < 0.99 without
  the cut type), and **log₂ G = 1234.3955** exactly. Floating-point checks: entropy 1194.68, 99% quantile of
  −log₂ p 1243.31, (1 − 2^{−20}) quantile of log₂ G 1277.30, 512·H_{1/2} = 1286.95. All match the note. The
  correctness argument holds: q is prime and y − s ≢ 0 has entries in [−6, 6], so A(s − y) is uniform. The
  total success probability is ≥ 0.9900018 − 2^{1234.4}·(7/q)^{511} > 0.99.

**Issues and corrections.**
1. **§3 "Integral termination (classical)" is false.** The LLL potential ∏D_i does *not* decrease
   monotonically under a BKZ insertion. Inserting v with ‖π_k(v)‖ < δ‖b*_k‖ at position k lowers D_k. But for
   k < j < k+β−1 the new prefix determinant is at most D_{j−1}·δ²‖b*_k‖², which can exceed
   D_j = D_{j−1}‖b*_j‖² whenever ‖b*_j‖ < δ‖b*_k‖. So no bound of the form log_{1/δ²}∏D_i ≤ poly(D)·log q
   on the number of insertions follows. A polynomial tour bound for the original BKZ is not known. The note's
   own next statement (HPS11 App. A: O(β)^n SVP calls, via a doubly exponential weighted potential) exists
   precisely because of this. *Correction:* delete the bullet, or restrict it to LLL (β = 2). The rigorous
   tour bounds are HPS11 Thm 1 (for the modified, terminated BKZ'), Li–Nguyen and Li–Walter, and O(β)^n for
   original BKZ. §3's conclusion is unaffected.
2. **§3 "about 450× too large"** treats λ₂ ≈ GH(L) as a fact, but it is a heuristic for these lattices. Part 39
   certifies only that no other pair has norm ≤ ‖v‖, which gives no upper bound on λ₂. *Correction:* say that
   HPS's guarantee certifies recovery only if λ₂ > ≈ 2800·det^{1/D}. Nothing certifies that, and heuristically
   λ₂ ≈ 6.15·det^{1/D}.
3. **§4 type count:** 22.8·10⁶ → **22,632,705** (= C(515, 3)).
4. **§4 false-accept exponent:** 511·log₂(7/3329) = **−4544.59**, not −4544.7. The bound becomes
   2^{1234.4−4544.6} = 2^{−3310.2}. The effect is negligible.
5. **§4 per-candidate cost.** The mat-vec is 511·512 = 261,632 multiply-adds (2^{18.00}). Counting a
   multiply-add as 2 operations already gives 523,264, just under 2^{19} = 524,288. So "< 2^{19}" holds only
   with lazy reduction (one mod per row) and if the range check is not counted. Generating candidates in
   likelihood order (walking the sorted type list and the sign and position patterns within each type) is
   also not counted. That overhead is polynomial per candidate, and poly(512) once for sorting the types.
   *Correction:* state "≤ 2^{19}·(1 + o(1)) word operations, plus candidate-generation overhead", or bound
   the total by 2^{1254} to absorb both.
6. **§4 table, Rényi-½ row:** Arıkan's bound is E[R] ≥ 2^{H_{1/2}}/(1 + ln 7^{512}) ≈ 2^{1286.95−9.96}, and
   it lower-bounds the *expected* rank under the optimal order. *Correction:* label the row as the Rényi-½
   entropy, and note that Arıkan's lower bound on E[R] is ≈ 2^{1277}. This is context only. It does not
   affect the 99% bound.
7. **§1, last bullet, overstated:** "Any shell-based sieve with shells of relative width O(D^{-2}) … meets the
   same integrality obstruction". A shell of absolute width < 1 can always be placed to contain an integer
   level. The real obstruction is that population is concentrated on integer levels, so the (1 ± θ)·vol/covol
   form of S1 fails (the shell is either empty or overfull by a factor of about 1/width). *Correction:* reword
   to say that S1's volume-proportional population fails.
8. **§0 item 5, overstated:** it says "I know of no lattice algorithm with explicit constants…" and then
   "This is the best fully numeric, fully rigorous cost bound available today". The second claim is a
   literature-completeness claim. *Correction:* "the best such bound known to the author".
9. **Not independently verified by this audit:** PS09 (2.465 / 1.233 exponents and theorem number) and the
   HPS11 Thm 1 text, footnote 4 and App. A. Both PDFs were unreachable. The note marks PS09 as unchecked but
   marks HPS11 "verified from the PDF". A future pass should confirm HPS11 before anything depends on the
   ν_β exponent.
10. **Minor:** §0 item 4 writes 2^{2D}·D^{c}. The MV definition gives 2^{2D}·(2D)^{c}·poly(M, d). The two
    differ by 2^{c}, which is absorbed into the unspecified c. No change needed beyond consistency with the
    table.
