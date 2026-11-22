# Wall 1 · Restart certificates: what acceptance must satisfy

Part 131 left the restart architecture with one gap: a proof that acceptance is not rare. This note settles what that gap
actually is in the decoupled setting of Part 47, and what each randomization can and cannot provide. Parameters: plain LWE
(511, 512, 3329), CBD(3), final width β ∈ [406, 506].

**Verdict.**

1. **Certificates are not the bottleneck (proved).** In the decoupled architecture a plant-free certificate on the selected
   output is sound with no stopping-time bias. A Monte Carlo certificate built from simulated plants is also *complete* up
   to binomial error. Per-trial acceptance therefore equals, up to about 10⁻⁹, the design mass on which the reducer output is
   good (Theorem 1). Part 131's soundness/completeness worry disappears.
2. **"Not rare on average" is never sufficient (proved).** With a shared design, restart failure is exactly
   E_A[(1−α(A))^T], where α(A) is the per-design acceptance. Reaching 99% needs a *lower quantile* of α(A) of order 1/T
   (Theorem 2), so mean acceptance is useless. With K disjoint row blocks failure is exactly ∏(1−ᾱ_t), but K ≤ 3 here,
   so the blocks need ᾱ ≥ 0.785 to 0.9, not 1/poly.
3. **Randomization audit (proved).**
   * Only fresh rows give exact independence.
   * Random overlapping row subsets give at most K-fold amplification of the bad-design mass, with K = ⌊m/m′⌋.
   * Basis and symmetry randomization give nothing generic: zero gain for canonicalizing or equivariant reducers.
   * A-independent planes are provably rare-accepting (Parts 40 and 45).
   * Re-selecting the terminal vector can beat shortest-vector selection by at most 2/√3, because every reselection is
     capped by λ₂ of the final window (Lemma 5).
4. **Moment methods (proved barrier plus a template).**
   * Relaxing the failure budget from 1% to 1 − 1/poly moves any first-moment (counting) certificate's radius by at most
     100^{1/D}: 1.0092 at D = 505 and 1.0114 at D = 405 (Proposition 6).
   * Second-moment methods help only with an *upper* bound on the joint failure of two restarts on one design
     (Proposition 7). Nothing on record provides one.
   * Positive template (Theorem 8): Part 105 plus the Lean pair second moment, used by PZ, gives *instance-level*
     acceptance for a reselect-by-certificate rule on a Haar window. At rank 506 and ratio 0.954 the failure is
     < 1.372·10⁻⁵.
5. **Remaining gap.** One of Gap A (an instance-level lower tail of α), Gap B (ᾱ ≥ 1 − 0.01^{1/K} on m/K-row designs) or
   Gap R (two unselected statistics of the final window law). All three are statements about the same unknown BKZ output
   law. None is implied by Parts 105 and 108.

Notation follows [Part 94](wall1_threshold.md), [Part 47](wall1_decoupled.md), [Part 105](wall1_selection_law.md) and
[Part 108](wall1_first_tour.md).

## 0. Setting

* **Design and plant.** A is the m × n design (m = 511, n = 512), uniform over F_q. A row block B ⊆ [m] gives the
  sub-design A_B. The plant is X = (e, s) with iid CBD(3) entries, independent of A. Write L₀(A) for the height-zero lattice.
  Part 47 gives L = L₀ ⊕ ℤu.
* **Trial.** A trial uses design data D (A, or A_B), coins ω, and a **plant-free reducer** R(D, ω). R reads only L₀(D):
  BKZ or slide with any randomization, ending in a prefix and a final horizontal block H of rank β − 1.
* **Pipeline.** Φ(R(D, ω), b) is the fixed postprocessing on the true right-hand side b = Ds + e_B: one exact SVP on the
  rank-β block H ⊕ ℤ(y, 1), then the lift (Babai on the prefix, Part 47). It returns a candidate secret. Any final-step tie
  coins are fresh.
* **Conditional success.** G(D, ω) := Pr_X[Φ(R(D, ω), Ds + e_B) = s]. This is well defined because X ⊥ (D, ω).
* **Good designs.** For a threshold θ, p_θ(A) := Pr_ω[1 − G(A, ω) ≤ θ]. The quantity δ of the Lean reduction
  (success ≥ (1−δ)(1−ε)) is δ = 1 − E_A p_ε(A).

## 1. Soundness and completeness of a plant-free restart certificate

**Monte Carlo certificate C(M, k).** Given (D, ω), draw fresh fake plants X′₁, …, X′_M iid CBD(3), independent of
everything else. Run the pipeline on b′_j = D s′_j + e′_j and count the failures F (output ≠ s′_j). Accept iff F ≤ k. The cost is M
extra rank-β SVP calls and lifts per trial, all in the same oracle dimension β. Since the pipeline is the same map, F is
exactly Bin(M, 1 − G(D, ω)) given (D, ω).

**Restart attack.** For t = 1, …, T: draw (D_t, ω_t), run R, test C. At the first acceptance t* output Φ(R(D_t*, ω_t*), b_t*)
on the *true* data. Write N_run = min(t*, T).

**Theorem 1.** Fix 0 ≤ θ_good < θ_bad < 1. Put B := Pr[Bin(M, θ_bad) ≤ k] and ε′ := Pr[Bin(M, θ_good) > k].

(a) Pr[attack fails] ≤ Pr[t* > T] + θ_bad + B · E[N_run] ≤ Pr[t* > T] + θ_bad + B·T.

(b) Shared design (D_t = A for every t): Pr[t* > T] = E_A[(1 − α(A))^T], where α(A) := Pr[accept | A] ≥ (1 − ε′) p_{θ_good}(A).

(c) Disjoint row blocks (D_t = A_{B_t} with pairwise disjoint B_t): Pr[t* > T] = ∏_t (1 − ᾱ_t), with ᾱ_t := Pr[accept_t]. This
holds **unconditionally**, with no average over s.

*Proof.* (X, (D_t), (ω_t), (X′_t)) are independent apart from the D_t being functions of A, and X ⊥ A. Trial t's
real outcome is a function of (D_t, ω_t, X). The event {t* = t} is a function of (A, ω_{≤t}, X′_{≤t}). Hence

Pr[fail at t | A, ω, X′] = 1 − G(D_t, ω_t) =: 1 − G_t,

and therefore Pr[fail, t* ≤ T] = Σ_t E[1{t* = t}(1 − G_t)]. Split each term on bad_t := {1 − G_t > θ_bad}.

* On bad_tᶜ the term is at most θ_bad · Pr[t* = t]. These sum to at most θ_bad.
* On bad_t, write {t* = t} = {N_run ≥ t} ∩ accept_t. The event {N_run ≥ t} is determined by trials before t. Given A and the
  past, trial t's fake plants are fresh, so Pr[accept_t | A, ω_{≤t}, X′_{<t}] = Pr[Bin(M, 1 − G_t) ≤ k]. This is ≤ B on
  bad_t, because the binomial CDF decreases in p. Summing, Σ_t Pr[t* = t, bad_t] ≤ B Σ_t Pr[N_run ≥ t] = B·E[N_run].

This proves (a).

For (b), the acceptance indicators are conditionally iid given A. On {1 − G ≤ θ_good} acceptance has probability
≥ 1 − ε′ by monotonicity.

For (c), accept_t is a function of (A_{B_t}, ω_t, X′_t). These are independent across disjoint blocks because rows are
iid and **s does not enter the certificate**. ∎

**Numbers.** With M = 10⁵, k = 290, θ_good = 0.002 and θ_bad = 0.004 (exact binomial sums in §7), B < 4.2·10⁻⁹ and
ε′ < 9.5·10⁻¹⁰. So per-trial acceptance is within 10⁻⁹ of p_{0.002}(A). The attack fails with probability at most
Pr[t* > T] + 0.004 + 4.2·10⁻⁹·T.

**Remarks.**

* Soundness holds for every reducer, including adaptive and randomized selection. The certificate never inspects the
  true plant, and the plant is independent of everything the stopping rule reads. This is exactly why the plant-dependent
  reducers of Parts 30–46 were hard and the decoupled one is not.
* Any deterministic plant-free sufficient condition can replace C, with B = 0 and θ_bad equal to its proven conditional
  failure. Examples are Part 102's λ₁(H) ≥ 61.3, and Part 94's λ₁(H) > T(R) combined with a norm cap. These are cheaper but
  less complete. Theorem 1 shows completeness is free with the Monte Carlo version.
* Alternatively one can accept on verification on v reserved rows (Part 132). Acceptance then depends on s, and the bound
  in (b) becomes E_{A,X}[(1 − α′(A, X))^T] with α′(A, X) = Pr_ω[success | A, X]. It costs rows, and Part 132's caveat on
  integer versus residue verification applies.
* **Restart form of the Lean reduction:** success ≥ 1 − θ_bad − δ_T − B·E[N_run], with
  δ_T := E_A[(1 − (1−ε′) p_{θ_good}(A))^T] ≤ δ + ε′. Restarts never hurt, and as T → ∞, δ_T → Pr_A[p_{θ_good}(A) = 0].

## 2. Exhaustion is a lower-quantile statement

**Theorem 2.** Let α ∈ [0, 1] be any random variable (here α(A)) and T ≥ 1.

1. For all x ∈ (0, 1): Pr[α ≤ x](1−x)^T ≤ E[(1−α)^T] ≤ Pr[α < x] + (1−x)^T.
2. E[(1−α)^T] ≤ E[1/(1+Tα)] ≤ E[1/α]/T. Hence the Las Vegas form (restart until acceptance) uses E_A[1/α(A)] expected trials,
   and T = 250·E[1/α] gives exhaustion ≤ 0.004.
3. Jensen gives E[(1−α)^T] ≥ (1−Eα)^T and ≥ Pr[α = 0]. Mean acceptance alone certifies nothing: if α ∈ {0, 1} with
   Pr[α = 1] = ᾱ, exhaustion equals 1 − ᾱ for every T.
4. **Necessity.** If Pr[α ≤ x] ≥ 0.02, exhaustion ≤ 0.01 needs T ≥ ln 2/(−ln(1−x)) ≥ (ln 2)(1−x)/x.

*Proof.* (1): split on {α < x} and use monotonicity of (1−α)^T. (2): Bernoulli gives (1−α)^{−T} ≥ 1 + Tα. (3): convexity.
(4): from (1), 0.02(1−x)^T ≤ 0.01 is needed. ∎

So in the shared-design architecture, "acceptance not rare" must mean: the 1–2% lower quantile of α(A) is at least of
order 1/T. That is an **instance-level** statement, uniform over 98–99% of designs.

## 3. Which randomizations give independence

### 3.1 Fresh disjoint rows

Theorem 1(c) is exact. With K blocks and T_i restarts on block i, the exhaustion is ∏_i E[(1 − α(A_{B_i}))^{T_i}].

| K | 1 − 0.01^{1/K} (required ᾱ, single restart per block) |
|---:|---:|
| 2 | 0.9 |
| 3 | 0.78456 |
| 4 | 0.68377 |
| 5 | 0.60189 |

The 511 rows bound K by ⌊511/m′⌋. At the β ≈ 406–506 regime the design uses most rows, so K ∈ {1, 2, 3}, and each block
is then a *harder* instance with m′ rows. Fresh-row independence turns "1/poly acceptance" into "≥ 0.785–0.9 acceptance",
not into a rare-event requirement. (These parameter tradeoffs are not optimized here.)

Sample amplification cannot manufacture more blocks. New rows formed as signed subset sums of w old rows have only
≤ 2^{511} choices per row, against q^{512} for a uniform row. No leftover-hash argument can make them independent of
the old design, and their error grows to w·CBD(3).

### 3.2 Random overlapping row subsets

Suppose trial t uses a uniformly random m′-subset S_t, randomly ordered (so the kernel below is symmetric), and fresh coins.
Then α(A) = C(m, m′)⁻¹ Σ_{|S|=m′} a(A_S), with a(B) := Pr[accept | design B].

**Theorem 3.** Let K = ⌊m/m′⌋ and let a₁, …, a_K be iid copies of a(A_B) for an m′-row uniform design B. Then:

(i) E[φ(α(A))] ≤ E[φ((a₁ + ⋯ + a_K)/K)] for every convex φ. In particular exhaustion
E[(1−α)^T] ≤ Pr[a < Kx]^K + (1−x)^T.

(ii) Var α(A) ≤ Var(a)/K ≤ ᾱ(1−ᾱ)/K.

*Proof.* Hoeffding's (1963) representation applies. For a permutation π of the rows put
W_π = K⁻¹ Σ_{i≤K} a(A_{π(B_i)}), with B_i = {(i−1)m′ + 1, …, i·m′}. Averaging over π gives every m′-subset equal weight,
so α = avg_π W_π. Jensen gives φ(α) ≤ avg_π φ(W_π). Rows are iid, so each W_π has the law of (a₁ + ⋯ + a_K)/K.
For the tail: (Σ a_i)/K < x forces every a_i < Kx, and the a_i are independent. (ii) is (i) with φ(x) = x². ∎

**Consequences.**

* For m′ > m/2, K = 1, and the generic bound is no better than restarts on one fixed subset.
* Any further gain depends on the kernel. Row-local defects are amplified. Defects *inherited by every row restriction* are
  not. For example, a short (0, y) ∈ L₀(A) with Ay ≡ 0 lies in L₀(A_S) for all S, so α(A) = 0 whenever such a vector
  violates the height-zero floor.
* The variance factor 1/K would satisfy Proposition 7's requirement Var ≤ ᾱ²/800 only when ᾱ ≥ 1 − O(K/800). In that
  regime restarts are unnecessary.

### 3.3 Basis and symmetry randomization (same lattice)

**Proposition 4.**

(a) For signed permutation matrices P (rows) and S (secret coordinates), L₀(PAS) = diag(P, S⁻¹)·L₀(A), an isometry.
The CBD(3) product law is invariant under it. So the group Γ = B_m × B_n preserves the joint law of (A, X) and maps the
uniqueness criterion to itself.

(b) If R is Γ-equivariant in law, or first canonicalizes, then randomizing the input by Γ (or by any unimodular presentation
change) leaves α(A) unchanged. Canonicalizing means computing HNF in ambient coordinates; output then depends only on the
lattice (Part 24). A canonicalizing reducer with a deterministic tie rule has α(A) ∈ {0, 1}, so restarts give exactly zero
gain.

(c) For a general deterministic R composed with a uniform γ ∈ Γ, α(A) = |Γ|⁻¹ Σ_γ 1{R good on γA} is an orbit average.
E α = 1 − δ_R. If R's bad set is a union of Γ-orbits, then α ∈ {0, 1}. No generic concentration of α holds.

*Proof.* (a): x + PASy ≡ 0 ⇔ P⁻¹x + A(Sy) ≡ 0, and signed permutations are orthogonal and preserve iid symmetric
coordinates. (b): the law of R(γL₀) equals that of γR(L₀), and goodness is Γ-invariant by (a). The rest is immediate. ∎

So any restart gain from presentation randomness must come from the reducer's *non-equivariant sensitivity*. Proving it
needs reducer-specific dynamics. This is the regime where Parts 24, 106 and 113 found that reduction erases input randomness
and windows keep history dependence.

### 3.4 A-independent randomization is provably rare

If a trial's prefix plane is chosen independently of (A, X), its success probability is the fixed-plane probability. By
Part 40(iii) that is < 2^{−678.61} for every fixed rational plane at D = 406. By Part 45 it is < 9.03·10⁻⁸ for an A- and
plant-independent plane at 512. By a union bound over trials, Pr[attack succeeds] ≤ T·p. So such restarts need
T ≥ 0.99/p, which is ≥ 2^{678.6} at 406. The same holds for the independent pilot of Part 129E. Non-rare acceptance needs
an A-adaptive prefix, and adaptive prefixes have no exact law.

### 3.5 Re-selection inside the final window

**Lemma 5.** Let W be a lattice of rank ≥ 2 and K ⊂ W a primitive sublattice of rank j < rank W. Then

λ₁(π_{K⊥}W) ≤ λ_{j+1}(W).

For j = 1 and K = ℤv with v a shortest vector,

λ₁(π_{v⊥}W) ≥ √(λ₂(W)² − λ₁(W)²/4) ≥ (√3/2)·λ₂(W).

*Proof.* Upper bound: j + 1 independent vectors of length ≤ λ_{j+1} cannot all lie in span K, and the one outside projects to
a nonzero vector of no greater length.

Lower bound: a nonzero x̄ ∈ π_{v⊥}W has a lift x ∈ W, x ∉ ℝv, with |⟨x, v⟩|/|v| ≤ |v|/2 after adding a multiple of v.
Since x and v are independent, max(|x|, |v|) ≥ λ₂. If λ₁ < λ₂ this forces |x| ≥ λ₂; if λ₁ = λ₂, then |x| ≥ λ₁ = λ₂.
So |x̄|² = |x|² − ⟨x, v⟩²/|v|² ≥ λ₂² − λ₁²/4. ∎

(Checked numerically on 300 random rank-3 lattices with exact enumeration boxes; the two apparent violations were box
truncations and disappear at box radius 25.)

**Consequence.** Restarting only the terminal selection, by choosing any v in the final rank-β window W of L₀, can raise
the horizontal minimum by at most a factor 2/√3 over shortest-vector selection. It cannot accept at all unless
λ₂(W) > 27.4538 (at 506). Restart gains must come from changing W itself, that is, the rank-(1023 − β) prefix.

## 4. Moment methods for a lower bound on acceptance

### 4.1 First-moment certificates gain at most 100^{1/D} from restarts

**Proposition 6.** Suppose a certificate bounds the bad event Bad_ρ ⊆ {N_ρ ≥ 1} only through E N_ρ ≤ F(ρ), with
homogeneous scaling F(ρ) = F(ρ₀)(ρ/ρ₀)^D. This covers every count on record:

* Siegel or primitive-Siegel counts, D = rank;
* Part 105 flag counts, D = m;
* Part 101 dual counts, D ≈ 504;
* Part 115 flag counts in the ratio c, D = d.

A single 99% run certifies up to ρ₁ with F(ρ₁) = 0.01. A restart scheme with any number of trials, any independence, and
per-trial target 1 − 1/poly still needs F(ρ) < 1, since a first-moment bound ≥ 1 certifies nothing. Hence ρ_∞/ρ₁ ≤ 100^{1/D}.

| D | 100^{1/D} | (100·2^{40})^{1/D} |
|---:|---:|---:|
| 405 | 1.011436 | 1.083103 |
| 505 | 1.009161 | 1.066116 |

The last column is the gain even if each trial needed only failure ≤ 1 − 2^{−40} *and* that relaxation could somehow be
charged to the count. The gaps on record are far larger: factor 3.4 in radius (Part 101); 10^{45.2} in a rank-3 mean
(Part 126); a bad-flag count ≥ 1 on every design at the automatic cap (Part 116). **The 1/poly relaxation is worthless for
counting certificates.** Any gain from restarts must come from tools that *lower-bound* good events.

### 4.2 Second moment and Paley–Zygmund at instance level

**Proposition 7.** Let acc₁, acc₂ be two independent restarts on the same design, and ᾱ = E α(A).

(a) E[α²] = Pr[acc₁ ∧ acc₂]. Paley–Zygmund gives Pr[α > θᾱ] ≥ (1−θ)²ᾱ²/E[α²]. Without joint information, E α² ≤ ᾱ gives
only Pr[α > θᾱ] ≥ (1−θ)²ᾱ, which is useless when ᾱ is small. The 0/1 example is extremal.

(b) Var α = Pr[¬acc₁ ∧ ¬acc₂] − (1−ᾱ)². Chebyshev gives exhaustion ≤ 4 Var α/ᾱ² + (1 − ᾱ/2)^T. So exhaustion ≤ 0.01 follows
from Pr[¬acc₁ ∧ ¬acc₂] ≤ (1−ᾱ)² + ᾱ²/800 together with T ≥ (2 ln 200)/ᾱ ≈ 10.6/ᾱ.

(c) The requirement in (b) is an **upper bound on the joint failure** of two restarts on one design. Counting bounds it by
E_A[m(A)²], where m(A) = E[N | A] for a witness count N (Part 25's cross moment). By §4.1 that is informative only when
m(A) < 1 on most designs, i.e. in the 99% regime where restarts are not needed.

*Proof.* Identities: E[α²] = E[Pr[acc₁ | A] Pr[acc₂ | A]], and 1 − 2ᾱ + E α² = Pr[both fail]. The bound is Chebyshev on
{α < ᾱ/2} plus Theorem 2(1) with x = ᾱ/2. ∎

### 4.3 A positive template: reselect-by-certificate on a Haar window

Here PZ does work, because the variable is a count *inside one window* rather than a restart indicator.

**Theorem 8.** Let W be a Haar random unimodular lattice of rank b, with m = b − 1 ≥ 2. Fix ℓ > 0 and put
μ = V_b ℓ^b/(2ζ(b)), the mean number of primitive sign pairs with |v| ≤ ℓ. Consider the rule: list the primitive v ∈ W with
|v| ≤ ℓ, and accept the first whose quotient satisfies λ₁(π_{v⊥}W) ≥ c′·GH(π_{v⊥}W), where GH(π_{v⊥}W) = G_m|v|^{−1/m}.
Then

Pr[no v is accepted] ≤ 1/(1+μ) + μ c′^m/ζ(m),

and optimizing μ gives ≈ 2c′^{m/2}.

*Proof.* Let P be the oriented primitive count in the ℓ-ball and N the oriented count whose normalized quotient has
λ₁ < c′G_m. If P ≥ 1 and N = 0, some v is accepted. So Pr[fail] ≤ Pr[P = 0] + E N. Two Lean results bound these terms:

* By `primitiveBallPairs_hit_lower` (HaarMinimumLower.lean), a second-moment/PZ bound, Pr[P = 0] ≤ 1/(1+μ).
* By `part105` (TransverseMinimumBound.lean) with c = c′G_m, so that c^m V_m = c′^m, E N ≤ (V_bℓ^b/ζ(b))·c′^m/(2ζ(m))
  = μc′^m/ζ(m).

"Normalized" means scaled to unit covolume. Since det π_{v⊥}W = 1/|v|, the normalized test is exactly the own-GH test. ∎

| b | c′ | bound (optimized μ) | μ* | ℓ*/G_b |
|---:|---:|---:|---:|---:|
| 406 | 0.954 | 1.4443·10⁻⁴ | 1.4·10⁴ | 1.02556 |
| 506 | 0.925 | 5.647·10⁻⁹ | 3.5·10⁸ | 1.04110 |
| 506 | 0.954 | 1.3716·10⁻⁵ | 1.4·10⁵ | 1.02512 |
| 506 | 0.99 | 0.152 | 11 | 1.00617 |

**Physical scale at 506.** ℓ*G_b ≈ 5.62 < J₅₀₆ = √56.2142 ≈ 7.498, the Part 98 Hermite cap. Part 114's recurrence uses only
s_t ≤ J_b D_{t−1}^{1/b}. So in the Part 108 first-pass model its floor GH ≥ 28.8095 also holds for a reselected quotient,
and 0.954 × 28.8095 = 27.4843 > 27.4538 (Part 116). At 406 the first pass cannot reach the floor at all (Part 114: 15.50
< 24.58), so the template is moot there.

The bound is **instance-level** in the sense of §2. It is deterministic search inside one window, with no coin restarts and
no α(A). It uses only **unselected** window statistics: a lower tail of the primitive count and an unweighted bad-flag count.
On an actual Haar window it is unnecessary, since Part 105's shortest-vector result already gives 0.925 at 99.98%. Its value
is the shape of the remaining requirement.

**Mean-acceptance version under any window law ν.** Let G = P − N be the number of acceptable v. Cauchy–Schwarz on
{G > 0} gives ᾱ ≥ (E_ν P − E_ν N)₊² / E_ν[P²]. This needs only that bad candidates are not almost all candidates on
average, together with concentration of P. That is weaker than 99% control, but it is a *mean*, so §2 or §3.1 must still
be passed.

## 5. The exact remaining gap

All three forms concern the law of the BKZ / first-pass output on L₀(A) at width β, for the specified randomized,
plant-free reducer.

**Gap A (shared design, coin restarts).** Exhibit R with Pr_A[p_{0.002}(A) < x] ≤ 0.004 for some x ≥ 1/poly. Then T = O(1/x)
trials and Theorem 1 give 99%. Equivalent sufficient forms:

* E_A[1/α(A)] ≤ poly;
* Pr[two restarts on one design both fail] ≤ (1−ᾱ)² + ᾱ²/800.

**Gap B (K fresh row blocks).** On uniform designs with m/K rows, ᾱ = E_A p_{0.002}(A) ≥ 1 − (0.006)^{1/K}. With
θ_bad = 0.004 the exhaustion budget is 0.006, giving 0.923 at K = 2 and 0.818 at K = 3. This is a mean statement but
far from rare.

**Gap R (final-window statistics).** Let ν be the law of the final rank-β window W of L₀ under R, in own-determinant units.
Required:

Pr_ν[no primitive v ∈ W with |v| ≤ ℓ] + E_ν[N_{0.954}(W; ℓ)] ≤ 0.006,

where N_{0.954}(W; ℓ) counts oriented primitive v ∈ W with |v| ≤ ℓ and λ₁(π_{v⊥}W) < 0.954·GH(π_{v⊥}W), for some
ℓ ≤ J_β. By Theorem 8 this alone gives 99% at 506 with no restart. Compared with Part 118's obligation, the *terminal*
selection weight is gone, but W's law still carries every earlier selection (Part 122's diagnosis applies).

**Conjectures (labelled, unproved).**

* **Conjecture R.** E_ν[N_{0.954}] and Pr_ν[P = 0] exceed their Haar values by at most a factor 300 at β = 506. This would
  close Gap R, since 300 × 1.3716·10⁻⁵ < 0.0042.
  * Part 111 rules out a density version.
  * Part 124 found a benign GH-band rank-1 ratio (< 5.803) for restart columns. Rank-2 flags on the band are not covered.
* **Conjecture A (no evidence either way).** For BKZ with random unimodular input and random tie-breaks, failures are
  coin-driven: Var α(A) ≤ ᾱ²/800. A direct small-parameter test fits the Part 119/123 harness: pairs of independent restarts
  per design, estimating Pr[both fail] − (1−ᾱ)². Note Part 113's history persistence and Part 24's erasure of input
  randomization as reasons for caution.

## 6. What is rigorous

**Proved here.**

* Theorem 1: soundness without stopping bias; exact binomial completeness; restart form of the (1−δ)(1−ε) reduction.
* Theorem 2: two-sided exhaustion bounds, the Las Vegas form, and necessity.
* Theorem 3: convex-order amplification for row subsets.
* Proposition 4: symmetry and canonicalization barrier.
* §3.4: rarity of A-independent restarts, from the cited Parts 40 and 45.
* Lemma 5: λ₂ sandwich.
* Proposition 6: first-moment barrier.
* Proposition 7: PZ and Chebyshev criteria.
* Theorem 8: composed from two Lean-proved statements plus the union and lift arguments above.

All numbers are reproduced by §7.

**Not proved.** Any of Gaps A, B or R at β ≤ 506. The note establishes no new width. The frontier of Parts 131–132 (two
width-646 calls) is unchanged.

**Lean candidates (straightforward).**

* The stopping-time lemma and the identity in Theorem 1(a)–(c) over finite probability spaces.
* Theorem 2(1)–(2).
* Lemma 5.
* Theorem 8, as a corollary of `primitiveBallPairs_hit_lower` and `part105`.

## 7. Reproduction

```python
from mpmath import mp, mpf, zeta, pi, gamma, binomial, fsum, sqrt
mp.dps = 40
for D in (405, 505):
    print(D, mpf(100)**(mpf(1)/D), (100*mpf(2)**40)**(mpf(1)/D))
for K in range(2, 6):
    print(K, 1 - mpf('0.01')**(mpf(1)/K), 1 - mpf('0.006')**(mpf(1)/K))
for b in (406, 506):
    m = b - 1
    for c in ('0.925', '0.954', '0.99'):
        kap = mpf(c)**m / zeta(m)
        val, mu = min((1/(1+mu) + mu*kap, mu) for mu in [mpf(10)**(j/mpf(20)) for j in range(400)])
        print(b, c, val, mu, (2*mu*zeta(b))**(mpf(1)/b))   # last: ell/G_b
    V = pi**(mpf(b)/2)/gamma(1+mpf(b)/2); G = V**(-mpf(1)/b)
    print('G_b', G)
print('J506', sqrt(mpf('56.2142')), '0.954*28.8095', mpf('0.954')*mpf('28.8095'))
cdf = lambda M, p, k: fsum(binomial(M, i)*p**i*(1-p)**(M-i) for i in range(k+1))
print('B', cdf(100000, mpf('0.004'), 290), "eps'", 1 - cdf(100000, mpf('0.002'), 290))
```

Output checked: 1.011436/1.083103 (D = 405), 1.009161/1.066116 (D = 505); 0.9, 0.78456, 0.68377, 0.60189; Theorem 8 rows
as tabulated; G₅₀₆ = 5.48279, J₅₀₆ = 7.49761, 0.954 × 28.8095 = 27.4843; B = 4.1993·10⁻⁹, ε′ = 9.4037·10⁻¹⁰.

## Audit

**Verdict: MINOR CAVEATS, with one substantive correction (Gap R and the "physical scale" paragraph of §4.3).** Every
labelled theorem, proposition and lemma (Theorems 1–3 and 8, Propositions 4, 6 and 7, Lemma 5, §3.4) is correct as a
mathematical statement. One interpretive claim is false: Gap R is **not** sufficient for 99%. The 0.954·GH test meets only
the *necessary* height-zero floor. Conjectures R and A are correctly labelled as unproved. All numbers were recomputed
independently with mpmath (exact regularized incomplete beta for the binomial tails, closed-form optimum for Theorem 8).

**Checked and correct.**

* **Theorem 1.** The stopping-time argument holds. {N_run ≥ t} is determined by (A, ω_{<t}, X′_{<t}). bad_t is determined by
  (D_t, ω_t). Trial t's fake plants are fresh, so Pr[accept_t | past, D_t, ω_t] = Pr[Bin(M, 1−G_t) ≤ k]. The true X is
  independent of (A, ω, X′), so conditional failure at the selected index is 1 − G_{t*}. There is no stopping-time bias.
  (b) holds because the acceptance indicators are conditionally iid given A. (c) holds because accept_t depends only on
  (A_{B_t}, ω_t, X′_t), which are independent across disjoint row blocks. Recomputed exactly: B = 4.19932·10⁻⁹ and
  ε′ = 9.40370·10⁻¹⁰. The restart form also holds: δ_T is decreasing in T, δ_1 ≤ δ_{θ_good} + ε′, and
  δ_T → Pr_A[p_{θ_good} = 0].
* **Theorem 2.** (1) follows by splitting on {α < x}. (2): (1−α)^{−T} ≥ (1 + α/(1−α))^T ≥ 1 + Tα. (3) is convexity.
  (4): ln 2/(−ln(1−x)) ≥ (ln 2)(1−x)/x because −ln(1−x) ≤ x/(1−x). All four are correct.
* **Theorem 3.** The Hoeffding permutation representation is valid even when m′ does not divide m. For fixed π the K
  disjoint blocks are iid, Jensen applies to φ(y) = (1−y)^T and to φ(y) = y², and {ā < x} ⊆ ∩{a_i < Kx}.
* **Proposition 4(a).** (x, y) ∈ L₀(PAS) ⇔ (P⁻¹x, Sy) ∈ L₀(A). The plant maps to (Pe, S⁻¹s), whose CBD product law is
  invariant.
* **§3.4.** 0.99·2^{678.61} = 2^{678.596}. Part 40(iii) and Part 45 are cited as stated in PROOF_GAP. The union bound over
  trials is valid because each trial's real outcome has the fixed-plane law.
* **Lemma 5.** Both bounds and both proofs are correct. In particular, independence of x and v gives
  max(|x|, |v|) ≥ λ₂, and the case split handles λ₁ = λ₂. The resulting ratio is 2/√3 = 1.1547.
* **Proposition 6.** Recomputed: 1.011436 / 1.083103 at D = 405 and 1.009161 / 1.066116 at D = 505.
* **Proposition 7.** The identities E α² = Pr[acc₁ ∧ acc₂] and Var α = Pr[both fail] − (1−ᾱ)² are correct. Chebyshev on
  {α < ᾱ/2} plus Theorem 2(1) gives 4Var/ᾱ² + (1−ᾱ/2)^T. With Var ≤ ᾱ²/800 and T ≥ 2 ln 200/ᾱ = 10.597/ᾱ this totals
  ≤ 0.01.
* **Theorem 8, check against the Lean statements.**
  * `primitiveBallPairs_hit_lower` (HaarMinimumLower.lean:507) states m/(1+m) ≤ Pr[primitiveBallPairs r > 0]. Here
    m = vol(B_r)/(2Σ_k (k+1)^{−n}) = V_n rⁿ/(2ζ(n)), for an **open** ball and n > 2. This gives Pr[P = 0] ≤ 1/(1+μ).
  * `part105` (TransverseMinimumBound.lean:88) bounds the normalized oriented count over ContentFiber (m+1) 1 (both signs)
    for a **closed** ball of radius ℓ and the **strict** test ‖|x|^{1/m}·y‖ < c on the physical projected lattice. That is
    unit-covolume scaling, since det π_{x⊥}W = 1/|x|. The bound is (ℓ^{m+1}V_{m+1}/ζ(m+1))·(c^m V_m/(2ζ(m))).
  * With c = c′G_m this equals μc′^m/ζ(m), as the note says.
  * The open/closed mismatch is harmless: P_open ≥ 1 implies P_closed ≥ 1, and the union bound uses the closed-ball N.
  * Both results quantify over the same fundamental domain D, with 2 ≤ m.
* **Theorem 8, numbers.** The exact optimum is 2√κ − κ, with κ = c′^m/ζ(m).
  * At 506 / 0.954 this gives 1.37086·10⁻⁵. The note's grid value 1.3716·10⁻⁵ is a valid, slightly weaker upper bound.
  * The other rows are 1.44398·10⁻⁴ (406/0.954), 5.647·10⁻⁹ (506/0.925) and 0.151846 (506/0.99).
  * Supporting values: G₅₀₆ = 5.482791, ℓ* = 5.6205 < J₅₀₆ = 7.497613, and 0.954 × 28.8095 = 27.484263.
  * Mean-acceptance version: Cauchy–Schwarz with 0 ≤ G ≤ P is correct.
* **Gap B thresholds.** 1 − 0.006^{1/2} = 0.92254 and 1 − 0.006^{1/3} = 0.81829 confirm 0.923 and 0.818.
  The §3.1 table (0.9, 0.78456, 0.68377, 0.60189) is also correct.
* **Conjecture R.** 300 × 1.3716·10⁻⁵ = 4.115·10⁻³ < 0.0042.

**Issues and corrections.**

1. **(Substantive) Gap R and §4.3 "Physical scale" overstate sufficiency.** 27.4538 is Part 103's *necessary* Cantelli
   floor, √(1 + 1.5d − √(4.5d/99)). Part 114 says explicitly that the 0.954 ratio meets the *necessary* floor.
   * Clearing it does not give 99% conditional success. The certified λ₁(H) ≥ 27.4843 is *below* the mean plant-image norm
     √(1 + 1.5·505) = 27.5409.
   * With Var ‖πu‖² ≈ 4.5d, a normal approximation gives height-zero success only ≈ 47% at that floor. The 99% quantile of
     the plant norm is ≈ 29.49 (normal approximation); the Cantelli-sufficient value is 35.11.
   * Heights ≥ 1 are also uncovered (Part 94 conditions, Part 102), and so is the Babai-lift prefix floor (Part 47).
   * **Correction:** delete "By Theorem 8 this alone gives 99% at 506 with no restart." Restate Gap R as a necessary-side
     window statistic, or replace 0.954 by a ratio whose physical floor is a *sufficient* certificate at every height. For
     example, Part 94's T(R) with a norm cap, or Part 102 plus a height-≥2 and lift condition, giving θ_bad ≤ 0.004.
   * Verdict item 5 should then list Gap R as incomplete. Conjecture R would close only this necessary-side statement.
2. **Wrong citation for 27.4538.** The note credits Part 116 in §3.5 and §4.3. The floor is Part 103's (used in
   Parts 114 and 130).
3. **Remark after Theorem 1.** Part 102's λ₁(H) ≥ 61.3 is a **height-one** condition (failure < 0.00207). It is not a full
   plant-free success certificate. Part 47 notes that λ₁ > 2‖πu‖ fails at height 2. Only Part 94's T(R) ≈ R² with a norm
   cap, plus the lift term, serves as a complete deterministic C.
4. **Verdict item 3, Theorem 3 wording.** "At most K-fold amplification" inverts the direction. Theorem 3 is an *upper*
   bound on exhaustion, i.e. a guaranteed minimum gain, not a cap on the gain. U-statistic averaging can concentrate α far
   more than K blocks when the first Hoeffding projection is small. The body ("generic bound", "further gain depends on the
   kernel") is correct; the summary line should say "at least the K-block gain, generically no more is guaranteed."
5. **Inconsistent budgets.**
   * Verdict item 2 quotes ᾱ ≥ 0.785–0.9 (0.01 budget). Gap B correctly uses 0.006 (0.818–0.923) after θ_bad = 0.004.
   * Proposition 7's ᾱ²/800 criterion spends the full 0.01 on exhaustion, yet Gap A lists it as sufficient alongside
     θ_bad = 0.004. Within a 0.006 budget it should read Var α ≤ ᾱ²/1334 with T ≥ 2 ln(333.3)/ᾱ ≈ 11.62/ᾱ.
   * Gap A's "equivalent sufficient forms" are sufficient, not equivalent.
6. **Proposition 4(b).** Two small inaccuracies:
   * A deterministic canonicalizing reducer has p_θ(A) ∈ {0, 1}. α(A) still carries certificate noise, so α ∈ [0, ε′] ∪
     [1−ε′−B, 1] rather than {0, 1}.
   * "Γ-equivariant, or first canonicalizes … randomizing by Γ (or by any unimodular presentation change)" pairs the
     hypotheses loosely. Canonicalization kills *basis* randomization of the same lattice. Γ moves the lattice, and HNF is not
     Γ-equivariant, so killing Γ-randomization needs equivariance.
7. **§3.1 count.** Signed subset sums of old rows have up to 3^{511} ≈ 2^{809.9} coefficient patterns, not 2^{511}. The
   conclusion is unaffected (≪ q^{512} ≈ 2^{5988}).
8. **Restart form.** "δ = 1 − E p_ε" should be δ_{θ_good}. Compared with the Lean (1−δ)(1−ε) bound, the certificate costs
   θ_bad − θ_good extra.
   * "Restarts never hurt" holds for the δ_T term only. B·E[N_run] grows linearly in T when Pr[α = 0] > 0, so T must stay
     ≪ 1/B ≈ 2.4·10⁸.
   * Each trial costs M = 10⁵ (≈ 2^{16.6}) extra rank-β SVP calls. Cost is not optimized here.
9. **Minor.** Part 105 gives 0.925 at > 99.9937% at 506 (the note's "99.98%" is the 406 value). The Theorem 8 table's μ*
   and ℓ*/G_b values are grid optima: 1.025181 exact vs 1.02512 at 506/0.954. This is immaterial.

No attack parameters were searched or optimized during this audit.
