# Discrete-Gaussian SVP (ADRS15 / ASD18) with every constant explicit

Research note, 2026-11-22. Mathematics and arithmetic only. No Lean or Python in the repository is touched; the
numbers in §5 come from a scratch `mpmath` script (60 digits), not committed.

**Task.** [wall1_provable_cost.md](wall1_provable_cost.md) (Part 133) found that no published theorem gives a
number at D = 647 for the 2^{n+o(n)} discrete-Gaussian SVP algorithm of Aggarwal–Dadush–Regev–Stephens-Davidowitz
[ADRS15] and Aggarwal–Stephens-Davidowitz [ASD18]. The only fully explicit rigorous bound was brute force,
2^{1234.3955}·2^{19} = 2^{1253.40} operations. This note re-proves the ASD18 algorithm with every factor tracked.
It evaluates the result at the recorded Part 39 instance (D = 647, and D = 646 × 2 for Part 131), with entry bound
B = q = 3329. Instance parameters are not re-optimized.

Convention, as in Part 133: "bits" means log₂. "Explicit" means every constant is a number. No O, o, Ω, Θ or Õ
appears in Theorem E or in its proof.

## 0. Verdict

1. **Explicit theorem (Theorem E, §3).** Let L ⊆ Z^d have rank n ≥ 2 and a basis with integer entries of absolute
   value ≤ B. A no-rejection pair-and-average algorithm (ASD18 Procedure 3, modified as in §2) outputs a shortest
   nonzero vector of L with failure probability ≤ p(n, B). It uses ≤ T(n, B) operations, where T and p are the
   closed-form expressions (3.1)–(3.2). The list size per run is Λ₀ = 2^n·A·8^{ℓ−1} ≤ 2^n·A·Q⁶, with
   ℓ = ⌈2 log₂ Q⌉, A = 400.25 and Q = c_n·√(nd)·B·√(ln(2n+4)/(2π)) for n ≥ 8, where c_n ≈ 0.42.
2. **At the Part 39 instance** (n = d = 647, B = 3329): ℓ = 40 combiner steps and an initial list of
   M₀ = 2^{772.65} vectors per run, 4 runs. **T(647) = 2^{799.23} operations**, space 2^{781.98} words, and
   **p ≤ 2^{−120.9}**. For Part 131 (two calls at n = 646), the total is 2·2^{798.22} = 2^{799.22}.
3. **This beats the explicit brute-force baseline 2^{1253.40} by about 454 bits.** It is also below
   Micciancio–Voulgaris 2^{1294}·D^c by more than 490 bits. Combined with Part 39, the rigorous end-to-end
   statement is: plain LWE (511, 512, 3329) with CBD(3) is solved with probability ≥ 99.51664% − 2^{−120} in
   ≤ 2^{799.23} operations. The cost model is stated in §1, and one flagged gap (G1) concerns the initial sampler.
4. **What changed relative to the published proofs** (§6). Three published ingredients have no constants, and each
   is replaced by an explicit one:
   * The square sampler (ADRS15 Thm 3.3; ASD18 Thm A.3), with a loss of 32κ per step and failure
     C₁MN log N·e^{−C₂κ} with unknown C₁, C₂, becomes a new analysis-only coupling lemma (Lemma 4.3). It loses a
     factor 8 per step, and its failure is an explicit Poisson tail.
   * The Kabatiansky–Levenshtein kissing bound behind "1.38^{−n−o(n)}" (ADRS15 Lemma 4.1 / Prop 4.3; ASD18
     Prop A.7) becomes Banaszczyk's explicit tail bound, applied after a telescoping cancellation (Lemma 4.6). The
     result is stronger as well as explicit.
   * The 2^{O(u)} Schnorr/AKS sublattice step (ASD18 Thm C.1, Prop C.3, Cor C.4) is dropped. The cost is a
     poly(B) factor in the list size.

   I found one genuine gap in ASD18's stated proof, its domination calculus (§6, item A1). It does not affect
   their theorem, because their Thm D.1 can be re-proved by the coupling in Lemma 4.5.
5. **Remaining honest gaps** (§7): (G1) a real-RAM model is used for the exact initial sampler; a bit-complexity
   version is sketched at about +15 to +21 bits, not proved. (G2) Lemma 4.3 and Lemma 4.5 are new here and have not
   been independently audited. (G3) Banaszczyk's two lemmas are cited, not re-proved; both rest on Poisson summation.

## 1. Setting, notation, cost model

* L = L(b₁,…,b_n) ⊆ Z^d, rank n, |b_{ij}| ≤ B. λ₁ = λ₁(L). Since L is integral, **1 ≤ λ₁ ≤ min_i‖b_i‖ ≤ √d·B**.
  N₁ := #{y ∈ L : ‖y‖ = λ₁} ≥ 2.
* ρ_s(x) = exp(−π‖x‖²/s²) and ρ_s(S) = Σ_{x∈S} ρ_s(x). D_{L,s} is the discrete Gaussian on L. The 2^n cosets of 2L
  in L are written c ∈ L/2L. The coset law of D_{L,s} is p_c(s) = ρ_s(2L+c)/ρ_s(L).
* ψ(j) := ρ_{s₀2^{−j/2}}(L) for a run started at parameter s₀, with s_j := s₀2^{−j/2}.
* **Cost model.** The list phase (the 2^{n+…}-sized part) uses only integer vectors in Z^d and is counted in word
  operations. Coordinates stay below 2^{23} at the instance, so norms² fit in 64 bits (§5). The initial sampler
  (§4.8) is counted in a real-RAM model: unit cost for +, −, ×, ÷ and comparisons on reals, for one evaluation of
  erf, exp or a one-dimensional theta sum ρ_r(αZ + β), for one draw from a truncated continuous normal, and for
  one coin with a real bias. This is the model in which BLP13 Lemma 2.3 is "exact". See gap G1.

## 2. The algorithm (ASD18 Procedure 3, made explicit)

Fixed analysis constants: **θ = 1/8, k = 4, K₀ = 800, A := 4θ(K₀ + ½) = 400.25.** These are constants of the proof,
not instance parameters. They are fixed once and not tuned per instance.

Derived quantities, all explicit in (n, d, B):

* c_n := (1 + √(2 ln 2 / n))/√(2π) and γ := 2^{1/(2k)} = 2^{1/8}.
* s_* := √d·B·max{ √(ln(2n+4)/π), √2/(c_n√n) }. The first term is the larger one for n ≥ 8.
* Q := c_n·√(n/2)·s_*, ℓ := ⌈2 log₂ Q⌉, Λ₀ := 2^n·A·θ^{−(ℓ−1)} and M₀ := ⌈(1 + 2^{−10})·Λ₀⌉.

**Procedure E.** Input: the basis.
1. Compute the Gram–Schmidt vectors b̃_i.
2. For r = 0, 1, …, k−1 (k runs):
   1. Draw M₀ independent exact samples from D_{L, s_*γ^r} with the BLP13 sampler (§4.8). Keep each sample
      together with its integer coefficient vector z (y = Σ z_i b_i), which the sampler produces anyway.
   2. Repeat ℓ times: apply Pair-and-Average (ASD18 Procedure 1) to the current list. Bucket by the coset label
      z mod 2 with a *stable* radix sort on the label only. Inside each bucket, pair consecutive elements in list
      order, and append the averages (y₁+y₂)/2, (z₁+z₂)/2 in bucket order.
   3. After each step (and before the first), record the shortest nonzero vector in the list.
3. Output the shortest recorded vector over all runs and steps.

**Implementation constraint (needed by the proof).** The pairing inside a coset must not depend on the vectors'
values: it may depend only on coset labels, list positions and independent coins. A pairing that, for example,
sorts by norm inside a bucket destroys the "mixture of Gaussians" structure (ASD18 Def 3.2), and the proof below
no longer applies. ASD18 leaves this implicit ("for each unpaired vector X_i").

*Simplification for the instance.* If det L is odd, then L/2L → Z^d/2Z^d (y ↦ y mod 2) is a bijection, so coset
labels are the coordinate parities and z need not be stored. Proof: y = 2w ∈ L with w ∈ Z^d gives det·w ∈ L and
2w ∈ L, so w ∈ L. The Part 39 embedding lattice has det = 3329^{134}, which is odd.

## 3. Main theorem

**Theorem E.** Let n ≥ 2 and let L ⊆ Z^d be a rank-n lattice given by a basis with integer entries of absolute
value ≤ B. Procedure E, with the constants of §2, uses at most

  (3.1) T(n,d,B) = k·M₀·[ 2e²(4nd + 32n) + 2(10d + 2⌈d/16⌉) ] + k(ℓ+1)·⌈d/16⌉·2^{17} + 2n²d

operations (§1 cost model; with aborts on the running-time caps of §4.8, this is a worst-case bound). It
outputs a vector of norm λ₁(L), except with probability at most

  (3.2) p(n,d,B) = ℓ·Λ₀·[ e^{3/2}(e/16)^{K₀−1}/K₀ + e²(e/4)^{2K₀−1}/(2K₀) ]
        + exp( −Aθ·2^{n/2}·exp(−γ²(√n + √(2 ln 2))²/4) )
        + exp( −Λ₀·h(1 + 2^{−10}) ) + k·[ e^{−M₀/4} + e^{−M₀/2} ],

where h(x) = x ln x − x + 1. The four lines are, in order: combiner failures (Lemma 4.3), the final hit
(Lemma 4.6), Poissonization (Lemma 4.5) and the running-time caps (§4.8). Space is M₀·d words plus O(d²).

Here e/16 = 4eθ² and e/4 = 2eθ at θ = 1/8. For general θ < 1/(2e), replace 8^{ℓ−1}, e/16 and e/4 by θ^{−(ℓ−1)},
4eθ² and 2eθ. The proof assembles §4 and is given in §4.9.

## 4. Ingredients and proofs

### 4.1 Exact Gaussian identities (verified in ASD18; no constants)

* **(I1) ASD18 Lemma 2.1** (from [ADS15]): Σ_{c∈L/2L} ρ_s(2L+c−t)² = ρ_{s/√2}(L)·ρ_{s/√2}(L−t). At t = 0:
  Σ_c p_c(s)² = ψ(1)²/ψ(0)², with ψ relative to s.
* **(I2) ASD18 Lemma 3.1 and Corollary 3.3 items 2 and 4.** If X₁, X₂ are independent with law D_{2L+c,s}, then
  conditional on (X₁+X₂)/2 ∈ 2L + d, the average has law D_{2L+d, s/√2}. If the common coset c is drawn with
  probability ∝ ρ_s(2L+c)², the average has law exactly D_{L,s/√2}. (Both proofs are three-line computations
  from the parallelogram identity ρ_s(x)ρ_s(y) = ρ_{√2s}(x+y)ρ_{√2s}(x−y), ASD18 eq. (1).)
* **(I3) Central coset is heaviest:** ρ_s(2L+c) ≤ ρ_s(2L), so p_max(s) = p_{2L}(s) = ρ_{s/2}(L)/ρ_s(L). This
  follows from Poisson summation, as stated in ADRS15 §2.2 ("the zero coset has maximal weight", citing [Ban93]).
* **(I4) Banaszczyk scaling** (ADRS15 Lemma 2.3 = [Ban93, Lemma 1.4]; ASD18 Lemma A.5): ρ_{as}(L) ≤ a^n ρ_s(L)
  for a ≥ 1. In particular ψ(j)/ψ(j+1) ≤ 2^{n/2}.
* **(I5) Banaszczyk tail** (ADRS15 Lemma 2.4, from [DRS14, Lemma 2.13], specialized to u = 0): for t ≥ 1/√(2π),
  Pr_{X∼D_{L,s}}[‖X‖ > t s√n] < C(t)^n, where C(t) := t√(2πe)·e^{−πt²}.

### 4.2 Poisson facts (elementary, explicit)

* **(P1)** (ADRS15 Lemma 2.22.) If R ∼ Pois(Λ) and X₁,…,X_R are iid with coset law p, the coset counts N_c are
  independent Pois(Λp_c). Conversely, independent K_c ∼ Pois(μ q_c) with Σq_c = 1 are a Pois(μ)-sized iid
  q-sample.
* **(P2)** Pr[Pois(b) ≥ k] ≤ b^k/k!, because k! ≥ j!(k−j)! termwise.
* **(P3)** Chernoff bounds: Pr[Pois(Λ) > xΛ] ≤ e^{−Λh(x)} for x > 1, and Pr[Bin(t, q) ≤ tq/2] ≤ e^{−tq/8}.

### 4.3 The step lemma (new; replaces ADRS15 Thm 3.3 / Prop 3.5 and ASD18 Thm A.3 / Thm B.1)

**Lemma 4.3a (likelihood-ratio coupling).** Let 0 < a ≤ A, θ > 0, b := θa²/A, N ∼ Pois(a), N' := ⌊N/2⌋,
K ∼ Pois(b), and m := ⌊A/(4θ) − ½⌋ ≥ 1. Then there is a coupling of (N, K) with
Pr[K > N'] ≤ Pr[K > m] + Pr[N' > m].

*Proof.* We have P[N' = j] = e^{−a}(a^{2j}/(2j)!)(1 + a/(2j+1)). Let R_j := P[K=j]/P[N'=j]. A direct computation
gives

  R_{j+1}/R_j = (2b/a²)·(2j+3)·(2j+1+a)/(2j+3+a) ≤ 2b(2j+3)/a² = 2θ(2j+3)/A,

which is ≤ 1 for j ≤ m−1, because 2θ(2m+1) ≤ A. So R is nonincreasing on {0,…,m}. Likelihood-ratio order implies
the usual stochastic order, so law(K | K ≤ m) ≤_st law(N' | N' ≤ m). Couple those two conditional laws
comonotonically (Y ≤ Z). Then set K := Y with probability 1 − P[K > m], and otherwise draw K from law(K | K > m).
Set N' := Z with probability 1 − P[N' > m], and otherwise draw N' from law(N' | N' > m). Finally draw N given N'
(N ∈ {2N', 2N'+1} with the right odds). The marginals are exact, and K > N' requires one of the two "otherwise"
branches. ∎ (Numerically checked for A ∈ {50, 400.25} and a from 10⁻³ to A: the ratio R is monotone on {0..m},
and the comonotone failure is 0 to 80 digits.)

**Lemma 4.3b (one combiner step).** Suppose the list is Pois(Λ)-many iid samples of D_{L,s}. Put
p_c := p_c(s), A_s := Λ·p_max and a_c := Λp_c ≤ A_s. Inside each coset independently, apply the kernel of Lemma
4.3a (with a = a_c, A = A_s) to N_c. This yields K_c; select K_c disjoint pairs from coset c, or ⌊N_c/2⌋ pairs if
K_c > ⌊N_c/2⌋ ("failure in c"). Then:

1. The selection depends only on coset counts and independent coins.
2. Outside a failure event of probability ε ≤ Σ_c (P[Pois(b_c) > m] + P[Pois(a_c) ≥ 2m+2]), the averages of the
   selected pairs are exactly a Pois(Λ')-sized iid D_{L,s/√2} list, with

   Λ' = Σ_c θa_c²/A_s = θΛ·p_col/p_max = θΛ·ψ(1)²/(ψ(0)ψ(2))   (by I1 and I3).
3. With K := m+1 ≥ A_s/(4θ) − ½, we have ε ≤ Λ'·g₁(K) + Λ·g₂(K), where
   g₁(K) ≤ e^{3/2}(4eθ²)^{K−1}/K and g₂(K) ≤ e²(2eθ)^{2K−1}/(2K).

*Proof.*
* (1) is by construction.
* (2): the K_c are independent Pois(b_c), where b_c = θΛp_c²/p_max (P1 and Lemma 4.3a). The vectors in a coset are
  iid D_{2L+c,s} given all counts and coins. So on the no-failure event, the selected pairs are distributed as in
  the "ideal" process: Pois(Σb_c) pairs with coset law ∝ p_c², fed with fresh Gaussians. By I2, item 4, their
  averages are iid D_{L,s/√2}. The failure bound is a union bound over cosets using Lemma 4.3a.
* (3): by P2, using b_c ≤ θA_s and a_c ≤ A_s:
  * P[Pois(b_c) ≥ K] ≤ b_c(θA_s)^{K−1}/K!;
  * P[Pois(a_c) ≥ 2K] ≤ a_c A_s^{2K−1}/(2K)!.

  Sum over c (Σb_c = Λ', Σa_c = Λ). Then use k! ≥ (k/e)^k, A_s < 4θ(K+½) and (1 + 1/(2K))^{2K} ≤ e. ∎

Both g-bounds decrease in K, so A_s ≥ A = 4θ(K₀+½) gives K ≥ K₀ + 1 and lets us evaluate them at K₀. Also
Λ' ≤ θΛ ≤ Λ, because p_col ≤ p_max.

*Comparison with ADRS15.* Their combiner keeps a fraction p_col/(32κ·p_max) per step, with κ = Θ(n) for a
2^{−Ω(n)} error. At n = 647 that would be 2^{−14.3} per step. Here the fraction is θ·p_col/p_max = 2^{−3}·p_col/p_max.
No p_max estimation (ADRS15 Prop 3.1) is needed, because the selection exists only in the analysis: it may use
the true p_c. The algorithm that actually runs never rejects anything (Lemma 4.5).

### 4.4 Telescoping over ℓ steps

Iterating Lemma 4.3b from Λ₀ gives, on the no-failure event, a Pois(Λ_j)-sized iid D_{L,s_j} list after j steps,
with

  Λ_j = Λ₀θ^j·ψ(1)ψ(j)/(ψ(0)ψ(j+1)),   A_{s_j} = Λ_j·ψ(j+2)/ψ(j) = Λ₀θ^j·ψ(1)ψ(j+2)/(ψ(0)ψ(j+1)) ≥ Λ₀θ^j 2^{−n}

(by I4). So Λ₀ = 2^n·A·θ^{−(ℓ−1)} gives A_{s_i} ≥ A for every i ≤ ℓ−1. The total combiner failure up to step ℓ
is at most ℓ·Λ₀·(g₁(K₀) + g₂(K₀)), which is the first line of (3.2). Compare ASD18 Cor B.2, where the hypothesis
M ≥ (10κ)^{2ℓ}·ρ/max ρ and the factor (32κ)^ℓ give the 2^{Θ(log² n)}.

### 4.5 No rejection is at least as good (replaces ASD18 Thm 3.4 and Cor 3.3 item 3)

**Lemma 4.5.** Fix a run. There is a coupling of Procedure E's lists with the analysis process (Poissonized input
plus the selections of Lemma 4.3b) such that, at every step, the analysis list is a sub-multiset of Procedure E's
list, except on the event R > M₀. Here R ∼ Pois(Λ₀) and Pr[R > M₀] ≤ e^{−Λ₀h(1+2^{−10})} (P3).

*Proof.*
* Step 0: the analysis list is the first R of the M₀ samples.
* Inductive step: Procedure E pairs maximally inside each coset (⌊N_c/2⌋ pairs). Run it with a pairing that first
  takes the analysis process's selected pairs and then pairs the remainder. This is a maximal pairing, it contains
  the analysis pairs, and it depends only on coset labels, list membership and coins. Call that information H.
* This modified pairing has the same law as the canonical one. Given H, the vectors are independent with law
  D_{2L+c,s} on their cosets. This is ASD18 Lemma 3.1 in its conditional form, applied inductively, because H
  never contains vector values. So every H-measurable maximal pairing produces the same conditional law of output
  cosets and values: each pair from coset c independently yields an average with the Lemma 3.1 law, and the
  number of pairs per coset is ⌊N_c/2⌋ regardless of which pairs are formed.
* By induction, Procedure E's sequence of lists has the same law under either pairing, and under the modified one
  it contains the analysis lists. ∎

If a list contains a vector of norm λ₁, then the minimum over any superset is λ₁. So
Pr[E finds a λ₁-vector] ≥ Pr[analysis list finds one] − Pr[R > M₀].

### 4.6 Final hit (replaces ADRS15 Lemma 4.1, Prop 4.3, Thm 4.4 and ASD18 Prop A.7, Cor A.8)

**Lemma 4.6.** Let c > 1/√(2π) and n ≥ 1, and suppose σ := s_j/√2 satisfies σ ≤ λ₁/(c√n). Then

  ρ_σ(L) ≤ 1/(1 − C(c)^n),   and   Λ_j·P_{D_{L,s_j}}[‖X‖ = λ₁] ≥ Λ₀θ^j·2^{−n/2}·2(1 − C(c)^n)·e^{−πλ₁²/s_j²}.

*Proof.*
* Since cσ√n ≤ λ₁, we have L∖{0} ⊆ {‖x‖ ≥ cσ√n}. Applying I5 with t' ↑ c, by continuity of C, gives
  ρ_σ(L∖0) ≤ C(c)^n ρ_σ(L), and then ρ_σ(L) ≤ 1/(1−C^n).
* The hit probability is N₁e^{−πλ₁²/s_j²}/ψ(j). Multiply by Λ_j from §4.4. The ψ(j) cancels, leaving
  Λ₀θ^j(ψ(1)/ψ(0))·N₁e^{−πλ₁²/s_j²}/ψ(j+1), with ψ(j+1) = ρ_σ(L).
* Use ψ(1)/ψ(0) ≥ 2^{−n/2} (I4), N₁ ≥ 2 and ρ_σ(L) ≤ 1/(1−C^n). ∎

**Choice of c.** Let φ(c) := ln C(c). Then φ(1/√(2π)) = 0, φ'(1/√(2π)) = 0 and φ'' = −1/c² − 2π ≤ −2π, so
φ(c) ≤ −π(c − 1/√(2π))². With c = c_n we get C(c_n)^n ≤ ½. (At n = 647 the actual value is 2^{−1.97}.) Since
πc_n²/2 = (1 + √(2 ln 2/n))²/4, a parameter σ ∈ [σ*/γ, σ*] with σ* := λ₁/(c_n√n) gives

  e^{−πλ₁²/s_j²} = e^{−πλ₁²/(2σ²)} ≥ exp(−γ²(√n + √(2 ln 2))²/4).

The number of hits in the final list is exactly Poisson, so Pr[no hit] = exp(−Λ_j P_hit). With θ^j ≥ θ^ℓ and
Λ₀θ^ℓ = 2^nAθ, this gives the second line of (3.2).

*Why this beats ADRS15 Prop 4.3, not only by being explicit.* ADRS bound the hit probability at s_ℓ by
e^{−π/s²}/ρ_s(L), and control ρ_s(L) = 2^{o(n)} by the kissing number. In the telescoped product, ψ(ℓ) cancels, and
only ψ(ℓ+1) = ρ_{s/√2}(L) remains. At s/√2 ≤ λ₁/(c√n), Banaszczyk alone bounds it by 2. The resulting margin is
2^{n(1/2 − γ²(1+…)²/(4 ln 2))}, about 2^{0.139n} at γ = 1. ADRS's margin is (√2/1.38)^n·2^{−o(n)} ≈ 2^{0.035n−o(n)}
(§6, A4).

### 4.7 Grid lemma (replaces ASD18's LLL estimate and 200n radii)

Run r, step j uses σ_{r,j} = s_*γ^r 2^{−j/2}/√2 = σ_top·γ^{−t}, where σ_top := s_*γ^{k−1}/√2,
t = kj + (k−1−r) and t ranges over 0, …, k(ℓ+1) − 1. Two facts hold:
* σ_top ≥ s_*/√2 ≥ √dB/(c_n√n) ≥ σ*. This is the reason for the second term in s_*.
* σ_top·γ^{−(k(ℓ+1)−1)} ≤ (s_*/√2)·2^{−ℓ/2} ≤ 1/(c_n√n) ≤ σ*, using ℓ ≥ 2 log₂ Q, where Q = c_n√n·s_*/√2. The
  bound λ₁ ≥ 1 gives σ* ≥ 1/(c_n√n).

So the first t with σ_t ≤ σ* exists, and it satisfies σ_t > σ*/γ. Every run starts at a parameter ≥ s_*, which is
at least the BLP threshold ‖B̃‖√(ln(2n+4)/π), because ‖b̃_i‖ ≤ ‖b_i‖ ≤ √dB. No LLL call or λ₁ estimate is needed.
The algorithm never uses s_j after sampling, because Pair-and-Average has no parameter.

### 4.8 Initial sampler and its cost (BLP13 Lemma 2.3, §5; verified in the arXiv text)

BLP13 Lemma 2.3: "a probabilistic polynomial-time algorithm that, given a basis B…, c, and r ≥ ‖B̃‖·√(ln(2n+4)/π),
outputs a sample distributed according to D_{Λ+c,r}." The proof (§5.2) works as follows:
* Klein/GPV SampleD makes n calls to an exact 1-D sampler. That sampler (§5.1) accepts each iteration with
  probability ≥ ½.
* SampleD is followed by a rejection step. Its acceptance probability is ∏ρ_r(‖b̃_i‖Z + ⟨c_i, b̄_i⟩)/∏ρ_r(‖b̃_i‖Z)
  ∈ ((1 − 2/(n+2))^n, 1] ⊆ (e^{−2}, 1] (eq. 5.1). That interval uses GPV Lemma 3.1 (η_ε(Z) bound) and
  Regev Claim 3.8 with ε = 1/(n+1).

Explicit count per SampleD iteration, in the §1 model:
* the inner products and updates cost ≤ 4nd;
* per coordinate, the 1-D setup (2 erf, 2 exp, 1 theta sum, 1 product) costs 6 operations, and each 1-D iteration
  costs ≤ 5. With a cap of 4 iterations per 1-D sample on aggregate, that is ≤ 26 ≤ 32 operations per coordinate.

Caps (the algorithm aborts beyond them, which turns expected time into worst-case time):
* ≤ 2e²M₀ SampleD iterations per run. Exceeded with probability ≤ Pr[Bin(⌈2e²M₀⌉, e^{−2}) < M₀] ≤ e^{−M₀/4}.
* ≤ 4× the number of 1-D samples for the 1-D iterations. Exceeded with probability ≤ e^{−M₀/2}, since there are
  at least nM₀ ≥ 2M₀ 1-D samples.

Together these give the 2e²(4nd + 32n) per sample in (3.1). List phase per vector per step:
* label: d parity bits;
* stable LSD radix sort with 16-bit digits: 2⌈d/16⌉ per element, plus 2^{17}⌈d/16⌉ per step;
* averaging y and z: 4d;
* norm²: 2d;
* bookkeeping: ≤ 4d.

That is ≤ 10d + 2⌈d/16⌉ per vector per step. List sizes at least halve each step, so all steps together cost
≤ 2M₀ vector-steps. Gram–Schmidt costs ≤ 2n²d.

### 4.9 Proof of Theorem E

* By §4.7, some (r, j) with j ≤ ℓ has σ_{r,j} ∈ [σ*/γ, σ*]. Fix that run.
* By Lemma 4.5, Procedure E finds a λ₁-vector in it unless one of the following happens: R > M₀; a combiner
  failure in steps 0..j−1 (§4.4, whose condition A_{s_i} ≥ A holds for i ≤ ℓ−1); or no hit in the Pois(Λ_j)
  final list (Lemma 4.6).
* The other runs and steps can only lower the recorded minimum to λ₁; they never raise it, since every recorded
  vector is a nonzero lattice vector.
* Adding the probabilities, plus the cap aborts, gives (3.2). The operation count is §4.8 times k runs. ∎

## 5. Evaluation at the recorded instance (B = 3329, d = n; no parameter search)

The Part 39 lattice is the full-rank embedding lattice in Z^647 with entries in {0,…,3328} ∪ {1}, so d = n = 647
and B = 3329. Initial samples have norm ≤ √n·s_*γ³ ≈ 4.22·10⁶ < 2^{23}, except with probability C(1)^{647}·4M₀
< 2^{−830} (I5 at t = 1). So integer words suffice in the list phase.

| Quantity | n = 647 | n = 646 |
| --- | --- | --- |
| c_n | 0.417409 | 0.417423 |
| C(c_n)^n (≤ ½ required) | 2^{−1.970} | 2^{−1.970} |
| log₂ Q | 19.873 | 19.871 |
| ℓ (combiner steps per run) | 40 | 40 |
| log₂ Λ₀ = n + log₂ 400.25 + 3·39 | 772.645 | 771.645 |
| log₂ M₀ | 772.646 | 771.646 |
| per-sample cost 2e²(4n² + 32n) | 2^{24.578} | 2^{24.574} |
| list-phase cost per vector-step | 6552 (2^{12.68}) | 6542 |
| **log₂ T** (k = 4 runs) | **799.225** | **798.221** (two calls: **799.221**) |
| log₂ space (words) | 781.98 | 780.98 |
| combiner failure, line 1 of (3.2) | 2^{−120.92} | 2^{−121.92} |
| log₂ of exponent in the final-hit term: log₂(Aθ) + n/2 − γ²(√n+√(2ln2))²/(4 ln 2) | 25.35, so failure e^{−4.3·10⁷} | 25.30 |
| Poissonization, line 3 | e^{−2^{751}} | e^{−2^{750}} |
| **p** | **< 2^{−120.9}** | **< 2^{−121.9}** per call |

**Comparison.**

| Bound at the recorded instance | bits | status |
| --- | --- | --- |
| Theorem E (this note), D = 647 | **799.23** | fully explicit; real-RAM sampler (G1) |
| Theorem E, two calls at D = 646 (Part 131) | 799.22 | same |
| Brute-force likelihood search (Part 133 §4) | 1253.40 | fully explicit, word ops |
| Micciancio–Voulgaris [MV13] | 1294 + c·log₂(1294) | c unspecified |
| ASD18 "with the hidden constant set to 1" (Part 133 §0) | ≈ 734.2 | not a theorem |

End to end, with Part 39 (`failure_647` < 1/100, success ≥ 99.51664%) and `exact_svp_recovery`: s is recovered
with probability ≥ 0.9951664 − 2^{−120.9} in ≤ 2^{799.23} operations. The margin over brute force is 454.2 bits.

*Sensitivity to the fixed analysis constants (not used for the headline).* θ = 1/8 and k = 3 give 798.81, with a
final-hit exponent of only 2^{7.3}. θ = 1/6 and K₀ = 3200 give 785.45. With the instance's Gram–Schmidt norms
(the embedding basis is triangular, so ‖B̃‖ = q rather than √n·q), ℓ would drop by 9 steps and log₂ T by about 27.
None of these is adopted, since the task fixes the evaluation, not an optimization.

## 6. Audit of the published proofs: gaps and non-explicit lemmas

Sources: ASD18 arXiv:1709.01535v1 and ADRS15 arXiv:1412.7994, both downloaded and read for this note.

* **A1 (genuine gap, ASD18).** ASD18 Definition 2.2 defines domination as an upper-orthant inequality: for every
  k, Pr[counts ≥ k] ≥ Pr[counts' ≥ k]. Corollary 3.3 item 3 ("Procedure 1 preserves domination") is called
  immediate. For orthant order it is not. Procedure 1 maps counts through k ↦ ⌊k/2⌋, and then each pair moves
  randomly to another coset by Lemma 3.1. Upper-orthant order is not in general preserved by such random monotone
  maps; the usual multivariate stochastic order (existence of a monotone coupling) is.

  ASD18 Thm B.1 also applies "Corollary A.4: M dominates M'" across a type mismatch: lists of cosets versus lists
  of coset pairs. ⌊M/2⌋ is intended.

  *Repair:* Lemma 4.5 here proves the needed statement with an explicit coupling (sub-multiset), which implies
  every monotone event, including "contains a λ₁-vector". It needs the value-oblivious pairing constraint of §2.
* **A2 (non-explicit, ADRS15 Thm 3.3 / ASD18 Thm A.3).** The square sampler's error C₁MN log N·exp(−C₂κ) with
  N = 2^n, its "κ ≥ Ω(log M)" and the Chernoff constant C of ADRS15 Lemma 2.21 are all unnumbered. Corollary 2.20
  is stated only as "there exist C₁, C₂". *Replaced* by Lemma 4.3, which has explicit Poisson tails.
* **A3 (non-explicit, the initial-sampler sublattice).** ASD18 Thm C.1 ([Sch87, AKS01]: a u^{n/u}-reduced basis
  in time exp(O(u))·poly(n)) is used with u = Θ(n). That makes exp(O(u)) a 2^{Θ(n)} term with an unknown
  constant, which ASD18 Thm D.1 needs to be ≤ 2^{n+o(n)}. It is true for u = εn with ε small enough, but the
  constant is not given.

  Minor slips: Prop C.3's proof "calls the procedure from Theorem C.1 again… receiving… a √n u^{n/u}-approximate
  closest vector" should be a Babai step on the reduced basis (Thm A.2 style); "s^{n/s}-HKZ" should be
  "u^{n/u}-HKZ"; and "Thm C.1 … u^{n/y}" is a typo.

  *Removed:* Theorem E samples on L itself at s_* ≈ √dB·√(ln(2n+4)/π) and pays ℓ = ⌈2 log₂ Q⌉ = O(log(nB))
  steps instead.
* **A4 (non-explicit, and fragile at fixed n, ADRS15 Lemma 4.1 / Prop 4.3; ASD18 Prop A.7 / Cor A.8).** These rest
  on PS09 Lemma 3 / KL78: #{y : ‖y‖ ≤ rλ₁} ≤ 2^{0.401n+o(n)}r^n, with no explicit o(n). ADRS15 Lemma 4.2's proof
  also replaces a sum by "(1+s)·max" where (1+s)·poly(n) is meant.

  The conclusion uses 2^{n/2} samples × 1.4^{−n−o(n)}. With the 1.01 grid, the slack is (√2/(1.38·1.01))^n·2^{−o(n)},
  only 2^{0.021n} ≈ 2^{13.6} at n = 647, before the unknown o(n). So the published route gives no guarantee at
  n = 647 even in principle unless the KL o(n) is below about 13 bits. *Replaced* by Lemma 4.6 (Banaszczyk only).
* **A5 (non-explicit failure).** ASD18 Thm D.1's "exp(−Ω(n))" uses κ = Θ(n) and ℓ = Θ(log n) without constants,
  so even the constant-probability statement is asymptotic. The 2^{Θ(log² n)} in M is (10κ)^{2ℓ}·(32κ)^ℓ.
  Illustratively, with κ = n and ℓ = 34 at n = 647, that is ≈ 2^{861+488}, which is more than brute force. So
  ADRS/ASD with their own analysis would not beat brute force at 647 even if every hidden constant were 1.
  *Replaced* by (3.2).
* **A6 (fine as cited).** BLP13 Lemma 2.3 is exact, with explicit expected-iteration bounds (½ and e^{−2}) in its
  §5 (read for this note). ASD18 Lemma 2.1, Lemma 3.1 and Cor 3.3 item 4 are exact identities with complete proofs.
  ADRS15 Lemma 2.3 and Lemma 2.4 are explicit.

## 7. Honest gap list for this note

* **G1, the cost model of the initial sampler.** Theorem E counts BLP13's exact sampler in a real-RAM model (unit
  cost for erf, exp, theta sums, truncated normals and real-bias coins). This is the model in which BLP13 calls it
  "exact". A bit-complexity version is not proved here. Two routes are sketched:
  * (a) Lazy-precision evaluation of the coins and theta sums. Expected precision is small, but no explicit
    worst-case bound is derived.
  * (b) Drop the rejection step and use Klein/GPV with ε ≈ 2^{−913} (= 2^{−(log₂M₀+130+log₂ 2n)}). The smoothing
    factor √(ln(2(1+1/ε))/π) replaces √(ln(2n+4)/π), which raises s_* by √(633.6/7.169) ≈ 9.4× and adds 7 steps
    (≈ +21 bits). The list then has total-variation distance
    ≤ 2nεM₀ < 2^{−120}, and 1-D samples with rational centre and rational σ² can be drawn exactly in integer
    arithmetic (Canonne–Kamath–Steinke-style). The Gram–Schmidt rationals have about n·log₂(nB) ≈ 10⁴ bits, so
    about 2^{15} word operations per arithmetic operation with schoolbook multiplication. For the instance's
    triangular q-ary basis, b̃_i ∈ {q e_i, e_i} and this overhead vanishes.

  Either way the estimate stays below 2^{840}, far under 2^{1253}. But it is an estimate, not a theorem.
* **G2, new lemmas.** Lemmas 4.3a, 4.3b and 4.5 are new here. They are short and elementary, but they have not been
  independently audited. Lemma 4.3a was checked numerically (§4.3). An audit should re-derive R_{j+1}/R_j, the g₁/g₂
  bounds, and the conditional-independence induction in Lemma 4.5. That induction needs "H never contains vector
  values", which holds because the pairing in §2 uses list order and coset labels only.
* **G3, cited and not re-proved.** I3, I4 and I5 (Banaszczyk via Poisson summation; I5 as stated in ADRS15
  Lemma 2.4, from DRS14 Lemma 2.13) and BLP13 Lemma 2.3. [Ban93] itself was not re-read.
* **G4, scope.** The theorem gives a vector of norm λ₁. Part 39 certifies that ±v is the unique shortest pair with
  probability ≥ 99.51664%, so on that event the output is ±v. The composition was argued in §5, not formalized.
* **G5, the operation count's granularity.** "10d + 2⌈d/16⌉ per vector-step" and "≤ 32 per coordinate" are
  careful counts of the obvious implementation, not of a written program. The headline is insensitive to them: the
  sampler term dominates, and a 4× error moves log₂ T by 2.

## 8. What would be feasible in Lean

The repository proves probabilities, not running times. "Cost" below means an explicit count of a stated quantity.

| Item | Content | Effort | Notes |
| --- | --- | --- | --- |
| Poisson toolkit | splitting/marking (P1), b^k/k! tail (P2), Chernoff (P3) | 1–2 weeks | finite and countable sums; Mathlib has Poisson PMFs |
| Lemma 4.3a | likelihood ratio on {0..m} ⇒ stochastic order ⇒ coupling with failure ≤ α+β | 1–2 weeks | purely elementary; good first target |
| Gaussian identities I1, I2 | parallelogram identity and lattice-sum rearrangements (tsum over Z^n) | 2–4 weeks | summability by comparison with a product Gaussian |
| I3, I4, I5 (Banaszczyk) | need Poisson summation for Gaussians on a lattice in R^n | 1–3 months | Mathlib has 1-D Poisson summation and the Fourier transform of Gaussians on inner-product spaces; the n-dimensional lattice version is the main infrastructure gap |
| Lemma 4.5 coupling | conditional independence given the coset σ-field, through ℓ steps | 1–2 months | measure-theoretic bookkeeping; can be phrased with finite-support approximations |
| BLP13 sampler | exactness of SampleD + rejection; 1-D sampler via a continuous normal | 1–2 months | real-RAM model only (G1) |
| Numerics of §5 | log₂ T, p at 647/646 | 1 week | interval bounds for π, e, ln 2 (Mathlib `Real.pi_gt_d6` etc.); no `native_decide` needed |

Total: roughly 4–8 months. The order with the best value: Lemma 4.3a and the Poisson toolkit first (cheap and
self-contained), then I1/I2, then the Banaszczyk infrastructure.

## References

* [ADRS15] D. Aggarwal, D. Dadush, O. Regev, N. Stephens-Davidowitz. Solving the Shortest Vector Problem in 2^n Time
  via Discrete Gaussian Sampling. STOC 2015; arXiv:1412.7994. Cited: Lemmas 2.3, 2.4, 2.19, 2.21, 2.22, Cor 2.20,
  Claim 2.23, Prop 3.1, Thm 3.3, Lemma 3.4, Prop 3.5, Cor 3.6, Thm 3.7, Lemma 4.1, Lemma 4.2, Prop 4.3, Thm 4.4,
  Cor 4.5.
* [ASD18] D. Aggarwal, N. Stephens-Davidowitz. Just Take the Average! SOSA 2018; arXiv:1709.01535v1. Cited:
  eq. (1), Lemma 2.1, Def 2.2, Fact 2.3, Lemma 3.1, Def 3.2, Cor 3.3, Thm 3.4, Thms A.1–A.3, Cor A.4, Lemma A.5,
  Props A.6–A.7, Cor A.8, Thm B.1, Cor B.2, Thm C.1, Thm C.2, Prop C.3, Cor C.4, Procedure 3, Thm D.1.
* [BLP+13] Z. Brakerski, A. Langlois, C. Peikert, O. Regev, D. Stehlé. Classical Hardness of Learning with Errors.
  STOC 2013; arXiv:1306.0281. Lemma 2.3, Lemmas 2.5 and 2.7, §5 (eq. 5.1).
* [Ban93] W. Banaszczyk. New bounds in some transference theorems in the geometry of numbers. Math. Ann. 296, 1993.
  Lemmas 1.4 and 1.5 (via ADRS15 Lemma 2.3 and Lemma 2.4).
* [DRS14] D. Dadush, O. Regev, N. Stephens-Davidowitz. On the closest vector problem with a distance guarantee.
  CCC 2014. Lemma 2.13.
* [GPV08] C. Gentry, C. Peikert, V. Vaikuntanathan. Trapdoors for hard lattices. STOC 2008. Lemma 3.1, Thm 4.1.
* [KL78] G. Kabatiansky, V. Levenshtein. Bounds for packings on a sphere and in space. 1978 (via [PS09, Lemma 3]).
* [MV13] D. Micciancio, P. Voulgaris. SIAM J. Comput. 42(3), 2013.
* Part 133: [wall1_provable_cost.md](wall1_provable_cost.md). Part 39: [PROOF_GAP.md](../PROOF_GAP.md),
  `Attacks/Primal/SampleDeletion*.lean`.

## Audit

Independent adversarial audit, 2026-11-22. The audit was read-only apart from this section. Scratch scripts (mpmath
at 60 digits, numpy) were not committed. Sources: ASD18 arXiv:1709.01535v1, ADRS15 arXiv:1412.7994 and BLP13
arXiv:1306.0281, all read as text (pdftotext).

**Verdict: MINOR CAVEATS.** Theorem E's mathematics holds. Every lemma was re-derived step by step, and no
counterexample was found. Every number in §5 reproduces. The caveats concern (i) how the cost model is attributed and
how prominently it is flagged (C1), (ii) an operation count (C2), and (iii) presentation and citation details. None of
them changes the exponent by more than about 0.6 bits within the stated model. The headline 2^{799.23} is a figure in
the hybrid model of §1 (real-RAM initial sampler), not a word-RAM theorem.

### Checks performed

1. **Lemma 4.3a.**
   * Re-derived: P[N′=j] = e^{−a}a^{2j}/(2j)!·(1+a/(2j+1)), and R_{j+1}/R_j = (2b/a²)(2j+3)(2j+1+a)/(2j+3+a). This is
     ≤ 1 on j ≤ m−1 exactly when 2θ(2m+1) ≤ A, which holds for m = ⌊A/(4θ)−½⌋.
   * The chain "monotone likelihood ratio ⇒ stochastic order ⇒ comonotone coupling; K > N′ only off the Y ≤ Z branch"
     is correct, and the marginals are exact.
   * Numerically, for θ ∈ {1/8, 1/6, 1/4, 1/2.1}, A from the m = 1 boundary up to 400.25, and a/A ∈ [10⁻³, 1]: the
     ratio is monotone on {0..m} and the conditional CDFs are ordered in every case (0 failures).
2. **Lemma 4.3b.**
   * g₁ and g₂ re-derived, using P2, b_c ≤ θa_c ≤ θA_s, A_s < 4θ(K+½), K! ≥ (K/e)^K and (1+1/(2K))^{K−1} ≤ e^{1/2}.
     Both bounds are correct as stated.
   * Λ′ = θΛψ(1)²/(ψ(0)ψ(2)) follows from I1 and I3, both of which were checked to 10⁻¹⁵ on 328 random lattices of
     rank 1–3 (truncation-controlled).
   * End-to-end simulation of the kernel: L = Z, s = 2.5, Λ = 60, θ = 1/8, m = 60, 6·10⁴ trials. The selected-pair
     count has mean 7.380 and variance 7.317, against Pois(Λ′ = 7.392). The averages fit D_{Z,s/√2} with χ² = 1.23
     on 4 degrees of freedom. The exact coupling failure is about 10⁻⁵⁰.
3. **Telescoping (§4.4).**
   * Λ_j = Λ₀θ^jψ(1)ψ(j)/(ψ(0)ψ(j+1)) and A_{s_j} ≥ Λ₀θ^j2^{−n} (I4 used twice) re-derived. This gives
     A_{s_i} ≥ A for i ≤ ℓ−1.
   * The union bound over steps is valid, but the proof leaves one point implicit: the ideal process, with phantom
     fresh Gaussians when K_c > ⌊N_c/2⌋, coincides with the actual analysis process up to the first failure.
     Recommend stating this explicitly.
4. **Lemma 4.5 (no-rejection coupling).**
   * Correct. Given every coset label, list position and independent coin (analysis membership, R and the 4.3a coins
     included), the values are conditionally independent D_{2L+c,s}. This follows from Lemma 3.1, applied inductively.
   * Every such H-measurable maximal pairing therefore induces the same Markov kernel on (coset, value) multisets:
     ⌊N_c/2⌋ independent Lemma 3.1 averages per coset. The canonical stable-sort pairing and the "analysis pairs first"
     pairing thus give equal laws for the sequence of multisets, and the sub-multiset containment is immediate.
   * The value-oblivious constraint in §2 is necessary and is correctly stated.
5. **A1 (ASD18 gap). Confirmed as a genuine gap in the stated proof.**
   * ASD18 Def 2.2 is verbatim the upper-orthant order on count vectors, and Cor 3.3 item 3 is proved only by
     "immediate consequences of Lemma 3.1".
   * Explicit counterexample to item 3. Take L = Z and s = 2. Let M have coset counts (0,0) or (2,2), each with
     probability ½, and let M′ have counts (2,0) or (0,2), each with probability ½. Then M dominates M′ in the sense of
     Def 2.2 (checked for all orthants).
   * The exact transition probabilities are Pr[average ∈ 2Z | inputs in 2Z] = 0.8536 and Pr[average ∈ 2Z | inputs in
     2Z+1] = 0.5. After Procedure 1, Pr[≥ 1 output in coset 0] is 0.4634 from M but 0.6768 from M′. So domination is
     not preserved.
   * The last sentence of the proof of ASD18 Thm B.1 ("by Fact 2.3 … the output must dominate") uses the same
     invalid step.
   * ASD18's final claims still hold: Thm 3.4's "Pr[S ⊆ A] ≤ Pr[S ⊆ A′]" and Thm D.1 follow from a sub-multiset
     coupling such as Lemma 4.5. So the note's "gap in the proof, not the theorem" is accurate.
   * The Cor A.4 type mismatch (a list of elements "dominates" a list of pairs, where ⌊M/2⌋ is meant) is also
     confirmed.
6. **Lemma 4.6 and the choice of c.**
   * Re-derived: the ψ(j) cancellation, ρ_σ(L) ≤ 1/(1−C(c)^n) from I5 with t ↑ c, φ″ ≤ −2π ⇒ C(c_n)^n ≤ ½, and the
     exponent identity πc_n²n/2 = (√n+√(2 ln 2))²/4.
   * The inequality was checked numerically on random lattices of rank 1–3 and on Z^n for n ≤ 12 with c ∈ [0.40, 1.2].
     No violations were found.
   * C(c_647)^{647} = 2^{−1.970}, as stated.
7. **Grid (§4.7).** The bracketing σ_top ≥ σ* and the lowest grid value ≤ 1/(c_n√n) ≤ σ* were re-derived. So were the
   consecutive grid index t = kj + (k−1−r) and the BLP threshold check, using ‖b̃_i‖ ≤ ‖b_i‖ ≤ √dB.
8. **Item (2): dropping the sublattice step.** Correctness is unaffected. Samples come from D_L itself, so no
   short vector can be lost, which is the risk ASD18's L′ must guard against. The cost is the θ^{−(ℓ−1)} =
   8^{ℓ−1} ≤ Q⁶ factor, as stated.
9. **Item (3): exact shortest vector.** The output is a nonzero lattice vector of norm exactly λ₁ with probability
   ≥ 1 − p, worst case over L. That makes it an exact SVP solution, not an approximation. Identifying it with ±v
   relies on Part 39's uniqueness event (G4). The union bound 0.9951664 − p is valid because p is a worst-case bound.
10. **Numbers (§5).** Recomputed at 60 digits.

    | Quantity | n = 647 | n = 646 |
    | --- | --- | --- |
    | ℓ | 40 | 40 |
    | log₂ Λ₀ | 772.6448 | 771.6448 |
    | log₂ M₀ | 772.6462 | 771.6462 |
    | log₂ per-sample cost | 24.5784 | — |
    | list cost per vector-step | 6552 | 6542 |
    | log₂ T | 799.2253 | 798.2208 |
    | log₂ space | 781.9838 | — |
    | line 1 of (3.2) | 2^{−120.922} | 2^{−121.922} |
    | log₂ final-hit exponent | 25.3506 | 25.2994 |
    | line 3 | e^{−2^{751.64}} | — |
    | norm bound √n·s_*γ³ | 4.219·10⁶ (2^{22.01}) | — |
    | norm tail C(1)^n·4M₀ | 2^{−833.3} | — |

    For two calls at n = 646, 1 + 798.221 = 799.221. The sensitivity line "k = 3 ⇒ 798.81, exponent 2^{7.3}" also
    reproduces.
11. **Sanity run of Procedure E at the theorem's own constants.** n = d = 2, B = 3, ℓ = 5, M₀ = 6 564 100, 4 runs,
    exact (box-enumerated) initial sampling, coefficient-parity labels, stable sort. On 6 random lattices it output
    a vector of norm λ₁ every time. This is weak evidence, because at n = 2 the margin is enormous, but it
    exercises the implementation as written.
12. **Part 39 instance facts.**
    * Retained samples r = 134, so D = 134 + 512 + 1 = 647 and the covolume is q^r = 3329^{134}, which is odd
      (wall1_projected_reference.md). The odd-det parity-label shortcut is therefore valid.
    * Entries ≤ 3329, so B = 3329.

### Issues and corrections

* **C1 (cost model: attribution and scoping).**
  * The note says (§1, §7 G1) that real-RAM "is the model in which BLP13 Lemma 2.3 is 'exact'". That is not what BLP13
    says. §5 of BLP13 computes ρ_r(Z+c) "to within any desired t bits of accuracy in time poly(t)", which "agrees with
    our notion of efficiently computing a real number (following, e.g., the treatment in [Lov86, Section 1.4])". The
    1-D sampler draws continuous normals. BLP13's exactness is a bit-model statement with lazy precision and expected
    polynomial time.
  * The unit-cost real-RAM count (erf, exp, theta sums and truncated continuous normals at cost 1) is the note's own
    idealization. It is strictly stronger than BLP13's.
  * The sampler term dominates T: 2^{24.58} per sample against 2^{13.68} for the list phase. So 2^{799.23} rests
    entirely on that idealization, and the 454-bit margin compares a real-RAM-sampler count with a word-operation
    brute-force count.
  * G1 does flag this, and route (b) is a plausible sketch: Klein/GPV statistical distance ≈ 2nε per sample;
    rational parameters reduce to 1-D samplers on Z with rational centre and variance; about +21 bits. Route (b) is
    not proved, however.
  * *Correction:* replace "the model in which BLP13 Lemma 2.3 is 'exact'" with "an idealization of BLP13, whose own
    model is arbitrary-precision bit arithmetic with expected polynomial time". Write the headline as "2^{799.23}
    operations (real-RAM initial sampler; word-RAM bound unproved, estimated ≤ 2^{840})" wherever it appears,
    including §0 item 3 and the end-to-end sentence in §5.
* **C2 (sampler operation count).**
  * "Inner products and updates ≤ 4nd" does not match the literal BLP/GPV recursion. Each coordinate there costs an
    inner product ⟨c_i, b̄_i⟩ (2d) plus the update c ← c + (v_i − ⟨c_i, b̄_i⟩)·b̄_i/‖b̃_i‖ − v_i b_i (two axpys, 4d),
    so 6d per coordinate and 6nd in total.
  * 4nd is achievable with the standard μ-coefficient implementation: centres −Σ_{j>i} v_j μ_{j,i} in at most n²
    operations, plus y = Σ v_i b_i in 2nd.
  * *Correction:* name that implementation, or use 6nd. With 6nd, log₂ T becomes 799.81. Theorem E's (3.1) is then
    a bound only for the named implementation.
* **C3 (overflow event).** Words of 2^{23} suffice except with probability 2^{−833} (norm tail at t = 1). That event
  is not in (3.2). It affects only the word-size claim, not correctness. *Correction:* either add 4M₀·C(1)^n to p (no
  visible change), or state that the implementation falls back to multiword arithmetic.
* **C4 (proof presentation).** In §4.4 and §4.9, state the "ideal process with phantom samples, equal to the actual
  analysis process until the first failure" coupling explicitly. Lemma 4.3b(2) is written as "outside a failure
  event … exactly Pois(Λ′)". That is a coupling statement, and the union bound over steps depends on reading it so.
* **C5 (citations).**
  * Verified against the sources:
    * ADRS15 Lemma 2.3 is [Ban93, Lemma 1.4], ρ_s(L) ≤ s^nρ(L) for s > 1.
    * ADRS15 Lemma 2.4 is [DRS14, Lemma 2.13], the tail bound with the factor ρ_s(L)/ρ_s(L+u). At u = 0 it is I5,
      with strict inequality.
    * The zero-coset-maximal remark is in ADRS15 §2, citing [Ban93].
    * ADRS15 Lemma 2.22 is the Poisson splitting; Cor 2.20 has unnamed C₁, C₂; Thm 3.3 has the error
      C₁MN log N exp(−C₂κ).
    * BLP13 Lemma 2.3 has the threshold ‖B̃‖√(ln(2n+4)/π). BLP13 §5.1 gives acceptance ≥ ½, and §5.2 gives (5.1)
      with ((1−2/(n+2))^n, 1] ⊆ (e^{−2}, 1], via BLP13 Lemma 2.5 (= GPV Lemma 3.1) and Lemma 2.7 (= Reg05 Claim 3.8).
    * All ASD18 numbers listed in the note (Def 2.2, Fact 2.3, Lemma 3.1, Def 3.2, Cor 3.3, Thm 3.4, Cor A.4,
      Lemma A.5, Props A.6–A.7, Cor A.8, Thm B.1, Cor B.2, Thm C.1, Thm C.2, Prop C.3, Cor C.4, Procedure 3,
      Thm D.1) match v1.
    * The slips in A3 ("u^{n/y}", "s^{n/s}-HKZ", Prop C.3 calling Thm C.1 for a CVP step) are confirmed.
  * Small inaccuracy: the reference entry "[Ban93] Lemmas 1.4 and 1.5 (via ADRS15 Lemma 2.3 and Lemma 2.4)". ADRS15
    Lemma 2.4 cites DRS14 Lemma 2.13, not Ban93 Lemma 1.5 directly, though its u = 0 case is Banaszczyk's bound.
  * Not verified: the claim in A4 that ADRS15 Lemma 4.2's proof uses "(1+s)·max".
* **C6 (scope, not an error).**
  * The grid descends to λ₁ ≥ 1. At the instance λ₁ ≈ ‖v‖ ≈ 30, so about 10 of the 40 steps (about 30 bits) are
    spent on a range the instance cannot reach. This is consistent with "no optimization" and is noted only because
    it is a larger lever than the ‖B̃‖ remark in §5.
  * Like ASD18, Theorem E gives no constant-probability statement at smaller n beyond (3.2). At n = 2 the
    final-hit term is ≈ e^{−13.6}.

No change to Theorem E's statement is needed beyond C1's scoping of the cost model and C2's choice of implementation
in (3.1).
