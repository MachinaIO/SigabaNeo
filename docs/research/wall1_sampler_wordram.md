# A word-RAM initial sampler for Theorem E (closing gap G1 at the recorded instances)

Research note, 2026-11-22. Mathematics and arithmetic only. No Lean or Python in the repository is touched. The
numbers in §6 come from a scratch `mpmath` script (80 digits), not committed. A toy-scale numerical check of
Lemmas 2 and 3 (exact enumeration at q = 5, and a CDT table built at 30–48 bits) was also run in scratch and agreed
with the bounds.

**Task.** [wall1_adrs_explicit.md](wall1_adrs_explicit.md) (Part 140) proves Theorem E, an explicit exact-SVP bound of
2^{799.23} operations at n = d = 647, B = q = 3329. The initial discrete Gaussian sampler (BLP13 Lemma 2.3) is counted
in a real-RAM model: unit cost for erf, exp, theta sums, continuous normals and real-bias coins. The audit of that
note (C1) asks for a proven word-RAM bound, (C2) settles the 4d vs 6d recursion count, and (C3) flags an unaccounted
overflow event. This note proves an explicit word-RAM bound for the recorded instances: n = 647 (Part 39) and two
calls at n = 646 (Part 131). The constants of Theorem E (θ = 1/8, k = 4, K₀ = 800, s_*, γ, ℓ, M₀) are unchanged.
Only step 2.1 of Procedure E, "draw M₀ samples from D_{L,s_*γ^r}", is re-implemented. No parameter is optimized.

Conventions: "bits" means log₂. D_{S,s} and ρ_s(x) = exp(−π x²/s²) are as in Part 140. SD means statistical
(total-variation) distance.

## 0. Verdict

1. **Theorem W (§6).** At the recorded instances, Procedure E with step 2.1 implemented by Procedure S (§4) runs on
   a word-RAM in at most
   * **T_W(647) = 2^{794.98}** word operations, with failure probability **< 2^{−120.92}**;
   * **T_W(646) = 2^{793.98}** per call, so **2^{794.98}** for Part 131's two calls, with failure < 2^{−121.92} per call.

   The bound is worst case: the sampler has no rejection loop and no abort. Every integer in the list phase is
   deterministically below 2^{54} in absolute value.
2. **What is proved.**
   * The per-sample SD from D_{L,s} is ≤ 2^{−923.9}.
   * The total SD over all k·M₀ = 2^{774.65} samples is ≤ 2^{−149.26}.
   * Failure is bounded by data processing: Pr_real[fail] ≤ Pr_ideal[fail] + SD. The combiner is a deterministic
     function of the samples, so the 40 combiner steps add no further loss (§5).
3. **Why the word-RAM number is below the real-RAM 2^{799.23}.** The real-RAM count in Part 140 is for the generic
   BLP13 sampler. That sampler has rejection (factor 2e²), Gram–Schmidt updates of length d per coordinate, and
   theta sums. The recorded lattice has a q-ary triangular structure with Gram–Schmidt norms q (r times) and 1
   (t times), and s/q ≥ 38.38. Klein's algorithm *without* rejection is therefore 2^{−6668}-close to D_{L,s}
   (Lemma 2). Its 1-D steps are a centred discrete Gaussian and q coset Gaussians, which are table lookups. A sample
   costs 1.31·10⁶ ≈ 2^{20.32} word operations instead of 2^{24.58} real-RAM operations. The saving comes from the
   instance's structure, not from the change of model.
4. **Audit items.**
   * C1 (model) is resolved at the recorded instances by Theorem W.
   * C2 (4d vs 6d) does not arise: the count is for a fully specified program (§4) with no d-dimensional updates.
   * C3 (overflow) is removed: coordinates are bounded deterministically by R = 2^{22} − 1 (§4.3).
5. **Gaps (§8).**
   * The result is instance-specific. It covers every lattice of the form L_M (any M) at these (q, r, t), not
     Theorem E's general integral bases. For general bases, G1 stays open.
   * The model is a transdichotomous word-RAM. The word size must address 2^{782} words, which is standard but worth
     stating.
   * The list-phase operation count is inherited from Part 140, at that note's level of granularity (G5).

## 1. Model and goal

**Word-RAM.** Memory consists of words of w bits, with w ≥ 64 and w ≥ ⌈log₂(space)⌉. This is the standard
transdichotomous word-RAM (Fredman–Willard; Hagerup 1998). Since the space is about 2^{782} words, w ≥ 783. The
following each cost one operation:
* load and store with indirect addressing;
* +, −, ×, integer ÷ and mod;
* bitwise operations and shifts;
* comparison and conditional branch;
* RANDWORD, which returns a fresh uniform 64-bit string.

All arithmetic on *data* in this note uses values of absolute value < 2^{63}, so nothing depends on w beyond
addressing. Multiprecision arithmetic (§3.3) uses 32-bit limbs stored in words, so no double-word product or
quotient is needed.

**Goal.** Theorem E assumes that run r (r = 0..3) draws M₀ independent *exact* samples from D_{L,s_r}, where
s_r := s_*γ^r = s_*·2^{r/8}. We replace this by a word-RAM procedure whose output law is within an explicit SD of
the ideal, and we propagate that SD to the failure probability.

## 2. The instance lattice and Klein's algorithm without rejection

### 2.1 Structure

The Part 39 lattice is defined in [wall1_projected_reference.md](wall1_projected_reference.md) as follows. The
embedding is x + Ay ≡ tb (mod q). After deleting k error coordinates, it becomes the integral solution set of
x' + A'y ≡ tb' (mod q) in Z^{r+n_s+1}, with r = 134 retained samples, n_s = 512 secret coordinates and one height
coordinate. Put t := n_s + 1 = 513 and write M := [−A' | b'] mod q ∈ {0..q−1}^{r×t}. Then

  **L = L_M := {(h, u) ∈ Z^r × Z^t : h ≡ M u (mod q)},**   d = n = r + t.

Part 131's calls have r = 133, so d = 646 and t = 513.

The basis {q e_i (i ≤ r)} ∪ {(M e_j mod q, e_j) (j ≤ t)} has entries in {0..q} = {0..B}. In this order its
Gram–Schmidt vectors are q e_i and e_{r+j}. The determinant is q^r, which is odd, so the parity-label shortcut of
Part 140 §2 applies and coefficient vectors need not be stored. Everything below holds for **every** M; nothing is
assumed about the distribution of A'.

### 2.2 Exact factorization

**Lemma 1.** Let y = (h, u) ~ D_{L,s}. Then:
* The marginal of u is π_D(u) ∝ ρ_s(u)·∏_{i≤r} ρ_s(qZ + w_i(u)), where w(u) := Mu.
* Given u, the coordinates h_i are independent with laws D_{qZ+w_i(u), s}. These depend only on w_i(u) mod q.

*Proof.* We have D_{L,s}(h,u) ∝ ρ_s(u)·∏_i ρ_s(h_i), and the constraint h ≡ Mu (mod q) factorizes over i. Summing
over h_i ∈ qZ + w_i gives the marginal, and dividing gives the conditional. ∎

Define the **Klein law** K. Draw u ~ D_{Z,s}^{⊗t}, then draw each h_i independently from D_{qZ+w_i(u),s}. On this
basis, K is exactly the output law of Klein/GPV SampleD with no BLP rejection step: tail rows have centre 0 and
parameter s, and head rows have centre −w_i/q and parameter s/q, rescaled.

**Lemma 2 (Klein is nearly exact here).** Put τ := 2Σ_{k≥1} e^{−πk²s²/q²}. Then
SD(K, D_{L,s}) ≤ ½(((1+τ)/(1−τ))^r − 1).

*Proof.*
* Poisson summation in one dimension (Jacobi's theta transformation) applied to x ↦ e^{−π(qx+w)²/s²} gives
  ρ_s(qZ+w) = (s/q)·Σ_{k∈Z} e^{−πk²s²/q²}·cos(2πkw/q). Hence ρ_s(qZ+w) ∈ (s/q)[1−τ, 1+τ].
* Let g(u) := ∏_i ρ_s(qZ+w_i(u))/(s/q). Then g ∈ [a, b] := [(1−τ)^r, (1+τ)^r].
* By Lemma 1, the conditional laws of h given u are the same under K and D_{L,s}. The marginals satisfy
  π_D(u)/π_K(u) = g(u)/E_K[g] ∈ [a/b, b/a].
* Hence SD = ½·E_K|g/E_K g − 1| ≤ ½(b/a − 1). ∎

*At the instance.* s_r ≥ s_* = √d·q·√(ln(2n+4)/π), so s/q ≥ √(d ln(2n+4)/π) = 38.42 at 647 and 38.39 at 646. Then
πs²/q² ≥ d·ln(2n+4) ≥ 4629.9, so τ ≤ 2.0001·e^{−4629.9} < 2^{−6678}. With r ≤ 134 this gives
SD(K, D_{L,s}) < 2^{−6668}.

This is where the instance helps. BLP13's threshold only guarantees s/‖b̃_i‖ ≥ √(ln(2n+4)/π) ≈ 1.51. At that level
Klein's non-uniformity is about 1/(n+1) per coordinate, and rejection is needed. Here every head coordinate has 38×
smoothing, and every tail coordinate has a constant centre, so no non-uniformity arises there at all.

## 3. One-dimensional samplers by inversion tables (CDT)

### 3.1 The table lemma

Let S = {x_1 < … < x_N} ⊂ Z be finite, let D be a law on Z, and put G_j := D({x_1,…,x_j}), so G_N = 1 − μ with
μ := D(Z∖S). A **CDT with P bits** is a list of integers 0 ≤ T_1 ≤ … ≤ T_{N−1} ≤ T_N := 2^P. The sampler draws a
uniform U ∈ {0,…,2^P−1} and outputs x_j for the unique j with T_{j−1} ≤ U < T_j (T_0 := 0).

**Lemma 3.** If |T_j/2^P − G_j/G_N| ≤ η for all j < N, then the output law Q satisfies SD(Q, D) ≤ (N−1)η + μ.

*Proof.*
* Q(x_j) = (T_j − T_{j−1})/2^P exactly.
* Let D_S be D conditioned on S. With e_j := T_j/2^P − G_j/G_N, we have e_0 = e_N = 0 and |e_j| ≤ η. So
  2·SD(Q, D_S) = Σ_j |e_j − e_{j−1}| ≤ 2(N−1)η.
* SD(D_S, D) = μ, and the triangle inequality finishes the proof. ∎

### 3.2 Gaussian weights by a fixed-point recurrence

Fix λ := π/s². An **F-format** number is an integer X standing for X·2^{−F}. Write mul_F(a,b) := ⌊ab·2^F⌋·2^{−F}.
For a, b ∈ [0, 1] its error lies in (−2^{−F}, 0], and the result stays in [0, 1].

Suppose Ê₁ and Ê₂ are F-format numbers in [0,1] with |Ê_i − e^{−iλ}| ≤ δ_E. Define

  r̂_0 := Ê₁,  r̂_{x+1} := mul_F(r̂_x, Ê₂),  ρ̂_0 := 1,  ρ̂_{x+1} := mul_F(ρ̂_x, r̂_x)   (0 ≤ x < R).

The exact counterparts are r_x = e^{−λ(2x+1)} = r_{x−1}e^{−2λ} and ρ_{x+1} = ρ_x r_x = e^{−λ(x+1)²}.

**Lemma 4.** For 0 ≤ x ≤ R, |ρ̂_x − e^{−λx²}| ≤ ε_a := ((R+2)²/2)·(δ_E + 2^{−F}).

*Proof.*
* All values lie in [0, 1]. For a, â, b, b̂ ∈ [0,1], |âb̂ − ab| ≤ |â − a| + |b̂ − b|.
* So |r̂_{x+1} − r_{x+1}| ≤ |r̂_x − r_x| + δ_E + 2^{−F}, which gives |r̂_x − r_x| ≤ (x+1)(δ_E + 2^{−F}).
* Likewise |ρ̂_{x+1} − ρ_{x+1}| ≤ |ρ̂_x − ρ_x| + |r̂_x − r_x| + 2^{−F}.
* Summing, |ρ̂_x − ρ_x| ≤ Σ_{y<x}(y+2)(δ_E + 2^{−F}) = (x(x+3)/2)(δ_E + 2^{−F}) ≤ ((x+2)²/2)(δ_E + 2^{−F}). ∎

**Tables.** Set ρ̂(x) := ρ̂_{|x|} for |x| ≤ R. For a support S ⊆ [−R, R], form the exact partial sums
Ĝ_j := Σ_{i≤j} ρ̂(x_i) and set T_j := ⌊2^P·Ĝ_j/Ĝ_N⌋ by exact integer division. The T_j are monotone, and T_N = 2^P.
Let G'_j be the exact unnormalized partial sums and assume G'_N ≥ g₀ > Nε_a. Then
|Ĝ_j − G'_j| ≤ Nε_a and

  |T_j/2^P − G'_j/G'_N| ≤ 2Nε_a/(g₀ − Nε_a) + 2^{−P} =: η.   (3.1)

### 3.3 The two transcendental constants (Lemma 5)

Run r uses λ_r = π/s_r² = π²·2^{−r/4}/(dB²·ln(2n+4)), because s_*² = dB² ln(2n+4)/π (the first term of s_* is
the active one for n ≥ 8) and γ² = 2^{1/4}. Every quantity in the tables is a rational function of the two numbers
e^{−λ_r} and e^{−2λ_r}.

**Lemma 5.** Let G := F + 64. There is a word-RAM procedure using ≤ 2^{28} operations that outputs F-format numbers
Ê₁, Ê₂ ∈ [0,1] with |Ê_i − e^{−iλ_r}| ≤ δ_E := 2^{−F} + 2^{6.4−G}.

*Proof.* Work in G-format with truncating operations. Each multiply, divide-by-integer, quotient or integer square
root adds an error in (−2^{−G}, 0]. Additions and multiplications by small integers are exact.

* **(K1) π** by Machin's formula, π = 16·arctan(1/5) − 4·arctan(1/239).
  * Set u_0 = ⌊2^G/m⌋ and u_k = ⌊u_{k−1}/m²⌋. Then |u_k − m^{−(2k+1)}2^G| ≤ k+1, in units of 2^{−G}.
  * Each term ⌊u_k/(2k+1)⌋ has error ≤ 2·2^{−G}.
  * The alternating remainder after K terms is ≤ m^{−(2K+1)} ≤ 2^{−G} for K = 234 (m = 5) and K = 69 (m = 239).
  * So |π̂ − π| ≤ (16·469 + 4·139)·2^{−G} < 2^{13}·2^{−G}.
* **(K2) π̂²**: |π̂² − π²| ≤ 2^{13}·6.3·2^{−G} + 2^{−G} < 2^{15.7}·2^{−G}.
* **(K3) ln(2n+4)** = 10·2·atanh(1/3) + 2·atanh(x₀), where x₀ = (2n+4−1024)/(2n+4+1024). This is 137/1161 at
  n = 647 and 17/145 at n = 646.
  * atanh(p/m') = Σ_k (p/m')^{2k+1}/(2k+1). Set u_k = ⌊u_{k−1}p²/m'²⌋, with p² < 2^{15} multiplied exactly.
  * The remainder is ≤ x^{2K+1}/(1−x²) ≤ 2^{−G} for K = 343 (x = 1/3) and K = 177 (x = x₀).
  * The error is ≤ (20·687 + 2·355)·2^{−G} < 2^{13.9}·2^{−G}.
* **(K4) 2^{−r/4}.**
  * √2 via one integer square root, ⌊√(2·2^{2G})⌋, with error ≤ 2^{−G}.
  * 2^{1/4} := √(√2̂), with error ≤ 1.5·2^{−G}.
  * 2^{3/4} := mul(√2̂, 2^{1/4}^), with error ≤ 4.4·2^{−G}.
  * Then c_r = 2^{(4−r)/4}/2, with error < 2^{2.2}·2^{−G}.
* **(K5) λ̂** = (π̂²·ĉ_r)/(dB²·L̂), where dB² < 2^{32.8} is an exact integer.
  * The numerator's error is < 2^{15.8}·2^{−G}. The denominator is ≈ 2^{35.6}, with error < 2^{46.8}·2^{−G}.
  * Quotient perturbation then gives |λ̂ − λ| ≤ 2·2^{−G}, and λ < 2^{−32.2}.
* **(K6) Ê_i** = Σ_{k=0}^{35} (−iλ̂)^k/k!, with t_k := ⌊mul(t_{k−1}, iλ̂)/k⌋.
  * The per-term error is ≤ 2·2^{−G}/(1 − 2^{−31}).
  * The alternating remainder is ≤ (2^{−31})^{36} < 2^{−G}.
  * Adding |e^{−iλ̂} − e^{−iλ}| ≤ i|λ̂ − λ| gives a total error < 2^{6.4}·2^{−G}.
  * Truncating to F bits adds ≤ 2^{−F}. Clamping at 1 cannot increase the error, since e^{−iλ} < 1.

*Cost.* There are fewer than 3000 G-format operations on numbers of ≤ 2G + 64 bits, i.e. ≤ 72 limbs of 32 bits.
Schoolbook multiplication and division (Knuth Vol. 2 §4.3.1, Algorithms M and D) take ≤ 10·72² operations each.
The two bit-by-bit integer square roots take ≤ 2G·4·72 operations each. The total is < 2^{28}. ∎

### 3.4 Tail masses (Lemma 6)

**Lemma 6.** Let R ≥ s and s ≥ q.
* (a) ρ_s(Z) ≥ s, and the mass of D_{Z,s} outside [−R,R] is μ_T ≤ (s/(πR))·e^{−πR²/s²}.
* (b) For every w, the mass of D_{qZ+w,s} outside [−R,R] is
  μ_C ≤ 2e^{−πR²/s²}/((1 − e^{−2πRq/s²})·(s/q)(1−τ)).

*Proof.*
* (a) Poisson summation gives ρ_s(Z) = s·Σ_k e^{−πk²s²} ≥ s. The tail is
  2Σ_{x>R} e^{−πx²/s²} ≤ 2∫_R^∞ e^{−πt²/s²} dt ≤ (s²/(πR))e^{−πR²/s²}.
* (b) The coset points beyond R are x₀ + jq with x₀ > R, so the sum on one side is
  ≤ Σ_{j≥0} e^{−π(R+jq)²/s²} ≤ e^{−πR²/s²}/(1 − e^{−2πRq/s²}). The denominator ρ_s(qZ+w) ≥ (s/q)(1−τ) comes from
  the proof of Lemma 2. ∎

## 4. Procedure S and its cost

### 4.1 Parameters (fixed once; the same for both instances)

R := 2^{22} − 1 = 4 194 303,  F := 1024 (16 words),  P := 960 (W := 15 words),  G := F + 64.

These values are not tuned to the instance. They are the smallest whole-word precisions for which the bound
of §6 is below 2^{−125}: P = 896 would give η ≈ 2^{−896} and fail, and F = 960 would fail similarly. R is chosen so
that the tail table has 2^{23} − 1 entries.

### 4.2 Procedure S (run r)

*Precomputation (once per run).*
1. Compute Ê₁ and Ê₂ for λ_r (Lemma 5).
2. Compute ρ̂_0, …, ρ̂_R (Lemma 4).
3. **Tail table.** Take S_T = {−R, …, R} (N_T = 2^{23} − 1). Store the support values and the P-bit thresholds T_j
   from (3.1), as W words each.
4. **Coset tables.** For each c ∈ {0,…,q−1}, take S_c = {x ∈ [−R,R] : x ≡ c (mod q)}. Then
   N_c ≤ ⌊2R/q⌋ + 1 = 2520, and the S_c partition S_T. Build each table with its own normalization, as in (3.1).

*One sample y ∈ L_M.*
1. For j = 1..t: u_j ← CDT(tail table).
2. For i = 1..r:
   * acc ← Σ_j M_{ij}u_j. This is a signed word: |acc| ≤ t(q−1)R < 2^{42.71}.
   * c ← acc mod q, taken in [0, q).
   * h_i ← CDT(coset table c).
3. Write y = (h, u) to the list.

Here CDT(·) means: draw U as W RANDWORDs, then binary-search on (lo, hi) = (0, N) with ⌈log₂ N⌉ lexicographic
W-word comparisons of U against T_mid, and output the stored support value x_hi.

### 4.3 Deterministic bounds (resolves C3)

Every coordinate of every initial sample lies in [−R, R], because all supports are inside [−R, R]. An average of two
vectors in the box [−R, R]^d stays in the box, so every list vector at every step has ‖y‖_∞ ≤ R < 2^{22}. The
following follow:
* the intermediate sums y₁ + y₂ are < 2^{23};
* squared norms are ≤ dR² < 2^{53.34};
* acc is < 2^{42.71}.

There is **no overflow event**: the bounds hold with probability 1. The truncation that buys this is paid inside the
SD budget (μ in Lemma 3).

### 4.4 Operation count (Lemma 7)

Count per comparison level: compute the midpoint (2), compare W words with loads and branches (≤ 4W), update and
test the loop (3). That is ≤ 4W + 5 per level. Drawing U costs 2W, and the output load costs 4. So:

* C_T := 2W + 23(4W+5) + 4 = **1529**, using ⌈log₂(2^{23}−1)⌉ = 23 levels;
* C_C := 2W + 12(4W+5) + 4 = **814**, using ⌈log₂ 2520⌉ = 12 levels;
* the matrix–vector step costs 6 per entry (two loads, multiply, add, loop increment and test), plus 2 per row for
  the mod and the table pointer;
* writing y costs 2d.

  **C_S = t·C_T + r(C_C + 2) + 6rt + 2d,**

which gives C_S = 1 307 467 ≈ 2^{20.318} at (r,t,d) = (134, 513, 647) and 1 303 571 ≈ 2^{20.314} at (133, 513, 646).

*Precomputation per run* (Lemma 5 plus tables):
* weights: 2^{22}·2 F-format products at ≤ 5·32² operations each, so < 2^{35.4};
* prefix sums: < 2^{31};
* thresholds: 2^{24} divisions (Algorithm D, about 63 by 33 limbs) at < 2^{12.7} each, so < 2^{36.7}.

The total satisfies **C_pre ≤ 2^{40}**. Table space is ≤ 2^{24}·16 words = 2^{28} words.

## 5. Propagation through Theorem E (item (c) of the task)

**Lemma 8 (per sample).** Within a run, each sample of Procedure S has law Q_r with

  SD(Q_r, D_{L,s_r}) ≤ ε_lat := t·ε_T + r·ε_C + ½(((1+τ)/(1−τ))^r − 1),

where ε_T := (N_T−1)η_T + μ_T and ε_C := max_c (N_c−1)η_c + μ_C.

*Proof.*
* The hybrid argument goes through the coordinates in sampling order. At each step the conditional kernel of
  Procedure S (a CDT) is within ε_T or ε_C of the ideal kernel, D_{Z,s} or D_{qZ+c,s}, uniformly in the past
  (Lemma 3). Replacing kernels one at a time costs at most that much each, by coupling.
* The fully ideal process is the Klein law K. Lemma 2 bounds SD(K, D_{L,s}). ∎

**Lemma 9 (whole algorithm).** Let X be the k·M₀ samples drawn by Procedure S, and X* be independent exact
samples. Then SD(X, X*) ≤ kM₀·ε_lat. Moreover

  Pr[Procedure E with S fails] ≤ (lines 1–3 of (3.2)) + kM₀·ε_lat.

*Proof.*
* Independent samples: SD of a product is at most the sum of the SDs.
* Given its initial lists, Procedure E's list phase is a deterministic function Φ: the stable radix sort, pairing
  consecutive elements in list order, exact integer averaging, and recording minima. The output is Φ(X), and
  "fail" is the event {‖Φ(X)‖ ≠ λ₁}.
* For any event E, Pr[Φ(X) ∈ E] ≤ Pr[Φ(X*) ∈ E] + SD(X, X*).
* Theorem E's proof bounds Pr[Φ(X*) fails] by lines 1–3 of (3.2): combiner, final hit and Poissonization. Line 4
  bounds only the BLP sampler's running-time caps, and Procedure S has none. ∎

*Remarks on (c).*
* **No per-step loss.** The 40 combiner steps are post-processing, so the distance is paid once, at the input. A
  per-step accounting would be needed only if the combiner itself were approximate. Here it is exact integer
  arithmetic, and the averages are integral because paired vectors share parities.
* **The Poisson coupling inside Theorem E's analysis needs no change.** That coupling, with phantom samples,
  Lemmas 4.3 and 4.5 of Part 140, is applied only to X*, which is exact.
* **Rényi divergence is not needed.** The order-a Rényi bound Pr_real ≤ (Pr_ideal·R_a^{kM₀})^{(a−1)/a} (Prest
  2017; Bai–Langlois–Lepoint–Sakzad–Stehlé–Steinfeld 2018) would allow roughly half the precision, about 8 words
  instead of 15. That saves under 0.6 bits of total cost, at the price of a non-additive failure bound. SD is
  simpler and suffices.
* **Why not an exact sampler (option (b)).** λ_r = π²·2^{−r/4}/(dB² ln(2n+4)) is transcendental. An exact
  sampler for D_{Z,s_r} (Karney 2016; Canonne–Kamath–Steinke 2020, which need a rational σ²) would need lazily
  refined coins whose worst-case running time is unbounded. That would require caps and tail events again.
  Perturbing s_r to make σ² rational would change Theorem E's grid (§4.7), which the task forbids. The SD route
  gives a deterministic worst case.

## 6. Theorem W and the numbers

**Theorem W.** Let q = B = 3329, (r, t) ∈ {(134, 513), (133, 513)}, d = n = r + t, and let M ∈ {0..q−1}^{r×t} be
arbitrary. Run Procedure E of Part 140 on L_M with its constants (θ = 1/8, k = 4, K₀ = 800, s_*, γ = 2^{1/8},
ℓ, M₀), implementing step 2.1 by Procedure S with the parameters of §4.1. Then on the word-RAM of §1:

  T_W = k·[C_pre + M₀·(C_S + 2(10d + 2⌈d/16⌉))] + k(ℓ+1)·⌈d/16⌉·2^{17}

operations suffice in the worst case, with C_S from Lemma 7 and C_pre ≤ 2^{40}. No Gram–Schmidt computation is
needed. The output has norm λ₁(L_M) except with probability at most p₁₋₃ + kM₀·ε_lat. The term 2(10d + 2⌈d/16⌉)
per sample is Part 140's list-phase count.

*Proof.* Combine Lemmas 3–9 with Theorem E. The list-phase count and its no-overflow premise now hold
deterministically (§4.3). ∎

| Quantity | n = 647 | n = 646 |
| --- | --- | --- |
| s_*/q | 38.423 | 38.389 |
| log₂ τ | −6690.3 | −6678.5 |
| R/s_3 (largest s) | 25.29 | 25.31 |
| log₂ μ_T, log₂ μ_C | −2904.0, −2901.9 | −2909.1, −2907.0 |
| log₂ ε_a (Lemma 4) | −980.0 | −980.0 |
| log₂ η_T | −955.9 | −955.9 |
| log₂ ε_T, log₂ ε_C | −932.9, −948.7 | −932.9, −948.7 |
| log₂ ε_lat | −923.91 | −923.91 |
| log₂ kM₀ | 774.65 | 773.65 |
| **log₂ total SD** | **−149.26** | **−150.26** |
| C_S (sampler, per sample) | 1 307 467 (2^{20.318}) | 1 303 571 (2^{20.314}) |
| list phase per sample | 13 104 | 13 084 |
| **log₂ T_W** | **794.979** | **793.975** (two calls: **794.975**) |
| line 1 of (3.2) | 2^{−120.922} | 2^{−121.922} |
| **p_W** | **< 2^{−120.92}** | **< 2^{−121.92}** per call |
| space (words) | 2^{781.98} + 2^{28} | 2^{780.98} + 2^{28} |
| Part 140 real-RAM T (4nd / literal 6nd) | 799.23 / 799.81 | 798.22 |

**End to end.** Combined with Part 39 (success ≥ 99.51664%), plain LWE (511, 512, 3329) with CBD(3) is solved with
probability ≥ 0.9951664 − 2^{−120.9} in ≤ **2^{794.98} word operations**. That is 458 bits below the explicit
brute-force bound 2^{1253.40} (Part 133), which is also counted in word operations. The Part 131 two-call variant
also costs 2^{794.98}.

## 7. Audit items C1–C3 of Part 140

* **C1 (model).** Resolved for the recorded instances. Theorem W is a word-RAM theorem with no real-number oracle.
  Part 140's real-RAM count stays valid as stated for general bases, but it is no longer the headline at the
  instance.
* **C2 (6d vs 4d).**
  * In real-RAM, Part 140's (3.1) holds for the μ-coefficient implementation (4nd). The literal BLP recursion (6nd)
    gives 799.81.
  * Procedure S needs neither. On L_M the Klein centres are −(Mu)_i/q for head coordinates and 0 for tail
    coordinates. This is the μ-coefficient implementation, with μ_{j,i} = M_{ij}/q and all other μ zero, computed
    as r·t integer multiply-adds with no division until the final mod.
  * Lemma 7 counts this program line by line, so no recursion choice is left open.
* **C3 (overflow).** Removed by §4.3. The bound ‖y‖_∞ ≤ 2^{22} − 1 is deterministic, and the corresponding tail
  mass is inside ε_lat. The 2^{−833} event of Part 140 §5 is no longer needed.

## 8. Honest gap list

1. **Instance-specific.** Theorem W covers the lattices L_M (every M) at q = 3329 with r ∈ {133, 134}, t = 513.
   Those are the recorded instances. It uses s_r/q ≥ 38 (Lemma 2) and the coordinate structure. For a general
   integral basis, as in Theorem E's statement, no word-RAM bound is proved here. G1 remains open there, and BLP's
   rejection step or Klein with ε-smoothing (Part 140 G1(b), about +21 bits) would be needed.
2. **Word size.** The model is transdichotomous (w ≥ 783, needed to address 2^{782} words). All data arithmetic uses
   < 64-bit values, but list indices and addresses are about 773-bit words at unit cost. Under a fixed w = 64 with
   multiword pointers, the list phase's address arithmetic would cost more. Since a sample costs about 2^{20.3} and
   its d writes are a 2^{−10} fraction of that, the effect is plausibly under 2 bits, but it is not proved. No
   bit-complexity (Turing machine) bound is claimed.
3. **List-phase count inherited.** The term 10d + 2⌈d/16⌉ per vector-step and the 2^{17}⌈d/16⌉ per step come from
   Part 140 §4.8 (its G5 granularity, "careful counts of the obvious implementation"). They were not re-derived
   here. Only their no-overflow premise is now proved. The sampler term dominates T_W by a factor of about 100.
4. **Granularity of Lemma 7.** It counts the operations of a stated pseudo-program, not of compiled code. A 2× error
   moves log₂ T_W by 1. C_pre ≤ 2^{40} is deliberately crude and contributes nothing visible.
5. **Ideal randomness.** RANDWORD is assumed to return exactly uniform bits, as in every randomized RAM model.
6. **Cited, not re-proved.**
   * One-dimensional Poisson summation for Gaussians (Jacobi's theta transformation), used in Lemmas 2 and 6.
     Mathlib has the Jacobi theta functional equation; the exact lemma name was not re-checked.
   * Machin's formula; the series for arctan and atanh; Knuth's Algorithms M and D.
   * Theorem E itself, with its inherited gaps G2–G4. Its lemmas were audited (Part 140 Audit) but are not
     formalized.
7. **Numbers.** The §6 values come from an 80-digit `mpmath` scratch script, not committed. Lemma 2's bound
   underflows at that precision and is bounded analytically (< 2^{−6668}). The toy checks of Lemmas 2 and 3 are
   sanity checks only.
8. **Not audited.** This note has not had an independent audit. The points most worth checking are:
   * the error recursions of Lemma 4;
   * the K-values in Lemma 5;
   * (3.1) with g₀ = 1 for the tail and g₀ ≥ e^{−πq²/(4s²)} > 0.999 for the cosets;
   * the claim that Procedure E's list phase is a deterministic function of the samples (it uses no coins in
     Part 140 §2).

## References

* [Part 140] [wall1_adrs_explicit.md](wall1_adrs_explicit.md), Theorem E, (3.1)–(3.2), §2, §4.7–4.8, Audit C1–C3.
* [Part 39 / Part 131] [PROOF_GAP.md](../PROOF_GAP.md); the lattice definition is in
  [wall1_projected_reference.md](wall1_projected_reference.md).
* [BLP+13] Brakerski, Langlois, Peikert, Regev, Stehlé. Classical hardness of LWE. STOC 2013; Lemma 2.3, §5. This is
  context only: Procedure S does not use it.
* [GPV08] Gentry, Peikert, Vaikuntanathan. STOC 2008; Klein's SampleD, §4.
* [Pre17] T. Prest. Sharper bounds in lattice-based cryptography using the Rényi divergence. ASIACRYPT 2017. Cited
  only in the §5 remark.
* [BLL+18] Bai, Langlois, Lepoint, Sakzad, Stehlé, Steinfeld. Improved security proofs in lattice-based
  cryptography: using the Rényi divergence rather than the statistical distance. J. Cryptology 2018. Cited only in
  the §5 remark.
* [Kar16] C. Karney. Sampling exactly from the normal distribution. ACM TOMS 2016. [CKS20] Canonne, Kamath, Steinke.
  The discrete Gaussian for differential privacy. NeurIPS 2020. Both cited only in the §5 remark on exact samplers.
* [Knu97] D. Knuth. TAOCP Vol. 2, §4.3.1 (Algorithms M, D).
* [Hag98] T. Hagerup. Sorting and searching on the word RAM. STACS 1998 (transdichotomous model).

## Audit

Independent adversarial audit, 2026-11-22. The audit was read-only apart from this section. Scratch scripts (mpmath
at 80 digits, plus an integer toy run of Lemma 4 and (3.1)) were not committed.

**Verdict: MINOR CAVEATS.** The mathematics is sound and every number in §6 reproduces. The caveats are editorial
or about scope. None of them moves log₂ T_W or log₂ p_W by more than 0.01 bits.

### Checks performed

1. **Instance lattice (§2.1).**
   * The lattice in wall1_projected_reference.md is {(x′, y, t) ∈ Z^{r+512+1} : x′ + A′y ≡ t·b′ (mod q)}. It is the
     exact coordinate projection of the embedding after deleting k error axes; the surjectivity argument is in that
     note.
   * With u := (y, t) and M := [−A′ | b′] mod q, this is exactly L_M. The height t is an unconstrained integer
     coordinate of u, so it has Gram–Schmidt norm 1 and is sampled from D_{Z,s} like the secret coordinates. That is
     correct: the plant (e, s, 1) is the lattice point with t = 1, and the lattice does not fix t.
   * In the order {q e_i} then {(M e_j mod q, e_j)}, the Gram–Schmidt vectors are q e_i (r of them) and e_{r+j}
     (t of them). The entries lie in {0..q}, so B = q is respected, and det = q^r is odd.
   * Klein's algorithm on this basis has tail centres 0 at parameter s, and head centres −(Mu)_i/q at parameter
     s/q. So the law K of §2.2 is Klein without rejection, as claimed.
   * Part 131 uses r = 133 (PROOF_GAP Part 131), so d = 646.
2. **Lemmas 1 and 2 (no rejection).**
   * Re-derived. The Poisson identity ρ_s(qZ+w) = (s/q)Σ_k e^{−πk²s²/q²}cos(2πkw/q) holds for every real w, so it
     holds for every M.
   * π_D/π_K = g/E_K g ∈ [a/b, b/a] holds, and SD ≤ ½(b/a − 1) follows.
   * **Every sampling parameter was checked.** Initial samples are drawn only in step 2.1 of the k = 4 runs. The
     40 combiner levels per run draw no fresh samples, since Pair-and-Average has no parameter (Part 140 §4.7). At
     n = 647, s_r/q = 38.42, 41.90, 45.69 and 49.83 for r = 0..3. At n = 646 it is 38.39, 41.86, 45.65 and 49.78.
   * τ is worst at r = 0, where πs²/q² = d·ln(2n+4) = 4638.07 (647) and 4629.91 (646). That gives
     log₂ τ = −6690.32 and −6678.54, so SD(K, D_{L,s}) < 2^{−6670} < 2^{−6668} at every run.
   * The tail masses are worst at r = 3. The note correctly evaluates μ at s_3, with R/s_3 = 25.285 (647) and 25.307
     (646), so Lemma 6's hypothesis R ≥ s ≥ q holds at all four runs.
3. **CDT layer (Lemmas 3–6, (3.1)).**
   * Lemma 3: telescoping with e_0 = e_N = 0 is correct.
   * Lemma 4: re-derived, including |r̂_x − r_x| ≤ (x+1)(δ_E + 2^{−F}) and the sum Σ_{y<x}(y+2) = x(x+3)/2.
   * (3.1): re-derived from |(a+δa)/(A+δA) − a/A| ≤ (|δa|+|δA|)/(A+δA) with a ≤ A. g₀ = 1 is valid for the tail
     table (the x = 0 term). For the cosets, g₀ ≥ e^{−πq²/(4s²)} = 0.99947 > 0.999 (some x ≡ c has |x| ≤ q/2).
   * Lemma 5 K-values were re-derived:
     * Machin: K = 234 at m = 5 and K = 69 at m = 239, error 8060 < 2^{13}.
     * atanh: K = 343 at x = 1/3 and K = 177 at x₀ = 137/1161 (and 17/145 at 646), error 14450 < 2^{13.9}.
     * 2^{−r/4}: correct.
     * λ: λ ≈ 2^{−32.3}, and the quotient error ≪ 2·2^{−G}.
     * Taylor: 36 terms, error ≈ 72 + 1 + 4 < 2^{6.4}.
   * Lemma 6: (a) and (b) re-derived.
   * Toy integer run: 30 random instances with F ∈ {40, 48, 56}, P = F − 8, R ≤ 1000 and q ∈ {7, 13, 29}, comparing
     the exact Python-integer recurrence and thresholds against 60-digit references. The worst error was 1.1% of the
     Lemma 4 bound and 0.03% of the (3.1) bound.
4. **Propagation (Lemmas 8 and 9).**
   * The hybrid over coordinates is valid: each CDT kernel is within ε_T or ε_C of its ideal kernel, uniformly in
     the past.
   * Samples within and across runs use fresh RANDWORDs, and the tables are deterministic, so the product bound
     kM₀·ε_lat holds.
   * Procedure E's list phase is deterministic: a stable radix sort on the parity labels, consecutive pairing, exact
     averaging, and recording minima. It uses no coins (Part 140 §2), so data processing gives
     Pr_real[fail] ≤ Pr_ideal[fail] + SD.
   * The Poisson and phantom-sample coupling of Part 140 Lemmas 4.3b and 4.5 is applied only to the ideal X*.
     Line 4 of (3.2), the caps, is correctly dropped.
5. **Numbers (own script).**

   | Quantity | n = 647 | n = 646 |
   | --- | --- | --- |
   | log₂ ε_a | −980.00 | −980.00 |
   | log₂ η_T | −955.91 | −955.91 |
   | log₂ η_c | −959.99 | −959.99 |
   | log₂ ε_T | −932.91 | −932.91 |
   | log₂ ε_C | −948.69 | −948.69 |
   | log₂ μ_T | −2904.03 | −2909.14 |
   | log₂ μ_C | −2902.30 | −2907.41 |
   | log₂ ε_lat | −923.910 | −923.910 |
   | log₂ kM₀ | 774.646 | 773.646 |
   | log₂ total SD | −149.264 | −150.264 |
   | C_T, C_C | 1529, 814 | 1529, 814 |
   | C_S | 1 307 467 (2^{20.3183}) | 1 303 571 (2^{20.3140}) |
   | list phase per sample | 13 104 | 13 084 |
   | log₂ T_W | 794.9789 | 793.9746 (two calls 794.9746) |
   | line 1 of (3.2) | 2^{−120.92241} | 2^{−121.92241} |
   | line 1 + SD | 2^{−120.92241} < 2^{−120.92} | 2^{−121.92241} |
   | log₂ space | 781.984 | 780.982 |
   | \|acc\| bound | 2^{42.70} | 2^{42.70} |
   | dR² | 2^{53.34} | 2^{53.34} |

   C_pre ≤ 2^{40} per run is generous: I get about 2^{35.3} for the weights and about 2^{36.7} for the thresholds.
   Even k·2^{40} is invisible next to 2^{795}.
6. **Comparison with Part 140.** Part 140's per-sample cost is 2e²(4nd + 32n) + 13104 = 2^{24.579}. Here it is
   1 320 571 = 2^{20.333}. The difference is 4.246 bits, which matches 799.2253 − 794.9789 = 4.2464 (and 4.2462 at
   646). The 458.4-bit margin over 2^{1253.40} is correct.

### Issues and corrections

* **W1 (wording in §1, scope).** §1 says "all arithmetic on *data* uses values of absolute value < 2^{63}, so nothing
  depends on w beyond addressing."
  * Procedure E's radix sort keeps bucket counts and prefix sums up to M₀ ≈ 2^{772.6}. The loop counters over
    k·M₀ samples are similar. These are index-sized values (about 773 bits), not addresses.
  * Under the transdichotomous assumption w ≥ 783 they are single words, so the count is unaffected. §8.2 already
    says "list indices … about 773-bit words at unit cost".
  * *Correction:* in §1, say "all sample and vector-coordinate arithmetic uses values < 2^{63}; addresses, list
    indices and counters are w-bit words".
  * The fixed-w = 64 estimate in §8.2 ("plausibly under 2 bits") is correctly marked as unproved. I agree it is
    plausible: even a 13× surcharge on the whole list phase would add only about 0.17 bits.
* **W2 (granularity of Lemma 7).**
  * The outer loop overhead of step 1 (j-loop) and step 2 (i-loop) is not counted. That is about 2(r + t) ≈ 1300 ops
    per sample.
  * The address computation base + mid·W in the binary search is not itemized. At most +2 per level, that is about
    +50 for C_T and +25 for C_C.
  * Together these add < 0.03% to C_S, under 0.001 bits. This is covered by §8.4's granularity caveat. *Optional
    correction:* add the loop terms to C_S for completeness.
* **W3 (cosmetic table values).**
  * §6 lists log₂ μ_C = −2901.9 (647) and −2907.0 (646). Lemma 6(b) evaluates to −2902.30 and −2907.41. The note's
    values are about 0.4 bits more conservative and are dominated anyway.
  * §0 item 3 says s/q ≥ 38.38, while §2.2 says 38.39 at 646. Both are true lower bounds.
  * No effect on any headline.
* **W4 (scope, correctly stated).**
  * Theorem W is a theorem about L_M at (q, r, t) ∈ {(3329, 134, 513), (3329, 133, 513)}, for every M. It is not a
    word-RAM version of Theorem E for general bases.
  * Procedure S reads M from the basis in the stated form. So the input must be presented as the Part 39 embedding
    basis, or M must be extracted from it, which is trivial for that basis.
  * The 2^{794.98} headline should therefore always carry "at the recorded instance", as §0 item 5 and §8.1 already
    do. G1 in its general form remains open, as the note says.
* **W5 (unverifiable as written).** The toy checks mentioned in the preamble and §8.7 are not in the repository.
  This audit's own toy run covers Lemma 4 and (3.1) independently. Lemma 2 was checked analytically only.
  * One clarification would help: the coset-table normalization in (3.1) uses Ĝ_N of S_c itself. So the CDT targets
    D_{qZ+c,s} restricted to [−R, R], and μ_C pays for the truncation. The note does this correctly.

The proposed corrections are W1 (one sentence in §1) and, optionally, W2 and W3. No change to Theorem W's statement or
its numbers is needed.
