import SigabaNeoStd.Lattices.Automorphism.Basis

/-!
# Lookup tables over exponents (Lemma 8 of ePrint 2026/2539), over an abstract `ExpRing`

For a table `L : ℕ → ℕ` (read on `[0, W)`) and an index `k`,

  `alpha E L k = W⁻¹ Σ_{j<W} X^{L j} σ_k(X^{2n − j})`,  `vcoef E L k = W⁻¹ Σ_{j<W} L j · σ_k(X^{2n − j})`

(`X^{2n − j} = X^{−j}` since `X^{2n} = 1`), both instances of `lutCoef E c k` for values
`c : ℕ → R`. Main results:

* `sum_σ_hIdx_pow_sub`: the selection `Σ_{k∈H} σ_k(X^{2n − j + u}) = W · [j = u]` for `j, u < W`.
* **`lut_hIdx`**, `lut_alpha_hIdx`, `lut_vcoef_hIdx`: `Σ_{k∈H} lutCoef E c k · σ_k(X^u) = c u`, so
  `Σ_{k∈H} α_{k,L} σ_k(X^u) = X^{L u}` and `Σ_{k∈H} v_{k,L} σ_k(X^u) = L u`, for `u < W`.
* With the binary basis (`W = 2^b`, `2W ∣ n`, `g = gGen n W = 1 + 2n/W`):
  `sum_σ_pow_gGen` (reindexing `H = {g^i : i < W}` modulo `2n`), **`lut_pow`**, `lut_alpha_pow`,
  `lut_vcoef_pow` (the same identities summed over `σ_{g^i}`, `i < W`).
* The rounds: `σ_pow_add` (`σ_{g^(i + 2^j)} = σ_{g^(2^j)} ∘ σ_{g^i}`, with `range_two_pow_succ`
  this is `H_{j+1} = H_j ∪ H_j · g_j`), `σ_foldr`, **`σ_pow_bits`**
  (`σ_{g^i} = σ_{g^(2^{j_1})} ∘ ⋯ ∘ σ_{g^(2^{j_t})}` over the bits `j_1 < ⋯ < j_t` of `i < 2^b`),
  and `sum_two_pow_testBit_list`.
-/

namespace SigabaNeo.Lattices

namespace ExpRing

open Finset

variable {R : Type*} [CommRing R] (E : ExpRing R)

theorem X_pow_two_n : E.X ^ (2 * E.n) = 1 := by
  rw [mul_comm, pow_mul, E.X_pow_n]; simp

theorem σ_add_mul (k m : ℕ) : E.σ (k + 2 * E.n * m) = E.σ k := by
  induction m with
  | zero => simp
  | succ m ih => rw [mul_add, mul_one, ← add_assoc, E.σ_period, ih]

/-- `σ_k` depends on `k` modulo `2n`. -/
theorem σ_mod (k : ℕ) : E.σ (k % (2 * E.n)) = E.σ k := by
  conv_rhs => rw [← Nat.mod_add_div k (2 * E.n), E.σ_add_mul]

/-- The table coefficient `W⁻¹ Σ_{j<W} c_j φ(X^{2n − j})` of the values `c` for the
endomorphism `φ`. -/
def lutCoefOf (c : ℕ → R) (φ : R →+* R) : R :=
  E.Winv * ∑ j ∈ range E.W, c j * φ (E.X ^ (2 * E.n - j))

/-- The table coefficient `W⁻¹ Σ_{j<W} c_j σ_k(X^{2n − j})` of the values `c`. -/
def lutCoef (c : ℕ → R) (k : ℕ) : R := E.lutCoefOf c (E.σ k)

/-- `α_{k,L} = W⁻¹ Σ_{j<W} X^{L(j)} σ_k(X^{−j})`. -/
def alpha (L : ℕ → ℕ) (k : ℕ) : R := E.lutCoef (fun j => E.X ^ L j) k

/-- `v_{k,L} = W⁻¹ Σ_{j<W} L(j) σ_k(X^{−j})`. -/
def vcoef (L : ℕ → ℕ) (k : ℕ) : R := E.lutCoef (fun j => (L j : R)) k

theorem alpha_def (L : ℕ → ℕ) (k : ℕ) :
    E.alpha L k = E.Winv * ∑ j ∈ range E.W, E.X ^ L j * E.σ k (E.X ^ (2 * E.n - j)) := rfl

theorem vcoef_def (L : ℕ → ℕ) (k : ℕ) :
    E.vcoef L k = E.Winv * ∑ j ∈ range E.W, (L j : R) * E.σ k (E.X ^ (2 * E.n - j)) := rfl

/-- `W ∣ 2n − j + u` iff `j = u`, for `j, u < W ∣ n`. -/
theorem dvd_two_n_sub_add_iff {j u : ℕ} (hj : j < E.W) (hu : u < E.W) :
    E.W ∣ 2 * E.n - j + u ↔ j = u := by
  obtain ⟨t, ht⟩ := E.W_dvd
  have hW := E.W_pos
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · have := E.n_pos; rw [ht, h, mul_zero] at this; omega
    · exact h
  have hsplit : 2 * E.n - j + u = E.W * (2 * t - 1) + (E.W + u - j) := by
    rw [ht]
    have : E.W * (2 * t - 1) + E.W = 2 * (E.W * t) := by
      rw [← Nat.mul_succ, show (2 * t - 1).succ = 2 * t by omega]; ring
    have h2 : E.W ≤ 2 * (E.W * t) := by nlinarith
    omega
  rw [hsplit, Nat.dvd_add_right (dvd_mul_right _ _)]
  constructor
  · rintro ⟨s, hs⟩
    rcases Nat.lt_or_ge s 2 with h | h
    · rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl <;>
        simp only [mul_zero, mul_one] at hs <;> omega
    · have : E.W * 2 ≤ E.W * s := Nat.mul_le_mul_left _ h
      omega
  · rintro rfl; exact ⟨1, by omega⟩

/-- **Selection**: `Σ_{k∈H} σ_k(X^{2n − j + u}) = W · [j = u]` for `j, u < W`. -/
theorem sum_σ_hIdx_pow_sub {j u : ℕ} (hj : j < E.W) (hu : u < E.W) :
    ∑ i ∈ range E.W, E.σ (hIdx E.n E.W i) (E.X ^ (2 * E.n - j + u)) =
      if j = u then (E.W : R) else 0 := by
  rw [E.sieve]
  by_cases h : j = u
  · rw [if_pos ((E.dvd_two_n_sub_add_iff hj hu).mpr h), if_pos h]
    subst h
    rw [Nat.sub_add_cancel (by have := E.W_lt; omega), E.X_pow_two_n, mul_one]
  · rw [if_neg (fun h' => h ((E.dvd_two_n_sub_add_iff hj hu).mp h')), if_neg h]

/-- **Lemma 8** (general values): `Σ_{k∈H} lutCoef E c k · σ_k(X^u) = c u` for `u < W`. -/
theorem lut_hIdx (c : ℕ → R) {u : ℕ} (hu : u < E.W) :
    ∑ i ∈ range E.W, E.lutCoef c (hIdx E.n E.W i) * E.σ (hIdx E.n E.W i) (E.X ^ u) = c u := by
  have hstep : ∀ i, E.lutCoef c (hIdx E.n E.W i) * E.σ (hIdx E.n E.W i) (E.X ^ u) =
      ∑ j ∈ range E.W, E.Winv * c j * E.σ (hIdx E.n E.W i) (E.X ^ (2 * E.n - j + u)) := by
    intro i
    rw [lutCoef, lutCoefOf, mul_assoc, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add, map_mul]; ring
  simp only [hstep]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  have hsel : ∀ j ∈ range E.W, E.Winv * c j *
      ∑ i ∈ range E.W, E.σ (hIdx E.n E.W i) (E.X ^ (2 * E.n - j + u)) =
        if j = u then E.Winv * c j * E.W else 0 := by
    intro j hj
    rw [E.sum_σ_hIdx_pow_sub (Finset.mem_range.mp hj) hu]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hsel, Finset.sum_ite_eq' (range E.W) u, if_pos (Finset.mem_range.mpr hu),
    mul_comm E.Winv, mul_assoc, mul_comm E.Winv, E.W_mul_Winv, mul_one]

/-- **Lemma 8**: `Σ_{k∈H} α_{k,L} σ_k(X^u) = X^{L(u)}` for `u < W`. -/
theorem lut_alpha_hIdx (L : ℕ → ℕ) {u : ℕ} (hu : u < E.W) :
    ∑ i ∈ range E.W, E.alpha L (hIdx E.n E.W i) * E.σ (hIdx E.n E.W i) (E.X ^ u) =
      E.X ^ L u :=
  E.lut_hIdx _ hu

/-- **Lemma 8**: `Σ_{k∈H} v_{k,L} σ_k(X^u) = L(u)` for `u < W`. -/
theorem lut_vcoef_hIdx (L : ℕ → ℕ) {u : ℕ} (hu : u < E.W) :
    ∑ i ∈ range E.W, E.vcoef L (hIdx E.n E.W i) * E.σ (hIdx E.n E.W i) (E.X ^ u) = (L u : R) :=
  E.lut_hIdx _ hu

/-! ### The binary basis -/

/-- **Reindexing `H = {g^i mod 2n : i < W}`**: any function of `σ_k` summed over `k ∈ H` is the
same summed over `σ_{g^i}`, `i < W` (`W = 2^b`, `2W ∣ n`). -/
theorem sum_σ_pow_gGen {M : Type*} [AddCommMonoid M] {b : ℕ} (hb : E.W = 2 ^ b)
    (h2 : 2 * E.W ∣ E.n) (F : (R →+* R) → M) :
    ∑ i ∈ range E.W, F (E.σ (gGen E.n E.W ^ i)) = ∑ j ∈ range E.W, F (E.σ (hIdx E.n E.W j)) := by
  rw [hb] at h2 ⊢
  have hn := E.n_pos
  calc ∑ i ∈ range (2 ^ b), F (E.σ (gGen E.n (2 ^ b) ^ i))
      = ∑ i ∈ range (2 ^ b), F (E.σ (gGen E.n (2 ^ b) ^ i % (2 * E.n))) :=
        Finset.sum_congr rfl fun i _ => by rw [E.σ_mod]
    _ = ∑ x ∈ (range (2 ^ b)).image (fun i => gGen E.n (2 ^ b) ^ i % (2 * E.n)), F (E.σ x) :=
        (Finset.sum_image (f := fun x => F (E.σ x)) (pow_gGen_mod_injOn h2 hn)).symm
    _ = ∑ x ∈ (range (2 ^ b)).image (fun j => hIdx E.n (2 ^ b) j % (2 * E.n)), F (E.σ x) := by
        rw [image_pow_gGen h2 hn]
    _ = ∑ j ∈ range (2 ^ b), F (E.σ (hIdx E.n (2 ^ b) j % (2 * E.n))) :=
        Finset.sum_image (f := fun x => F (E.σ x)) (hIdx_mod_injOn h2 hn)
    _ = ∑ j ∈ range (2 ^ b), F (E.σ (hIdx E.n (2 ^ b) j)) :=
        Finset.sum_congr rfl fun j _ => by rw [E.σ_mod]

/-- **Lemma 8 over the binary basis** (general values):
`Σ_{i<W} lutCoef E c (g^i) · σ_{g^i}(X^u) = c u` for `u < W`. -/
theorem lut_pow {b : ℕ} (hb : E.W = 2 ^ b) (h2 : 2 * E.W ∣ E.n) (c : ℕ → R) {u : ℕ}
    (hu : u < E.W) :
    ∑ i ∈ range E.W, E.lutCoef c (gGen E.n E.W ^ i) * E.σ (gGen E.n E.W ^ i) (E.X ^ u) = c u := by
  rw [← E.lut_hIdx c hu]
  exact E.sum_σ_pow_gGen hb h2 (fun φ => E.lutCoefOf c φ * φ (E.X ^ u))

/-- **Lemma 8 over the binary basis**: `Σ_{i<W} α_{g^i,L} σ_{g^i}(X^u) = X^{L(u)}`. -/
theorem lut_alpha_pow {b : ℕ} (hb : E.W = 2 ^ b) (h2 : 2 * E.W ∣ E.n) (L : ℕ → ℕ) {u : ℕ}
    (hu : u < E.W) :
    ∑ i ∈ range E.W, E.alpha L (gGen E.n E.W ^ i) * E.σ (gGen E.n E.W ^ i) (E.X ^ u) =
      E.X ^ L u :=
  E.lut_pow hb h2 _ hu

/-- **Lemma 8 over the binary basis**: `Σ_{i<W} v_{g^i,L} σ_{g^i}(X^u) = L(u)`. -/
theorem lut_vcoef_pow {b : ℕ} (hb : E.W = 2 ^ b) (h2 : 2 * E.W ∣ E.n) (L : ℕ → ℕ) {u : ℕ}
    (hu : u < E.W) :
    ∑ i ∈ range E.W, E.vcoef L (gGen E.n E.W ^ i) * E.σ (gGen E.n E.W ^ i) (E.X ^ u) =
      (L u : R) :=
  E.lut_pow hb h2 _ hu

/-! ### Rounds -/

/-- One round: `σ_{x^(i + 2^j)} = σ_{x^(2^j)} ∘ σ_{x^i}` for odd `x` (with `x = g`:
`H_{j+1} = H_j ∪ H_j · g_j`, `range_two_pow_succ`). -/
theorem σ_pow_add {x : ℕ} (hx : Odd x) (i j : ℕ) :
    E.σ (x ^ (i + 2 ^ j)) = (E.σ (x ^ (2 ^ j))).comp (E.σ (x ^ i)) := by
  rw [E.σ_comp _ _ hx.pow hx.pow, ← pow_add, add_comm]

/-- Composing `σ_{x^(2^j)}` over a list of `j`s is `σ_{x^(Σ 2^j)}`. -/
theorem σ_foldr {x : ℕ} (hx : Odd x) (l : List ℕ) (φ : R →+* R) :
    l.foldr (fun j f => (E.σ (x ^ (2 ^ j))).comp f) φ =
      (E.σ (x ^ (l.map (2 ^ ·)).sum)).comp φ := by
  induction l with
  | nil => simp [E.σ_one]
  | cons j l ih =>
    rw [List.foldr_cons, ih, ← RingHom.comp_assoc, E.σ_comp _ _ hx.pow hx.pow, ← pow_add,
      List.map_cons, List.sum_cons]

/-- The bits of `i` below `b` (as a list) sum to `i mod 2^b`. -/
theorem sum_two_pow_testBit_list (i b : ℕ) :
    (((List.range b).filter (fun j => i.testBit j)).map (2 ^ ·)).sum = i % 2 ^ b := by
  induction b with
  | zero => simp [Nat.mod_one]
  | succ b ih =>
    have hsplit : i % 2 ^ (b + 1) = i % 2 ^ b + 2 ^ b * (i / 2 ^ b % 2) := by
      rw [pow_succ, Nat.mod_mul]
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, ih, hsplit]
    by_cases hb : i.testBit b
    · have hb' := hb
      rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq] at hb'
      simp [hb, hb']
    · have : i / 2 ^ b % 2 = 0 := by
        rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq] at hb; omega
      simp [hb, this]

/-- **The binary-basis decomposition of `σ_{g^i}`**: for odd `x` and `i < 2^b`,
`σ_{x^i}` is the composition of `σ_{x^(2^j)}` over the bits `j < b` of `i`. -/
theorem σ_pow_bits {x : ℕ} (hx : Odd x) {i b : ℕ} (hi : i < 2 ^ b) :
    E.σ (x ^ i) = ((List.range b).filter (fun j => i.testBit j)).foldr
      (fun j f => (E.σ (x ^ (2 ^ j))).comp f) (RingHom.id R) := by
  rw [E.σ_foldr hx, sum_two_pow_testBit_list, Nat.mod_eq_of_lt hi, RingHom.comp_id]

end ExpRing

end SigabaNeo.Lattices
