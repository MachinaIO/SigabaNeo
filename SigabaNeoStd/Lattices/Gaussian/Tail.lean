import SigabaNeoStd.Lattices.Gaussian.Smooth
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Short preimages

If the nonzero dual mass of `Λ^⊥(B)` at width `1/τ` is at most `1/2` (`dualMassE B τ ≤ 1/2`, true
for all but a `1/64` fraction of `B` by `card_bad_le`), then cslib-frontier's mass bounds give
`ρ_{2τ}(Λ + c) / ρ_τ(Λ + c) ≤ 3 · 2^m` for every center, and its tail bound
(`discreteGaussian_norm_ge_le`, comparing widths `τ` and `2τ`) gives, for every column drawn by
`cosetGauss B u τ`, `Pr[‖x‖ ≥ τ √m] ≤ 3 · 2^{−m}`.
-/

namespace SigabaNeo.Lattices

open SigabaNeo.Lattices ProbabilityTheory ZLattice MeasureTheory
open scoped ENNReal

variable {n m q : ℕ} [NeZero q]

theorem toInt_embed (y : Fin m → ℤ) : toInt (embed m y) = y := by
  funext i; simp [toInt, embed]

instance dualPerp_discrete (B : Matrix (Fin n) (Fin m) (ZMod q)) :
    DiscreteTopology (dualPerp B) :=
  discreteTopology_dualSubmodule (perp B)

theorem half_ennreal : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp

/-- A small nonzero dual mass at width `1/τ` bounds cslib-frontier's dual mass at every width
`1/t ≤ 1/τ`. -/
theorem dual_mass_le (B : Matrix (Fin n) (Fin m) (ZMod q)) {τ t : ℝ} (hτ : 0 < τ) (ht : τ ≤ t)
    (hB : dualMassE B τ ≤ 1 / 2) :
    gaussianMass (dualPerp B) (1 / t) 0 - 1 ≤ 1 / 2 := by
  have ht0 : 0 < t := lt_of_lt_of_le hτ ht
  have hs : 0 < 1 / t := by positivity
  rw [gaussianMass_zero_sub_one_eq_tsum (dualPerp B) (1 / t) hs]
  by_cases hsum : Summable (fun z : ↥{z : dualPerp B | z ≠ 0} =>
      gaussianWeight (1 / t) ((z : dualPerp B) : EuclideanSpace ℝ (Fin m)))
  swap
  · rw [tsum_eq_zero_of_not_summable hsum]; norm_num
  have hle : ENNReal.ofReal (∑' z : ↥{z : dualPerp B | z ≠ 0},
      gaussianWeight (1 / t) ((z : dualPerp B) : EuclideanSpace ℝ (Fin m))) ≤
      ENNReal.ofReal (1 / 2) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun z => (gaussianWeight_pos _ _).le) hsum,
      ← half_ennreal]
    refine le_trans ?_ hB
    refine tsum_le_tsum fun z => ENNReal.ofReal_le_ofReal ?_
    unfold gaussianWeight
    apply Real.exp_le_exp.mpr
    have hx := sq_nonneg ‖((z : dualPerp B) : EuclideanSpace ℝ (Fin m))‖
    have htt : τ ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hτ.le ht 2
    simp only [one_div, inv_pow, div_inv_eq_mul]
    nlinarith [Real.pi_pos, mul_nonneg Real.pi_pos.le hx]
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp hle

/-- Doubling the width multiplies the mass of every coset by at most `3 · 2^m`. -/
theorem mass_ratio_le (B : Matrix (Fin n) (Fin m) (ZMod q)) {τ : ℝ} (hτ : 0 < τ)
    (hB : dualMassE B τ ≤ 1 / 2) (c : EuclideanSpace ℝ (Fin m)) :
    gaussianMass (perp B) (2 * τ) c / gaussianMass (perp B) τ c ≤ 3 * 2 ^ m := by
  have h1 := gaussianMass_mem_Icc_of_dual_mass_le (perp B) τ hτ (1 / 2)
    (dual_mass_le B hτ le_rfl hB) c
  have h2 := gaussianMass_mem_Icc_of_dual_mass_le (perp B) (2 * τ) (by positivity) (1 / 2)
    (dual_mass_le B hτ (by linarith) hB) c
  rw [finrank_euclideanSpace_fin] at h1 h2
  rw [div_le_iff₀ (gaussianMass_pos _ _ hτ c)]
  calc gaussianMass (perp B) (2 * τ) c
      ≤ (2 * τ) ^ m / covolume (perp B) * (1 + 1 / 2) := h2.2
    _ = 3 * 2 ^ m * (τ ^ m / covolume (perp B) * (1 - 1 / 2)) := by rw [mul_pow]; ring
    _ ≤ 3 * 2 ^ m * gaussianMass (perp B) τ c := by gcongr; exact h1.1

theorem exp_neg_nine_quarters : Real.exp (-(9 / 4)) ≤ 1 / 4 := by
  have h := Real.quadratic_le_exp_of_nonneg (x := 9 / 4) (by norm_num)
  have hinv : Real.exp (-(9 / 4)) * Real.exp (9 / 4) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (-(9 / 4))]

/-- The tail of the discrete Gaussian on a coset of `Λ^⊥(B)`, at radius `τ √M`. -/
theorem gauss_tail_gen (B : Matrix (Fin n) (Fin m) (ZMod q)) {τ : ℝ} (hτ : 0 < τ)
    (hB : dualMassE B τ ≤ 1 / 2) (c : EuclideanSpace ℝ (Fin m)) (M : ℕ) :
    (discreteGaussian (perp B) τ hτ c).toOuterMeasure
        {z : perp B | τ * Real.sqrt M ≤ ‖(z : EuclideanSpace ℝ (Fin m)) - c‖} ≤
      ENNReal.ofReal (3 * 2 ^ m * (1 / 4) ^ M) := by
  have h := discreteGaussian_norm_ge_le (perp B) τ hτ (2 * τ) (by linarith) c
    (τ * Real.sqrt M) (by positivity)
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hexp : -Real.pi * (1 / τ ^ 2 - 1 / (2 * τ) ^ 2) * (τ * Real.sqrt M) ^ 2 =
      -(3 * Real.pi / 4) * M := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg M)]
    field_simp
    ring
  rw [hexp]
  have hE : Real.exp (-(3 * Real.pi / 4) * M) ≤ (1 / 4) ^ M := by
    calc Real.exp (-(3 * Real.pi / 4) * M) ≤ Real.exp (M * (-(9 / 4))) := by
          apply Real.exp_le_exp.mpr
          have := Real.pi_gt_three
          have hm : (0 : ℝ) ≤ M := Nat.cast_nonneg M
          nlinarith
      _ = Real.exp (-(9 / 4)) ^ M := Real.exp_nat_mul _ _
      _ ≤ (1 / 4) ^ M := pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_nine_quarters M
  have hr := mass_ratio_le B hτ hB c
  have hr0 : 0 ≤ gaussianMass (perp B) (2 * τ) c / gaussianMass (perp B) τ c :=
    div_nonneg (gaussianMass_pos _ _ (by positivity) c).le (gaussianMass_pos _ _ hτ c).le
  calc Real.exp (-(3 * Real.pi / 4) * M) *
        (gaussianMass (perp B) (2 * τ) c / gaussianMass (perp B) τ c)
      ≤ (1 / 4) ^ M * (3 * 2 ^ m) := mul_le_mul hE hr hr0 (by positivity)
    _ = 3 * 2 ^ m * (1 / 4) ^ M := by ring

/-- The tail at radius `τ √m`. -/
theorem gauss_tail (B : Matrix (Fin n) (Fin m) (ZMod q)) {τ : ℝ} (hτ : 0 < τ)
    (hB : dualMassE B τ ≤ 1 / 2) (c : EuclideanSpace ℝ (Fin m)) :
    (discreteGaussian (perp B) τ hτ c).toOuterMeasure
        {z : perp B | τ * Real.sqrt m ≤ ‖(z : EuclideanSpace ℝ (Fin m)) - c‖} ≤
      ENNReal.ofReal (3 * (1 / 2) ^ m) := by
  refine (gauss_tail_gen B hτ hB c m).trans (le_of_eq ?_)
  congr 1
  rw [show (1 / 2 : ℝ) = 1 / 4 * 2 by norm_num, mul_pow]; ring

/-- Every column drawn by `cosetGauss B u τ` is shorter than `τ √m`, except with probability at
most `3 · 2^{−m}`. -/
theorem cosetGauss_tail (B : Matrix (Fin n) (Fin m) (ZMod q)) (u : Fin n → ZMod q) {τ : ℝ}
    (hτ : 0 < τ) (hB : dualMassE B τ ≤ 1 / 2) {d : PMF (Fin m → ℤ)}
    (hd : cosetGauss B u τ hτ = some d) :
    d.toOuterMeasure {x | τ * Real.sqrt m ≤ ‖embed m x‖} ≤ ENNReal.ofReal (3 * (1 / 2) ^ m) := by
  unfold cosetGauss at hd
  split_ifs at hd with h
  obtain rfl := Option.some.inj hd
  have hb : (ZLattice.discreteGaussian (perp B) τ hτ (-(embed m h.choose)) >>= fun a =>
      pure (a : EuclideanSpace ℝ (Fin m))) =
      (ZLattice.discreteGaussian (perp B) τ hτ (-(embed m h.choose))).map Subtype.val := rfl
  rw [PMF.toOuterMeasure_map_apply, hb, PMF.toOuterMeasure_map_apply]
  refine le_trans (measure_mono ?_) (gauss_tail B hτ hB _)
  intro z hz
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hz ⊢
  obtain ⟨y, -, hy⟩ := Submodule.mem_map.mp z.2
  have : embed m (h.choose + toInt (z : EuclideanSpace ℝ (Fin m))) =
      (z : EuclideanSpace ℝ (Fin m)) - -embed m h.choose := by
    rw [map_add, ← hy, toInt_embed, sub_neg_eq_add, add_comm]
  rwa [this] at hz

end SigabaNeo.Lattices
