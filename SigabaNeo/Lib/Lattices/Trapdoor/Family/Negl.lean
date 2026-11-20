import SigabaNeo.Lib.Lattices.Trapdoor.Family.Const
import CslibFrontier.Crypto.Negligible.Dyadic

/-!
# Trapdoor sampler: the error is negligible

With `ε = 2^{−κ}`: `a₁/b₁ ≥ 1 − 24ε` (`ratio_ge`), so `(a₁/b₁)^m ≥ 1 − 24 m ε`; `2θ ≤ 3 m³ ε`,
the tails are at most `72 m ε` and `3ε`, and `ε_LHL ≤ m ε`. Hence
`k · colErr + ε_LHL ≤ 200 (m + 1)^4 ε` (`err_le`), which is negligible, and with `SmoothCond`
(eventually true) the sampled `(B, K)` is negligibly close to uniform `B` with Gaussian
preimages (`joint_negligible`).
-/

namespace SigabaNeo.Lattices.Trapdoor.Family

open SigabaNeo.Lattices Cslib Cslib.Crypto Cslib.Probability
open scoped ENNReal NNReal

theorem one_sub_mul_le' (X W : ℝ≥0∞) (hW : W ≤ 1) : 1 - X * W ≤ (1 - X) + (1 - W) := by
  rw [tsub_le_iff_right]
  have h1 : W ≤ X * W + (1 - X) := by
    by_cases hX : 1 ≤ X
    · calc W = 1 * W := (one_mul W).symm
        _ ≤ X * W := mul_le_mul_left hX W
        _ ≤ _ := le_self_add
    · push Not at hX
      calc W = X * W + (1 - X) * W := by rw [← add_mul, add_tsub_cancel_of_le hX.le, one_mul]
        _ ≤ X * W + (1 - X) * 1 := add_le_add le_rfl (mul_le_mul_right hW _)
        _ = X * W + (1 - X) := by rw [mul_one]
  calc (1 : ℝ≥0∞) ≤ (1 - W) + W := le_tsub_add
    _ ≤ (1 - W) + (X * W + (1 - X)) := add_le_add le_rfl h1
    _ = (1 - X) + (1 - W) + X * W := by ring

theorem one_sub_le_ofReal {X : ℝ≥0∞} {y : ℝ} (_hy : 0 ≤ y) (h : ENNReal.ofReal (1 - y) ≤ X) :
    1 - X ≤ ENNReal.ofReal y := by
  refine (tsub_le_tsub_left h 1).trans ?_
  by_cases hy1 : y ≤ 1
  · rw [one_sub_ofReal _ (by linarith)]; exact ENNReal.ofReal_le_ofReal (by linarith)
  · push Not at hy1
    exact tsub_le_self.trans (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hy1.le)

section
variable (κ : ℕ)

theorem qU_le : qU κ ≤ εκ κ / 4 := by
  unfold qU εκ
  calc (1 / 4 : ℝ) ^ (κ + 1) = (1 / 4) ^ κ / 4 := by ring
    _ ≤ (1 / 2) ^ κ / 4 :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (by norm_num) (by norm_num) κ) (by norm_num)
    _ = 1 / 2 ^ κ / 4 := by rw [one_div_pow]

theorem ζ_eq : qU κ * (5 * τ κ) = 10 * εκ κ := by
  unfold qU εκ τ
  rw [pow_succ, one_div_pow, show (4 : ℝ) ^ κ = 2 ^ κ * 2 ^ κ by rw [← mul_pow]; norm_num, pow_add]
  field_simp; ring

/-- `a₁ / b₁ ≥ 1 − 24ε`, in reals. -/
noncomputable def ratioR : ℝ := ((1 - qU κ) / uR κ) / (uR κ + qU κ * (5 * τ κ))

theorem ratio_pos : 0 < ratioR κ := by
  have hu := (u_bounds κ).1
  have hq := qU_le κ
  have he := εκ_le_one κ
  unfold ratioR
  have : 0 < 1 - qU κ := by linarith
  have hz : 0 ≤ qU κ * (5 * τ κ) := by rw [ζ_eq]; have := εκ_pos κ; linarith
  positivity

theorem ratio_ge : 1 - 24 * εκ κ ≤ ratioR κ := by
  obtain ⟨hu1, hu2⟩ := u_bounds κ
  have hq := qU_le κ
  have hq0 : 0 ≤ qU κ := by unfold qU; positivity
  have hε := εκ_pos κ
  have he := εκ_le_one κ
  unfold ratioR
  rw [ζ_eq, div_div, le_div_iff₀ (by nlinarith)]
  have hD : uR κ * (uR κ + 10 * εκ κ) ≤ 1 + 23 * εκ κ := by nlinarith
  by_cases h24 : 0 ≤ 1 - 24 * εκ κ
  · nlinarith
  · push Not at h24
    have : 0 ≤ uR κ * (uR κ + 10 * εκ κ) := by positivity
    nlinarith

theorem X_ge : ENNReal.ofReal (1 - 24 * m κ * εκ κ) ≤ a1 κ ^ m κ * (b1 κ ^ m κ)⁻¹ := by
  have hr := ratio_pos κ
  have hu := (u_bounds κ).1
  have hb : 0 < uR κ + qU κ * (5 * τ κ) := by
    have : 0 ≤ qU κ * (5 * τ κ) := by unfold qU; have := τ_pos κ; positivity
    linarith
  have ha0 : 0 ≤ (1 - qU κ) / uR κ := le_of_lt (by
    have := ratio_pos κ; unfold ratioR at this; exact (div_pos_iff_of_pos_right hb).mp this)
  calc ENNReal.ofReal (1 - 24 * m κ * εκ κ) ≤ ENNReal.ofReal (ratioR κ ^ m κ) := by
        apply ENNReal.ofReal_le_ofReal
        have h := one_add_mul_le_pow (a := ratioR κ - 1) (by linarith) (m κ)
        have hg := ratio_ge κ
        have hm : (0 : ℝ) ≤ m κ := Nat.cast_nonneg _
        rw [add_sub_cancel] at h
        nlinarith
    _ = ENNReal.ofReal ((1 - qU κ) / uR κ) ^ m κ *
          (ENNReal.ofReal (uR κ + qU κ * (5 * τ κ)) ^ m κ)⁻¹ := by
        rw [← ENNReal.ofReal_pow ha0, ← ENNReal.ofReal_pow hb.le,
          ← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        unfold ratioR
        rw [div_pow, div_eq_mul_inv]
    _ ≤ a1 κ ^ m κ * (b1 κ ^ m κ)⁻¹ := by
        refine mul_le_mul' (pow_le_pow_left₀ bot_le (a1_ge κ) _) ?_
        exact ENNReal.inv_le_inv.mpr (pow_le_pow_left₀ bot_le (b1_le κ) _)

theorem θT_le : 2 * θT κ ≤ 3 * (m κ : ℝ) ^ 3 * εκ κ := by
  have hmb : (mb κ : ℝ) ≤ m κ := by exact_mod_cast (show mb κ ≤ m κ by rw [m_eq_mb]; omega)
  have hmb0 : (0 : ℝ) ≤ mb κ := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m κ := Nat.cast_nonneg _
  have hτ1 := one_le_τ κ
  have hτ : τ κ = 8 * 2 ^ κ := by unfold τ; rw [pow_add]; ring
  have h2 : (0 : ℝ) < 2 ^ κ := by positivity
  unfold θT Rr εκ
  have hsq : (mb κ : ℝ) ^ 2 + 2 * (τ κ * m κ) * mb κ ≤ 3 * τ κ * (m κ) ^ 2 := by
    have : (mb κ : ℝ) ^ 2 ≤ τ κ * (m κ) ^ 2 := by nlinarith
    have h2 : 2 * (τ κ * m κ) * mb κ ≤ 2 * (τ κ * m κ) * m κ :=
      mul_le_mul_of_nonneg_left hmb (by have := τ_pos κ; positivity)
    nlinarith
  have hπ := Real.pi_le_four
  have hp0 := Real.pi_pos
  have hA : Real.pi * m κ * ((mb κ : ℝ) ^ 2 + 2 * (τ κ * m κ) * mb κ) ≤
      3 / 2 * (m κ : ℝ) ^ 3 * (1 / 2 ^ κ) * τ κ ^ 2 := by
    have e : 3 / 2 * (m κ : ℝ) ^ 3 * (1 / 2 ^ κ) * τ κ ^ 2 = 4 * m κ * (3 * τ κ * (m κ) ^ 2) := by
      rw [hτ]; field_simp; try ring
    rw [e]
    have := mul_le_mul hπ hsq (by positivity) (by norm_num)
    nlinarith
  have hτ2 : 0 < τ κ ^ 2 := by positivity
  calc 2 * (Real.pi * m κ * ((mb κ : ℝ) ^ 2 + 2 * (τ κ * m κ) * mb κ) / τ κ ^ 2)
      ≤ 2 * (3 / 2 * (m κ : ℝ) ^ 3 * (1 / 2 ^ κ) * τ κ ^ 2 / τ κ ^ 2) := by
        gcongr
    _ = 3 * (m κ : ℝ) ^ 3 * (1 / 2 ^ κ) := by field_simp

theorem tgV_le : tgV κ ≤ ENNReal.ofReal (72 * m κ * εκ κ) := by
  have hε := εκ_pos κ
  have he := εκ_le_one κ
  have hbU : uR κ + qU κ * (5 * τ κ) ≤ 12 := by rw [ζ_eq]; have := (u_bounds κ).2; linarith
  have hb0 : 0 ≤ uR κ + qU κ * (5 * τ κ) := by have := (u_bounds κ).1; rw [ζ_eq]; linarith
  have h4 : (1 / 4 : ℝ) ^ m κ ≤ εκ κ := by
    unfold εκ; rw [one_div_pow]
    apply one_div_le_one_div_of_le (by positivity)
    calc (2 : ℝ) ^ κ ≤ 2 ^ m κ := pow_le_pow_right₀ (by norm_num) (by
          have : κ ≤ m κ := by unfold m n w; nlinarith
          exact this)
      _ ≤ 4 ^ m κ := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  unfold tgV
  calc (m κ : ℝ≥0∞) * (b1 κ * ENNReal.ofReal (6 * (1 / 4) ^ m κ))
      ≤ ENNReal.ofReal (m κ) * (ENNReal.ofReal (uR κ + qU κ * (5 * τ κ)) *
          ENNReal.ofReal (6 * (1 / 4) ^ m κ)) := by
        rw [ENNReal.ofReal_natCast]
        exact mul_le_mul_right (mul_le_mul_left (b1_le κ) _) _
    _ = ENNReal.ofReal (m κ * ((uR κ + qU κ * (5 * τ κ)) * (6 * (1 / 4) ^ m κ))) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul hb0]
    _ ≤ ENNReal.ofReal (72 * m κ * εκ κ) := by
        apply ENNReal.ofReal_le_ofReal
        have hm0 : (0 : ℝ) ≤ m κ := Nat.cast_nonneg _
        have h6 : 0 ≤ 6 * (1 / 4 : ℝ) ^ m κ := by positivity
        have := mul_le_mul hbU (show 6 * (1 / 4 : ℝ) ^ m κ ≤ 6 * εκ κ by linarith) h6 (by norm_num)
        nlinarith

theorem tail_le : 3 * 2 ^ m κ * (1 / 4 : ℝ) ^ (m κ ^ 2) ≤ 3 * εκ κ := by
  have hm : κ ≤ m κ := by unfold m n w; nlinarith
  have hm2 : 2 * m κ ≤ m κ ^ 2 := by have := m_ge_four κ; nlinarith
  unfold εκ
  rw [one_div_pow, mul_one_div, show (4 : ℝ) ^ (m κ ^ 2) = 2 ^ (2 * m κ ^ 2) by
    rw [pow_mul]; norm_num]
  rw [mul_div_assoc, mul_le_mul_iff_right₀ (by norm_num), div_le_div_iff₀ (by positivity)
    (by positivity), one_mul, ← pow_add]
  exact pow_le_pow_right₀ (by norm_num) (by nlinarith)

theorem εLHL_le : εLHL κ ≤ m κ * εκ κ := by
  have hq : (q κ : ℝ) ≤ 2 ^ (w κ + 1) := by
    have := (exists_q κ).choose_spec.2.2
    rw [pow_succ]; exact_mod_cast (show q κ ≤ 2 ^ w κ * 2 by unfold q; omega)
  have hqn : (q κ : ℝ) ^ n κ * (3 / 8) ^ mb κ ≤ (3 / 4) ^ mb κ := by
    calc (q κ : ℝ) ^ n κ * (3 / 8) ^ mb κ ≤ (2 ^ (w κ + 1)) ^ n κ * (3 / 8) ^ mb κ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hq _) (by positivity)
      _ = (3 / 4) ^ mb κ := by
          rw [← pow_mul, show (w κ + 1) * n κ = mb κ by unfold mb; ring, ← mul_pow]; norm_num
  have h34 : (3 / 4 : ℝ) ^ mb κ ≤ ((1 / 2) ^ κ) ^ 2 := by
    have hmb : 5 * κ ≤ mb κ := by unfold mb n w; nlinarith
    calc (3 / 4 : ℝ) ^ mb κ ≤ (3 / 4) ^ (5 * κ) := pow_le_pow_of_le_one (by norm_num) (by norm_num) hmb
      _ = ((3 / 4) ^ 5) ^ κ := by rw [pow_mul]
      _ ≤ (1 / 4) ^ κ := pow_le_pow_left₀ (by norm_num) (by norm_num) κ
      _ = ((1 / 2) ^ κ) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hs : Real.sqrt ((q κ : ℝ) ^ n κ * (3 / 8) ^ mb κ) ≤ εκ κ := by
    rw [Real.sqrt_le_left (by positivity)]
    unfold εκ; rw [← one_div_pow]; linarith
  have hmb : (mb κ : ℝ) ≤ m κ := by exact_mod_cast (show mb κ ≤ m κ by rw [m_eq_mb]; omega)
  unfold εLHL
  have hε := εκ_pos κ
  have hs0 := Real.sqrt_nonneg ((q κ : ℝ) ^ n κ * (3 / 8) ^ mb κ)
  have hmb0 : (0 : ℝ) ≤ mb κ := Nat.cast_nonneg _
  nlinarith

theorem colErr_le : colErr κ ≤ ENNReal.ofReal ((96 * m κ + 3 * (m κ : ℝ) ^ 3 + 3) * εκ κ) := by
  have hε := εκ_pos κ
  have hm0 : (0 : ℝ) ≤ m κ := Nat.cast_nonneg _
  have hθ0 : 0 ≤ θT κ := by unfold θT Rr; have := τ_pos κ; positivity
  set X := a1 κ ^ m κ * (b1 κ ^ m κ)⁻¹
  set Y := ENNReal.ofReal (Real.exp (-(2 * θT κ)))
  have hY1 : Y ≤ 1 := by
    rw [← ENNReal.ofReal_one]; apply ENNReal.ofReal_le_ofReal
    rw [Real.exp_le_one_iff]; linarith
  have h1 : 1 - X * Y * (1 - tgV κ) ≤ (1 - X) + (1 - Y) + tgV κ := by
    refine (one_sub_mul_le' (X * Y) (1 - tgV κ) tsub_le_self).trans ?_
    refine add_le_add (one_sub_mul_le' X Y hY1) ?_
    exact tsub_le_iff_right.mpr le_add_tsub
  have hX : 1 - X ≤ ENNReal.ofReal (24 * m κ * εκ κ) :=
    one_sub_le_ofReal (by positivity) (X_ge κ)
  have hYb : 1 - Y ≤ ENNReal.ofReal (3 * (m κ : ℝ) ^ 3 * εκ κ) := by
    refine one_sub_le_ofReal (by positivity) ?_
    apply ENNReal.ofReal_le_ofReal
    have := Real.add_one_le_exp (-(2 * θT κ))
    have := θT_le κ
    linarith
  unfold colErr
  calc _ ≤ (ENNReal.ofReal (24 * m κ * εκ κ) + ENNReal.ofReal (3 * (m κ : ℝ) ^ 3 * εκ κ) +
        ENNReal.ofReal (72 * m κ * εκ κ)) + ENNReal.ofReal (3 * εκ κ) :=
        add_le_add ((h1.trans (add_le_add (add_le_add hX hYb) (tgV_le κ))))
          (ENNReal.ofReal_le_ofReal (tail_le κ))
    _ = ENNReal.ofReal ((96 * m κ + 3 * (m κ : ℝ) ^ 3 + 3) * εκ κ) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

/-- The bound `200 (m + 1)^4 / 2^κ`. -/
noncomputable def errTd : ℝ≥0 := ((200 * (m κ + 1) ^ 4 : ℕ) : ℝ≥0) * ((1 : ℝ≥0) / 2 ^ κ)

theorem err_le : (k κ : ℝ≥0∞) * colErr κ + ENNReal.ofReal (εLHL κ) ≤ (errTd κ : ℝ≥0∞) := by
  have hε := εκ_pos κ
  have hm0 : (0 : ℝ) ≤ m κ := Nat.cast_nonneg _
  have hk : (k κ : ℝ≥0∞) = ENNReal.ofReal ((m κ : ℝ) + 1) := by
    rw [show ((m κ : ℝ) + 1) = ((m κ + 1 : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]; rfl
  have hB : (errTd κ : ℝ≥0∞) = ENNReal.ofReal (200 * ((m κ : ℝ) + 1) ^ 4 * εκ κ) := by
    unfold errTd εκ
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    push_cast; ring
  rw [hk, hB]
  calc ENNReal.ofReal ((m κ : ℝ) + 1) * colErr κ + ENNReal.ofReal (εLHL κ)
      ≤ ENNReal.ofReal ((m κ : ℝ) + 1) * ENNReal.ofReal ((96 * m κ + 3 * (m κ : ℝ) ^ 3 + 3) * εκ κ) +
          ENNReal.ofReal (m κ * εκ κ) :=
        add_le_add (mul_le_mul_right (colErr_le κ) _) (ENNReal.ofReal_le_ofReal (εLHL_le κ))
    _ = ENNReal.ofReal (((m κ : ℝ) + 1) * ((96 * m κ + 3 * (m κ : ℝ) ^ 3 + 3) * εκ κ) +
          m κ * εκ κ) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have h : ((m κ : ℝ) + 1) * (96 * m κ + 3 * (m κ : ℝ) ^ 3 + 3) + m κ ≤
            200 * ((m κ : ℝ) + 1) ^ 4 := by nlinarith [sq_nonneg ((m κ : ℝ)), pow_two_nonneg ((m κ : ℝ) + 1)]
        nlinarith

end

theorem polyBound200 : PolynomiallyBounded fun κ => 200 * (m κ + 1) ^ 4 := by
  rw [polynomiallyBounded_iff_le]
  refine ⟨200 * 19 ^ 4, 8, fun κ => ?_⟩
  have : m κ + 1 ≤ 19 * (κ + 1) ^ 2 := by unfold m n w; nlinarith
  calc 200 * (m κ + 1) ^ 4 ≤ 200 * (19 * (κ + 1) ^ 2) ^ 4 := by gcongr
    _ = 200 * 19 ^ 4 * (κ + 1) ^ 8 := by ring

theorem errTd_negligible : Negligible errTd :=
  negligible_one_div_two_pow.polynomiallyBounded_mul polyBound200

/-- **The trapdoor sampler is statistically close.** For all large `κ` and every `P`, the
`(B, K)` drawn with the trapdoor is within the negligible `errTd κ` of uniform `B` with coset
Gaussian preimages of the columns of `P`, for every event. -/
theorem joint_negligible :
    ∀ᶠ κ in Filter.atTop, ∀ P, CloseTo (realJ κ P) (idealJ κ P) (errTd κ) := by
  filter_upwards [smoothCond_eventually] with κ hc P
  exact (joint_close κ hc P).mono (err_le κ)

end SigabaNeo.Lattices.Trapdoor.Family
