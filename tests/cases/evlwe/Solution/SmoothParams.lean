import Definitions.Def_EvLWE
import SigabaNeoStd.Lattices.Gaussian.Bounds

/-!
# Smoothing at the EvLWE parameters

`card_bad_le`: at most `q^{nm}/64` matrices `B` have nonzero dual mass above `1/2` at width `1/τ`
(`dualMassE B τ > 1/2`). The two sums of `sum_dualMassE_le` are each at most `1/256` (relative to
`q^{nm}`), and Markov's inequality gives the count.
-/

namespace TestCase.EvLWE

open SigabaNeo.Lattices

open TestCase TestCase.EvLWE
open scoped ENNReal

/-! ### Parameter facts -/

theorem q_gt (κ : ℕ) : (2 : ℝ) ^ w κ < q κ := by
  have := (exists_q κ).choose_spec.2.1
  exact_mod_cast this

theorem q_le (κ : ℕ) : (q κ : ℝ) ≤ 2 ^ (w κ + 1) := by
  have := (exists_q κ).choose_spec.2.2
  rw [pow_succ]
  have h : ((q κ : ℕ) : ℝ) ≤ ((2 * 2 ^ w κ : ℕ) : ℝ) := by exact_mod_cast this
  push_cast at h; linarith

theorem q_pos (κ : ℕ) : (0 : ℝ) < q κ := lt_of_le_of_lt (by positivity) (q_gt κ)

theorem two_pow_ge (κ : ℕ) : (κ : ℝ) + 1 ≤ 2 ^ κ := by
  have := one_add_mul_le_pow (a := (1 : ℝ)) (by norm_num) κ
  norm_num at this; linarith

theorem m_le_real (κ : ℕ) : (m κ : ℝ) ≤ 18 * ((κ : ℝ) + 1) ^ 2 := by
  unfold m n w; push_cast; nlinarith

theorem m_ge (κ : ℕ) : 1 ≤ m κ := by
  unfold m n w; nlinarith

/-! ### The two sums -/

/-- `256 · Σ_{u ≠ 0} e^{−π τ² ‖u‖²} ≤ 1`. -/
theorem wt1_bound (κ : ℕ) : 256 * ∑' u : Fin (m κ) → ℤ, wt1 (τ κ) u ≤ 1 := by
  set x := Real.pi * τ κ ^ 2 with hxdef
  set R := Real.exp (-x) with hRdef
  have hk := two_pow_ge κ
  have hτ : 8 * ((κ : ℝ) + 1) ≤ τ κ := by
    unfold τ; rw [pow_add]; nlinarith
  have hx : 128 * ((κ : ℝ) + 1) ≤ x := by
    have := Real.two_le_pi
    have : 64 * ((κ : ℝ) + 1) ≤ τ κ ^ 2 := by nlinarith
    nlinarith
  have hx0 : 0 ≤ x := by positivity
  have hex : x ^ 3 / 6 ≤ Real.exp x := by
    have := Real.pow_div_factorial_le_exp x hx0 3
    simpa [Nat.factorial] using this
  have hm := m_le_real κ
  have hm1 : (1 : ℝ) ≤ m κ := by exact_mod_cast m_ge κ
  have hR0 : 0 ≤ R := (Real.exp_pos _).le
  have hRe : R * Real.exp x = 1 := by rw [hRdef, ← Real.exp_add]; simp
  have hbig : 1536 * (m κ : ℝ) ≤ Real.exp x := by
    have h3 : (128 * ((κ : ℝ) + 1)) ^ 3 ≤ x ^ 3 :=
      pow_le_pow_left₀ (by positivity) hx 3
    have hk1 : (1 : ℝ) ≤ κ + 1 := by linarith [(Nat.cast_nonneg κ : (0 : ℝ) ≤ κ)]
    nlinarith
  have hRm : 1536 * (R * m κ) ≤ 1 := by nlinarith
  have hR4 : R ≤ 1 / 4 := by nlinarith
  -- the one-dimensional sum
  have hA : ∑' k : ℤ, g1 x k ≤ ENNReal.ofReal (1 + 3 * R) := by
    refine le_trans (tsum_g1_le_large hx0) ?_
    rw [geom_eq hR0 (by linarith)]
    exact ENNReal.ofReal_le_ofReal (ratio_le hR0 hR4)
  have hpow : (∑' k : ℤ, g1 x k) ^ m κ ≤ ENNReal.ofReal (1 + 1 / 256) := by
    refine le_trans (pow_le_pow_left' hA _) ?_
    rw [← ENNReal.ofReal_pow (by linarith)]
    apply ENNReal.ofReal_le_ofReal
    have := one_add_pow_le (x := 3 * R) (by linarith) (m κ) (by nlinarith)
    nlinarith
  have hZ : ∑' u : Fin (m κ) → ℤ, wt1 (τ κ) u + 1 ≤ ENNReal.ofReal (1 / 256) + 1 := by
    rw [tsum_wt1_add_one, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    rw [add_comm (1 / 256 : ℝ)]; exact hpow
  have hZ' := ENNReal.le_of_add_le_add_right ENNReal.one_ne_top hZ
  calc 256 * ∑' u : Fin (m κ) → ℤ, wt1 (τ κ) u ≤ 256 * ENNReal.ofReal (1 / 256) := by gcongr
    _ = 1 := ennreal_256

/-- The exponent count behind `256 · q^n · 4^m ≤ τ^m`. -/
theorem exponent_le (κ : ℕ) : 8 + (w κ + 1) * n κ + 2 * m κ ≤ (κ + 3) * m κ := by
  have hP : 9 ≤ (w κ + 1) * n κ := by unfold w n; nlinarith
  have hm : m κ = 2 * ((w κ + 1) * n κ) := by unfold m; ring
  rw [hm]; nlinarith

theorem real_bound (κ : ℕ) :
    256 * (q κ : ℝ) ^ n κ * (4 * q κ / τ κ) ^ m κ ≤ (q κ : ℝ) ^ m κ := by
  have hq := q_pos κ
  have hτ := τ_pos κ
  have hkey : 256 * (q κ : ℝ) ^ n κ * 4 ^ m κ ≤ τ κ ^ m κ := by
    have h1 : (q κ : ℝ) ^ n κ ≤ 2 ^ ((w κ + 1) * n κ) := by
      rw [pow_mul]; exact pow_le_pow_left₀ hq.le (q_le κ) _
    have h2 : (2 : ℝ) ^ (8 + (w κ + 1) * n κ + 2 * m κ) ≤ 2 ^ ((κ + 3) * m κ) :=
      pow_le_pow_right₀ (by norm_num) (exponent_le κ)
    have h3 : (2 : ℝ) ^ (8 + (w κ + 1) * n κ + 2 * m κ) =
        256 * 2 ^ ((w κ + 1) * n κ) * 4 ^ m κ := by
      rw [pow_add, pow_add, pow_mul, pow_mul]; norm_num
    have h4 : τ κ ^ m κ = 2 ^ ((κ + 3) * m κ) := by unfold τ; rw [pow_mul]
    rw [h4]
    calc 256 * (q κ : ℝ) ^ n κ * 4 ^ m κ ≤ 256 * 2 ^ ((w κ + 1) * n κ) * 4 ^ m κ := by gcongr
      _ ≤ _ := by rw [← h3]; exact h2
  rw [div_pow, mul_pow]
  have hτm : 0 < τ κ ^ m κ := by positivity
  rw [mul_div_assoc', div_le_iff₀ hτm]
  calc 256 * (q κ : ℝ) ^ n κ * (4 ^ m κ * (q κ : ℝ) ^ m κ)
      = (256 * (q κ : ℝ) ^ n κ * 4 ^ m κ) * (q κ : ℝ) ^ m κ := by ring
    _ ≤ τ κ ^ m κ * (q κ : ℝ) ^ m κ := by gcongr
    _ = _ := by ring

/-- `256 · q^n · Σ_v e^{−π τ² ‖v‖² / q²} ≤ q^m`. -/
theorem wt_bound (κ : ℕ) :
    256 * ((q κ : ℝ≥0∞) ^ n κ * ∑' v : Fin (m κ) → ℤ, wt (τ κ) (q κ) v) ≤
      (q κ : ℝ≥0∞) ^ m κ := by
  have hq := q_pos κ
  have hτ := τ_pos κ
  set c := Real.sqrt Real.pi * τ κ / q κ with hcdef
  have hspi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hc0 : 0 < c := by positivity
  have hc2 : Real.pi * τ κ ^ 2 / (q κ : ℝ) ^ 2 = c ^ 2 := by
    rw [hcdef, div_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le]
  -- `c ≤ 1`: `√π ≤ 2` and `2 τ ≤ q`
  have hc1 : c ≤ 1 := by
    have hsp : Real.sqrt Real.pi ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt Real.pi_le_four
    have h2τ : 2 * τ κ ≤ q κ := by
      have hg := q_gt κ
      have : 2 * τ κ ≤ 2 ^ w κ := by
        unfold τ w
        rw [← pow_succ']
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    rw [hcdef, div_le_one hq]; nlinarith
  set R := Real.exp (-c) with hRdef
  have hR0 : 0 ≤ R := (Real.exp_pos _).le
  have hR1 : R < 1 := by rw [hRdef]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hsub := one_sub_exp_neg_ge hc0.le hc1
  -- the one-dimensional sum is at most `4 q / τ`
  have hreal : Real.exp (1 / 4) * ((1 + R) / (1 - R)) ≤ 4 * q κ / τ κ := by
    have hr : (1 + R) / (1 - R) ≤ 4 / c := by
      rw [div_le_div_iff₀ (by linarith) hc0]; nlinarith
    have he := exp_quarter_le_sqrt_pi
    calc Real.exp (1 / 4) * ((1 + R) / (1 - R)) ≤ Real.sqrt Real.pi * (4 / c) := by
          gcongr
      _ = 4 * q κ / τ κ := by rw [hcdef]; field_simp
  have hA : ∑' k : ℤ, g1 (Real.pi * τ κ ^ 2 / (q κ : ℝ) ^ 2) k ≤
      ENNReal.ofReal (4 * q κ / τ κ) := by
    rw [hc2]
    refine le_trans tsum_g1_le_small ?_
    rw [geom_eq hR0 hR1, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact ENNReal.ofReal_le_ofReal hreal
  rw [tsum_wt_eq]
  have hqe : (q κ : ℝ≥0∞) = ENNReal.ofReal (q κ) := by simp
  calc 256 * ((q κ : ℝ≥0∞) ^ n κ * (∑' k : ℤ, g1 (Real.pi * τ κ ^ 2 / (q κ : ℝ) ^ 2) k) ^ m κ)
      ≤ 256 * ((q κ : ℝ≥0∞) ^ n κ * ENNReal.ofReal (4 * q κ / τ κ) ^ m κ) := by gcongr
    _ = ENNReal.ofReal (256 * (q κ : ℝ) ^ n κ * (4 * q κ / τ κ) ^ m κ) := by
        rw [hqe, ← ENNReal.ofReal_pow hq.le, ← ENNReal.ofReal_pow (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), mul_assoc]
        simp
    _ ≤ ENNReal.ofReal ((q κ : ℝ) ^ m κ) := ENNReal.ofReal_le_ofReal (real_bound κ)
    _ = _ := by rw [hqe, ENNReal.ofReal_pow hq.le]

/-! ### Markov -/

open Classical in
/-- At most a `1/64` fraction of the matrices `B` has nonzero dual mass above `1/2`. -/
theorem card_bad_le (κ : ℕ) :
    64 * (Finset.univ.filter fun B : Matrix (Fin (n κ)) (Fin (m κ)) (ZMod (q κ)) =>
      (1 / 2 : ℝ≥0∞) < dualMassE B (τ κ)).card ≤ q κ ^ (n κ * m κ) := by
  set S := Finset.univ.filter fun B : Matrix (Fin (n κ)) (Fin (m κ)) (ZMod (q κ)) =>
    (1 / 2 : ℝ≥0∞) < dualMassE B (τ κ)
  set T := ∑ B : Matrix (Fin (n κ)) (Fin (m κ)) (ZMod (q κ)), dualMassE B (τ κ)
  set Q : ℝ≥0∞ := ((q κ : ℕ) : ℝ≥0∞)
  have hcard : (S.card : ℝ≥0∞) ≤ 2 * T := by
    calc (S.card : ℝ≥0∞) = ∑ _B ∈ S, (1 : ℝ≥0∞) := by simp
      _ ≤ ∑ B ∈ S, 2 * dualMassE B (τ κ) := by
          refine Finset.sum_le_sum fun B hB => ?_
          have h := (Finset.mem_filter.mp hB).2
          calc (1 : ℝ≥0∞) = 2 * (1 / 2) := by
                rw [one_div, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]
            _ ≤ _ := by gcongr
      _ ≤ ∑ B, 2 * dualMassE B (τ κ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => zero_le)
      _ = 2 * T := by rw [Finset.mul_sum]
  have hsum := sum_dualMassE_le (n := n κ) (m := m κ) (q := q κ) (τ κ)
  have h1 := wt1_bound κ
  have h2 := wt_bound κ
  have hT : 256 * T * Q ^ m κ ≤ 2 * Q ^ (n κ * m κ) * Q ^ m κ := by
    calc 256 * T * Q ^ m κ = 256 * (T * Q ^ m κ) := by ring
      _ ≤ 256 * (Q ^ m κ * Q ^ (n κ * m κ) * ∑' u : Fin (m κ) → ℤ, wt1 (τ κ) u +
            Q ^ n κ * Q ^ (n κ * m κ) * ∑' v : Fin (m κ) → ℤ, wt (τ κ) (q κ) v) := by gcongr
      _ = Q ^ m κ * Q ^ (n κ * m κ) * (256 * ∑' u : Fin (m κ) → ℤ, wt1 (τ κ) u) +
            Q ^ (n κ * m κ) * (256 * (Q ^ n κ * ∑' v : Fin (m κ) → ℤ, wt (τ κ) (q κ) v)) := by
          ring
      _ ≤ Q ^ m κ * Q ^ (n κ * m κ) * 1 + Q ^ (n κ * m κ) * Q ^ m κ := by gcongr
      _ = 2 * Q ^ (n κ * m κ) * Q ^ m κ := by ring
  have hQ0 : Q ^ m κ ≠ 0 := pow_ne_zero _ (by simp [Q, NeZero.ne (q κ)])
  have hQt : Q ^ m κ ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  have hT' : 256 * T ≤ 2 * Q ^ (n κ * m κ) := (ENNReal.mul_le_mul_iff_left hQ0 hQt).mp hT
  have h2' : 2 * (64 * (S.card : ℝ≥0∞)) ≤ 2 * Q ^ (n κ * m κ) := by
    calc 2 * (64 * (S.card : ℝ≥0∞)) = 128 * S.card := by ring
      _ ≤ 128 * (2 * T) := by gcongr
      _ = 256 * T := by ring
      _ ≤ _ := hT'
  have h3 := (ENNReal.mul_le_mul_iff_right two_ne_zero ENNReal.ofNat_ne_top).mp h2'
  have : ((64 * S.card : ℕ) : ℝ≥0∞) ≤ ((q κ ^ (n κ * m κ) : ℕ) : ℝ≥0∞) := by
    push_cast; exact h3
  exact_mod_cast this

end TestCase.EvLWE
