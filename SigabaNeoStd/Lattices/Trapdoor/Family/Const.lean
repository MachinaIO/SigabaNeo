import SigabaNeoStd.Lattices.Trapdoor.Family.Joint

/-!
# Trapdoor sampler: the constants are close to `1`

With `ε = 2^{−κ}`: `δP, ηN − 1, e^K / 2^T, t ≤ ε/16` (`δP_le`, `ηN_le`, `eK_le`, `tqR_le`),
`τ/6 ≤ ρ_τ(Z) ≤ 5τ` (`Mz_le`), and the loop fails with probability `q^{Rt} ≤ 4^{−(κ+1)}`
(`qfail_pow_le`). Hence `a₁ ≥ (1 − q_U)/u` and `b₁ ≤ u + 5τ q_U` with `u = c_H e^{δP}/(1 − t)`
(`a1_ge`, `b1_le`), and `1 ≤ u ≤ 1 + ε` (`u_bounds`).
-/

namespace SigabaNeo.Lattices.Trapdoor.Family

open SigabaNeo.Lattices Cslib.Probability
open scoped ENNReal

theorem two_pow_le_factorial (n : ℕ) : 2 ^ n ≤ (n + 1).factorial := by
  have h := @Nat.factorial_mul_pow_le_factorial 1 n
  rw [Nat.factorial_one, one_mul, add_comm 1 n] at h
  exact h

theorem exp_le_one_add_two {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.exp x ≤ 1 + 2 * x := by
  have h := Real.exp_bound' h0 h1 (n := 1) (by norm_num)
  norm_num at h
  linarith

theorem one_sub_ofReal (t : ℝ) (ht : 0 ≤ t) : 1 - ENNReal.ofReal t = ENNReal.ofReal (1 - t) := by
  rw [← ENNReal.ofReal_one, ENNReal.ofReal_sub _ ht]

section
variable (κ : ℕ)

/-- `ε = 2^{−κ}`. -/
noncomputable abbrev εκ : ℝ := 1 / 2 ^ κ

theorem εκ_pos : 0 < εκ κ := by positivity
theorem εκ_le_one : εκ κ ≤ 1 := by
  unfold εκ; rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)

theorem pow_two_eq (a : ℕ) : (4 : ℝ) ^ a = 2 ^ (2 * a) := by
  rw [pow_mul]; norm_num

theorem δP_le : δP κ ≤ εκ κ / 16 := by
  have he := errPi_le κ
  have hP : Pbits κ / 2 = 2 * κ + 2 * Lg κ + 32 := by unfold Pbits; omega
  rw [hP] at he
  unfold δP
  rw [pow_two_eq]
  calc errPi κ * 2 ^ (2 * (Lg κ + 1)) ≤ 1 / 2 ^ (2 * κ + 2 * Lg κ + 32) * 2 ^ (2 * (Lg κ + 1)) :=
        mul_le_mul_of_nonneg_right he (by positivity)
    _ = εκ κ / 16 * (1 / 2 ^ (κ + 26)) := by
        unfold εκ; field_simp; try ring
    _ ≤ εκ κ / 16 := by
        have : (1 : ℝ) / 2 ^ (κ + 26) ≤ 1 := by
          rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
        have h0 : 0 ≤ εκ κ / 16 := by positivity
        nlinarith

theorem δP_nonneg : 0 ≤ δP κ := by
  unfold δP errPi; positivity

theorem ηN_le : ηN κ ≤ 1 + εκ κ / 16 := by
  set N := Nterms κ
  set E := Ecnt κ
  have hN : (2 : ℝ) ^ (κ + 2 * Lg κ + 39) ≤ N.factorial := by
    have := two_pow_le_factorial (κ + 2 * Lg κ + 39)
    have hN' : N = κ + 2 * Lg κ + 39 + 1 := by simp only [N, Nterms]
    rw [hN']; exact_mod_cast this
  have hE : (E : ℝ) = 2 ^ (2 * Lg κ + 4) := by
    simp only [E, Ecnt]; push_cast; rw [pow_two_eq]; ring_nf
  set y := (E : ℝ) * (2 / N.factorial)
  have hy0 : 0 ≤ y := by positivity
  have hy : y ≤ εκ κ / 32 := by
    have hf : (0 : ℝ) < N.factorial := by positivity
    simp only [y, hE]
    rw [mul_div_assoc', div_le_iff₀ hf]
    calc (2 : ℝ) ^ (2 * Lg κ + 4) * 2 = εκ κ / 32 * 2 ^ (κ + 2 * Lg κ + 39) / 2 ^ 29 := by
          unfold εκ; field_simp; try ring
      _ ≤ εκ κ / 32 * 2 ^ (κ + 2 * Lg κ + 39) := by
          apply div_le_self (by positivity); exact one_le_pow₀ (by norm_num)
      _ ≤ εκ κ / 32 * N.factorial := mul_le_mul_of_nonneg_left hN (by positivity)
  have hy1 : y ≤ 1 := hy.trans (by have := εκ_le_one κ; linarith)
  unfold ηN
  calc (1 + 2 / (N.factorial : ℝ)) ^ E ≤ Real.exp (2 / N.factorial) ^ E := by
        apply pow_le_pow_left₀ (by positivity)
        have := Real.add_one_le_exp (2 / (N.factorial : ℝ)); linarith
    _ = Real.exp y := by rw [← Real.exp_nat_mul]
    _ ≤ 1 + 2 * y := exp_le_one_add_two hy0 hy1
    _ ≤ 1 + εκ κ / 16 := by linarith

theorem ηN_ge' : 1 ≤ ηN κ := ηN_ge κ

theorem eK_le : eK κ / 2 ^ Tbits κ ≤ εκ κ / 16 := by
  set E := Ecnt κ
  have hE : (E : ℝ) = 4 * 4 ^ (Lg κ + 1) := by
    simp only [E, Ecnt]; push_cast; ring
  have h1 : eK κ ≤ (2 : ℝ) ^ (2 * E) := by
    unfold eK
    calc Real.exp (Real.pi * 4 ^ (Lg κ + 1)) ≤ Real.exp (E : ℝ) := by
          apply Real.exp_le_exp.mpr
          rw [hE]
          exact mul_le_mul_of_nonneg_right Real.pi_le_four (by positivity)
      _ = Real.exp 1 ^ E := by rw [← Real.exp_nat_mul, mul_one]
      _ ≤ 4 ^ E := pow_le_pow_left₀ (Real.exp_pos 1).le
          (by have := Real.exp_one_lt_d9; linarith) E
      _ = 2 ^ (2 * E) := pow_two_eq E
  have hT : (2 : ℝ) ^ Tbits κ = 2 ^ (2 * E) * (2 ^ κ * 2 ^ 10) := by
    rw [show Tbits κ = 2 * E + κ + 10 from rfl, pow_add, pow_add]; ring
  rw [hT, div_le_iff₀ (by positivity)]
  calc eK κ ≤ 2 ^ (2 * E) := h1
    _ = εκ κ / 16 * (2 ^ (2 * E) * (2 ^ κ * 2 ^ 10)) / 64 := by unfold εκ; field_simp; try ring
    _ ≤ _ := div_le_self (by positivity) (by norm_num)

/-- The tail mass of `D_{Z,τ}` outside the proposals, as a real number. -/
noncomputable def tqR : ℝ := 6 * (1 / 4) ^ (4 ^ (Lg κ + 1))

theorem tqR_nonneg : 0 ≤ tqR κ := by unfold tqR; positivity

theorem tqR_le : tqR κ ≤ εκ κ / 16 := by
  have hX : κ + 4 ≤ 4 ^ (Lg κ + 1) := by
    have h1 := m_lt_two_pow_Lg κ
    have h2 : κ + 4 ≤ m κ := by unfold m n w; nlinarith
    have h3 : 2 ^ Lg κ ≤ 4 ^ (Lg κ + 1) :=
      (Nat.pow_le_pow_left (by norm_num) _).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    omega
  unfold tqR
  calc 6 * (1 / 4 : ℝ) ^ (4 ^ (Lg κ + 1)) ≤ 6 * (1 / 4) ^ (κ + 4) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) hX) (by norm_num)
    _ = 6 / 256 * (1 / 4) ^ κ := by ring
    _ ≤ 1 / 16 * (1 / 2) ^ κ :=
        mul_le_mul (by norm_num) (pow_le_pow_left₀ (by norm_num) (by norm_num) κ) (by positivity)
          (by norm_num)
    _ = εκ κ / 16 := by unfold εκ; rw [one_div_pow]; ring

theorem tq_eq : tq κ = ENNReal.ofReal (tqR κ) := rfl

/-! ### `ρ_τ(Z)` -/

set_option maxHeartbeats 1000000 in
theorem Mz_le : Mz (τ κ) ≤ 5 * τ κ := by
  classical
  set N : ℕ := 2 ^ (κ + 4)
  have hNτ : (N : ℝ) = 2 * τ κ := by simp only [N, τ]; push_cast; ring
  set S : Finset ℤ := Finset.Ioo (-(N : ℤ)) N
  have hcard : (S.card : ℝ) ≤ 2 * N := by
    simp only [S, Int.card_Ioo]
    have : ((N : ℤ) - -(N : ℤ) - 1).toNat ≤ 2 * N := by omega
    exact_mod_cast this
  set g := gaussZ (τ κ) (τ_pos κ)
  have hM := Mz_pos (τ_pos κ)
  have ht := gaussZ_tail (one_le_τ κ) (τ_pos κ) 4
  rw [toOuterMeasure_eq_ev] at ht
  have hsplit := ev_ind_add_not g (fun z => z ∈ S)
  have hin : ev g (fun z => ind (z ∈ S)) ≤ ENNReal.ofReal (S.card / Mz (τ κ)) := by
    have : (fun z => ind (z ∈ S)) = fun z => ∑ s ∈ S, ind (z = s) := by
      funext z
      by_cases hz : z ∈ S
      · rw [ind_of hz, Finset.sum_eq_single z]
        · rw [ind_of rfl]
        · intro b _ hb; rw [ind_of_not (Ne.symm hb)]
        · intro h; exact absurd hz h
      · rw [ind_of_not hz]
        exact (Finset.sum_eq_zero fun s hs => ind_of_not fun h : z = s => hz (by rw [h]; exact hs)).symm
    rw [this, ev_finset_sum]
    simp only [ev_point]
    calc ∑ s ∈ S, g s ≤ ∑ _s ∈ S, ENNReal.ofReal (1 / Mz (τ κ)) := by
          refine Finset.sum_le_sum fun s _ => ?_
          rw [gaussZ_apply, ← ENNReal.ofReal_div_of_pos hM]
          exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (gw_le_one _ _) hM.le)
      _ = ENNReal.ofReal (S.card / Mz (τ κ)) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul
            (by positivity)]
          congr 1; ring
  have hout : ev g (fun z => ind (¬ z ∈ S)) ≤ ENNReal.ofReal (6 * (1 / 4) ^ 4) := by
    refine le_trans (ev_mono _ fun z => ind_mono ?_) ht
    intro hz
    simp only [Set.mem_ofPred_eq]
    have h4 : Real.sqrt ((4 : ℕ) : ℝ) = 2 := by
      rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
    rw [h4, mul_comm, ← hNτ]
    have : (N : ℤ) ≤ |z| := by
      simp only [S, Finset.mem_Ioo, not_and_or, not_lt] at hz
      rw [le_abs']; omega
    exact_mod_cast this
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (S.card / Mz (τ κ) + 6 * (1 / 4) ^ 4) := by
    rw [ENNReal.ofReal_add (by positivity) (by norm_num), ← hsplit]
    exact add_le_add hin hout
  rw [ENNReal.one_le_ofReal] at h1
  have h2 : (250 / 256 : ℝ) * Mz (τ κ) ≤ S.card := by
    have : (250 / 256 : ℝ) ≤ S.card / Mz (τ κ) := by norm_num at h1 ⊢; linarith
    rwa [le_div_iff₀ hM] at this
  have hτ := τ_pos κ
  nlinarith

/-! ### The failure probability of the loop -/

theorem cL_ge : ENNReal.ofReal (1 / 2) ≤ cL κ := by
  unfold cL
  apply ENNReal.ofReal_le_ofReal
  have h := δP_le κ
  have he := εκ_le_one κ
  have := Real.add_one_le_exp (-δP κ)
  linarith

theorem one_sub_tq_ge : ENNReal.ofReal (1 / 2) ≤ 1 - tq κ := by
  rw [tq_eq, one_sub_ofReal _ (tqR_nonneg κ)]
  apply ENNReal.ofReal_le_ofReal
  have := tqR_le κ; have := εκ_le_one κ; linarith

theorem pow_Aex_succ : (2 : ℝ) ^ (Aex κ + 1) = τ κ * 2 ^ (Lg κ + 2) := by
  rw [τ, Aex, ← pow_add]; congr 1; ring

/-- `c = 1 / (96 · 2^{Lg})`. -/
noncomputable def cfail : ℝ := 1 / (96 * 2 ^ Lg κ)

theorem S_div_ge : ENNReal.ofReal (cfail κ) ≤
    (∑ v ∈ Finset.range (2 ^ (Aex κ + 1)), pacc κ v) / 2 ^ (Aex κ + 1) := by
  have hτ := τ_pos κ
  have hR : (2 : ℝ≥0∞) ^ (Aex κ + 1) = ENNReal.ofReal ((2 : ℝ) ^ (Aex κ + 1)) := by
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  rw [hR, ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl ENNReal.ofReal_ne_top),
    ← ENNReal.ofReal_mul (by unfold cfail; positivity)]
  have hZ : ENNReal.ofReal (τ κ / 6) ≤ Zm κ := ENNReal.ofReal_le_ofReal (Mz_ge (τ_pos κ))
  refine le_trans ?_ (S_ge κ)
  calc ENNReal.ofReal (cfail κ * 2 ^ (Aex κ + 1)) =
        ENNReal.ofReal (1 / 2) * ENNReal.ofReal (τ κ / 6) * ENNReal.ofReal (1 / 2) := by
        rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [pow_Aex_succ]; unfold cfail; field_simp; try ring
    _ ≤ cL κ * Zm κ * (1 - tq κ) := by
        gcongr
        · exact cL_ge κ
        · exact one_sub_tq_ge κ

theorem qfail_le : qfail κ ≤ ENNReal.ofReal (1 - cfail κ) := by
  have h := qfail_add κ
  have hq : qfail κ = 1 - (∑ v ∈ Finset.range (2 ^ (Aex κ + 1)), pacc κ v) / 2 ^ (Aex κ + 1) :=
    ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top
      (h ▸ le_add_self)) h
  rw [hq, ← one_sub_ofReal _ (by unfold cfail; positivity)]
  exact tsub_le_tsub_left (S_div_ge κ) 1

/-- `q_U = 4^{−(κ+1)}`. -/
noncomputable def qU : ℝ := (1 / 4) ^ (κ + 1)

theorem qfail_pow_le : qfail κ ^ Rt κ ≤ ENNReal.ofReal (qU κ) := by
  have hc0 : 0 ≤ cfail κ := by unfold cfail; positivity
  have hc1 : cfail κ ≤ 1 := by
    unfold cfail; rw [div_le_one (by positivity)]
    have : (1 : ℝ) ≤ 2 ^ Lg κ := one_le_pow₀ (by norm_num)
    nlinarith
  refine (pow_le_pow_left₀ bot_le (qfail_le κ) _).trans ?_
  rw [← ENNReal.ofReal_pow (by linarith)]
  apply ENNReal.ofReal_le_ofReal
  have hcR : 2 * ((κ : ℝ) + 1) ≤ cfail κ * Rt κ := by
    unfold cfail Rt; push_cast
    rw [pow_add]
    field_simp
    have : (0 : ℝ) ≤ κ := Nat.cast_nonneg κ
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (Lg κ)]
  calc (1 - cfail κ) ^ Rt κ ≤ Real.exp (-cfail κ) ^ Rt κ :=
        pow_le_pow_left₀ (by linarith) (by have := Real.add_one_le_exp (-cfail κ); linarith) _
    _ = Real.exp (-(cfail κ * Rt κ)) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ Real.exp (-(2 * ((κ : ℝ) + 1))) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-2) ^ (κ + 1) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
    _ ≤ (1 / 4) ^ (κ + 1) := by
        apply pow_le_pow_left₀ (Real.exp_pos _).le
        rw [Real.exp_neg, one_div]
        apply inv_anti₀ (by norm_num)
        have h := Real.add_one_le_exp 1
        calc (4 : ℝ) = 2 * 2 := by norm_num
          _ ≤ Real.exp 1 * Real.exp 1 := by nlinarith
          _ = Real.exp 2 := by rw [← Real.exp_add]; norm_num

/-! ### `a₁` and `b₁` -/

noncomputable def cHR : ℝ := Real.exp (δP κ) * ηN κ + eK κ / 2 ^ Tbits κ

/-- `u = c_H e^{δP} / (1 − t)`. -/
noncomputable def uR : ℝ := cHR κ * Real.exp (δP κ) / (1 - tqR κ)

theorem cHR_ge : 1 ≤ cHR κ := by
  unfold cHR
  have h1 := Real.one_le_exp (δP_nonneg κ)
  have h2 := ηN_ge κ
  have h3 : 0 ≤ eK κ / 2 ^ Tbits κ := by unfold eK; positivity
  nlinarith

theorem tqR_le_half : tqR κ ≤ 1 / 16 := by
  have := tqR_le κ; have := εκ_le_one κ; linarith

theorem u_bounds : 1 ≤ uR κ ∧ uR κ ≤ 1 + εκ κ := by
  have hε := εκ_pos κ
  have hε1 := εκ_le_one κ
  have hδ := δP_le κ
  have hδ0 := δP_nonneg κ
  have ht := tqR_le κ
  have ht0 := tqR_nonneg κ
  have hc := cHR_ge κ
  have he1 : Real.exp (δP κ) ≤ 1 + εκ κ / 8 :=
    (exp_le_one_add_two hδ0 (by linarith)).trans (by linarith)
  have he0 := Real.one_le_exp hδ0
  have hcU : cHR κ ≤ (1 + εκ κ / 8) * (1 + εκ κ / 16) + εκ κ / 16 := by
    unfold cHR
    have := ηN_le κ
    have := eK_le κ
    have := ηN_ge κ
    nlinarith
  have hpos : 0 < 1 - tqR κ := by linarith
  unfold uR
  constructor
  · rw [le_div_iff₀ hpos]; nlinarith
  · rw [div_le_iff₀ hpos]
    have h1 : cHR κ * Real.exp (δP κ) ≤
        ((1 + εκ κ / 8) * (1 + εκ κ / 16) + εκ κ / 16) * (1 + εκ κ / 8) :=
      mul_le_mul hcU he1 (by linarith) (by positivity)
    have h2 : ((1 + εκ κ / 8) * (1 + εκ κ / 16) + εκ κ / 16) * (1 + εκ κ / 8) ≤
        (1 + εκ κ) * (1 - εκ κ / 16) := by nlinarith
    have h3 : (1 + εκ κ) * (1 - εκ κ / 16) ≤ (1 + εκ κ) * (1 - tqR κ) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith

theorem cH_eq : cH κ = ENNReal.ofReal (cHR κ) := rfl

theorem a1_ge : ENNReal.ofReal ((1 - qU κ) / uR κ) ≤ a1 κ := by
  have hu := (u_bounds κ).1
  have hc := cHR_ge κ
  have hq : qU κ ≤ 1 := by unfold qU; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hq0 : 0 ≤ qU κ := by unfold qU; positivity
  unfold a1
  have h1 : ENNReal.ofReal (1 - qU κ) ≤ 1 - qfail κ ^ Rt κ := by
    rw [← one_sub_ofReal _ hq0]; exact tsub_le_tsub_left (qfail_pow_le κ) 1
  have h2 : cL κ * (cH κ)⁻¹ = ENNReal.ofReal (Real.exp (-δP κ) / cHR κ) := by
    rw [cL, cH_eq, ENNReal.ofReal_div_of_pos (by linarith), div_eq_mul_inv]
  rw [mul_assoc, h2]
  calc ENNReal.ofReal ((1 - qU κ) / uR κ) ≤
        ENNReal.ofReal (1 - qU κ) * ENNReal.ofReal (Real.exp (-δP κ) / cHR κ) := by
        rw [← ENNReal.ofReal_mul (by linarith)]
        apply ENNReal.ofReal_le_ofReal
        rw [div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        have ht := tqR_nonneg κ
        have hcp : 0 < cHR κ := by linarith
        have he := Real.exp_pos (δP κ)
        have hu' : (uR κ)⁻¹ = (1 - tqR κ) * (Real.exp (-δP κ) / cHR κ) := by
          unfold uR; rw [Real.exp_neg]; field_simp
        rw [hu']
        exact mul_le_of_le_one_left (by positivity) (by linarith)
    _ ≤ _ := mul_le_mul_left h1 _

theorem b1_le : b1 κ ≤ ENNReal.ofReal (uR κ + qU κ * (5 * τ κ)) := by
  have hc := cHR_ge κ
  have ht := tqR_le_half κ
  have hq0 : 0 ≤ qU κ := by unfold qU; positivity
  unfold b1
  rw [ENNReal.ofReal_add (by have := (u_bounds κ).1; linarith) (by have := τ_pos κ; positivity)]
  refine add_le_add (le_of_eq ?_) ?_
  · rw [cH_eq, cL, tq_eq, one_sub_ofReal _ (tqR_nonneg κ), ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← ENNReal.ofReal_inv_of_pos (by have := Real.exp_pos (-δP κ); nlinarith),
      ← ENNReal.ofReal_mul (by linarith)]
    congr 1
    unfold uR
    rw [Real.exp_neg]
    field_simp
  · rw [ENNReal.ofReal_mul hq0]
    exact mul_le_mul' (qfail_pow_le κ) (ENNReal.ofReal_le_ofReal (Mz_le κ))

end

end SigabaNeo.Lattices.Trapdoor.Family
