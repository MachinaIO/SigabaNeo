import SigabaNeoStd.Lattices.Trapdoor.Family.Samp1

/-!
# Trapdoor sampler: the acceptance probability is `ρ_τ(z)` up to small factors

For a proposal `v < 2^{A+1}` with `z = v − 2^A`:

  `e^{−δ} ρ_τ(z) ≤ pacc v ≤ e^{δ} (1 + 2/N!)^E ρ_τ(z) + 2^{−T}`  (`pacc_ge`, `pacc_le`)

where `δ = |π̂ − π| · 4^{Lg+1}` bounds the effect of `π̂` on the exponent (`z² / τ² ≤ 4^{Lg+1}`).
-/

namespace SigabaNeo.Lattices.Trapdoor.Family

open SigabaNeo.Lattices Cslib.Probability
open scoped ENNReal

section
variable (κ : ℕ)

/-- `π̂ = piNat / 2^P`. -/
noncomputable def piHat : ℝ := piNat κ / 2 ^ Pbits κ

/-- The error of `π̂`. -/
noncomputable def errPi : ℝ :=
  (20 * Pbits κ + 40 * 2 ^ Pbits κ * (1 / 5) ^ (2 * Pbits κ + 1)) / 2 ^ Pbits κ

theorem P_ge : 64 ≤ Pbits κ := by unfold Pbits; omega

theorem errPi_le : errPi κ ≤ 1 / 2 ^ (Pbits κ / 2) := by
  unfold errPi
  set P := Pbits κ
  have hP := P_ge κ
  have h1 : (20 : ℝ) * P ≤ 2 ^ (P / 2) / 2 := by
    have : 20 * P * 2 ≤ 2 ^ (P / 2) := by
      have h := Nat.lt_two_pow_self (n := P / 2)
      calc 20 * P * 2 ≤ 40 * (2 * (P / 2) + 1) := by omega
        _ ≤ 2 ^ (P / 2) := by
          have : 80 * (P / 2) + 40 ≤ 2 ^ (P / 2) := by
            have hk : 32 ≤ P / 2 := by omega
            obtain ⟨k, hk'⟩ : ∃ k, P / 2 = k + 32 := ⟨P / 2 - 32, by omega⟩
            rw [hk', pow_add]
            have := Nat.lt_two_pow_self (n := k)
            nlinarith [Nat.one_le_two_pow (n := k)]
          omega
    have : ((20 * P * 2 : ℕ) : ℝ) ≤ (2 ^ (P / 2) : ℕ) := by exact_mod_cast this
    push_cast at this; linarith
  have h2 : 40 * 2 ^ P * (1 / 5 : ℝ) ^ (2 * P + 1) ≤ 2 ^ (P / 2) / 2 := by
    have h5 : (1 / 5 : ℝ) ^ (2 * P + 1) ≤ (1 / 4) ^ P * (1 / 5) := by
      rw [pow_succ, pow_mul]
      gcongr
      norm_num
    have : 40 * 2 ^ P * ((1 / 4 : ℝ) ^ P * (1 / 5)) = 8 * (1 / 2) ^ P := by
      rw [show (1 / 4 : ℝ) = (1 / 2) * (1 / 2) by norm_num, mul_pow]
      have h22 : (2 : ℝ) ^ P * (1 / 2) ^ P = 1 := by rw [← mul_pow]; norm_num
      linear_combination (8 * (1 / 2 : ℝ) ^ P) * h22
    calc 40 * 2 ^ P * (1 / 5 : ℝ) ^ (2 * P + 1) ≤ 40 * 2 ^ P * ((1 / 4 : ℝ) ^ P * (1 / 5)) := by
          gcongr
      _ = 8 * (1 / 2) ^ P := this
      _ ≤ 1 := by
          have : (1 / 2 : ℝ) ^ P ≤ (1 / 2) ^ 3 := pow_le_pow_of_le_one (by norm_num) (by norm_num)
            (by omega)
          norm_num at this ⊢; linarith
      _ ≤ 2 ^ (P / 2) / 2 := by
          have : (2 : ℝ) ≤ 2 ^ (P / 2) := by
            calc (2 : ℝ) = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ (P / 2) := pow_le_pow_right₀ (by norm_num) (by omega)
          linarith
  have hP2 : (2 : ℝ) ^ P = 2 ^ (P / 2) * 2 ^ (P - P / 2) := by
    rw [← pow_add]; congr 1; omega
  have hge : (2 : ℝ) ^ (P / 2) ≤ 2 ^ (P - P / 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  have hpos : (0 : ℝ) < 2 ^ (P / 2) := by positivity
  have hsum : 20 * (P : ℝ) + 40 * 2 ^ P * (1 / 5 : ℝ) ^ (2 * P + 1) ≤ 2 ^ (P / 2) := by linarith
  calc (20 * (P : ℝ) + 40 * 2 ^ P * (1 / 5 : ℝ) ^ (2 * P + 1)) * 2 ^ (P / 2)
      ≤ 2 ^ (P / 2) * 2 ^ (P / 2) := by gcongr
    _ ≤ 2 ^ (P / 2) * 2 ^ (P - P / 2) := by gcongr
    _ = 2 ^ P := hP2.symm

theorem piInt_nonneg : 0 ≤ piInt (Pbits κ) (Pbits κ) := by
  have h := piInt_err (Pbits κ) (Pbits κ)
  have he := errPi_le κ
  unfold errPi at he
  have hP : (0 : ℝ) < 2 ^ Pbits κ := by positivity
  rw [div_le_iff₀ hP] at he
  have hpi := Real.pi_gt_three
  have hhalf : (1 : ℝ) / 2 ^ (Pbits κ / 2) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  have : (0 : ℝ) ≤ piInt (Pbits κ) (Pbits κ) := by
    rw [abs_le] at h; nlinarith
  exact_mod_cast this

theorem piHat_err : |piHat κ - Real.pi| ≤ errPi κ := by
  have h := piInt_err (Pbits κ) (Pbits κ)
  have hn : (piNat κ : ℝ) = piInt (Pbits κ) (Pbits κ) := by
    unfold piNat; exact_mod_cast Int.toNat_of_nonneg (piInt_nonneg κ)
  have hP : (0 : ℝ) < 2 ^ Pbits κ := by positivity
  have e : piHat κ - Real.pi =
      ((piInt (Pbits κ) (Pbits κ) : ℝ) - Real.pi * 2 ^ Pbits κ) / 2 ^ Pbits κ := by
    unfold piHat; rw [hn]; field_simp
  rw [e, abs_div, abs_of_pos hP]
  unfold errPi
  exact div_le_div_of_nonneg_right h hP.le


/-! ### The acceptance probability -/

noncomputable def δP : ℝ := errPi κ * 4 ^ (Lg κ + 1)
noncomputable def ηN : ℝ := (1 + 2 / (Nterms κ).factorial) ^ Ecnt κ

theorem τ_sq : τ κ ^ 2 = 2 ^ (2 * κ + 6) := by
  unfold τ; rw [← pow_mul]; ring_nf

theorem zsq_le (v : ℕ) (hv : v < 2 ^ (Aex κ + 1)) :
    ((zOf κ v : ℤ) : ℝ) ^ 2 / τ κ ^ 2 ≤ 4 ^ (Lg κ + 1) := by
  have h1 : -(2 : ℤ) ^ Aex κ ≤ zOf κ v := by unfold zOf; omega
  have h2 : zOf κ v < 2 ^ Aex κ := by
    unfold zOf; have : (v : ℤ) < 2 ^ (Aex κ + 1) := by exact_mod_cast hv
    rw [pow_succ] at this; linarith
  have hsq : ((zOf κ v : ℤ) : ℝ) ^ 2 ≤ ((2 : ℝ) ^ Aex κ) ^ 2 := by
    have a1 : (-(2 : ℝ) ^ Aex κ) ≤ ((zOf κ v : ℤ) : ℝ) := by exact_mod_cast h1
    have a2 : ((zOf κ v : ℤ) : ℝ) ≤ (2 : ℝ) ^ Aex κ := by exact_mod_cast h2.le
    nlinarith
  rw [τ_sq, div_le_iff₀ (by positivity)]
  calc ((zOf κ v : ℤ) : ℝ) ^ 2 ≤ ((2 : ℝ) ^ Aex κ) ^ 2 := hsq
    _ = 4 ^ (Lg κ + 1) * 2 ^ (2 * κ + 6) := by
        unfold Aex
        rw [← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]; ring_nf

theorem y_eq (v : ℕ) :
    (yN κ v : ℝ) / yD κ = piHat κ * (((zOf κ v : ℤ) : ℝ) ^ 2 / τ κ ^ 2) := by
  unfold yN yD piHat
  rw [τ_sq]
  have hz : (((zOf κ v).natAbs : ℕ) : ℝ) ^ 2 = ((zOf κ v : ℤ) : ℝ) ^ 2 := by
    rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  push_cast
  rw [hz, pow_add, pow_add]
  field_simp
  ring

theorem piHat_le : piHat κ ≤ 4 := by
  have h := abs_le.mp (piHat_err κ)
  have he := errPi_le κ
  have hp := Real.pi_lt_d2
  have : (1 : ℝ) / 2 ^ (Pbits κ / 2) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (Pbits κ / 2) := pow_le_pow_right₀ (by norm_num) (by have := P_ge κ; omega)
  linarith [h.2]

theorem piHat_nonneg : 0 ≤ piHat κ := by unfold piHat; positivity

theorem yN_le (v : ℕ) (hv : v < 2 ^ (Aex κ + 1)) : yN κ v ≤ Ecnt κ * yD κ := by
  have h : (yN κ v : ℝ) / yD κ ≤ Ecnt κ := by
    rw [y_eq]
    have hz := zsq_le κ v hv
    calc piHat κ * (((zOf κ v : ℤ) : ℝ) ^ 2 / τ κ ^ 2) ≤ 4 * 4 ^ (Lg κ + 1) :=
          mul_le_mul (piHat_le κ) hz (by positivity) (by norm_num)
      _ = Ecnt κ := by unfold Ecnt; push_cast; ring
  have hyD : (0 : ℝ) < yD κ := by unfold yD; positivity
  rw [div_le_iff₀ hyD] at h
  exact_mod_cast h

theorem sNum_ge_sDen (yN yD E N : ℕ) (hN : 0 < N) : sDen yD E N ≤ sNum yN yD E N := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  unfold sNum sDen
  rw [Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Nat.sub_zero, Nat.factorial_zero, Nat.div_one, Nat.add_sub_cancel]
  exact Nat.le_add_left _ _


theorem ceil_bounds (X a : ℕ) (ha : 0 < a) :
    (X : ℝ) / a ≤ ((X + a - 1) / a : ℕ) ∧ (((X + a - 1) / a : ℕ) : ℝ) < X / a + 1 := by
  set c := (X + a - 1) / a
  have h1 : ¬ c * a < X := fun h => lt_irrefl c ((lt_ceil_iff c a X ha).mpr h)
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  constructor
  · rw [div_le_iff₀ ha']; exact_mod_cast not_lt.mp h1
  · rcases Nat.eq_zero_or_pos c with hc | hc
    · rw [hc]; push_cast; positivity
    · have h2 : (c - 1) * a < X := (lt_ceil_iff (c - 1) a X ha).mp (by omega)
      have h3 : ((c - 1 : ℕ) : ℝ) * a < X := by exact_mod_cast h2
      push_cast [Nat.cast_sub (by omega : 1 ≤ c)] at h3
      rw [← sub_lt_iff_lt_add, lt_div_iff₀ ha']
      linarith

/-- The exact acceptance probability as a real number. -/
theorem pacc_eq (v : ℕ) :
    pacc κ v = ENNReal.ofReal ((((2 ^ Tbits κ * Lden κ + Lnum κ v - 1) / Lnum κ v : ℕ) : ℝ) /
      2 ^ Tbits κ) := by
  have hN : 0 < Nterms κ := by unfold Nterms; omega
  have hden : 0 < sDen (yD κ) (Ecnt κ) (Nterms κ) :=
    sDen_pos (by unfold yD; positivity) (by unfold Ecnt; positivity)
  have hnum : 0 < Lnum κ v := by
    unfold Lnum; exact pow_pos (hden.trans_le (sNum_ge_sDen _ _ _ _ hN)) _
  have hle : Lden κ ≤ Lnum κ v := by
    unfold Lden Lnum; exact Nat.pow_le_pow_left (sNum_ge_sDen _ _ _ _ hN) _
  unfold pacc
  have hf : ((Finset.range (2 ^ Tbits κ)).filter fun u => accept κ v u = true) =
      (Finset.range (2 ^ Tbits κ)).filter fun u => u * Lnum κ v < 2 ^ Tbits κ * Lden κ := by
    ext u; simp [accept]
  rw [hf, card_accept _ _ _ hnum hle, ENNReal.ofReal_div_of_pos (by positivity),
    ENNReal.ofReal_natCast]
  congr 1
  rw [ENNReal.ofReal_pow (by norm_num)]; simp


/-- The common facts: `1 ≤ s`, `s^E ≤ e^y ≤ s^E ηN`, and the bounds on `pacc` in terms of `s`. -/
theorem pacc_facts (v : ℕ) (hv : v < 2 ^ (Aex κ + 1)) :
    let sr : ℝ := (sNum (yN κ v) (yD κ) (Ecnt κ) (Nterms κ) : ℝ) / sDen (yD κ) (Ecnt κ) (Nterms κ)
    let y : ℝ := (yN κ v : ℝ) / yD κ
    1 ≤ sr ∧ sr ^ Ecnt κ ≤ Real.exp y ∧ Real.exp y ≤ sr ^ Ecnt κ * ηN κ ∧
      (1 / sr ^ Ecnt κ ≤ (((2 ^ Tbits κ * Lden κ + Lnum κ v - 1) / Lnum κ v : ℕ) : ℝ) / 2 ^ Tbits κ) ∧
      ((((2 ^ Tbits κ * Lden κ + Lnum κ v - 1) / Lnum κ v : ℕ) : ℝ) / 2 ^ Tbits κ ≤
        1 / sr ^ Ecnt κ + 1 / 2 ^ Tbits κ) := by
  intro sr y
  have hN : 0 < Nterms κ := by unfold Nterms; omega
  have hyD : 0 < yD κ := by unfold yD; positivity
  have hE : 0 < Ecnt κ := by unfold Ecnt; positivity
  have hden : 0 < sDen (yD κ) (Ecnt κ) (Nterms κ) := sDen_pos hyD hE
  have hge := sNum_ge_sDen (yN κ v) (yD κ) (Ecnt κ) (Nterms κ) hN
  have hdr : (0 : ℝ) < sDen (yD κ) (Ecnt κ) (Nterms κ) := by exact_mod_cast hden
  have hs1 : 1 ≤ sr := by
    simp only [sr]; rw [le_div_iff₀ hdr, one_mul]; exact_mod_cast hge
  have hs0 : 0 < sr := by linarith
  have hlow := exp_ge_pow (yN κ v) (yD κ) (Ecnt κ) (Nterms κ) hyD hE
  have hhigh := exp_le_pow (yN κ v) (yD κ) (Ecnt κ) (Nterms κ) hyD hE hN (yN_le κ v hv)
  have hmul : (sr + 2 / (Nterms κ).factorial) ^ Ecnt κ ≤ sr ^ Ecnt κ * ηN κ := by
    unfold ηN
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have ht : (0 : ℝ) ≤ 2 / (Nterms κ).factorial := by positivity
    have := mul_le_mul_of_nonneg_right hs1 ht
    linarith
  -- the ratio `Lden / Lnum = 1 / s^E`
  have hnum : 0 < Lnum κ v := by unfold Lnum; exact pow_pos (hden.trans_le hge) _
  have hratio : (Lden κ : ℝ) / Lnum κ v = 1 / sr ^ Ecnt κ := by
    unfold Lden Lnum; simp only [sr]; push_cast
    rw [div_pow, one_div_div]
  have hc := ceil_bounds (2 ^ Tbits κ * Lden κ) (Lnum κ v) hnum
  have hT : (0 : ℝ) < 2 ^ Tbits κ := by positivity
  have hX : ((2 ^ Tbits κ * Lden κ : ℕ) : ℝ) / Lnum κ v / 2 ^ Tbits κ = 1 / sr ^ Ecnt κ := by
    rw [← hratio]; push_cast; field_simp
  refine ⟨hs1, hlow, hhigh.trans hmul, ?_, ?_⟩
  · rw [← hX]; exact div_le_div_of_nonneg_right hc.1 hT.le
  · calc (((2 ^ Tbits κ * Lden κ + Lnum κ v - 1) / Lnum κ v : ℕ) : ℝ) / 2 ^ Tbits κ
        ≤ (((2 ^ Tbits κ * Lden κ : ℕ) : ℝ) / Lnum κ v + 1) / 2 ^ Tbits κ :=
          div_le_div_of_nonneg_right hc.2.le hT.le
      _ = 1 / sr ^ Ecnt κ + 1 / 2 ^ Tbits κ := by rw [add_div, hX]

theorem gw_eq_exp (z : ℤ) : gw (τ κ) z = Real.exp (-(Real.pi * ((z : ℝ) ^ 2 / τ κ ^ 2))) := by
  unfold gw; congr 1; ring

theorem y_bounds (v : ℕ) (hv : v < 2 ^ (Aex κ + 1)) :
    |(yN κ v : ℝ) / yD κ - Real.pi * (((zOf κ v : ℤ) : ℝ) ^ 2 / τ κ ^ 2)| ≤ δP κ := by
  have hX : (0 : ℝ) ≤ ((zOf κ v : ℤ) : ℝ) ^ 2 / τ κ ^ 2 := by positivity
  rw [y_eq, ← sub_mul, abs_mul, abs_of_nonneg hX]
  unfold δP
  exact mul_le_mul (piHat_err κ) (zsq_le κ v hv) hX (by unfold errPi; positivity)

theorem pacc_ge (v : ℕ) (hv : v < 2 ^ (Aex κ + 1)) :
    ENNReal.ofReal (Real.exp (-δP κ) * gw (τ κ) (zOf κ v)) ≤ pacc κ v := by
  obtain ⟨hs1, hlow, -, hp, -⟩ := pacc_facts κ v hv
  rw [pacc_eq]
  apply ENNReal.ofReal_le_ofReal
  refine le_trans ?_ hp
  have hy := abs_le.mp (y_bounds κ v hv)
  rw [gw_eq_exp, ← Real.exp_add]
  calc Real.exp (-δP κ + -(Real.pi * (((zOf κ v : ℤ) : ℝ) ^ 2 / τ κ ^ 2)))
      ≤ Real.exp (-((yN κ v : ℝ) / yD κ)) := Real.exp_le_exp.mpr (by linarith)
    _ = 1 / Real.exp ((yN κ v : ℝ) / yD κ) := by rw [Real.exp_neg, one_div]
    _ ≤ _ := one_div_le_one_div_of_le (by have := hs1; positivity) hlow

theorem pacc_le (v : ℕ) (hv : v < 2 ^ (Aex κ + 1)) :
    pacc κ v ≤ ENNReal.ofReal (Real.exp (δP κ) * ηN κ * gw (τ κ) (zOf κ v) + 1 / 2 ^ Tbits κ) := by
  obtain ⟨hs1, -, hhigh, -, hp⟩ := pacc_facts κ v hv
  rw [pacc_eq]
  apply ENNReal.ofReal_le_ofReal
  refine hp.trans ?_
  have hy := abs_le.mp (y_bounds κ v hv)
  gcongr
  have hη : 0 < ηN κ := by unfold ηN; positivity
  set sr := (sNum (yN κ v) (yD κ) (Ecnt κ) (Nterms κ) : ℝ) / sDen (yD κ) (Ecnt κ) (Nterms κ)
  have hsE : 0 < sr ^ Ecnt κ := by positivity
  have hey : 0 < Real.exp ((yN κ v : ℝ) / yD κ) := Real.exp_pos _
  rw [div_le_iff₀ hsE]
  have h1 : Real.exp ((yN κ v : ℝ) / yD κ) * Real.exp (-((yN κ v : ℝ) / yD κ)) = 1 := by
    rw [← Real.exp_add]; simp
  have h2 : Real.exp (-((yN κ v : ℝ) / yD κ)) ≤ Real.exp (δP κ) * gw (τ κ) (zOf κ v) := by
    rw [gw_eq_exp, ← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  calc (1 : ℝ) = Real.exp ((yN κ v : ℝ) / yD κ) * Real.exp (-((yN κ v : ℝ) / yD κ)) := h1.symm
    _ ≤ (sr ^ Ecnt κ * ηN κ) * (Real.exp (δP κ) * gw (τ κ) (zOf κ v)) :=
        mul_le_mul hhigh h2 (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

end

end SigabaNeo.Lattices.Trapdoor.Family


