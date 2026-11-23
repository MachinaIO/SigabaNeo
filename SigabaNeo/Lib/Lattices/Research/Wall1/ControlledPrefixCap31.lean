import SigabaNeo.Lib.Lattices.Research.Wall1.ControlledPrefixDescent

/-! Lower enclosures of the flag radii for direct backward descent through draw 31. -/
noncomputable section
namespace SigabaNeo.Wall1.ControlledPlane.PrefixCap
open Real Finset BKZ

private def base : ℚ := 33/32
private def powers : Array ℕ := #[
  0, 0, 4, 7, 11, 13, 16, 19, 22, 24, 28, 28, 31, 31, 34, 34,
  37, 37, 39, 39, 42, 42, 44, 44, 45, 46, 48, 48, 50, 50, 51, 51,
  53, 53, 54, 54, 56, 56, 57, 57, 59, 59, 60, 60, 61, 61, 62, 62,
  63, 63, 64, 64, 66, 66, 67, 67, 68, 68, 68, 68, 69, 69, 70, 70,
  71, 71, 72, 72, 73, 73, 74, 74, 74, 74, 75, 75, 76, 76, 77, 77,
  77, 77, 78, 78, 79, 79, 80, 80, 80, 80, 81, 81, 81, 81, 82, 82,
  83, 83, 83, 83, 84, 84, 84, 84, 85, 85, 86, 86, 86, 86, 87, 87,
  87, 87, 88, 88, 88, 88, 89, 89, 89, 89, 90, 90, 90, 90, 91, 91,
  91, 91, 92, 92, 92, 92, 92, 92, 93, 93, 93, 93, 94, 94, 94, 94,
  95, 95, 95, 95, 95, 95, 96, 96, 96, 96, 97, 97]
private def e (k : ℕ) := powers[k]?.getD 0

private theorem even_bound (n : ℕ) (b : ℚ) (hn : 0 < n) (hb : 0 ≤ b)
    (hc : (b * (3.142:ℚ)/2)^n ≤ (n+1).factorial) : (b:ℝ) ≤ blichfeldtConstant (2*n) := by
  have h : 0 < (n:ℝ) := by exact_mod_cast hn
  unfold blichfeldtConstant
  rw [show ((2*n:ℕ):ℝ)/2+2 = ((n+1:ℕ):ℝ)+1 by push_cast; ring, Gamma_nat_eq_factorial,
    show (2:ℝ)/((2*n:ℕ):ℝ) = (n:ℝ)⁻¹ by push_cast; field_simp]
  have h' := (Rat.cast_le (K := ℝ)).2 hc
  push_cast at h'
  have hb' : 0 ≤ (b:ℝ) := by exact_mod_cast hb
  have hh : ((b:ℝ)*π/2)^n ≤ (n+1).factorial := by
    refine le_trans ?_ h'
    apply pow_le_pow_left₀ (by positivity)
    gcongr
    linarith [pi_lt_d20]
  have he := rpow_le_rpow (by positivity) hh (inv_nonneg.mpr h.le)
  rw [← rpow_natCast,← rpow_mul (by positivity),mul_inv_cancel₀ h.ne',rpow_one] at he
  rw [div_mul_eq_mul_div,le_div_iff₀ pi_pos]
  linarith

private def hp : ℕ → ℚ
  | 2 => 4/3 | 3 => 2 | 4 => 4 | 5 => 8 | 6 => 64/3 | 7 => 64 | 8 => 256 | _ => 1

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem power_check (k : Fin 156) :
    if k.val ≤ 8 then (base^e k.val)^k.val ≤ hp k.val
    else if k.val = 24 then base^e k.val ≤ 4
    else (base^e k.val * (3.142:ℚ)/2)^(k.val/2) ≤ (k.val/2+1).factorial := by
  revert k
  decide +kernel

private theorem gamma_bound (k : ℕ) (h : 2 ≤ k) (h' : k ≤ 155) :
    ((base:ℝ)^e k) ≤ flagGamma k := by
  have hc := power_check ⟨k,by omega⟩
  simp only at hc
  by_cases low : k ≤ 8
  · simp only [low,ite_true] at hc
    have hh : (hp k : ℝ) = hermitePower k := by interval_cases k <;> norm_num [hp,hermitePower]
    have hpos : (0:ℝ) < hermitePower k := by interval_cases k <;> norm_num [hermitePower]
    have he := (Rat.cast_le (K:=ℝ)).2 hc
    push_cast at he
    rw [hh] at he
    rw [flagGamma,ite_eq_right (by omega),ite_eq_right (by omega),auditedGamma,ite_eq_left ⟨h,low⟩]
    have hk : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    rw [div_eq_mul_inv,← Real.rpow_def_of_pos hpos]
    apply (le_rpow_inv_iff_of_pos (by unfold base; positivity) hpos.le hk).2
    rwa [rpow_natCast]
  · simp only [low,ite_false] at hc
    by_cases h24 : k = 24
    · subst k
      rw [flagGamma,ite_eq_right (by decide),ite_eq_left rfl]
      exact_mod_cast (show base^e 24 ≤ (4:ℚ) by decide +kernel)
    · simp only [h24,ite_false] at hc
      rw [flagGamma,ite_eq_right (by omega),ite_eq_right h24,auditedGamma,ite_eq_right (by omega)]
      have H := even_bound (k/2) (base^e k) (by omega) (by unfold base; positivity) hc
      rw [Rat.cast_pow] at H
      exact H.trans (blichfeldtConstant_mono (by omega) (by omega))

private def peel (i : ℕ) : ℚ := e i / (2*((i:ℚ)-1))
private def mass (k : ℕ) : ℚ := e k / 2 + ∑ i ∈ Icc 2 k, peel i
private def power (k : ℕ) : ℕ := (47*(k-124)+9)/10

set_option maxHeartbeats 0 in
private theorem cap_check : ∀ k : Fin 156, 124 ≤ k.val →
    (1.155:ℚ)^(k.val-124) ≤ base^power k.val ∧ (power k.val:ℚ) ≤ mass k.val := by decide +kernel

theorem cap31 {k : ℕ} (lo : 124 ≤ k) (hi : k ≤ 155) :
    (1.155:ℝ)^(k-124) ≤ flagCap k := by
  have b : 1 ≤ (base:ℝ) := by norm_num [base]
  have bp : 0 < (base:ℝ) := by linarith
  have H (i : ℕ) (h : i ∈ Icc 2 k) :
      (base:ℝ)^(peel i : ℝ) ≤ flagGamma i ^ (1/(2*((i:ℝ)-1))) := by
    obtain ⟨hl,hu⟩ := mem_Icc.mp h
    have hl' : (2:ℝ) ≤ i := by exact_mod_cast hl
    have he := rpow_le_rpow (pow_nonneg bp.le _) (gamma_bound i hl (by omega))
      (by apply div_nonneg (by norm_num); linarith : 0 ≤ 1/(2*((i:ℝ)-1)))
    rw [← rpow_natCast,← rpow_mul bp.le] at he
    convert he using 2
    push_cast [peel]
    ring
  have hprod := prod_le_prod₀ (fun i (_ : i ∈ Icc 2 k) ↦ (rpow_pos_of_pos bp (peel i:ℝ)).le) H
  rw [← rpow_sum_of_pos bp] at hprod
  have hs := sqrt_le_sqrt (gamma_bound k (by omega) hi)
  rw [sqrt_eq_rpow,← rpow_natCast,← rpow_mul bp.le] at hs
  have hh := mul_le_mul hs hprod (rpow_nonneg bp.le _) (sqrt_nonneg _)
  rw [← rpow_add bp] at hh
  obtain ⟨hc,hd⟩ := cap_check ⟨k,by omega⟩ lo
  change (1.155:ℚ)^(k-124) ≤ base^power k at hc
  change (power k:ℚ) ≤ mass k at hd
  have hc' := (Rat.cast_le (K:=ℝ)).2 hc
  push_cast at hc'
  apply hc'.trans
  rw [← rpow_natCast]
  have he := (Rat.cast_le (K:=ℝ)).2 hd
  push_cast [mass] at he
  rw [div_eq_mul_inv] at he
  rw [← one_div (2:ℝ)] at he
  apply (rpow_le_rpow_of_exponent_le b he).trans
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
  exact hh.trans (le_max_right ..)

theorem descent_cap {t i : ℕ} (ht : t ≤ 31) (hi : i ≤ t) :
    (1.155:ℝ)^(t-i) ≤ flagCap (155-i) :=
  (pow_le_pow_right₀ (by norm_num : 1 ≤ (1.155:ℝ))
    (show t-i ≤ (155-i)-124 by omega)).trans (cap31 (by omega) (by omega))

end SigabaNeo.Wall1.ControlledPlane.PrefixCap

#print axioms SigabaNeo.Wall1.ControlledPlane.PrefixCap.cap31
