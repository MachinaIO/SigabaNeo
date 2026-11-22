module

public import SigabaNeo.Lib.Lattices.Research.Wall1.SphericalPacking
public import SigabaNeo.Lib.Lattices.Research.Wall1.FixedBlockCount
import all SigabaNeo.Lib.Lattices.Research.Wall1.FixedBlockCount
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! # Rank-505 numerical enclosure of the nonzero Gaussian mass in (3) -/

public section
namespace SigabaNeo.Wall1

open Real

set_option maxRecDepth 4096

/-- An outward rational enclosure at the inverse squared scale `1/12`. -/
theorem packingConstant_505 :
    2 * (505+1 : ℝ)^2 * Gamma (1+505/2) * (2 / ((1/12)*54.82^2))^(505/2 : ℝ) ≤
      3.635e-26 := by
  let X : ℝ := 60000/7513081
  have hx : 0 ≤ X := by dsimp [X]; positivity
  have hp : sqrt π ≤ 1.772454 := (sqrt_le_iff).2 ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hs : sqrt X ≤ 0.089365 := (sqrt_le_iff).2 ⟨by norm_num, by norm_num [X]⟩
  have poweq : X^(505/2 : ℝ) = X^(252 : ℕ) * sqrt X := by
    rw [show (505/2 : ℝ) = (252 : ℕ) + 1/2 by norm_num, rpow_add' hx (by norm_num),
      rpow_natCast, ← sqrt_eq_rpow]
  have gam : Gamma (1+505/2) = (Nat.doubleFactorial 505 : ℝ)*sqrt π/2^253 := by
    convert Gamma_nat_add_one_add_half 252 using 2; norm_num
  rw [show 2 / ((1/12 : ℝ)*54.82^2) = X by norm_num [X], poweq, gam]
  calc
    _ ≤ 2*(505+1 : ℝ)^2 * ((Nat.doubleFactorial 505 : ℝ)*1.772454/2^253) *
        (X^(252 : ℕ)*0.089365) := by
      apply mul_le_mul
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)
      · exact mul_le_mul_of_nonneg_left hs (pow_nonneg hx _)
      · positivity
      · positivity
    _ ≤ _ := by
      have h : 2*(505+1 : ℚ)^2 * ((Nat.doubleFactorial 505 : ℚ)*1.772454/2^253) *
          ((60000/7513081 : ℚ)^252*0.089365) ≤ 3.635e-26 := by decide +kernel
      have hh := (Rat.cast_le (K := ℝ)).2 h
      dsimp only [X]
      push_cast [Rat.cast_ofScientific] at hh
      exact hh

/-- The full nonzero theta series at `u = 1/12` for a lattice of minimum at least 54.82. -/
theorem latticePackingExcess_505 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hE : Module.finrank ℝ E = 505) (H : Submodule ℤ E)
    (minimum : ∀ v ∈ H, v ≠ 0 → 54.82 ≤ ‖v‖) :
    (∑' v : {w : H // w ≠ 0}, exp (-((1/12 : ℝ) * ‖(v.val : E)‖^2))) ≤ 3.635e-26 :=
  (latticePackingExcess hE (by decide) H (by norm_num) (by norm_num) minimum).trans
    packingConstant_505

/-- Removing the zero term identifies the certificate with the intrinsic nonzero theta sum. -/
theorem FinalBlock.oneTheta_eq_nonzero {N d : ℕ} (B : FinalBlock N d) :
    B.oneTheta = ∑' v : {v : Submodule.span ℤ (Set.range B.basis) // v ≠ 0},
      exp (-((1/12 : ℝ)*‖(v.val : B.V)‖^2)) := by
  classical
  let H := Submodule.span ℤ (Set.range B.basis)
  let b := B.basis.restrictScalars ℤ
  let f (v : H) := exp (-((1/12 : ℝ)*‖(v : B.V)‖^2))
  have term (z : Fin d → ℤ) : exp (-(1/12 : ℝ) * ‖B.vector z‖^2) =
      f (b.equivFun.symm z) := by
    dsimp only [f]
    rw [Module.Basis.equivFun_symm_apply]
    simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul, b,
      Module.Basis.restrictScalars_apply, Int.cast_smul_eq_zsmul ℝ, vector, neg_mul]
  have hs : Summable (fun z : Fin d → ℤ ↦ exp (-(1/12 : ℝ)*‖B.vector z‖^2)) :=
    by simpa only [vector] using (latticeThetaProfile B.basis (s := 1/12) (by norm_num)).1
  simp_rw [term] at hs
  have hsf : Summable f := b.equivFun.toEquiv.symm.summable_iff.mp hs
  have split := hsf.sum_add_tsum_subtype_compl
    ({0} : Finset H)
  simp only [Finset.sum_singleton, f, ZeroMemClass.coe_zero, norm_zero,
    zero_pow (by decide : 2 ≠ 0), mul_zero, neg_zero, exp_zero] at split
  unfold oneTheta
  simp_rw [term]
  change (∑' z, f (b.equivFun.toEquiv.symm z)) - 1 = _
  rw [b.equivFun.toEquiv.symm.tsum_eq, ← split]
  rw [add_comm (1 : ℝ), add_sub_cancel_right]
  let e : {x : H // x ∉ ({0} : Finset H)} ≃ {x : H // x ≠ 0} :=
    Equiv.subtypeEquivRight (fun _ ↦ not_congr Finset.mem_singleton)
  simpa only [e, f, Equiv.subtypeEquivRight_apply] using
    e.tsum_eq (fun x ↦ f x.val)

/-- The full height-one theta excess from the verified minimum. -/
theorem FinalBlock.oneTheta_le_packing505 {N : ℕ} (B : FinalBlock N 505)
    (minimum : B.MinFloor 54.82) : B.oneTheta ≤ 3.635e-26 := by
  rw [B.oneTheta_eq_nonzero]
  exact latticePackingExcess_505 (E := B.V)
    (by rw [Module.finrank_eq_card_basis B.basis, Fintype.card_fin]) _ minimum

theorem FinalBlock.oneCharge_le_packing505 {N : ℕ} (B : FinalBlock N 505)
    (minimum : B.MinFloor 54.82) (a : ℝ) : B.oneCharge a 54.82 ≤ 3.635e-26 := by
  unfold oneCharge
  split_ifs
  · norm_num
  · exact (min_le_right _ _).trans (B.oneTheta_le_packing505 minimum)

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.packingConstant_505
#print axioms SigabaNeo.Wall1.latticePackingExcess_505

#print axioms SigabaNeo.Wall1.FinalBlock.oneTheta_le_packing505
#print axioms SigabaNeo.Wall1.FinalBlock.oneCharge_le_packing505
