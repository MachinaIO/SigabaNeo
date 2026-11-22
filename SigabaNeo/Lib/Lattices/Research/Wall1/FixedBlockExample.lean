module

public import SigabaNeo.Lib.Lattices.Research.Wall1.FixedBlockRestart
import all SigabaNeo.Lib.Lattices.Research.Wall1.FixedBlockCount
import all SigabaNeo.Lib.Lattices.Research.Wall1.FixedBlockRestart
import all SigabaNeo.Lib.Lattices.Research.Wall1.FixedBlockChernoff
import Mathlib.Analysis.Complex.ExponentialBounds
import all SigabaNeo.Lib.Lattices.Research.Wall1.AttackLattice
import all SigabaNeo.Lib.Lattices.Research.Wall1.RestartLift
import Mathlib.Tactic

/-! # A flat abstract profile with a nonempty prefix -/

public section
namespace SigabaNeo.Wall1.FixedBlockExample

open Classical InnerProductSpace AttackLattice RestartLift

private noncomputable def side : ℝ := √3329
private theorem side_sq : side^2 = 3329 := Real.sq_sqrt (by norm_num)
private theorem side_gt : 50 < side := by
  have := Real.sqrt_nonneg 3329
  change 50 < √3329
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3329)]

private noncomputable def axes := EuclideanSpace.basisFun (Fin 2) ℝ
private noncomputable def basis :=
  axes.toBasis.unitsSMul (fun _ ↦ Units.mk0 side (by linarith [side_gt]))
private theorem basis_apply i : basis i = side • axes i := by
  simp [basis, Module.Basis.unitsSMul_apply, Units.smul_def]

private noncomputable def B : FinalBlock 2 1 :=
  canonicalFinal (J := 1) rfl basis basis.linearIndependent

private noncomputable def pre : PrefixData 2 := canonicalPrefix (J := 1) (d := 1) basis

private theorem terminal_axis : (B.basis 0).val = basis 1 := by
  change ((Module.Basis.span (projRem_linearIndependent basis.linearIndependent)) (0 : Fin 1)).val = _
  rw [Module.Basis.coe_span_apply]
  change hproj (J := 1) (d := 1) basis (basis 1) = _
  apply Submodule.starProjection_eq_self_iff.2
  rw [preSpan, Submodule.mem_orthogonal']
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    have eq : preVec (J := 1) (d := 1) basis j = basis 0 := by
      fin_cases j; rfl
    rw [eq, basis_apply, basis_apply, real_inner_smul_left, real_inner_smul_right]
    simp [axes.orthonormal.inner_eq_zero (show (1 : Fin 2) ≠ 0 by decide)]
  | zero => simp
  | add => simp_all [inner_add_right]
  | smul => simp_all [real_inner_smul_right]

private theorem axis_norm (i : Fin 2) : ‖basis i‖ = side := by
  simp [basis_apply, norm_smul, Real.norm_of_nonneg (by linarith [side_gt] : 0 ≤ side),
    axes.orthonormal.norm_eq_one]

private theorem minimum : B.MinFloor side := by
  intro h hh hn
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hh
  rw [Fin.sum_univ_one] at hc
  have cn : c 0 ≠ 0 := fun eq ↦ hn (by simpa [eq] using hc.symm)
  rw [← hc, ← Int.cast_smul_eq_zsmul ℝ, norm_smul, Real.norm_eq_abs]
  have mag : (1 : ℝ) ≤ |(c 0 : ℝ)| := by exact_mod_cast Int.one_le_abs cn
  have len : ‖B.basis 0‖ = side := by
    change ‖(B.basis 0).val‖ = _
    rw [terminal_axis, axis_norm]
  rw [len]
  exact le_mul_of_one_le_left (by linarith [side_gt]) mag

private theorem prefix_norm : ‖pre.bs 0‖ = side := by
  change ‖gramSchmidt ℝ (heightZeroFamily (J := 1) (d := 1) basis) (⊥ : ℕ)‖ = _
  rw [gramSchmidt_bot]
  change ‖horiz 2 (basis 0)‖ = _
  have eq := DecoupledDecoder.norm_sq_snocE (basis 0) 0
  rw [← horiz_apply, axis_norm] at eq
  nlinarith [norm_nonneg (horiz 2 (basis 0)), side_gt]

private theorem exp_pow_two (n : ℕ) : (2 : ℝ)^n ≤ Real.exp n := by
  simpa only [← Real.exp_nat_mul, mul_one] using
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) Real.exp_one_gt_two.le n

private theorem terminal_budget : B.smoothError 36 side ≤ 1/200 := by
  have h36 : √(36:ℝ) = 6 := by norm_num
  have h37 : √(1+(36:ℝ)) < 7 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1+36), Real.sqrt_nonneg (1+36)]
  have charge : (∑ k ∈ Finset.Icc 2 ⌊√(1+(36:ℝ))⌋₊, B.highCharge 36 side k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkle := (Nat.le_floor_iff (Real.sqrt_nonneg _)).1 (Finset.mem_Icc.mp hk).2
    have hr := Real.sqrt_le_sqrt (show 1+(36:ℝ)-(k:ℝ)^2 ≤ 1+36 by linarith [sq_nonneg (k:ℝ)])
    rw [FinalBlock.highCharge, ite_eq_left (by rw [h36]; linarith [side_gt])]
  rw [FinalBlock.smoothError, ite_eq_left ⟨by decide, by norm_num,
    h37.trans (by linarith [side_gt])⟩, charge, FinalBlock.oneCharge,
    ite_eq_left (by rw [h36]; linarith [side_gt]), add_zero, add_zero]
  apply (min_le_right _ _).trans
  have e5 := exp_pow_two 5
  have e8 := exp_pow_two 8
  norm_num at e5 e8
  have log24 : Real.log 24 < 5 := (Real.log_lt_iff_lt_exp (by norm_num)).2 (by linarith)
  norm_num [FinalBlock.normChernoff]
  apply (Real.exp_le_exp.mpr (show _ ≤ -(8:ℝ) by linarith)).trans
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) (by linarith)

/-- The canonical prefix GS length times the terminal length is 3329. The same
basis meets both allowances, each 1/200, with a nonempty prefix and final block. -/
theorem exists_flat_accepted :
    ∃ (β : Module.Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2))) (L : ℝ),
      let F := canonicalFinal (J := 1) (d := 1) rfl β β.linearIndependent
      let P := canonicalPrefix (J := 1) (d := 1) β
      (∀ i, ‖β i‖ = L) ∧ ‖P.bs 0‖ = L ∧ ‖F.basis 0‖ = L ∧
      ‖P.bs 0‖ * ‖F.basis 0‖ = 3329 ∧
      F.countAccept 1 (fun m ↦ ‖P.bs m‖) 36 L (1/200) (1/200) := by
  have terminal_norm : ‖B.basis 0‖ = side := by
    change ‖(B.basis 0).val‖ = _
    rw [terminal_axis, axis_norm]
  refine ⟨basis, side, axis_norm, prefix_norm, terminal_norm, ?_, minimum, terminal_budget, ?_⟩
  · change ‖pre.bs 0‖ * ‖B.basis 0‖ = _
    rw [prefix_norm, terminal_norm, ← sq, side_sq]
  · change (∑ m ∈ Finset.range 1, 2 * Real.exp (-‖pre.bs m‖^2 / 12)) ≤ 1/200
    rw [Finset.sum_range_one, prefix_norm, side_sq,
      show -(3329 : ℝ)/12 = -(3329/12) by ring, Real.exp_neg]
    have bound := (exp_pow_two 9).trans (Real.exp_le_exp.mpr (by norm_num : (9 : ℝ) ≤ 3329/12))
    rw [inv_eq_one_div, mul_one_div, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
    norm_num at bound
    linarith

end SigabaNeo.Wall1.FixedBlockExample

#print axioms SigabaNeo.Wall1.FixedBlockExample.exists_flat_accepted
