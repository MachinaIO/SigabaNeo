import SigabaNeo.Lib.Lattices.Research.Wall1.FixedBlockDualCharge
import SigabaNeo.Lib.Lattices.Research.Wall1.FixedBlockCap506
import SigabaNeo.Lib.Lattices.Research.Wall1.FixedBlockHeight506
import SigabaNeo.Lib.Lattices.Research.Wall1.FixedBlockModel506

/-! # The width-506 conditional bound with its nonintegral remainder -/

noncomputable section
namespace SigabaNeo.Wall1.FinalBlock
open Model506 Real ProbabilityTheory ZLattice

variable {N : ℕ} (B : FinalBlock N 505)

private theorem width_pos : 0 < width := by unfold width t; positivity
private theorem width_sq : width^2 = π/t := Real.sq_sqrt (by unfold t; positivity)

private theorem prefactor_eq (k : ℕ) :
    B.prefactor (1919/2) width k =
      exp (t*(960.5-(k:ℝ)^2)) * width^505 / covolume B.horizontal := by
  unfold prefactor
  rw [width_sq]
  congr 3
  field_simp [Real.pi_ne_zero]
  ring

/-- The zero Fourier mode, summed once per tested height. -/
def zeroMode506 := ∑ k ∈ Finset.Icc (2:ℕ) 30, B.prefactor (1919/2) width k

/-- The weighted contribution of all dual vectors outside the ambient integer section. -/
def nonintegralRemainder506 := ∑ k ∈ Finset.Icc (2:ℕ) 30,
  B.prefactor (1919/2) width k * B.nonintegralModes width k

theorem zeroMode506_lt (model : covolume B.horizontal = determinant) :
    B.zeroMode506 < 4.46272e-125 := by
  simpa [zeroMode506, B.prefactor_eq, model] using sum_prefactors_lt

private theorem zeroMode506_nonneg : 0 ≤ B.zeroMode506 := by
  apply Finset.sum_nonneg
  intro k _
  unfold prefactor
  positivity [width_pos, covolume_pos B.horizontal MeasureTheory.volume]

private theorem integerMode_eq (x : stdSection B.V) :
    gaussianWeight (1/width) x.val = exp (-aliasDecay505 * ‖x.val‖^2) := by
  unfold gaussianWeight aliasDecay505
  rw [div_pow, one_pow, div_div_eq_mul_div, div_one, width_sq]
  congr 1
  unfold t
  ring

/-- All nonzero integral aliases at the model determinant, across heights 2 through 30. -/
theorem integralCharge506_lt (model : covolume B.horizontal = determinant) :
    B.zeroMode506 * (∑' x : {x : stdSection B.V // x ≠ 0}, gaussianWeight (1/width) x.val.val) <
      2.23332e-138 := by
  simp_rw [integerMode_eq]
  rw [← integerSection_excess_eq B.V (show 0 < aliasDecay505 by unfold aliasDecay505; positivity)]
  exact integerSection_charge_505 _ (by rw [Module.finrank_eq_card_basis B.basis, Fintype.card_fin])
    B.zeroMode506_nonneg (B.zeroMode506_lt model).le

/-- Sum of the capped higher-height charges for an arbitrary physical covolume. -/
theorem highCharges506_le
    (inside : stdSection B.V ≤ metricDual B.horizontal) :
    ∑ k ∈ Finset.Icc (2:ℕ) 30, B.highCharge (1919/2) 54.82 k ≤
      B.zeroMode506 * (∑' x : stdSection B.V, exp (-aliasDecay505 * ‖x.val‖^2)) +
      B.nonintegralRemainder506 := by
  unfold zeroMode506 nonintegralRemainder506
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k hk
  have hk' : (k:ℝ) ≤ 30 := by exact_mod_cast (Finset.mem_Icc.mp hk).2
  have hkn : 0 ≤ (k:ℝ) := k.cast_nonneg
  have hk2 : (k:ℝ)^2 ≤ 30^2 := (sq_le_sq₀ hkn (by norm_num)).mpr hk'
  have hr : 0 ≤ 1+(1919/2:ℝ)-(k:ℝ)^2 := by linarith
  simpa only [integerMode_eq, mul_add] using B.highCharge_le_modes width_pos 54.82 k hr inside

/-- The zero mode fits into the rational slack in the cap enclosure. Only nonintegral
dual classes occur in the remainder. The minimum and covolume are physical block hypotheses. -/
theorem smoothError506_le (floor : B.MinFloor 54.82)
    (physical : B.horizontal ≤ projectedModule
      (cubicModule (EuclideanSpace.basisFun (Fin N) ℝ)) B.V)
    (model : covolume B.horizontal = determinant) :
    B.smoothError (1919/2) 54.82 ≤
      0.000478351 + 6.44e-14 + 2.24e-138 + B.nonintegralRemainder506 := by
  have hsq := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1+1919/2)
  have hpos := Real.sqrt_nonneg (1+(1919/2:ℝ))
  have lo : 30 ≤ √(1+(1919/2:ℝ)) := Real.le_sqrt_of_sq_le (by norm_num)
  have hi : √(1+(1919/2:ℝ)) < 31 := by nlinarith
  have cutoff : ⌊√(1+(1919/2:ℝ))⌋₊ = 30 := (Nat.floor_eq_iff hpos).2 ⟨lo, hi.trans_le (by norm_num)⟩
  rw [smoothError, ite_eq_left ⟨by decide, by norm_num, by linarith⟩, cutoff]
  apply (min_le_right _ _).trans
  have high := B.highCharges506_le (B.integral_le_dual physical)
  have m := B.zeroMode506_lt model
  have aliases := integerSection_charge_505 B.V (by rw [Module.finrank_eq_card_basis B.basis,
    Fintype.card_fin]) B.zeroMode506_nonneg m.le
  linarith only [high, m, aliases, normChernoff_505_lt_with_slack,
    B.oneCharge_505_le floor (1919/2)]

/-- Specialization to the projected integer null lattice at the note's ambient dimension,
modulus and number of rows. -/
theorem smoothError506_projected_null (B : FinalBlock 1023 505)
    (F : cubicModule (EuclideanSpace.basisFun (Fin 1023) ℝ) →ₗ[ℤ] (Fin 511 → ZMod 3329))
    (horizontal_eq : B.horizontal = B.projectedIntegerKernel F)
    (floor : B.MinFloor 54.82) (model : covolume B.horizontal = determinant) :
    B.smoothError (1919/2) 54.82 ≤
      0.000478351 + 6.44e-14 + 2.24e-138 + B.nonintegralRemainder506 :=
  B.smoothError506_le floor (horizontal_eq ▸ (B.projectedIntegerKernel_bounds F).1) model

end SigabaNeo.Wall1.FinalBlock

#print axioms SigabaNeo.Wall1.FinalBlock.zeroMode506_lt
#print axioms SigabaNeo.Wall1.FinalBlock.integralCharge506_lt
#print axioms SigabaNeo.Wall1.FinalBlock.highCharges506_le
#print axioms SigabaNeo.Wall1.FinalBlock.smoothError506_le
#print axioms SigabaNeo.Wall1.FinalBlock.smoothError506_projected_null
