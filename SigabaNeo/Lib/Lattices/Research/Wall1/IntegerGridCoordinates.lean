module

public import SigabaNeo.Lib.Lattices.Research.Wall1.IntegerGridGeometry
public import SigabaNeo.Lib.Lattices.Research.Wall1.IntegralShiftedGaussianCVP
import Mathlib.Tactic

public section
noncomputable section
namespace SigabaNeo.Wall1.IntegerGrid

open SigabaNeo.LLL SigabaNeo.SampleDeletion

/-- Concatenate the two coordinate blocks of an integer grid. -/
def joinBlocks {r n : ℕ} : ((Fin r ⊕ Fin n) → ℤ) ≃ₗ[ℤ] (Fin (r + n) → ℤ) :=
  LinearEquiv.funCongrLeft ℤ ℤ finSumFinEquiv.symm

theorem normSq_joinBlocks {r n : ℕ} (x : (Fin r ⊕ Fin n) → ℤ) :
    normSq (joinBlocks x) = normSq x :=
  finSumFinEquiv.symm.sum_comp (fun i ↦ (x i).natAbs ^ 2)

variable {d : ℕ} (S : Submodule ℤ (Fin d → ℤ))

/-- Distinct integer points have Euclidean distance at least one. -/
instance discreteImage : DiscreteTopology (S.map (intVec (d := d))) := by
  rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff]
  refine ⟨1, zero_lt_one, fun x hx ↦ ?_⟩
  rw [dist_zero_right] at hx
  have hsq := residual_sq S x 0
  simp only [map_zero, sub_zero] at hsq
  have hn : ‖(x : EuclideanSpace ℝ (Fin d))‖ < 1 := hx
  have hlt : (normSq (((realization S).symm x).val) : ℝ) < 1 := by
    rw [← hsq]
    nlinarith [norm_nonneg (x : EuclideanSpace ℝ (Fin d))]
  have hi : normSq (((realization S).symm x).val) < 1 := by exact_mod_cast hlt
  have hz : normSq (((realization S).symm x).val) = 0 := by omega
  rw [hz, Nat.cast_zero, sq_eq_zero_iff, norm_eq_zero] at hsq
  exact Subtype.ext hsq

/-- The Euclidean image of an integer submodule has the original integral coordinates. -/
def integralCoordinates (S : Submodule ℤ (Fin 638 → ℤ)) (t : Fin 638 → ℤ) :
    CVP638.IntegralCoordinates (S.map intVec) (intVec t) where
  coordinates := S.subtype.toAddMonoidHom.comp (realization S).symm.toAddMonoidHom
  injective := Subtype.val_injective.comp (realization S).symm.injective
  shift := t
  distance_sq := fun x ↦ residual_sq S x t

/-- Pulling back a Euclidean closest point minimizes the squared integer residual. -/
theorem minimizes_normSq_of_closest (t : Fin d → ℤ) (x : S.map intVec)
    (hx : ∀ y : S.map intVec, ‖(x : EuclideanSpace ℝ (Fin d)) - intVec t‖ ≤
      ‖(y : EuclideanSpace ℝ (Fin d)) - intVec t‖) (z : S) :
    normSq (((realization S).symm x).val - t) ≤ normSq (z.val - t) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (hx (realization S z)) 2
  rw [residual_sq, residual_sq, LinearEquiv.symm_apply_apply] at h
  exact_mod_cast h

end SigabaNeo.Wall1.IntegerGrid

#print axioms SigabaNeo.Wall1.IntegerGrid.discreteImage
#print axioms SigabaNeo.Wall1.IntegerGrid.integralCoordinates
#print axioms SigabaNeo.Wall1.IntegerGrid.minimizes_normSq_of_closest
