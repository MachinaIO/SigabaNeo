module

public import SigabaNeo.Lib.Lattices.Attacks.Primal.LLL
import all SigabaNeo.Lib.Lattices.Attacks.Primal.LLL
public import SigabaNeo.Lib.Lattices.Attacks.Primal.SampleDeletionBall
import Mathlib.Tactic

public section
noncomputable section
namespace SigabaNeo.Wall1.IntegerGrid

open SigabaNeo.LLL SigabaNeo.SampleDeletion

variable {d : ℕ} (S : Submodule ℤ (Fin d → ℤ))

/-- The integer submodule is linearly equivalent to its Euclidean realization. -/
def realization : S ≃ₗ[ℤ] S.map (intVec (d := d)) :=
  Submodule.equivMapOfInjective _ (by
    intro x y h
    funext i
    have hi := congrArg (fun z : EuclideanSpace ℝ (Fin d) ↦ z i) h
    exact_mod_cast (show (x i : ℝ) = (y i : ℝ) from hi)) S

/-- Squared Euclidean residuals at integral targets are sums of squared integer residuals. -/
theorem residual_sq (x : S.map (intVec (d := d))) (t : Fin d → ℤ) :
    ‖(x : EuclideanSpace ℝ (Fin d)) - intVec (d := d) t‖ ^ 2 =
      normSq (((realization S).symm x : Fin d → ℤ) - t) := by
  obtain ⟨z, rfl⟩ := (realization S).surjective x
  rw [LinearEquiv.symm_apply_apply]
  change ‖intVec (d := d) z.val - intVec (d := d) t‖ ^ 2 = _
  rw [← map_sub, EuclideanSpace.real_norm_sq_eq]
  simp only [normSq, Nat.cast_sum, Nat.cast_pow]
  apply Finset.sum_congr rfl
  intro i _
  change (((z.val - t) i : ℤ) : ℝ) ^ 2 = _
  simpa only [Int.cast_pow, Int.cast_natCast, Nat.cast_pow] using
    congrArg (fun z : ℤ ↦ (z : ℝ)) (Int.natAbs_pow_two ((z.val - t) i)).symm

/-- A full-rank integer submodule gives a basis of its real-coordinate image over ℤ. -/
def basis (rank_eq : Module.finrank ℤ S = d) :
    Module.Basis (Fin d) ℤ (S.map (intVec (d := d))) :=
  ((Module.finBasis ℤ S).reindex (finCongr rank_eq)).map (realization S)

/-- Enumerate the parity vectors in the coordinates of a d-element basis. -/
def parityLabels (d : ℕ) : (Fin d → ZMod 2) ≃ Fin (2 ^ d) :=
  Fintype.equivFinOfCardEq (by simp)

end SigabaNeo.Wall1.IntegerGrid

#print axioms SigabaNeo.Wall1.IntegerGrid.realization
#print axioms SigabaNeo.Wall1.IntegerGrid.residual_sq
#print axioms SigabaNeo.Wall1.IntegerGrid.basis
#print axioms SigabaNeo.Wall1.IntegerGrid.parityLabels
