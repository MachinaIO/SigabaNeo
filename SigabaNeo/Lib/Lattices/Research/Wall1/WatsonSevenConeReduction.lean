import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonCodeBasis
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonOrbitComparison
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenPivots

/-! A local cone certificate suffices for all rank-seven residue charts. -/

noncomputable section
namespace SigabaNeo.Wall1.Watson.HigherGram.Seven
open Matrix Orbit
local notation "M" => Mat 7

theorem Pivot.real_endpoint {k : Fin 33} (w : Pivot k) :
    representative k + (w.step : ℝ) • realMatrix w.direction =
      pull (realMatrix w.change) (representative w.dst) := by
  have h := congrArg (fun A : Q ↦ A.map (Rat.castHom ℝ)) w.endpoint
  simp only [Matrix.map_mul, Matrix.transpose_map] at h
  change _ = (realMatrix w.change)ᴴ * representative w.dst * realMatrix w.change
  rw [conjTranspose_eq_transpose_of_trivial]
  convert h using 2 <;> first | rfl | ext i j; simp [realMatrix, representative]

/-- Dual description of the tangent cone by the tabulated directions and the
integral stabilizer of its source. -/
def RayCoverageAt (k : Fin 33) : Prop :=
  ∀ D : M, D.IsHermitian →
    (∀ z : Fin 7 → ℤ, z ≠ 0 → value (representative k) z = 1 → 0 ≤ value D z) →
    ∀ f : M →ₗ[ℝ] ℝ,
      (∀ w ∈ pivots k, ∀ S : IntMat, IsUnit S →
        pull (realMatrix S) (representative k) = representative k →
        0 ≤ f (pull (realMatrix S) (realMatrix w.direction))) → 0 ≤ f D

/-- The finite local cone obligations imply the determinant inequality on the full
minimum-one domain, including forms outside the marked charts. -/
theorem determinant_of_rays (h : ∀ k, RayCoverageAt k) (G : M) (pd : G.PosDef)
    (short : ∀ z : Fin 7 → ℤ, z ≠ 0 → 1 ≤ value G z) : (1:ℝ)/64 ≤ G.det := by
  apply determinant_of_comparison representative (fun k ↦ (representative_bound k).1)
    (fun k ↦ (representative_bound k).2.2) _ G pd short
  intro k D sym admissible f best
  apply h k D sym admissible f
  intro w _ S su hs
  have b := best w.dst (w.change * S) (w.unit.mul su)
  have e := congrArg (fun X ↦ f (pull (realMatrix S) X)) w.real_endpoint
  simp only [map_add,map_smul,smul_eq_mul,hs,pull_mul,← map_mul] at e
  exact nonneg_of_mul_nonneg_right (a := (w.step : ℝ)) (by linarith only [b,e])
    (by exact_mod_cast w.positive)

/-- The code order cancels after changing from numerator coordinates to a lattice basis. -/
theorem chart_bound_of_rays (h : ∀ k, RayCoverageAt k) : Bound 7 10 (11 * ·) 64 := by
  intro d hd _ C card G mem
  obtain ⟨pd,minimum⟩ := seven_box hd C mem
  apply chart_bound_of_minimum _ hd C card G pd minimum
  intro A ap short
  linarith [determinant_of_rays h A ap short]

end SigabaNeo.Wall1.Watson.HigherGram.Seven
