import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenConeReduction

/-! For a simplicial tangent cone the contact evaluations give nonnegative coordinates
directly. The integer moment identity below verifies their reconstruction map. -/

noncomputable section
namespace SigabaNeo.Wall1.Watson.HigherGram.Seven
open Finset Matrix Orbit

def Slopes (k : Fin 33) (f : Mat 7 →ₗ[ℝ] ℝ) : Prop :=
  ∀ w ∈ pivots k, ∀ S : IntMat, IsUnit S →
    pull (realMatrix S) (representative k) = representative k →
    0 ≤ f (pull (realMatrix S) (realMatrix w.direction))

structure SimplexAtom (k : Fin 33) where
  z : Fin 7 → ℤ
  coeff : IntMat
  tight : z ≠ 0 ∧ value (representative k) z = 1
  slope : ∀ f, Slopes k f → 0 ≤ f (realMatrix coeff)

abbrev qmat (S : IntMat) : Q := S.map (Int.castRingHom ℚ)

theorem tight_of_rat {k : Fin 33} (z : Fin 7 → ℤ)
    (h : (fun i ↦ (z i : ℚ)) ⬝ᵥ forms k *ᵥ (fun i ↦ (z i : ℚ)) = 1) :
    z ≠ 0 ∧ value (representative k) z = 1 := by
  refine ⟨?_,?_⟩
  · rintro rfl
    simp at h
  · have e := congrArg ((↑) : ℚ → ℝ) h
    simpa [value, representative, dotProduct, mulVec] using e

theorem slope_of_action {k : Fin 33} (j : Fin (pivots k).length) (S V A : IntMat)
    (s : ℤ) (hs : 0 ≤ s) (unit : S * V = 1)
    (fix : (qmat S)ᵀ * forms k * qmat S = forms k)
    (image : A = s • (Sᵀ * ((pivots k)[j.val]).direction * S)) :
    ∀ f, Slopes k f → 0 ≤ f (realMatrix A) := by
  intro f slopes
  let w := (pivots k)[j.val]
  have eq : pull (realMatrix S) (representative k) = representative k := by
    have e := congrArg ((Rat.castHom ℝ).mapMatrix) fix
    simp only [map_mul] at e
    simpa [pull, realMatrix, representative, qmat, Matrix.map_mul, Matrix.transpose_map,
      Matrix.map_map, Function.comp_def, Matrix.conjTranspose_eq_transpose_of_trivial] using e
  have h := slopes w (List.getElem_mem _) S (isUnit_iff_exists_inv.mpr ⟨V,unit⟩) eq
  have ae : realMatrix A = (s : ℝ) • pull (realMatrix S) (realMatrix w.direction) := by
    rw [image, map_zsmul, map_mul, map_mul, Int.cast_smul_eq_zsmul ℝ]
    rfl
  rw [ae,map_smul,smul_eq_mul]
  exact mul_nonneg (by exact_mod_cast hs) h

def picked (a b x y : Fin 7) : ℤ := if a = x then (if b = y then 1 else 0) else 0

def moment {k : Fin 33} (rows : Fin 28 → SimplexAtom k) (a b x y : Fin 7) : ℤ :=
  ∑ i, (rows i).coeff a b * (rows i).z x * (rows i).z y

theorem coverage_of_simplex {k : Fin 33} (rows : Fin 28 → SimplexAtom k)
    (c : ℤ) (hc : 0 < c) (cert : ∀ a b x y,
      moment rows a b x y = c * (picked a b x y + picked b a x y)) : RayCoverageAt k := by
  intro D sym admissible f slopes
  have eq : ∑ i, value D (rows i).z • realMatrix (rows i).coeff = (2 * (c : ℝ)) • D := by
    ext a b
    have flip : D b a = D a b := by simpa using sym.apply a b
    calc
      _ = ∑ i, ∑ x, ∑ y, (((rows i).coeff a b * (rows i).z x * (rows i).z y : ℤ) : ℝ) * D x y := by
        simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, value, dotProduct, mulVec,
          Finset.mul_sum, Finset.sum_mul, Int.cast_mul]
        apply sum_congr rfl; intro i _
        apply sum_congr rfl; intro x _
        apply sum_congr rfl; intro y _
        simp [realMatrix]
        ring
      _ = ∑ x, ∑ y, (moment rows a b x y : ℝ) * D x y := by
        rw [sum_comm]; apply sum_congr rfl; intro x _
        rw [sum_comm]; apply sum_congr rfl; intro y _
        simp [moment, Finset.sum_mul]
      _ = _ := by
        simp [cert, picked, Finset.sum_add_distrib, mul_add, add_mul,
          ite_mul, Finset.sum_ite_eq, flip]
        ring
  have good : 0 ≤ ∑ i, value D (rows i).z * f (realMatrix (rows i).coeff) :=
    sum_nonneg fun i _ ↦ mul_nonneg (admissible _ (rows i).tight.1 (rows i).tight.2)
      ((rows i).slope f slopes)
  have e := congrArg f eq
  simp only [map_sum,map_smul,smul_eq_mul] at e
  rw [e] at good
  exact nonneg_of_mul_nonneg_right good (by exact_mod_cast (by omega : 0 < 2 * c))

end SigabaNeo.Wall1.Watson.HigherGram.Seven
