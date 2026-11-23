import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonContactCone
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSevenSimplex

/-! Interpret support clauses and their resolution certificates at a rank-seven source. -/
noncomputable section
namespace SigabaNeo.Wall1.Watson.HigherGram.Seven.Local
open Matrix Orbit ContactCone
abbrev Lines (m : ℕ) := Fin m → Fin 7 → ℤ

def cone (k : Fin 33) : Cone 7 :=
  ⟨representative k, {R | ∃ w ∈ pivots k, w.direction = R}⟩

variable {m : ℕ}

theorem realized {k : Fin 33} {Z : Lines m} (p : Equiv.Perm (Fin m)) (U V : IntMat)
    (unit : U * V = 1) (fixed : (qmat U)ᵀ * forms k * qmat U = forms k)
    (action : ∀ i, U *ᵥ Z i = Z (p i) ∨ U *ᵥ Z i = -Z (p i)) :
    Realizes (cone k) Z p := by
  apply realized_perm p U V unit _ action
  have e := congrArg ((Rat.castHom ℝ).mapMatrix) fixed
  simp only [map_mul] at e
  simpa [cone, pull, realMatrix, representative, qmat, Matrix.transpose_map, Matrix.map_map, Function.comp_def,
    Matrix.conjTranspose_eq_transpose_of_trivial] using e

theorem seedValid_of_pivot {k : Fin 33} (Z : Lines m) (v : Fin m → ℤ)
    (j : Fin (pivots k).length)
    (sym : ((pivots k)[j.val]).direction.IsSymm)
    (values : ∀ i, Z i ⬝ᵥ (((pivots k)[j.val]).direction *ᵥ Z i) = v i)
    (ne : ∃ i, 0 < v i) (pos : ∀ i, 0 ≤ v i) : SeedValid (cone k) Z v := by
  let w := (pivots k)[j.val]
  refine ⟨⟨realMatrix w.direction, ?_, ?_, fun i ↦ ?_⟩, ne, pos⟩
  · ext a b
    change star (w.direction b a : ℝ) = (w.direction a b : ℝ)
    rw [star_trivial]
    exact_mod_cast sym.apply a b
  · exact ⟨w.direction, 1, ⟨w,List.getElem_mem _,rfl⟩, isUnit_one,
      by simp [pull_one], by simp [pull_one]⟩
  · rw [contact_integer,values]

theorem coverage {k : Fin 33} (Z : Lines m)
    (tight : ∀ i, Z i ≠ 0 ∧ value (representative k) (Z i) = 1)
    (separates : ∀ D : Mat 7, D.IsHermitian → (∀ i, contact (Z i) D = 0) → D = 0)
    (normal : NormalSupport (cone k) Z) : RayCoverageAt k := by
  intro D sym admissible f slopes
  apply cone_of_support Z tight separates normal D sym admissible f
  rintro _ ⟨_,S,⟨w,mem,rfl⟩,su,fix,rfl⟩
  exact slopes w mem S su fix

end SigabaNeo.Wall1.Watson.HigherGram.Seven.Local
