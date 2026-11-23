import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonMaskResolution
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSixSupportReduction

/-! Arithmetic witnesses for contact relations, contact permutations and support clauses. -/
noncomputable section
namespace SigabaNeo.Wall1.Watson.HigherGram.Six
open Finset Matrix MaskResolution
local notation "M" => Mat 6
variable {m : ℕ}

def moment (Z : Lines m) (w : Fin m → ℤ) (a b : Fin 6) : ℤ :=
  ∑ i, w i * Z i a * Z i b

theorem moment_eval (Z : Lines m) (w : Fin m → ℤ) (D : M) :
    ∑ i, (w i : ℝ) * contact (Z i) D = ∑ a, ∑ b, (moment Z w a b : ℝ) * D a b := by
  exact ContactCone.moment_eval Z w D

theorem eval_relation (Z : Lines m) (w : Fin m → ℤ) (h : ∀ a b, moment Z w a b = 0)
    (D : M) : ∑ i, (w i : ℝ) * contact (Z i) D = 0 := by simp [moment_eval,h]

def picked (a b x y : Fin 6) : ℤ := if a = x then (if b = y then 1 else 0) else 0

theorem separates_of_moments (Z : Lines m) (scale : ℤ) (hs : 0 < scale)
    (w : Fin 6 → Fin 6 → Fin m → ℤ)
    (cert : ∀ a b x y, moment Z (w a b) x y = scale * (picked a b x y + picked b a x y))
    (D : M) (sym : D.IsHermitian) (zero : ∀ i, contact (Z i) D = 0) : D = 0 := by
  exact ContactCone.separates_of_moments Z scale hs w cert D sym zero

theorem realized_perm {k : Fin 7} {Z : Lines m} (p : Equiv.Perm (Fin m)) (U V : IntMat)
    (unit : U * V = 1) (fix : (qmat U)ᵀ * forms k * qmat U = forms k)
    (action : ∀ i, U *ᵥ Z i = Z (p i) ∨ U *ᵥ Z i = -Z (p i)) : Realizes k Z p := by
  apply ContactCone.realized_perm (k := contactCone k) p U V unit _ action
  have h := congrArg (fun A : Matrix (Fin 6) (Fin 6) ℚ ↦ A.map (Rat.castHom ℝ)) fix
  change (((qmat U)ᵀ * forms k * qmat U).map (Rat.castHom ℝ)) = _ at h
  rw [Matrix.map_mul,Matrix.map_mul] at h
  have casts : (Rat.cast : ℚ → ℝ) ∘ (Int.cast : ℤ → ℚ) = (Int.cast : ℤ → ℝ) := by ext v; simp
  simpa [contactCone,representative,Orbit.pull,qmat,Orbit.realMatrix,Matrix.map_map,
    Matrix.transpose_map,casts,Matrix.conjTranspose_eq_transpose_of_trivial] using h

theorem contact_rational (Q : Matrix (Fin 6) (Fin 6) ℚ) (z : Fin 6 → ℤ) :
    value (Q.map (Rat.castHom ℝ)) z =
      ((fun i ↦ (z i : ℚ)) ⬝ᵥ (Q *ᵥ fun i ↦ (z i : ℚ)) : ℚ) := by
  simp [value,dotProduct,mulVec]

theorem ray_seed {k : Fin 7} (j : Fin 32) (src : (pivot j).src = k)
    (sym : (pivot j).direction.IsSymm) :
    (realMatrix (pivot j).direction).IsHermitian ∧ IsRay k (realMatrix (pivot j).direction) := by
  refine ⟨?_,j,1,src,isUnit_one,by simp [pull_one],by simp [pull_one]⟩
  ext a b
  change star ((pivot j).direction b a : ℝ) = ((pivot j).direction a b : ℝ)
  rw [star_trivial]; exact_mod_cast sym.apply a b

theorem contact_integer (U : IntMat) (z : Fin 6 → ℤ) :
    contact z (realMatrix U) = (z ⬝ᵥ (U *ᵥ z) : ℤ) := by
  simp [contact,value,realMatrix,mulVec,dotProduct]

theorem realizes_word {k : Fin 7} {Z : Lines m} {g : ℕ} (p : Fin g → Equiv.Perm (Fin m))
    (ok : ∀ i, Realizes k Z (p i)) (w : List (Fin g)) : Realizes k Z (composeWord p w) := by
  induction w with
  | nil => exact realizes_one _ _
  | cons i _ ih => exact realizes_mul (ok i) ih

theorem nonzero_clause {Z : Lines m} {D : M} {c : Clause}
    (h : ∀ i : Fin m, c.pos.testBit i) (ne : ∃ i, 0 < contact (Z i) D) :
    c.Sat (positiveBits Z D) := by
  exact ContactCone.nonzero_clause h ne

theorem relation_clause {Z : Lines m} {D : M} {c : Clause} (w : Fin m → ℤ) (i : Fin m)
    (eq : ∑ l, (w l : ℝ) * contact (Z l) D = 0) (pos : ∀ l, 0 ≤ contact (Z l) D)
    (wi : 0 < w i) (ci : c.neg.testBit i) (op : ∀ j : Fin m, w j < 0 → c.pos.testBit j) :
    c.Sat (positiveBits Z D) := by
  exact ContactCone.relation_clause w i eq pos wi ci op

theorem symmetry_clause {k : Fin 7} {Z : Lines m} {D : M} {c : Clause}
    (p : Equiv.Perm (Fin m)) (ok : Realizes k Z p) (h : 0 < lowerScore p c)
    (maximal : ∀ p, Realizes k Z p → score (positiveBits Z D ∘ p) ≤ score (positiveBits Z D)) :
    c.Sat (positiveBits Z D) := by
  exact ContactCone.symmetry_clause (k := contactCone k) p ok h maximal

theorem ray_clause {k : Fin 7} {Z : Lines m} {D R : M} {c : Clause} (p : Equiv.Perm (Fin m))
    (ok : Realizes k Z p) (sym : R.IsHermitian) (ray : IsRay k R)
    (v : Fin m → ℤ) (values : ∀ i, contact (Z i) R = (v i : ℝ)) (ne : ∃ i, 0 < v i)
    (pos : ∀ i, 0 ≤ v i) (mask : ∀ i : Fin m, 0 < v (p i) → c.neg.testBit i)
    (none : ¬ ∃ T, T.IsHermitian ∧ IsRay k T ∧ supported Z T D) :
    c.Sat (positiveBits Z D) := by
  apply ContactCone.ray_clause (k := contactCone k) p ok sym (isRay_cone_iff.mpr ray)
    v values ne pos mask
  rintro ⟨T,hs,hr,ht⟩
  exact none ⟨T,hs,isRay_cone_iff.mp hr,ht⟩

end SigabaNeo.Wall1.Watson.HigherGram.Six

#print axioms SigabaNeo.Wall1.Watson.HigherGram.Six.separates_of_moments
#print axioms SigabaNeo.Wall1.Watson.HigherGram.Six.realized_perm
#print axioms SigabaNeo.Wall1.Watson.HigherGram.Six.symmetry_clause
#print axioms SigabaNeo.Wall1.Watson.HigherGram.Six.relation_clause
#print axioms SigabaNeo.Wall1.Watson.HigherGram.Six.ray_clause
