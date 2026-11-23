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
  calc
    _ = ∑ i, ∑ a, ∑ b, ((w i * Z i a * Z i b : ℤ) : ℝ) * D a b := by
      apply sum_congr rfl; intro i _
      simp only [contact,value,LinearMap.coe_mk,AddHom.coe_mk,dotProduct,mulVec,
        Finset.mul_sum,Int.cast_mul]
      apply sum_congr rfl; intro a _
      apply sum_congr rfl; intro b _
      ring
    _ = _ := by
      rw [sum_comm]; apply sum_congr rfl; intro a _
      rw [sum_comm]; apply sum_congr rfl; intro b _
      simp [moment,Finset.sum_mul]

theorem eval_relation (Z : Lines m) (w : Fin m → ℤ) (h : ∀ a b, moment Z w a b = 0)
    (D : M) : ∑ i, (w i : ℝ) * contact (Z i) D = 0 := by simp [moment_eval,h]

def picked (a b x y : Fin 6) : ℤ := if a = x then (if b = y then 1 else 0) else 0

theorem separates_of_moments (Z : Lines m) (scale : ℤ) (hs : 0 < scale)
    (w : Fin 6 → Fin 6 → Fin m → ℤ)
    (cert : ∀ a b x y, moment Z (w a b) x y = scale * (picked a b x y + picked b a x y))
    (D : M) (sym : D.IsHermitian) (zero : ∀ i, contact (Z i) D = 0) : D = 0 := by
  ext a b
  have eq := moment_eval Z (w a b) D
  have flip : D b a = D a b := by simpa using sym.apply a b
  simp [zero,cert,picked,Finset.sum_add_distrib,Finset.mul_sum,add_mul,mul_add,
    ite_mul,Finset.sum_ite_eq,flip] at eq
  change D a b = 0
  have : 0 < (scale : ℝ) := by exact_mod_cast hs
  nlinarith

theorem realized_perm {k : Fin 7} {Z : Lines m} (p : Equiv.Perm (Fin m)) (U V : IntMat)
    (unit : U * V = 1) (fix : (qmat U)ᵀ * forms k * qmat U = forms k)
    (action : ∀ i, U *ᵥ Z i = Z (p i) ∨ U *ᵥ Z i = -Z (p i)) : Realizes k Z p := by
  have detunit : IsUnit U.det := isUnit_iff_exists_inv.mpr
    ⟨_, by simpa [det_mul] using congrArg det unit⟩
  obtain ⟨S,rfl⟩ := (Matrix.isUnit_iff_isUnit_det U).mpr detunit
  refine ⟨S,?_,fun D i ↦ ?_⟩
  · have h := congrArg (fun A : Matrix (Fin 6) (Fin 6) ℚ ↦ A.map (Rat.castHom ℝ)) fix
    change (((qmat (↑S))ᵀ * forms k * qmat (↑S)).map (Rat.castHom ℝ)) = _ at h
    rw [Matrix.map_mul,Matrix.map_mul] at h
    have casts : (Rat.cast : ℚ → ℝ) ∘ (Int.cast : ℤ → ℚ) = (Int.cast : ℤ → ℝ) := by ext v; simp
    simpa [representative,pull,qmat,realMatrix,Matrix.map_map,Matrix.transpose_map,casts,
      Matrix.conjTranspose_eq_transpose_of_trivial] using h
  · change value (pull _ D) _ = _
    rw [value_pull]
    rcases action i with h | h
    · rw [h]; rfl
    · rw [h]; change value D (-Z (p i)) = value D (Z (p i))
      have en : (fun j ↦ ((-Z (p i) j : ℤ) : ℝ)) = -(fun j ↦ (Z (p i) j : ℝ)) := by
        ext j; simp
      simp only [value,Pi.neg_apply,en,mulVec_neg,dotProduct_neg,neg_dotProduct,neg_neg]

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

def composeWord {g : ℕ} (p : Fin g → Equiv.Perm (Fin m)) (w : List (Fin g)) :
    Equiv.Perm (Fin m) := (w.map p).prod

theorem realizes_word {k : Fin 7} {Z : Lines m} {g : ℕ} (p : Fin g → Equiv.Perm (Fin m))
    (ok : ∀ i, Realizes k Z (p i)) (w : List (Fin g)) : Realizes k Z (composeWord p w) := by
  induction w with
  | nil => exact realizes_one _ _
  | cons i _ ih => exact realizes_mul (ok i) ih

theorem pos_of_dimacs {s : Fin m → Bool} {c : Clause} (bad : ¬ c.Sat s) (i : Fin m) :
    (c.neg.testBit i → s i = true) ∧ (c.pos.testBit i → s i = false) := by
  constructor
  · intro h; cases eq : s i
    · exact False.elim (bad ⟨i,Or.inr ⟨h,eq⟩⟩)
    · rfl
  · intro h; cases eq : s i
    · rfl
    · exact False.elim (bad ⟨i,Or.inl ⟨h,eq⟩⟩)

theorem nonzero_clause {Z : Lines m} {D : M} {c : Clause}
    (h : ∀ i : Fin m, c.pos.testBit i) (ne : ∃ i, 0 < contact (Z i) D) :
    c.Sat (positiveBits Z D) := by
  obtain ⟨i,hi⟩ := ne
  exact ⟨i,Or.inl ⟨h i,decide_eq_true hi⟩⟩

theorem relation_clause {Z : Lines m} {D : M} {c : Clause} (w : Fin m → ℤ) (i : Fin m)
    (eq : ∑ l, (w l : ℝ) * contact (Z l) D = 0) (pos : ∀ l, 0 ≤ contact (Z l) D)
    (wi : 0 < w i) (ci : c.neg.testBit i) (op : ∀ j : Fin m, w j < 0 → c.pos.testBit j) :
    c.Sat (positiveBits Z D) := by
  by_contra bad
  have nonneg (j : Fin m) : 0 ≤ (w j : ℝ) * contact (Z j) D := by
    by_cases hj : w j < 0
    · have h := (pos_of_dimacs bad j).2 (op j hj)
      simp [positiveBits] at h
      simp [le_antisymm h (pos j)]
    · exact mul_nonneg (by exact_mod_cast le_of_not_gt hj) (pos j)
  have hi := (pos_of_dimacs bad i).1 ci
  simp [positiveBits] at hi
  have h := single_le_sum (fun j _ ↦ nonneg j) (mem_univ i)
  exact (mul_pos (by exact_mod_cast wi : 0 < (w i : ℝ)) hi).not_ge (eq ▸ h)

def gain (p : Equiv.Perm (Fin m)) (i : Fin m) : ℤ := 2^(p.symm i).val - 2^i.val

def lowerScore (p : Equiv.Perm (Fin m)) (c : Clause) : ℤ :=
  ∑ i : Fin m, if c.neg.testBit i then gain p i else
    if c.pos.testBit i then 0 else min 0 (gain p i)

theorem symmetry_clause {k : Fin 7} {Z : Lines m} {D : M} {c : Clause}
    (p : Equiv.Perm (Fin m)) (ok : Realizes k Z p) (h : 0 < lowerScore p c)
    (maximal : ∀ p, Realizes k Z p → score (positiveBits Z D ∘ p) ≤ score (positiveBits Z D)) :
    c.Sat (positiveBits Z D) := by
  by_contra bad
  let b := positiveBits Z D
  have eq : score (b ∘ p) - score b = ∑ i, if b i then gain p i else 0 := by
    have reindex := Equiv.sum_comp p (fun i ↦ if b i then (2:ℤ)^(p.symm i).val else 0)
    simp only [Equiv.symm_apply_apply] at reindex
    change (∑ i, if b (p i) then (2:ℤ)^i.val else 0) - _ = _
    rw [reindex,score,← sum_sub_distrib]
    apply sum_congr rfl; intro i _; cases b i <;> simp [gain]
  have lb : lowerScore p c ≤ ∑ i, if b i then gain p i else 0 := by
    apply sum_le_sum; intro i _
    have hf := pos_of_dimacs bad i
    by_cases hn : c.neg.testBit i
    · simp [hn,b,hf.1 hn]
    · by_cases hp : c.pos.testBit i
      · simp [hn,hp,b,hf.2 hp]
      · simp only [hn,hp,Bool.false_eq_true,ite_false]
        cases b i <;> simp
  have upper := maximal p ok
  rw [← eq] at lb
  dsimp only [b] at lb
  omega

theorem ray_clause {k : Fin 7} {Z : Lines m} {D R : M} {c : Clause} (p : Equiv.Perm (Fin m))
    (ok : Realizes k Z p) (sym : R.IsHermitian) (ray : IsRay k R)
    (v : Fin m → ℤ) (values : ∀ i, contact (Z i) R = (v i : ℝ)) (ne : ∃ i, 0 < v i)
    (pos : ∀ i, 0 ≤ v i) (mask : ∀ i : Fin m, 0 < v (p i) → c.neg.testBit i)
    (none : ¬ ∃ T, T.IsHermitian ∧ IsRay k T ∧ supported Z T D) :
    c.Sat (positiveBits Z D) := by
  by_contra bad
  obtain ⟨S,fix,act⟩ := ok
  obtain ⟨i,hi⟩ := ne
  obtain ⟨j,rfl⟩ := p.surjective i
  apply none
  refine ⟨pull (realMatrix S) R,isHermitian_conjTranspose_mul_mul _ sym,ray_pull ray S.isUnit fix,
    ⟨j,by rw [act,values]; exact_mod_cast hi⟩,fun i ↦ ?_⟩
  rw [act,values]
  refine ⟨by exact_mod_cast pos _,fun hi ↦ ?_⟩
  have bit := (pos_of_dimacs bad i).1 (mask i (by exact_mod_cast hi))
  simpa [positiveBits] using bit

end SigabaNeo.Wall1.Watson.HigherGram.Six

#print axioms SigabaNeo.Wall1.Watson.HigherGram.Six.separates_of_moments
#print axioms SigabaNeo.Wall1.Watson.HigherGram.Six.realized_perm
#print axioms SigabaNeo.Wall1.Watson.HigherGram.Six.symmetry_clause
#print axioms SigabaNeo.Wall1.Watson.HigherGram.Six.relation_clause
#print axioms SigabaNeo.Wall1.Watson.HigherGram.Six.ray_clause
