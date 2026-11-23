import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonContactClauseData
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonOrbitComparison

/-! Contact support certificates for a cone in arbitrary rank. The Boolean language and
resolution checker are shared with the rank-six certificates. -/
noncomputable section
namespace SigabaNeo.Wall1.Watson.HigherGram.ContactCone
open Matrix Finset Orbit MaskResolution
open Six (score gain lowerScore composeWord pos_of_dimacs signed usable Reason)

structure Cone (n : ℕ) where
  form : Mat n
  directions : Set (Matrix (Fin n) (Fin n) ℤ)

variable {n : ℕ}
abbrev ContactLines (n m : ℕ) := Fin m → Fin n → ℤ
local notation "M" => Mat n
local notation "IntMat" => Matrix (Fin n) (Fin n) ℤ

def contact (z : Fin n → ℤ) : M →ₗ[ℝ] ℝ where
  toFun D := value D z
  map_add' A B := by simp [value,add_mulVec,dotProduct_add]
  map_smul' a A := by simp [value,smul_mulVec,dotProduct_smul]

def IsRay (k : Cone n) (R : M) := ∃ (j : IntMat) (S : IntMat),
  j ∈ k.directions ∧ IsUnit S ∧ pull (realMatrix S) k.form = k.form ∧
    R = pull (realMatrix S) (realMatrix j)

theorem ray_pull {k : Cone n} {R : M} (h : IsRay k R) {S : IntMat} (hu : IsUnit S)
    (hs : pull (realMatrix S) k.form = k.form) :
    IsRay k (pull (realMatrix S) R) := by
  obtain ⟨j,U,src,hU,fix,rfl⟩ := h
  refine ⟨j,U*S,src,hU.mul hu,?_,?_⟩
  · rw [map_mul,← pull_mul,fix,hs]
  · rw [pull_mul,map_mul]

variable {m : ℕ}

def supported (Z : ContactLines n m) (R D : M) : Prop :=
  (∃ i, 0 < contact (Z i) R) ∧ ∀ i,
    0 ≤ contact (Z i) R ∧ (0 < contact (Z i) R → 0 < contact (Z i) D)


def positiveBits (Z : ContactLines n m) (D : M) (i : Fin m) : Bool := decide (0 < contact (Z i) D)

/-- A permutation of contact evaluations induced by an integral automorphism. -/
def Realizes (k : Cone n) (Z : ContactLines n m) (p : Equiv.Perm (Fin m)) : Prop :=
  ∃ S : IntMatˣ, pull (realMatrix S) k.form = k.form ∧
    ∀ (D : M) i, contact (Z i) (pull (realMatrix S) D) = contact (Z (p i)) D

theorem realizes_one (k : Cone n) (Z : ContactLines n m) : Realizes k Z 1 := by
  refine ⟨1,?_,fun D i ↦ ?_⟩ <;> simp [pull]

theorem realizes_mul {k : Cone n} {Z : ContactLines n m} {p q : Equiv.Perm (Fin m)}
    (h : Realizes k Z p) (h' : Realizes k Z q) : Realizes k Z (p*q) := by
  obtain ⟨S,hS,eq⟩ := h
  obtain ⟨T,hT,eq'⟩ := h'
  refine ⟨S*T,?_,fun D i ↦ ?_⟩ <;> simp only [Units.val_mul,map_mul,← pull_mul]
  · rw [hS,hT]
  · rw [eq',eq]; rfl

def NormalSupport (k : Cone n) (Z : ContactLines n m) : Prop :=
  ∀ (D : M), D.IsHermitian → (∀ i, 0 ≤ contact (Z i) D) → (∃ i, 0 < contact (Z i) D) →
    (∀ p, Realizes k Z p → score (positiveBits Z D ∘ p) ≤ score (positiveBits Z D)) →
    ∃ R, R.IsHermitian ∧ IsRay k R ∧ supported Z R D

private theorem support_exists {k : Cone n} {Z : ContactLines n m} (norm : NormalSupport k Z)
    (D : M) (sym : D.IsHermitian) (pos : ∀ i, 0 ≤ contact (Z i) D)
    (ne : ∃ i, 0 < contact (Z i) D) : ∃ R, R.IsHermitian ∧ IsRay k R ∧ supported Z R D := by
  classical
  let s := univ.filter fun p : Equiv.Perm (Fin m) ↦ Realizes k Z p
  obtain ⟨p,hp,maximal⟩ := exists_max_image s (fun p ↦ score (positiveBits Z D ∘ p))
    ⟨1,mem_filter.mpr ⟨mem_univ _,realizes_one _ _⟩⟩
  have act := (mem_filter.mp hp).2
  obtain ⟨S,fixed,action⟩ := act
  let D' := pull (realMatrix S) D
  have bit : positiveBits Z D' = positiveBits Z D ∘ p := by ext i; simp [positiveBits,D',action]
  obtain ⟨i,hi⟩ := ne
  obtain ⟨j,rfl⟩ := p.surjective i
  obtain ⟨R,rs,ray,fit⟩ := norm D' (isHermitian_conjTranspose_mul_mul _ sym)
    (fun i ↦ (action _ i) ▸ pos _) ⟨j,(action _ j) ▸ hi⟩ (fun q hq ↦ by
      rw [bit]
      exact maximal (p*q) (mem_filter.mpr ⟨mem_univ _,realizes_mul ⟨S,fixed,action⟩ hq⟩))
  let T := realMatrix (↑S⁻¹ : IntMat)
  have back (X : M) : pull T (pull (realMatrix S) X) = X := by
    rw [pull_mul,show realMatrix S * T = 1 by simp [T,← map_mul],pull_one]
  have fT : pull T k.form = k.form := by
    simpa only [fixed] using back k.form
  have inv (X : M) (i : Fin m) : contact (Z (p i)) (pull T X) = contact (Z i) X := by
    rw [← action,pull_mul,show T * realMatrix S = 1 by simp [T,← map_mul],pull_one]
  obtain ⟨⟨i,hi⟩,hfit⟩ := fit
  refine ⟨pull T R,isHermitian_conjTranspose_mul_mul _ rs,ray_pull ray (Units.isUnit S⁻¹) fT,
    ⟨p i,(inv R i) ▸ hi⟩,?_⟩
  intro i
  obtain ⟨j,rfl⟩ := p.surjective i
  rw [inv,← action D j]
  exact hfit j

/-- A finite contact family and the normalized-support test suffice for one local cone. -/
theorem cone_of_support {k : Cone n} (Z : ContactLines n m)
    (tight : ∀ i, Z i ≠ 0 ∧ value k.form (Z i) = 1)
    (separates : ∀ D : M, D.IsHermitian → (∀ i, contact (Z i) D = 0) → D = 0)
    (norm : NormalSupport k Z) (D : M) (sym : D.IsHermitian)
    (admissible : ∀ z : Fin n → ℤ, z ≠ 0 → value k.form z = 1 → 0 ≤ value D z)
    (f : M →ₗ[ℝ] ℝ) (slopes : ∀ R, IsRay k R → 0 ≤ f R) : 0 ≤ f D := by
  classical
  let supp (X : M) := univ.filter fun i ↦ 0 < contact (Z i) X
  suffices ∀ X : M, X.IsHermitian → (∀ i, 0 ≤ contact (Z i) X) → 0 ≤ f X from
    this D sym (fun i ↦ admissible _ (tight i).1 (tight i).2)
  intro X
  induction hn : (supp X).card using Nat.strong_induction_on generalizing X with
  | ind n ih =>
    intro sx pos
    by_cases empty : ∀ i, contact (Z i) X = 0
    · simp [separates X sx empty]
    push Not at empty
    obtain ⟨i,hi⟩ := empty
    obtain ⟨R,rs,ray,⟨j,hj⟩,fit⟩ := support_exists norm X sx pos ⟨i,(pos i).lt_of_ne' hi⟩
    obtain ⟨j,hj,least⟩ := exists_min_image (supp R)
      (fun i ↦ contact (Z i) X / contact (Z i) R) ⟨j,mem_filter.mpr ⟨mem_univ _,hj⟩⟩
    let t := contact (Z j) X / contact (Z j) R
    have rj := (mem_filter.mp hj).2
    have tp : 0 < t := div_pos ((fit j).2 rj) rj
    let Y := X - t • R
    have ey (i : Fin m) : contact (Z i) Y = contact (Z i) X - t*contact (Z i) R := by simp [Y]
    have py (i : Fin m) : 0 ≤ contact (Z i) Y := by
      rw [ey,sub_nonneg]
      rcases (fit i).1.eq_or_lt with zero | positive
      · simp [← zero,pos]
      · exact (le_div_iff₀ positive).mp (least i (mem_filter.mpr ⟨mem_univ _,positive⟩))
    have sub : supp Y ⊆ (supp X).erase j := by
      intro i hi
      have yi := (mem_filter.mp hi).2
      rw [ey] at yi
      refine mem_erase.mpr ⟨?_,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
      · intro eq
        subst i
        simp [t,rj.ne'] at yi
      · linarith [mul_nonneg tp.le (fit i).1]
    have dec : (supp Y).card < n := hn ▸ (card_le_card sub).trans_lt
      (card_erase_lt_of_mem (mem_filter.mpr ⟨mem_univ _,(fit j).2 rj⟩))
    have le := ih _ dec Y rfl (sx.sub (rs.smul (IsSelfAdjoint.of_nonneg tp.le))) py
    simp only [Y,map_sub,map_smul,smul_eq_mul] at le
    linarith [mul_nonneg tp.le (slopes R ray)]

def moment (Z : ContactLines n m) (w : Fin m → ℤ) (a b : Fin n) : ℤ :=
  ∑ i, w i * Z i a * Z i b

theorem moment_eval (Z : ContactLines n m) (w : Fin m → ℤ) (D : M) :
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

theorem eval_relation (Z : ContactLines n m) (w : Fin m → ℤ) (h : ∀ a b, moment Z w a b = 0)
    (D : M) : ∑ i, (w i : ℝ) * contact (Z i) D = 0 := by simp [moment_eval,h]

def picked (a b x y : Fin n) : ℤ := if a = x then (if b = y then 1 else 0) else 0

theorem separates_of_moments (Z : ContactLines n m) (scale : ℤ) (hs : 0 < scale)
    (w : Fin n → Fin n → Fin m → ℤ)
    (cert : ∀ a b x y, moment Z (w a b) x y = scale * (picked a b x y + picked b a x y))
    (D : M) (sym : D.IsHermitian) (zero : ∀ i, contact (Z i) D = 0) : D = 0 := by
  ext a b
  have eq := moment_eval Z (w a b) D
  have flip : D b a = D a b := by simpa using sym.apply a b
  simp [zero,cert,picked,Finset.sum_add_distrib,add_mul,mul_add,
    ite_mul,Finset.sum_ite_eq,flip] at eq
  change D a b = 0
  have : 0 < (scale : ℝ) := by exact_mod_cast hs
  nlinarith

theorem realized_perm {k : Cone n} {Z : ContactLines n m} (p : Equiv.Perm (Fin m)) (U V : IntMat)
    (unit : U * V = 1) (fix : pull (realMatrix U) k.form = k.form)
    (action : ∀ i, U *ᵥ Z i = Z (p i) ∨ U *ᵥ Z i = -Z (p i)) : Realizes k Z p := by
  have detunit : IsUnit U.det := isUnit_iff_exists_inv.mpr
    ⟨_, by simpa [det_mul] using congrArg det unit⟩
  obtain ⟨S,rfl⟩ := (Matrix.isUnit_iff_isUnit_det U).mpr detunit
  refine ⟨S,?_,fun D i ↦ ?_⟩
  · exact fix
  · change value (pull _ D) _ = _
    rw [value_pull]
    rcases action i with h | h
    · rw [h]; rfl
    · rw [h]; change value D (-Z (p i)) = value D (Z (p i))
      have en : (fun j ↦ ((-Z (p i) j : ℤ) : ℝ)) = -(fun j ↦ (Z (p i) j : ℝ)) := by
        ext j; simp
      simp only [value,Pi.neg_apply,en,mulVec_neg,dotProduct_neg,neg_dotProduct,neg_neg]

theorem contact_integer (U : IntMat) (z : Fin n → ℤ) :
    contact z (realMatrix U) = (z ⬝ᵥ (U *ᵥ z) : ℤ) := by
  simp [contact,value,realMatrix,mulVec,dotProduct]

theorem realizes_word {k : Cone n} {Z : ContactLines n m} {g : ℕ} (p : Fin g → Equiv.Perm (Fin m))
    (ok : ∀ i, Realizes k Z (p i)) (w : List (Fin g)) : Realizes k Z (composeWord p w) := by
  induction w with
  | nil => exact realizes_one _ _
  | cons i _ ih => exact realizes_mul (ok i) ih

theorem nonzero_clause {Z : ContactLines n m} {D : M} {c : Clause}
    (h : ∀ i : Fin m, c.pos.testBit i) (ne : ∃ i, 0 < contact (Z i) D) :
    c.Sat (positiveBits Z D) := by
  obtain ⟨i,hi⟩ := ne
  exact ⟨i,Or.inl ⟨h i,decide_eq_true hi⟩⟩

theorem relation_clause {Z : ContactLines n m} {D : M} {c : Clause} (w : Fin m → ℤ) (i : Fin m)
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

theorem symmetry_clause {k : Cone n} {Z : ContactLines n m} {D : M} {c : Clause}
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

theorem ray_clause {k : Cone n} {Z : ContactLines n m} {D R : M} {c : Clause} (p : Equiv.Perm (Fin m))
    (ok : Realizes k Z p) (sym : R.IsHermitian) (ray : IsRay k R)
    (v : Fin m → ℤ) (values : ∀ i, contact (Z i) R = (v i : ℝ)) (ne : ∃ i, 0 < v i)
    (pos : ∀ i, 0 ≤ v i) (mask : ∀ i : Fin m, 0 < v (p i) → c.neg.testBit i)
    (none : ¬ ∃ T, T.IsHermitian ∧ IsRay k T ∧ supported Z T D) :
    c.Sat (positiveBits Z D) := by
  classical
  apply Classical.byContradiction
  intro bad
  obtain ⟨S,fix,act⟩ := ok
  let T := pull (realMatrix (S : IntMat)) R
  have tv (i : Fin m) : contact (Z i) T = (v (p i) : ℝ) := (act R i).trans (values _)
  have hr : IsRay k T := ray_pull (S := (S : IntMat)) ray S.isUnit fix
  apply none
  refine ⟨T, isHermitian_conjTranspose_mul_mul (realMatrix (S : IntMat)) sym, hr, ?_, ?_⟩
  · obtain ⟨i,hi⟩ := ne
    obtain ⟨j,hj⟩ := p.surjective i
    refine ⟨j, ?_⟩
    rw [tv,hj]
    exact_mod_cast hi
  · intro i
    rw [tv]
    refine ⟨by exact_mod_cast pos (p i), fun hi ↦ ?_⟩
    have bit := (pos_of_dimacs bad i).1 (mask i (by exact_mod_cast hi))
    exact of_decide_eq_true bit

def SeedValid (k : Cone n) (Z : ContactLines n m) (v : Fin m → ℤ) : Prop :=
  (∃ R, R.IsHermitian ∧ IsRay k R ∧ ∀ i, contact (Z i) R = (v i : ℝ)) ∧
  (∃ i, 0 < v i) ∧ ∀ i, 0 ≤ v i

theorem normal_of_clauses {k : Cone n} (Z : ContactLines n m)
    (p : Fin g → Equiv.Perm (Fin m)) (rows : Fin r → Fin m → ℤ) (values : Fin d → Fin m → ℤ)
    (autos : ∀ a, Realizes k Z (p a)) (relations : ∀ a i j, moment Z (rows a) i j = 0)
    (seeds : ∀ a, SeedValid k Z (values a)) {count : ℕ} (input : ℕ → Clause)
    (reason : ℕ → Reason m g r d) (arithmetic : ∀ i : Fin count, usable p rows values (input i) (reason i))
    (unsat : ∀ b : Fin m → Bool, ¬ ∀ i : Fin count, (input i).Sat b) : NormalSupport k Z := by
  intro D _ pos ne maximal
  by_contra none
  apply unsat (positiveBits Z D)
  intro i
  have good := arithmetic i
  cases e : reason i with
  | nonzero => exact nonzero_clause (by simpa [e,usable] using good) ne
  | relation a flip j =>
    rw [e] at good
    obtain ⟨lo,on,opp⟩ := good
    have zero := eval_relation Z (rows a) (relations a) D
    apply relation_clause (signed (rows a) flip) j _ pos lo on opp
    cases flip <;> simpa [signed,Finset.sum_neg_distrib] using zero
  | symmetry w =>
    exact symmetry_clause _ (realizes_word p autos w) (by simpa [e,usable] using good) maximal
  | ray a w =>
    obtain ⟨⟨R,sym,ray,v⟩,ne',pos'⟩ := seeds a
    exact ray_clause _ (realizes_word p autos w) sym ray _ v ne' pos'
      (by simpa [e,usable] using good) none

end SigabaNeo.Wall1.Watson.HigherGram.ContactCone
