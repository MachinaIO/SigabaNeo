import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSixConeReduction

/-! Reduce ray spanning to a Boolean question about supports of contact evaluations.
Subtract a contained ray at the minimum positive ratio. The number of positive contact
evaluations strictly decreases. For the Boolean test one may normalize each support by
any signed permutation of the contact lines induced by a lattice automorphism. -/

noncomputable section
namespace SigabaNeo.Wall1.Watson.HigherGram.Six
open Matrix Finset
local notation "M" => Mat 6

def contact (z : Fin 6 → ℤ) : M →ₗ[ℝ] ℝ where
  toFun D := value D z
  map_add' A B := by simp [value,add_mulVec,dotProduct_add]
  map_smul' a A := by simp [value,smul_mulVec,dotProduct_smul]

def IsRay (k : Fin 7) (R : M) := ∃ (j : Fin 32) (S : IntMat),
  (pivot j).src = k ∧ IsUnit S ∧ pull (realMatrix S) (representative k) = representative k ∧
    R = pull (realMatrix S) (realMatrix (pivot j).direction)

theorem ray_pull {k : Fin 7} {R : M} (h : IsRay k R) {S : IntMat} (hu : IsUnit S)
    (hs : pull (realMatrix S) (representative k) = representative k) :
    IsRay k (pull (realMatrix S) R) := by
  obtain ⟨j,U,src,hU,fix,rfl⟩ := h
  refine ⟨j,U*S,src,hU.mul hu,?_,?_⟩
  · rw [map_mul,← pull_mul,fix,hs]
  · rw [pull_mul,map_mul]

variable {m : ℕ}
abbrev Lines (m : ℕ) := Fin m → Fin 6 → ℤ

def supported (Z : Lines m) (R D : M) : Prop :=
  (∃ i, 0 < contact (Z i) R) ∧ ∀ i,
    0 ≤ contact (Z i) R ∧ (0 < contact (Z i) R → 0 < contact (Z i) D)

def score (b : Fin m → Bool) : ℤ := ∑ i, if b i then (2:ℤ)^i.val else 0

def positiveBits (Z : Lines m) (D : M) (i : Fin m) : Bool := decide (0 < contact (Z i) D)

/-- A permutation of contact evaluations induced by an integral automorphism. -/
def Realizes (k : Fin 7) (Z : Lines m) (p : Equiv.Perm (Fin m)) : Prop :=
  ∃ S : IntMatˣ, pull (realMatrix S) (representative k) = representative k ∧
    ∀ (D : M) i, contact (Z i) (pull (realMatrix S) D) = contact (Z (p i)) D

theorem realizes_one (k : Fin 7) (Z : Lines m) : Realizes k Z 1 := by
  refine ⟨1,?_,fun D i ↦ ?_⟩ <;> simp [pull]

theorem realizes_mul {k : Fin 7} {Z : Lines m} {p q : Equiv.Perm (Fin m)}
    (h : Realizes k Z p) (h' : Realizes k Z q) : Realizes k Z (p*q) := by
  obtain ⟨S,hS,eq⟩ := h
  obtain ⟨T,hT,eq'⟩ := h'
  refine ⟨S*T,?_,fun D i ↦ ?_⟩ <;> simp only [Units.val_mul,map_mul,← pull_mul]
  · rw [hS,hT]
  · rw [eq',eq]; rfl

def NormalSupport (k : Fin 7) (Z : Lines m) : Prop :=
  ∀ (D : M), D.IsHermitian → (∀ i, 0 ≤ contact (Z i) D) → (∃ i, 0 < contact (Z i) D) →
    (∀ p, Realizes k Z p → score (positiveBits Z D ∘ p) ≤ score (positiveBits Z D)) →
    ∃ R, R.IsHermitian ∧ IsRay k R ∧ supported Z R D

private theorem support_exists {k : Fin 7} {Z : Lines m} (norm : NormalSupport k Z)
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
  have fT : pull T (representative k) = representative k := by
    simpa only [fixed] using back (representative k)
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
theorem cone_of_support {k : Fin 7} (Z : Lines m)
    (tight : ∀ i, Z i ≠ 0 ∧ value (representative k) (Z i) = 1)
    (separates : ∀ D : M, D.IsHermitian → (∀ i, contact (Z i) D = 0) → D = 0)
    (norm : NormalSupport k Z) (D : M) (sym : D.IsHermitian)
    (admissible : ∀ z : Fin 6 → ℤ, z ≠ 0 → value (representative k) z = 1 → 0 ≤ value D z)
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

end SigabaNeo.Wall1.Watson.HigherGram.Six

#print axioms SigabaNeo.Wall1.Watson.HigherGram.Six.cone_of_support
