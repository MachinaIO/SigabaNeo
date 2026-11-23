import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonSixConeReduction
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonContactCone

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

def contactCone (k : Fin 7) : ContactCone.Cone 6 :=
  ⟨representative k, {A | ∃ j, (pivot j).src = k ∧ (pivot j).direction = A}⟩

theorem isRay_cone_iff {k : Fin 7} {R : M} : ContactCone.IsRay (contactCone k) R ↔ IsRay k R := by
  constructor
  · rintro ⟨_,S,⟨j,src,rfl⟩,unit,fix,eq⟩
    exact ⟨j,S,src,unit,fix,eq⟩
  · rintro ⟨j,S,src,unit,fix,eq⟩
    exact ⟨_,S,⟨j,src,rfl⟩,unit,fix,eq⟩

theorem normalSupport_cone_iff {k : Fin 7} {Z : Lines m} :
    ContactCone.NormalSupport (contactCone k) Z ↔ NormalSupport k Z := by
  unfold ContactCone.NormalSupport NormalSupport
  simp only [isRay_cone_iff]
  rfl

/-- A finite contact family and the normalized-support test suffice for one local cone. -/
theorem cone_of_support {k : Fin 7} (Z : Lines m)
    (tight : ∀ i, Z i ≠ 0 ∧ value (representative k) (Z i) = 1)
    (separates : ∀ D : M, D.IsHermitian → (∀ i, contact (Z i) D = 0) → D = 0)
    (norm : NormalSupport k Z) (D : M) (sym : D.IsHermitian)
    (admissible : ∀ z : Fin 6 → ℤ, z ≠ 0 → value (representative k) z = 1 → 0 ≤ value D z)
    (f : M →ₗ[ℝ] ℝ) (slopes : ∀ R, IsRay k R → 0 ≤ f R) : 0 ≤ f D := by
  exact ContactCone.cone_of_support Z tight separates (normalSupport_cone_iff.mpr norm)
    D sym admissible f (fun R hr ↦ slopes R (isRay_cone_iff.mp hr))

end SigabaNeo.Wall1.Watson.HigherGram.Six

#print axioms SigabaNeo.Wall1.Watson.HigherGram.Six.cone_of_support
