import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonMaskResolution

/-! Boolean clauses for contact supports, independent of the dimension of the lattice. -/
namespace SigabaNeo.Wall1.Watson.HigherGram.Six
open Finset MaskResolution
variable {m g r d : ℕ}

def score (b : Fin m → Bool) : ℤ := ∑ i, if b i then (2:ℤ)^i.val else 0

def composeWord {g : ℕ} (p : Fin g → Equiv.Perm (Fin m)) (w : List (Fin g)) :
    Equiv.Perm (Fin m) := (w.map p).prod

theorem pos_of_dimacs {s : Fin m → Bool} {c : Clause} (bad : ¬ c.Sat s) (i : Fin m) :
    (c.neg.testBit i → s i = true) ∧ (c.pos.testBit i → s i = false) := by
  constructor
  · intro h; cases eq : s i
    · exact False.elim (bad ⟨i,Or.inr ⟨h,eq⟩⟩)
    · rfl
  · intro h; cases eq : s i
    · rfl
    · exact False.elim (bad ⟨i,Or.inl ⟨h,eq⟩⟩)

def gain (p : Equiv.Perm (Fin m)) (i : Fin m) : ℤ := 2^(p.symm i).val - 2^i.val

def lowerScore (p : Equiv.Perm (Fin m)) (c : Clause) : ℤ :=
  ∑ i : Fin m, if c.neg.testBit i then gain p i else
    if c.pos.testBit i then 0 else min 0 (gain p i)

inductive Reason (m g r d : ℕ)
  | nonzero
  | relation (row : Fin r) (negative : Bool) (index : Fin m)
  | symmetry (word : List (Fin g))
  | ray (seed : Fin d) (word : List (Fin g))
  deriving Inhabited

def signed (a : Fin m → ℤ) (flip : Bool) (i : Fin m) := if flip then -(a i) else a i

def usable (p : Fin g → Equiv.Perm (Fin m)) (rows : Fin r → Fin m → ℤ)
    (values : Fin d → Fin m → ℤ) (c : Clause) : Reason m g r d → Prop
  | .nonzero => ∀ i : Fin m, c.pos.testBit i = true
  | .relation a flip i => 0 < signed (rows a) flip i ∧ c.neg.testBit i = true ∧
      ∀ j : Fin m, signed (rows a) flip j < 0 → c.pos.testBit j = true
  | .symmetry w => 0 < lowerScore (composeWord p w) c
  | .ray u w => ∀ i : Fin m, 0 < values u (composeWord p w i) → c.neg.testBit i = true

instance (p : Fin g → Equiv.Perm (Fin m)) (rows : Fin r → Fin m → ℤ)
    (values : Fin d → Fin m → ℤ) (c : Clause) (why : Reason m g r d) :
    Decidable (usable p rows values c why) := by
  cases why <;> unfold usable <;> infer_instance

end SigabaNeo.Wall1.Watson.HigherGram.Six
