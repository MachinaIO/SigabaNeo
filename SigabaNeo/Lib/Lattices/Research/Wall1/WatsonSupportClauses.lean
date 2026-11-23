import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonContactSupport

/-! A typed description of the geometric justification for each resolution input. -/
noncomputable section
namespace SigabaNeo.Wall1.Watson.HigherGram.Six
open MaskResolution Finset Matrix
variable {m g r d : ℕ}

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

def SeedValid (k : Fin 7) (Z : Lines m) (v : Fin m → ℤ) : Prop :=
  (∃ R, R.IsHermitian ∧ IsRay k R ∧ ∀ i, contact (Z i) R = (v i : ℝ)) ∧
  (∃ i, 0 < v i) ∧ ∀ i, 0 ≤ v i

theorem seedValid_of_pivot {k : Fin 7} (Z : Lines m) (v : Fin m → ℤ) (j : Fin 32)
    (src : (pivot j).src = k) (sym : (pivot j).direction.IsSymm)
    (values : ∀ i, Z i ⬝ᵥ ((pivot j).direction *ᵥ Z i) = v i)
    (ne : ∃ i, 0 < v i) (pos : ∀ i, 0 ≤ v i) : SeedValid k Z v := by
  obtain ⟨herm,ray⟩ := ray_seed j src sym
  exact ⟨⟨_,herm,ray,fun i ↦ by rw [contact_integer,values]⟩,ne,pos⟩

theorem tight_of_rational (k : Fin 7) (Z : Lines m)
    (nz : ∀ i, Z i ≠ 0)
    (h : ∀ i, (fun a ↦ (Z i a : ℚ)) ⬝ᵥ (forms k *ᵥ fun a ↦ (Z i a : ℚ)) = 1) :
    ∀ i, Z i ≠ 0 ∧ value (representative k) (Z i) = 1 := by
  intro i; refine ⟨nz i,?_⟩
  change value ((forms k).map (Rat.castHom ℝ)) _ = _
  rw [contact_rational,h]; norm_num

theorem normal_of_clauses {k : Fin 7} (Z : Lines m)
    (p : Fin g → Equiv.Perm (Fin m)) (rows : Fin r → Fin m → ℤ) (values : Fin d → Fin m → ℤ)
    (autos : ∀ a, Realizes k Z (p a)) (relations : ∀ a i j, moment Z (rows a) i j = 0)
    (seeds : ∀ a, SeedValid k Z (values a)) {n : ℕ} (input : ℕ → Clause)
    (reason : ℕ → Reason m g r d) (arithmetic : ∀ i : Fin n, usable p rows values (input i) (reason i))
    (unsat : ∀ b : Fin m → Bool, ¬ ∀ i : Fin n, (input i).Sat b) : NormalSupport k Z := by
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

end SigabaNeo.Wall1.Watson.HigherGram.Six

#print axioms SigabaNeo.Wall1.Watson.HigherGram.Six.normal_of_clauses
