import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonContactSupport

/-! A typed description of the geometric justification for each resolution input. -/
noncomputable section
namespace SigabaNeo.Wall1.Watson.HigherGram.Six
open MaskResolution Finset Matrix
variable {m g r d : ℕ}

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
  apply normalSupport_cone_iff.mp
  apply ContactCone.normal_of_clauses (k := contactCone k) Z p rows values autos relations _ input reason arithmetic unsat
  intro i
  obtain ⟨⟨R,sym,ray,hs⟩,rest⟩ := seeds i
  exact ⟨⟨R,sym,isRay_cone_iff.mpr ray,hs⟩,rest⟩

end SigabaNeo.Wall1.Watson.HigherGram.Six

#print axioms SigabaNeo.Wall1.Watson.HigherGram.Six.normal_of_clauses
