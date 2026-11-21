module

public import SigabaNeo.Lib.Lattices.QAry.Basis
public import SigabaNeo.Lib.Lattices.Reduction.Slide.Update

@[expose] public section

namespace SigabaNeo.Wall1

open QAry
open scoped Matrix

noncomputable section

/-- The canonical q-ary rows are fed to the verified deterministic slide loop at tolerance 1/10. -/
def selectedRows {m n q β k : ℕ} [Fact q.Prime] (pos : 0 < β) (shape : k*β = dim m n)
    (A : Matrix (Fin m) (Fin n) (ZMod q)) (c : Fin m → ZMod q) :=
  let input : Slide.SlideBasis β k (dim m n) :=
    ⟨fun i ↦ rows A c (Fin.cast shape i),
      (rows_independent A c).comp _ (finCongr shape).injective⟩
  let factor : ℚ := (1 + 1/10)^2
  let fuel := Slide.slideFuel factor (by norm_num [factor])
    (Slide.flatPotential input.val (Slide.boundaryEnds pos))
  (Slide.slideLoop (Slide.slidePass pos factor) fuel input).1.val

/-- Split the terminal test into same-line and off-line failures. A vanished plant fails. -/
structure Test where
  sameLine : Prop
  offLine : Prop

def terminal {m n q β k : ℕ} [Fact q.Prime] (pos : 0 < β) (shape : k*β = dim m n)
    (e : Fin m → ℤ) (s : Fin n → ℤ) (A : Matrix (Fin m) (Fin n) (ZMod q)) : Test :=
  let c := fun i ↦ A i ⬝ᵥ (fun j ↦ (s j : ZMod q)) + e i
  let B := selectedRows pos shape A c
  let eu := fun (z : Fin (dim m n) → ℤ) ↦
    (WithLp.toLp 2 (fun i ↦ (z i : ℝ)) : EuclideanSpace ℝ (Fin (dim m n)))
  let W := Submodule.span ℝ (Set.range (fun i : {i : Fin (k*β) // i.val < k*β-β} ↦ eu (B i)))
  let project := fun z ↦ Wᗮ.orthogonalProjectionOnto (eu z)
  let u := project (Planted.plantedPoint e s ∘ indexEquiv.symm)
  let short := fun z ↦ FinMember A c z ∧ project z ≠ 0 ∧ ‖project z‖ ≤ ‖u‖
  ⟨u ≠ 0 ∧ ∀ z, short z → project z ∈ Submodule.span ℝ {u} → project z = u ∨ project z = -u,
    ∀ z, short z → project z ∈ Submodule.span ℝ {u}⟩

def mass {α : Type*} [Fintype α] (p : α → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter p).card : ℝ) / Fintype.card α

/-- Union bound for two terminal tests under the uniform finite input law. -/
theorem combine {α : Type*} [Fintype α] [Nonempty α] (t : α → Test) (a b : ℝ)
    (h : 1-a ≤ mass (fun x ↦ (t x).sameLine)) (g : 1-b ≤ mass (fun x ↦ (t x).offLine)) :
    1-(a+b) ≤ mass (fun x ↦ (t x).sameLine ∧ (t x).offLine) := by
  classical
  let S := Finset.univ.filter (fun x ↦ (t x).sameLine)
  let T := Finset.univ.filter (fun x ↦ (t x).offLine)
  have eqn : S ∩ T = Finset.univ.filter (fun x ↦ (t x).sameLine ∧ (t x).offLine) := by
    ext
    simp [S,T]
  have cap := Finset.card_union_add_card_inter S T
  have bound := Finset.card_le_univ (S ∪ T)
  rw [eqn] at cap
  have positive : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  unfold mass at *
  rw [le_div_iff₀ positive] at *
  change (1-a)*_ ≤ (S.card : ℝ) at h
  change (1-b)*_ ≤ (T.card : ℝ) at g
  have counts : (S.card : ℝ) + T.card ≤ Fintype.card α +
      (Finset.univ.filter (fun x ↦ (t x).sameLine ∧ (t x).offLine)).card := by
    exact_mod_cast (show _ ≤ _ by omega : S.card + T.card ≤ _)
  apply le_of_add_le_add_left (a := (Fintype.card α : ℝ))
  refine le_trans ?_ (le_trans counts ?_)
  swap
  · apply le_of_eq
    congr 2
    apply congrArg Finset.card
    ext x
    simp
  convert add_le_add h g using 1
  ring

end
end SigabaNeo.Wall1
