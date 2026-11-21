module

public import SigabaNeo.Lib.Lattices.Research.Wall1.SelectedSlide
public import SigabaNeo.Lib.Lattices.Research.Wall1.Terminal
import all SigabaNeo.Lib.Lattices.Research.Wall1.Terminal

@[expose] public section

namespace SigabaNeo.Wall1
open QAry
open scoped Matrix

/-- The actual slide output contains the signed plant as an entire integral row. -/
def captured {m n q β k : ℕ} [Fact q.Prime] (pos : 0 < β) (shape : k*β = dim m n)
    (e : Fin m → ℤ) (s : Fin n → ℤ) (A : Matrix (Fin m) (Fin n) (ZMod q)) : Prop :=
  let c := fun i ↦ A i ⬝ᵥ (fun j ↦ (s j : ZMod q)) + e i
  let B := selectedRows pos shape A c
  let u := Planted.plantedPoint e s ∘ indexEquiv.symm
  ∃ i, B i = u ∨ B i = -u

/-- On a miss, the nonzero projected test can equivalently compare primitive vectors. -/
theorem capture_or_primitive_iff {d : ℕ} {ι : Type*} (C : Prop)
    (Q : Submodule ℤ (EuclideanSpace ℝ (Fin d))) (B : Module.Basis ι ℤ Q) (v : Q) :
    (C ∨ (v ≠ 0 ∧ ∀ w : Q, w ≠ 0 → w ≠ v → w ≠ -v → ‖v‖ < ‖w‖)) ↔
    (C ∨ (Primitive v ∧ ∀ w : Q, Primitive w → w ≠ v → w ≠ -v → ‖v‖ < ‖w‖)) := by
  apply or_congr_right
  constructor
  · rintro ⟨hv, h⟩
    exact (terminal_primitive_iff Q B v hv).mp h
  · intro h
    exact ⟨h.1.1, (terminal_primitive_iff Q B v h.1.1).mpr h⟩

theorem combine_capture {α : Type*} [Fintype α] [Nonempty α] (C : α → Prop) (t : α → Test)
    (a b : ℝ) (h : 1-a ≤ mass (fun x ↦ C x ∨ (t x).sameLine))
    (g : 1-b ≤ mass (fun x ↦ C x ∨ (t x).offLine)) :
    1-(a+b) ≤ mass (fun x ↦ C x ∨ (t x).sameLine ∧ (t x).offLine) := by
  simpa only [← or_and_left] using
    combine (fun x ↦ ⟨C x ∨ (t x).sameLine, C x ∨ (t x).offLine⟩) a b h g

end SigabaNeo.Wall1
