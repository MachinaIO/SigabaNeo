import SigabaNeo.Lib.Machines.Randomized
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant

/-!
# Almost constant functions are tidily polynomial-time

A function constant outside finitely many inputs is computed in constant time and zero space
(cslib's machine for almost constant functions), hence tidily in constant time
(`computableTidilyInPolyTime_of_almostConst`). So the builders of `Lib/Machines/Guarded` and
`Lib/Machines/Randomized` apply to every algorithm on bounded inputs. The machine reads its input
against a table: its description is large, which the cost of a primitive counts.
-/

namespace SigabaNeo

open Turing Turing.MultiTapeTM

theorem computableTidilyInPolyTime_of_almostConst {α β : Type} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {f : α → β} (h : ∃ b : β, {a : α | f a ≠ b}.Finite) :
    ComputableTidilyInPolyTime f encIn encOut := by
  obtain ⟨c, hc⟩ := computableInTimeAndSpace_of_exists_finite_ne (encIn := encIn)
    (encOut := encOut) h
  exact ⟨fun _ => 2 * c + 2, fun _ => 0, PolyBounded.const _, PolyBounded.const _,
    hc.computableTidilyInTimeAndSpace⟩

/-- **Randomized algorithms on bounded inputs**: if `G` is constant outside finitely many pairs
(input, coins), its guarded randomized machine exists. -/
theorem Machine.exists_randomized_of_almostConst {α β : Type} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {G : α × List Bool → β} (hG : ∃ b : β, {a | G a ≠ b}.Finite)
    (L m : ℕ) (d : β) :
    ∃ M : Machine, ∀ a, M.run (encIn a) =
      if (encIn a).length ≤ L then (Cslib.BitString.uniformList m).map (fun w => encOut (G (a, w)))
      else PMF.pure (encOut d) :=
  Machine.exists_randomized (computableTidilyInPolyTime_of_almostConst hG) L m d

end SigabaNeo
