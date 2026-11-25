import SigabaNeoStd.Lattices.ProgAlgo.SLPTape
import SigabaNeoStd.Machines.Gates

/-!
# The tape layout of gate lists

The input of the `f̂` generator: a gate list `gs` (the format of `SigabaNeo.parse`, wires `1`,
the inputs, then the gates) as the stream of its wire indices, two per gate, each in unary on `W`
bits (`unaryW W j = 1^j 0^(W-j)`, as in `gatesW`):

  `gsW W gs = unaryW W a₀ ++ unaryW W b₀ ++ unaryW W a₁ ++ unaryW W b₁ ++ …`.

It is the source stream of the register machine of the generator (`RegVM.senc E src =
(src.map (uw E.W)).flatten` with `uw = unaryW`) for the source `gsSrc gs = [a₀, b₀, a₁, b₁, …]`
(`gsW_eq_flatten`). With `W` at least every index, every block has `W` bits (`length_gsW`).
-/

namespace SigabaNeo.Tape.Prog

/-- The wire indices of a gate list, two per gate. -/
def gsSrc (gs : GateList) : List ℕ := gs.flatMap fun g => [g.1, g.2]

/-- **The word of a gate list**: its wire indices in unary on `W` bits. -/
def gsW (W : ℕ) (gs : GateList) : List Bool := gs.flatMap fun g => unaryW W g.1 ++ unaryW W g.2

theorem gsW_eq_flatten (W : ℕ) (gs : GateList) : gsW W gs = ((gsSrc gs).map (unaryW W)).flatten := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [gsW, gsSrc, List.flatMap_cons, List.map_append, List.flatten_append] at ih ⊢
    rw [ih]; simp

theorem gsW_nil (W : ℕ) : gsW W [] = [] := rfl

theorem gsW_cons (W : ℕ) (g : ℕ × ℕ) (gs : GateList) :
    gsW W (g :: gs) = unaryW W g.1 ++ unaryW W g.2 ++ gsW W gs := rfl

theorem length_gsW {W : ℕ} {gs : GateList} (h : ∀ g ∈ gs, g.1 ≤ W ∧ g.2 ≤ W) :
    (gsW W gs).length = gs.length * (2 * W) := by
  induction gs with
  | nil => simp [gsW]
  | cons g gs ih =>
    have hg := h g (by simp)
    rw [gsW_cons, List.length_append, List.length_append, length_unaryW hg.1, length_unaryW hg.2,
      ih (fun g' hg' => h g' (by simp [hg'])), List.length_cons]
    ring

end SigabaNeo.Tape.Prog
