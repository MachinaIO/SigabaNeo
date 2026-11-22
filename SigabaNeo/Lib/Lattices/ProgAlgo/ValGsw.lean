import SigabaNeo.Lib.Lattices.ProgAlgo.ValIns

/-!
# The predicate's simulation on the word machine

With the block `gate` (`F = fV V f`) and the slot `C = one` of the wire `1`, the results of the gate
loop are the values of the predicate's gates (`gl_values`), so its last result is the value of the
output wire (`getLast_gl_values`). The inputs: one joint word per input `i`, from the streams of the
`Ψᵢ`, of the `Rᵢ` and of the bits `xᵢ` (`insGC = rep jtBody`, one bit per input).
-/

namespace SigabaNeo.Tape

namespace ValVM

open SigabaNeo.Lattices SigabaNeo.Lattices.SLP SigabaNeo.Lattices.Algo SigabaNeo.Encode

set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

variable {V : ℕ} {f : List Bool → List Bool → List Bool}

/-- The slot of the operand `j` is the value of the wire `ofIdx 10 j`. -/
theorem slotOf_wireVal (one : List Bool) (ins rs : List (List Bool)) (hins : ins.length = 10)
    (j : ℕ) : slotOf one ins rs j = wireVal (fun i : Fin 10 => ins.getD i.val []) one rs (ofIdx 10 j) := by
  unfold slotOf ofIdx
  by_cases h0 : j = 0
  · subst h0; simp [wireVal]
  · by_cases h1 : j - 1 < 10
    · rw [if_neg h0, dif_pos h1, wireVal]
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [List.cons_append, List.getD_cons_succ, List.getD_append _ _ _ _ (by rw [hins]; simpa using h1)]
      have hj : j' < ins.length := by rw [hins]; simpa using h1
      simp [List.getElem?_eq_getElem hj]
    · rw [if_neg h0, dif_neg h1, wireVal]
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 11 := ⟨j - 11, by omega⟩
      rw [show j' + 11 = (j' + 10) + 1 by omega, List.cons_append, List.getD_cons_succ,
        List.getD_append_right _ _ _ _ (by rw [hins]; omega), hins,
        show j' + 10 - 10 = j' by omega, show j' + 10 + 1 - 1 - 10 = j' by omega]

/-- **The results of the gate loop with the step are the values of the gates.** -/
theorem gl_values (F : List Bool → List Bool → List Bool) (one : List Bool)
    (ins : List (List Bool)) (hins : ins.length = 10) (gs : GateList) :
    gl F one ins gs = SLP.values (fun i : Fin 10 => ins.getD i.val []) one F (fromGates 10 gs) := by
  have key : ∀ (gs : GateList) (rs : List (List Bool)), gs.foldl (glStep F one ins) rs =
      SLP.run (fun i : Fin 10 => ins.getD i.val []) one F (fromGates 10 gs) rs := by
    intro gs
    induction gs with
    | nil => intro rs; rfl
    | cons g gs ih =>
      intro rs
      rw [List.foldl_cons, ih]
      show _ = SLP.run _ one F (⟨ofIdx 10 g.1, ofIdx 10 g.2⟩ :: fromGates 10 gs) rs
      rw [SLP.run, glStep, slotOf_wireVal one ins _ hins, slotOf_wireVal one ins _ hins]
  exact key gs []

theorem length_values {ι : Type*} (inp : ι → List Bool) (one : List Bool)
    (step : List Bool → List Bool → List Bool) (p : SLP ι) :
    (SLP.values inp one step p).length = p.length := by
  rw [SLP.values]
  have : ∀ (p : SLP ι) (acc : List (List Bool)), (SLP.run inp one step p acc).length =
      acc.length + p.length := by
    intro p
    induction p with
    | nil => intro acc; simp [SLP.run]
    | cons g p ih => intro acc; rw [SLP.run, ih]; simp; omega
  rw [this]; simp

/-- **The last result is the value of the predicate's output wire.** -/
theorem getLast_gl_values (F : List Bool → List Bool → List Bool) (one : List Bool)
    (ins : List (List Bool)) (hins : ins.length = 10) (gs : GateList) (hne : gs ≠ []) :
    (gl F one ins gs).getLastD [] =
      valueOf (fun i : Fin 10 => ins.getD i.val []) one F (predOf 10 gs).1 (predOf 10 gs).2 := by
  rw [gl_values F one ins hins gs, predOf, valueOf, wireVal]
  have hl : (SLP.values (fun i : Fin 10 => ins.getD i.val []) one F (fromGates 10 gs)).length =
      gs.length := by rw [length_values]; simp [fromGates]
  have hpos : 0 < gs.length := List.length_pos_iff.mpr hne
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
  generalize SLP.values (fun i : Fin 10 => ins.getD i.val []) one F (fromGates 10 gs) = X at hl ⊢
  rw [hl, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  rfl

/-- **The inputs of the predicate**: `10` rounds of `jtBody`. -/
def insGC : Code := ofList [.cp CA T10, .rep CA jtBody]

end ValVM

end SigabaNeo.Tape
