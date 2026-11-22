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

/-- **The inputs of the predicate on the machine**: `INSW` receives
`Ψᵢ ++ Rᵢ ++ [xᵢ] ++ 0^(M − 1)` for the `10` inputs (`M = N K`; `TK1` blank, one bit per input). -/
theorem exec_insGC {A2 Ad M : ℕ} (w : St) (ht : ITmpl V A2 Ad M 1 w) (h10 : (w T10).length = 10)
    (pW rW : Fin 10 → List Bool) (hp : ∀ i, (pW i).length = A2) (hr : ∀ i, (rW i).length = Ad)
    (xs : List Bool) {RB RW : List Bool}
    (hB : w BSt = ((List.finRange 10).map pW).flatten ++ RB)
    (hW : w WSt = ((List.finRange 10).map rW).flatten ++ RW) (hZ : w rZ = xs) :
    exec V f insGC w INSW = (w INSW ++ ((List.finRange 10).map fun i =>
        jw (pW i) (rW i) (xs.getD i.val false) M 1).flatten).drop (10 * V) ∧
      ∀ j ∉ wr insGC, exec V f insGC w j = w j := by
  refine ⟨?_, fun j hj => exec_not_mem _ _ _ hj⟩
  simp only [insGC, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
  set w1 := Function.update w CA (w T10) with hw1
  have e1 : ∀ j, j ≠ CA → w1 j = w j := fun j h => Function.update_of_ne h _ _
  have I := exec_rep_inv (V := V) (f := f) (c := CA) (B := jtBody)
    (fun r w' => r ≤ 10 → ITmpl V A2 Ad M 1 w' ∧
      w' BSt = (((List.finRange 10).drop r).map pW).flatten ++ RB ∧
      w' WSt = (((List.finRange 10).drop r).map rW).flatten ++ RW ∧ w' rZ = xs.drop r ∧
      w' INSW = (w1 INSW ++ (((List.finRange 10).take r).map fun i =>
        jw (pW i) (rW i) (xs.getD i.val false) M 1).flatten).drop (r * V))
    (fun r w' ih hrr => by
      obtain ⟨t1, hB', hW', hZ', hI'⟩ := ih (by omega)
      have hrl : r < (List.finRange 10).length := by simp; omega
      set i := (List.finRange 10)[r] with hi
      have hiv : i.val = r := by simp [hi]
      have c0 : ∀ j, j ≠ CA → Function.update w' CA (w' CA).tail j = w' j :=
        fun j h => Function.update_of_ne h _ _
      obtain ⟨R1, R2, R3, R4, R5⟩ := exec_jtBody (V := V) (f := f)
        (Function.update w' CA (w' CA).tail) (t1.of_eq fun j hj => c0 j (by revert j hj; decide))
        (b := pW i) (x := rW i) (L0 := (((List.finRange 10).drop (r + 1)).map pW).flatten ++ RB)
        (L1 := (((List.finRange 10).drop (r + 1)).map rW).flatten ++ RW) (z := xs.drop r)
        (hp i) (hr i)
        (by rw [c0 BSt (by decide), hB', List.drop_eq_getElem_cons hrl, List.map_cons,
          List.flatten_cons, List.append_assoc])
        (by rw [c0 WSt (by decide), hW', List.drop_eq_getElem_cons hrl, List.map_cons,
          List.flatten_cons, List.append_assoc])
        (by rw [c0 rZ (by decide), hZ'])
      refine ⟨(t1.of_eq fun j hj => c0 j (by revert j hj; decide)).of_eq fun j hj =>
        R5 j (by revert j hj; decide) (by revert j hj; decide) (by revert j hj; decide)
          (by revert j hj; decide) (by revert j hj; decide) (by revert j hj; decide),
        R2, R3, by rw [R4]; simp [List.drop_drop, Nat.add_comm], ?_⟩
      rw [R1, c0 INSW (by decide), hI', takeD_one, List.getD_eq_getElem?_getD, List.getElem?_drop,
        Nat.add_zero, ← List.getD_eq_getElem?_getD]
      have hl : (((List.finRange 10).take r).map fun i =>
          jw (pW i) (rW i) (xs.getD i.val false) M 1).flatten.length = r * V := by
        rw [length_flatten_of (V := V) (fun y hy => by
          simp only [List.mem_map] at hy
          obtain ⟨j, -, rfl⟩ := hy
          simp [jw, hp, hr, t1.hV]; have := t1.hNK; omega)]
        simp; omega
      rw [drop_append_drop' (by rw [List.length_append, hl]; omega), List.append_assoc,
        List.take_succ, List.getElem?_eq_getElem hrl, Option.toList_some, List.map_append,
        List.map_singleton, List.flatten_append, List.flatten_singleton, ← hi, hiv, Nat.succ_mul]
      rfl) w1
    (fun _ => ⟨ht.of_eq fun j hj => e1 j (by revert j hj; decide),
      by rw [e1 BSt (by decide), hB]; simp, by rw [e1 WSt (by decide), hW]; simp,
      by rw [e1 rZ (by decide), hZ]; simp, by simp⟩)
  rw [show (w1 CA).length = 10 by rw [hw1, Function.update_self, h10]] at I
  rw [(I le_rfl).2.2.2.2, List.take_of_length_le (by simp), e1 INSW (by decide)]

end ValVM

end SigabaNeo.Tape
