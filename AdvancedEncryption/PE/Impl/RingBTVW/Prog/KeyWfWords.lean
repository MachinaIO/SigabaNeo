import PE.Impl.RingBTVW.Prog.KeyFront
import PE.Impl.RingBTVW.Prog.KeySumStore
import PE.Impl.RingBTVW.Prog.Layout

/-!
# The inputs of the two simulations from the simulation data

The `W_f` block of the key component (`WfSpec`, `PE.Impl.RingBTVW.Prog.KeyP`) runs the two SLP
evaluators (`run_slpSim`) and the sum `simKeyP` (`run_simKeyP_store`). Their input entries are
the joint words

* `insTW sd`: for every `j : Fin nA × BI N k`, in the order `Enum.list` of the codec
  `sdEnc` (the order of the `Wⱼ` and of the `Bⱼ` in the word of the simulation data),
  `jointW (rowW (B_j), colsW (W_j), psiBitsW … j)`, at the index `enumIx j`;
* `insGW sd`: for every `i : Fin nA`, `jointW (colsW (Ψᵢ), colsW (Rᵢ), constW (bitW K xᵢ))`, at
  the index `i`.

**`simKeyStoreW_sd`**: with these inputs, at the gate list `parse C` (the one the front end
carries, `KGsim_eq_front`), the word read from the two final stores (`simKeyStoreW`) is the word
of `W_f = simW sd C`. So the `W_f` block has the law `WfSpec` as soon as it writes the stores
`storeT … (insTW sd) enumIx` and `storeG … (insGW sd) (·.val)` and runs `simKeyP`
(`run_simKeyP_store`).
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  Matrix AdvancedEncryption.RingBTVW.Fresh AdvancedEncryption.RingBTVW.Algo
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPWord

/-! ### Positions in an enumeration -/

section Enum

variable {α β : Type} [Enum α] [DecidableEq α]

/-- The position of an element in the enumeration. -/
def enumIx (a : α) : ℕ := (Enum.list (α := α)).idxOf a

theorem enumIx_lt (a : α) : enumIx a < (Enum.list (α := α)).length :=
  List.idxOf_lt_length_of_mem (Enum.complete a)

theorem getD_enumIx (f : α → β) (d : β) (a : α) :
    ((Enum.list (α := α)).map f).getD (enumIx a) d = f a := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact enumIx_lt a), List.getElem_map]
  unfold enumIx
  rw [List.getElem_idxOf]

end Enum

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k}

/-- The index type of the inputs of `f̂`. -/
abbrev JT (N K k : ℕ) (hk : 2 ^ K < 2 ^ k) : Type :=
  (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index

instance : DecidableEq (JT N K k hk) := inferInstanceAs (DecidableEq (Fin nA × BI N k))

/-- **The inputs of the simulation of `f̂`**, in the order of the codec. -/
def insTW (sd : SimData hk c) : List (List Bool) :=
  (Enum.list (α := JT N K k hk)).map fun j => jointW (rowW N K k (sd.mpk.Bj j),
    colsW N K k c.d (sd.W j), psiBitsW N K k (fun i => colsW N K k 2 (sd.Ψ i)) j)

/-- **The inputs of the simulation of the predicate.** -/
def insGW (sd : SimData hk c) : List (List Bool) :=
  (List.finRange nA).map fun i => jointW (colsW N K k 2 (sd.Ψ i), colsW N K k c.d (sd.Rm i),
    constW N K (bitW K (attrBits sd.x i)))

/-- The index of an input of `f̂`. -/
def ixT (N K k : ℕ) (hk : 2 ^ K < 2 ^ k) (j : Fin nA × BI N k) : ℕ := enumIx (α := JT N K k hk) j

theorem length_insTW (sd : SimData hk c) :
    (insTW sd).length = (Enum.list (α := JT N K k hk)).length := by
  rw [insTW, List.length_map]

theorem length_insGW (sd : SimData hk c) : (insGW sd).length = nA := by
  rw [insGW, List.length_map, List.length_finRange]

/-- **`W_f` from the stores of the simulations on the inputs of the simulation data.** -/
theorem simKeyStoreW_sd (sd : SimData hk c) (C : List Bool) :
    simKeyStoreW N K k c.d (ordT₀ N k) (ordO₀ N k) (parse C) (insTW sd) (ixT N K k hk)
        (Enum.list (α := JT N K k hk)).length (insGW sd) (fun i => i.val) nA =
      colsW N K k c.d (simKeyMat (S := Sdw (N := N) hk) sd.Rm (attrBits sd.x) sd.W sd.Ψ sd.mpk.Bj
        (predOf nA (parse C))) := by
  exact simKeyStoreW_eq_mat hk sd.Rm (attrBits sd.x) sd.W sd.Ψ sd.mpk.Bj (parse C)
    (length_insTW sd) (fun j => enumIx_lt (α := JT N K k hk) j)
    (fun j => getD_enumIx (α := JT N K k hk) _ _ j) (length_insGW sd) (fun i => i.isLt)
    (fun i => by
      rw [insGW, List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_finRange]
      rfl)

/-- **The simulated trapdoor of a predicate program** `P` (`simW sd C = simWP sd (predC C)`). -/
noncomputable def simWP (sd : SimData hk c) (P : SLP (Fin nA) × Wire (Fin nA)) :
    Matrix (Fin c.d) (RingBTVW.Fresh.Col k) (Rg N K) :=
  simKeyMat (S := Sdw (N := N) hk) sd.Rm (attrBits sd.x) sd.W sd.Ψ sd.mpk.Bj P

theorem simW_eq_P (sd : SimData hk c) (C : List Bool) : simW sd C = simWP sd (predC C) := rfl

/-- **`W_f` from the stores of the simulations**, for a predicate program. -/
theorem simKeyStoreW_sdP (sd : SimData hk c) (P : SLP (Fin nA) × Wire (Fin nA)) :
    simKeyStoreWP N K k c.d (ordT₀ N k) (ordO₀ N k) P (insTW sd) (ixT N K k hk)
        (Enum.list (α := JT N K k hk)).length (insGW sd) (fun i => i.val) nA =
      colsW N K k c.d (simWP sd P) :=
  simKeyStoreWP_eq_mat hk sd.Rm (attrBits sd.x) sd.W sd.Ψ sd.mpk.Bj P
    (length_insTW sd) (fun j => enumIx_lt (α := JT N K k hk) j)
    (fun j => getD_enumIx (α := JT N K k hk) _ _ j) (length_insGW sd) (fun i => i.isLt)
    (fun i => by
      rw [insGW, List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_finRange]
      rfl)

theorem length_mem_insTW (sd : SimData hk c) :
    ∀ x ∈ insTW sd, x.length = lenA N K k 1 + lenA N K k c.d + N * K := by
  intro x hx
  simp only [insTW, List.mem_map] at hx
  obtain ⟨j, -, rfl⟩ := hx
  rw [length_jointW, length_rowW', length_colsW']
  simp only [AdvancedEncryption.RingBTVW.Algo.psiBitsW, bitsW]
  rw [SigabaNeo.Tape.Prog.length_constW (length_bitW _ _)]

theorem length_mem_insGW (sd : SimData hk c) :
    ∀ x ∈ insGW sd, x.length = lenA N K k 2 + lenA N K k c.d + N * K := by
  intro x hx
  simp only [insGW, List.mem_map] at hx
  obtain ⟨i, -, rfl⟩ := hx
  rw [length_jointW, length_colsW', length_colsW', SigabaNeo.Tape.Prog.length_constW (length_bitW _ _)]

/-- **`simKeyP` writes the word of `W_f`** on the final stores of the two simulations of the inputs
of the simulation data, with the positions of the output wires of `f̂` (`posW`) and of the
predicate's output wire (tape `87`). -/
theorem run_simKeyP_sd (sd : SimData hk c) (C : List Bool) {W W' : ℕ}
    (hW : (Enum.list (α := JT N K k hk)).length +
      (fhatProg K (ordT₀ N k) (ordO₀ N k) (parse C)).1.length ≤ W)
    (hW' : SigabaNeo.Tape.Prog.wireIx (fun i : Fin nA => i.val) nA (predOf nA (parse C)).1.length
      (predOf nA (parse C)).2 ≤ W') (r : Store 94)
    (ht : Prog.KTmpl N K k c.d W (lenA N K k 1 + lenA N K k c.d + N * K) (lenA N K k 1)
      (r ∘ Prog.oKs))
    (hb : ∀ t : Fin 94, 18 ≤ t.val → t.val < 86 → r t = [])
    (hb' : ∀ t : Fin 94, 91 ≤ t.val → r t = [])
    (h1 : r 1 = (storeT N K k c.d (ordT₀ N k) (ordO₀ N k) (parse C) (insTW sd)
      (ixT N K k hk)).flatten)
    (h2 : r 2 = Prog.posW W N k (fhatPos K (ordT₀ N k) (ordO₀ N k) (parse C) (ixT N K k hk)
      (Enum.list (α := JT N K k hk)).length))
    (h86 : r 86 = (storeG N K k c.d (parse C) (insGW sd) (fun i => i.val)).flatten)
    (h87 : r 87 = SigabaNeo.Tape.Prog.unaryW W' (SigabaNeo.Tape.Prog.wireIx (fun i : Fin nA => i.val) nA (predOf nA (parse C)).1.length
      (predOf nA (parse C)).2))
    (h88 : (r 88).length = W') (h89 : (r 89).length = lenA N K k 2 + lenA N K k c.d + N * K)
    (h90 : (r 90).length = lenA N K k 2) :
    Prog.run Prog.simKeyP r = Function.update r 0 (colsW N K k c.d
      (simKeyMat (S := Sdw (N := N) hk) sd.Rm (attrBits sd.x) sd.W sd.Ψ sd.mpk.Bj
        (predOf nA (parse C)))) := by
  rw [run_simKeyP_store (ordT₀ N k) (ordO₀ N k) (parse C) (length_mem_insTW sd) (length_insTW sd)
    (fun j => enumIx_lt (α := JT N K k hk) j) (length_mem_insGW sd) (length_insGW sd)
    (fun i => i.isLt) hW hW' r ht hb hb' h1 h2 h86 h87 h88 h89 h90]
  exact congrArg _ (simKeyStoreW_sd sd C)

end AdvancedEncryption.RingBTVW.Prog
