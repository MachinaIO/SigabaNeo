import SigabaNeoStd.Lattices.Homomorphic.SLP
import Mathlib.Tactic.Ring

/-!
# Register programs of NAND gates

A register program (`RP ι W`) is a list of NAND instructions `dst := NAND(a, b)` on `W` registers;
a source is an input (indexed by `ι`), the constant `1`, or a register (`Src`). It describes a
straight-line program whose gates are not all kept: a register holds the last value written to it.

`RP.run` runs it on any type of values, every register starting at the value of `1`.
`RP.toSLP` unfolds it into a straight-line program (instruction `t` is gate `t`) together with the
wire each register holds at the end (the gate last written to it, `Wire.one` if none).
**`RP.run_eq_valueOf`**: running the registers is reading the unfolded program at those wires, for
every value type; so one lemma gives the Boolean value, the depth, the homomorphic values and the
noise bounds of the unfolding.

`RP.rpW`: the word of a program over `Fin n` inputs, as a machine reads it: three unary slot words
of `S` bits per instruction (destination, left, right), slot `0` the constant, `1 … n` the inputs,
`n + 1 + r` register `r` (the operand layout of `GateListLayout.gsW`, with a destination added;
`unary S j` is `Tape.unaryW S j`).
-/

namespace SigabaNeo.Lattices

/-- A source: an input, the constant `1`, or a register. -/
inductive Src (ι : Type*) (W : ℕ) where
  /-- An input. -/
  | input (i : ι)
  /-- The constant `1`. -/
  | one
  /-- A register. -/
  | reg (r : Fin W)

/-- `dst := NAND(a, b)`. -/
structure Instr (ι : Type*) (W : ℕ) where
  /-- The register written. -/
  dst : Fin W
  /-- The left source. -/
  a : Src ι W
  /-- The right source. -/
  b : Src ι W

/-- A register program: NAND instructions in order. -/
abbrev RP (ι : Type*) (W : ℕ) := List (Instr ι W)

namespace Src

variable {ι α : Type*} {W : ℕ}

/-- The value of a source, from the inputs, the value of `1` and the registers. -/
def val (inp : ι → α) (one : α) (regs : Fin W → α) : Src ι W → α
  | .input i => inp i
  | .one => one
  | .reg r => regs r

/-- The wire of a source, from the wires the registers hold. -/
def wire (m : Fin W → Wire ι) : Src ι W → Wire ι
  | .input i => .input i
  | .one => .one
  | .reg r => m r

end Src

namespace RP

variable {ι α : Type*} {W : ℕ}

/-- Run on any type of values. -/
def run (inp : ι → α) (one : α) (step : α → α → α) : RP ι W → (Fin W → α) → (Fin W → α)
  | [], regs => regs
  | ins :: rp, regs =>
    run inp one step rp
      (Function.update regs ins.dst (step (ins.a.val inp one regs) (ins.b.val inp one regs)))

theorem run_nil (inp : ι → α) (one : α) (step : α → α → α) (regs : Fin W → α) :
    run inp one step ([] : RP ι W) regs = regs := rfl

theorem run_cons (inp : ι → α) (one : α) (step : α → α → α) (ins : Instr ι W) (rp : RP ι W)
    (regs : Fin W → α) :
    run inp one step (ins :: rp) regs = run inp one step rp
      (Function.update regs ins.dst (step (ins.a.val inp one regs) (ins.b.val inp one regs))) :=
  rfl

theorem run_append (inp : ι → α) (one : α) (step : α → α → α) (rp rp' : RP ι W)
    (regs : Fin W → α) :
    run inp one step (rp ++ rp') regs = run inp one step rp' (run inp one step rp regs) := by
  induction rp generalizing regs with
  | nil => rfl
  | cons ins rp ih => exact ih _

/-- Unfold the instructions after a program `p` already built, the registers holding `m`. -/
def toSLPAux : RP ι W → SLP ι × (Fin W → Wire ι) → SLP ι × (Fin W → Wire ι)
  | [], s => s
  | ins :: rp, (p, m) =>
    toSLPAux rp (p ++ [⟨ins.a.wire m, ins.b.wire m⟩], Function.update m ins.dst (.gate p.length))

/-- **The unfolding**: instruction `t` is gate `t`; a register is the wire of the last gate written
to it (`Wire.one` if none). -/
def toSLP (rp : RP ι W) : SLP ι × (Fin W → Wire ι) := toSLPAux rp ([], fun _ => .one)

theorem length_toSLPAux (rp : RP ι W) (s : SLP ι × (Fin W → Wire ι)) :
    (toSLPAux rp s).1.length = s.1.length + rp.length := by
  induction rp generalizing s with
  | nil => simp [toSLPAux]
  | cons ins rp ih =>
    obtain ⟨p, m⟩ := s
    simp only [toSLPAux, ih, List.length_append, List.length_cons, List.length_nil]
    omega

/-- The unfolding has one gate per instruction. -/
theorem length_toSLP (rp : RP ι W) : (toSLP rp).1.length = rp.length := by
  simp [toSLP, length_toSLPAux]

/-- **Independent instructions**: `d m := NAND(a m, a m)` for `m < k`, where no `a m` reads a
register written. -/
theorem run_map_dup (inp : ι → α) (one : α) (step : α → α → α) (d : ℕ → Fin W) (a : ℕ → Src ι W)
    (P : Fin W → Prop) (ha : ∀ m r, a m = .reg r → P r) (k : ℕ) (hd : ∀ m, m < k → ¬ P (d m))
    (hinj : ∀ m m', m < k → m' < k → d m = d m' → m = m') (R : Fin W → α) :
    (∀ m, m < k → run inp one step ((List.range k).map fun m => (⟨d m, a m, a m⟩ : Instr ι W)) R
        (d m) = step ((a m).val inp one R) ((a m).val inp one R)) ∧
      ∀ r, (∀ m, m < k → r ≠ d m) →
        run inp one step ((List.range k).map fun m => (⟨d m, a m, a m⟩ : Instr ι W)) R r = R r := by
  have hval : ∀ (R' : Fin W → α) m, (∀ r, P r → R' r = R r) →
      (a m).val inp one R' = (a m).val inp one R := by
    intro R' m h
    cases e : a m with
    | input i => rfl
    | one => rfl
    | reg r => exact h r (ha m r e)
  induction k with
  | zero => exact ⟨fun m h => absurd h (Nat.not_lt_zero _), fun r _ => rfl⟩
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun m h => hd m (by omega)) (fun m m' h1 h2 => hinj m m' (by omega) (by omega))
    rw [List.range_succ, List.map_append, run_append]
    simp only [List.map_cons, List.map_nil, run_cons, run_nil]
    have hk : ∀ r, P r → run inp one step ((List.range k).map fun m =>
        (⟨d m, a m, a m⟩ : Instr ι W)) R r = R r :=
      fun r hr => ih2 r (fun m h e => hd m (by omega) (e ▸ hr))
    refine ⟨fun m hm => ?_, fun r hr => ?_⟩
    · by_cases e : m = k
      · subst e; rw [Function.update_self, hval _ _ hk]
      · rw [Function.update_of_ne (fun h => e (hinj m k (by omega) (by omega) h)), ih1 m (by omega)]
    · rw [Function.update_of_ne (hr k (by omega)), ih2 r (fun m h => hr m (by omega))]

/-! ### Running is reading the unfolding -/

section Correct

variable (inp : ι → α) (one : α) (step : α → α → α)

theorem SLP_run_append (p q : SLP ι) (acc : List α) :
    SLP.run inp one step (p ++ q) acc = SLP.run inp one step q (SLP.run inp one step p acc) := by
  induction p generalizing acc with
  | nil => rfl
  | cons g p ih => exact ih _

theorem SLP_length_run (p : SLP ι) (acc : List α) :
    (SLP.run inp one step p acc).length = acc.length + p.length := by
  induction p generalizing acc with
  | nil => simp [SLP.run]
  | cons g p ih =>
    simp only [SLP.run, ih, List.length_append, List.length_cons, List.length_nil]
    omega

/-- A wire whose gate, if any, is among the first `n`. -/
def WireLt (n : ℕ) : Wire ι → Prop
  | .gate j => j < n
  | _ => True

theorem wireVal_append_of_lt (vals : List α) (x : α) (w : Wire ι) (hw : WireLt vals.length w) :
    SLP.wireVal inp one (vals ++ [x]) w = SLP.wireVal inp one vals w := by
  cases w with
  | input i => rfl
  | one => rfl
  | gate j =>
    simp only [WireLt] at hw
    simp only [SLP.wireVal]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hw,
      List.getElem_append_left hw]

/-- The invariant: the registers are the values of their wires, which point into the program. -/
def Inv (p : SLP ι) (m : Fin W → Wire ι) (regs : Fin W → α) : Prop :=
  (∀ r, regs r = SLP.wireVal inp one (SLP.values inp one step p) (m r)) ∧
    ∀ r, WireLt p.length (m r)

theorem inv_toSLPAux (rp : RP ι W) (p : SLP ι) (m : Fin W → Wire ι) (regs : Fin W → α)
    (h : Inv inp one step p m regs) :
    Inv inp one step (toSLPAux rp (p, m)).1 (toSLPAux rp (p, m)).2 (run inp one step rp regs) := by
  induction rp generalizing p m regs with
  | nil => exact h
  | cons ins rp ih =>
    obtain ⟨hv, hl⟩ := h
    apply ih
    have hlen : (SLP.values inp one step p).length = p.length := by
      simp [SLP.values, SLP_length_run]
    have hsrc : ∀ s : Src ι W, s.val inp one regs =
        SLP.wireVal inp one (SLP.values inp one step p) (s.wire m) := by
      intro s; cases s with
      | input i => rfl
      | one => rfl
      | reg r => exact hv r
    have hsl : ∀ s : Src ι W, WireLt p.length (s.wire m) := by
      intro s; cases s with
      | input i => trivial
      | one => trivial
      | reg r => exact hl r
    have hvals : SLP.values inp one step (p ++ [⟨ins.a.wire m, ins.b.wire m⟩]) =
        SLP.values inp one step p ++ [step (ins.a.val inp one regs) (ins.b.val inp one regs)] := by
      simp only [SLP.values, SLP_run_append, SLP.run]
      rw [hsrc, hsrc]; rfl
    refine ⟨fun r => ?_, fun r => ?_⟩
    · rw [hvals]
      by_cases hr : r = ins.dst
      · subst hr
        simp only [Function.update_self, SLP.wireVal]
        rw [List.getD_eq_getElem _ _ (by simp [hlen])]
        simp [hlen]
      · rw [Function.update_of_ne hr, Function.update_of_ne hr, hv r,
          wireVal_append_of_lt _ _ _ _ _ (hlen ▸ hl r)]
    · by_cases hr : r = ins.dst
      · subst hr; simp [WireLt]
      · rw [Function.update_of_ne hr]
        have := hl r
        revert this
        cases m r <;> simp [WireLt]; omega

/-- **Running the registers is reading the unfolding**, for every value type. -/
theorem run_eq_valueOf (rp : RP ι W) (r : Fin W) :
    run inp one step rp (fun _ => one) r =
      SLP.valueOf inp one step (toSLP rp).1 ((toSLP rp).2 r) :=
  (inv_toSLPAux inp one step rp [] (fun _ => .one) (fun _ => one)
    ⟨fun _ => rfl, fun _ => trivial⟩).1 r

/-- The predicate of a register program read at register `r`: its unfolding and the wire of
`r`. Statements about the unfolding of a concrete program go through `RP.pred` and
`valueOf_pred`, so that the unfolding is never computed. -/
def pred (rp : RP ι W) (r : Fin W) : SLP ι × Wire ι := ((toSLP rp).1, (toSLP rp).2 r)

/-- **Reading the predicate is running the registers.** -/
theorem valueOf_pred (rp : RP ι W) (r : Fin W) :
    SLP.valueOf inp one step (pred rp r).1 (pred rp r).2 = run inp one step rp (fun _ => one) r :=
  (run_eq_valueOf inp one step rp r).symm

theorem length_pred (rp : RP ι W) (r : Fin W) : (pred rp r).1.length = rp.length :=
  length_toSLP rp

end Correct

/-! ### The word of a program -/

/-- `j` in unary on `S` bits: `j` ones, then zeros (`Tape.unaryW S j`). -/
def unary (S j : ℕ) : List Bool := List.replicate j true ++ List.replicate (S - j) false

/-- The slot of a source: `0` the constant, `1 … n` the inputs, `n + 1 + r` the register `r`. -/
def _root_.SigabaNeo.Lattices.Src.slot {n : ℕ} : Src (Fin n) W → ℕ
  | .one => 0
  | .input i => i.val + 1
  | .reg r => n + 1 + r.val

/-- The slot of a register. -/
def regSlot (n : ℕ) (r : Fin W) : ℕ := n + 1 + r.val

/-- **The word of a register program**: per instruction, the slots of its destination and of its
two sources, each in unary on `S` bits. -/
def rpW {n : ℕ} (S : ℕ) (rp : RP (Fin n) W) : List Bool :=
  rp.flatMap fun ins =>
    unary S (regSlot n ins.dst) ++ unary S (Src.slot ins.a) ++ unary S (Src.slot ins.b)

theorem rpW_nil {n : ℕ} (S : ℕ) : rpW S ([] : RP (Fin n) W) = [] := rfl

theorem rpW_cons {n : ℕ} (S : ℕ) (ins : Instr (Fin n) W) (rp : RP (Fin n) W) :
    rpW S (ins :: rp) = unary S (regSlot n ins.dst) ++ unary S (Src.slot ins.a) ++
      unary S (Src.slot ins.b) ++ rpW S rp := rfl

theorem rpW_append {n : ℕ} (S : ℕ) (rp rp' : RP (Fin n) W) :
    rpW S (rp ++ rp') = rpW S rp ++ rpW S rp' := by
  simp [rpW]

theorem length_unary {S j : ℕ} (h : j ≤ S) : (unary S j).length = S := by
  simp [unary]; omega

theorem _root_.SigabaNeo.Lattices.Src.slot_lt {n : ℕ} (s : Src (Fin n) W) : s.slot < n + 1 + W := by
  cases s with
  | one => simp [Src.slot]
  | input i => simp only [Src.slot]; omega
  | reg r => simp only [Src.slot]; omega

/-- The slots of a program are below `n + 1 + W`. -/
theorem length_rpW {n : ℕ} {S : ℕ} (hS : n + 1 + W ≤ S) (rp : RP (Fin n) W) :
    (rpW S rp).length = rp.length * (3 * S) := by
  induction rp with
  | nil => simp [rpW]
  | cons ins rp ih =>
    rw [rpW_cons]
    simp only [List.length_append, ih, List.length_cons]
    rw [length_unary (by simp only [regSlot]; have := ins.dst.isLt; omega),
      length_unary ((Src.slot_lt _).le.trans hS), length_unary ((Src.slot_lt _).le.trans hS)]
    ring

end RP

end SigabaNeo.Lattices
