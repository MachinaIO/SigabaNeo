import SigabaNeo.Lib.Machines.Compose.Plumbing
import SigabaNeo.Lib.Machines.Compose.Clocked

/-!
# Sequential composition of closed machines

`Machine.andThen M₁ M₂` runs `M₁` on its input under `M₁`'s clock, exactly as `Machine.run` does
(the output tape after `M₁.time` steps, whether or not `M₁` halted), then runs `M₂` on that word
under `M₂`'s clock:

* `Machine.run_andThen`: `(M₁.andThen M₂).run x = (M₁.run x).bind M₂.run`;
* `Machine.acceptProb_andThen`: `(M₁.andThen M₂).acceptProb μ = M₂.acceptProb (μ.bind M₁.run)`.

## The machine

Tapes (`k₁ + k₂ + 3`, `k_i = M_i.tapes`): the work tapes of `M₁`, a buffer, a clock, the work
tapes of `M₂`, a flag. With `T = M₁.time`, four phases (`MultiTapePTM.seq`):

1. `prepTM T` (`T + 5` steps): a unary clock of `T + 1` cells and the flag of a virtual input;
2. `M₁` with its output redirected to the buffer (`outputToTape`), under the clock (`withClock`,
   budget `T`): exactly `2 T + 1` steps, and its final configuration is that of `T` steps of `M₁`;
3. `rewTM` (`T + 3` steps): rewinds the buffer, consuming the rest of the clock, so that its
   running time does not depend on the output of `M₁` (of length at most `T`);
4. `M₂` reading its input from the buffer and the flag (`inputFromTape`).

The first three phases run a fixed number `4 T + 9` of steps, so the clock `4 T + 9 + M₂.time` of
the composed machine stops `M₂` after exactly `M₂.time` of its steps: no clock is needed for `M₂`.
-/

namespace SigabaNeo

open Cslib Turing MultiTapeMachine Compose

namespace AndThen

variable (k₁ k₂ : ℕ)

/-- The buffer. -/
def buf : Fin (k₁ + k₂ + 3) := ⟨k₁, by omega⟩
/-- The clock. -/
def clk : Fin (k₁ + k₂ + 3) := ⟨k₁ + 1, by omega⟩
/-- The flag. -/
def flag : Fin (k₁ + k₂ + 3) := ⟨k₁ + 2 + k₂, by omega⟩

/-- The tapes of the first phase (`M₁`, the buffer, the clock). -/
def eA : Fin (k₁ + 2) ↪ Fin (k₁ + k₂ + 3) := Fin.castLEEmb (by omega)

/-- The tapes of the preparation (the clock, the flag). -/
def eP : Fin 2 ↪ Fin (k₁ + k₂ + 3) :=
  ⟨![clk k₁ k₂, flag k₁ k₂], by
    intro a b h; fin_cases a <;> fin_cases b <;> simp_all [clk, flag, Fin.ext_iff] <;> omega⟩

/-- The tapes of the rewinding (the buffer, the clock). -/
def eR : Fin 2 ↪ Fin (k₁ + k₂ + 3) :=
  ⟨fun j => ⟨k₁ + j, by have := j.isLt; omega⟩, by
    intro a b h; have := congrArg Fin.val h; simp only at this; exact Fin.ext (by omega)⟩

/-- The tapes of the last phase (`M₂`, the buffer as its input, the flag). -/
def eBf (j : Fin (k₂ + 2)) : Fin (k₁ + k₂ + 3) :=
  if h : j.val < k₂ then ⟨k₁ + 2 + j, by omega⟩
  else if j.val = k₂ then ⟨k₁, by omega⟩ else ⟨k₁ + 2 + k₂, by omega⟩

theorem eBf_val (j : Fin (k₂ + 2)) :
    (eBf k₁ k₂ j).val = if j.val < k₂ then k₁ + 2 + j else if j.val = k₂ then k₁ else k₁ + 2 + k₂ := by
  unfold eBf; split_ifs <;> rfl

/-- The tapes of the last phase. -/
def eB : Fin (k₂ + 2) ↪ Fin (k₁ + k₂ + 3) :=
  ⟨eBf k₁ k₂, by
    intro a b h
    have := congrArg Fin.val h
    rw [eBf_val, eBf_val] at this
    have ha := a.isLt; have hb := b.isLt
    ext; split_ifs at this <;> omega⟩

end AndThen

open AndThen

variable (M₁ M₂ : Machine)

/-- The state type of the composed machine. -/
abbrev Machine.AndThenState : Type :=
  Fin (M₁.time + 5) ⊕ (Clock.Control (Fin M₁.states) ⊕ (Fin 3 ⊕ Fin M₂.states))

/-- The four phases. -/
def Machine.andThenP : MultiTapePTM (M₁.tapes + M₂.tapes + 3) Bool (Fin (M₁.time + 5)) (Fin 0) :=
  (prepTM M₁.time).extendTapes (eP M₁.tapes M₂.tapes)

def Machine.andThenA :
    MultiTapePTM (M₁.tapes + M₂.tapes + 3) Bool (Clock.Control (Fin M₁.states)) (Fin 0) :=
  (M₁.machine.outputToTape.withClock).extendTapes (eA M₁.tapes M₂.tapes)

def Machine.andThenR : MultiTapePTM (M₁.tapes + M₂.tapes + 3) Bool (Fin 3) (Fin 0) :=
  rewTM.extendTapes (eR M₁.tapes M₂.tapes)

def Machine.andThenB : MultiTapePTM (M₁.tapes + M₂.tapes + 3) Bool (Fin M₂.states) (Fin 0) :=
  M₂.machine.inputFromTape.extendTapes (eB M₁.tapes M₂.tapes)

/-- The composed fair-coin machine. -/
def Machine.andThenPTM :
    MultiTapePTM (M₁.tapes + M₂.tapes + 3) Bool (Machine.AndThenState M₁ M₂) (Fin 0) :=
  (M₁.andThenP M₂).seq ((M₁.andThenA M₂).seq ((M₁.andThenR M₂).seq (M₁.andThenB M₂)))

/-- The clock of the composed machine. -/
def Machine.andThenTime : ℕ := (M₁.time + 5) + ((2 * M₁.time + 1) + ((M₁.time + 3) + M₂.time))

/-- **Sequential composition**: run `M₁`, then `M₂` on its output. -/
noncomputable def Machine.andThen : Machine :=
  Machine.ofPTMOps (M₁.andThenPTM M₂) (M₁.andThenTime M₂)

/-! ### The configurations at the handoffs -/

namespace AndThen

variable {M₁ M₂} (x : List Bool)

/-- After the preparation. -/
def cP : Config (M₁.tapes + M₂.tapes + 3) Bool (Fin (M₁.time + 5)) (Fin 0) x :=
  (prepFin (x := x) M₁.time).embed (eP M₁.tapes M₂.tapes) (fun _ _ => none) (fun _ => 0)

theorem cP_w (l : Fin (M₁.tapes + M₂.tapes + 3)) :
    (cP (M₁ := M₁) (M₂ := M₂) x).tapes.workTapes l =
      if l.val = M₁.tapes + 1 then clkTape M₁.time
      else if l.val = M₁.tapes + 2 + M₂.tapes then flagTape else fun _ => none := by
  split_ifs with h1 h2
  · exact embed_workTapes_of _ _ _ _ (j := 0) (Fin.ext (by simp [eP, clk]; omega))
  · exact embed_workTapes_of _ _ _ _ (j := 1) (Fin.ext (by simp [eP, flag]; omega))
  · refine embed_workTapes_of_not _ _ _ _ (fun j hj => ?_)
    have := congrArg Fin.val hj
    fin_cases j <;> simp [eP, clk, flag] at this <;> omega

theorem cP_p (l : Fin (M₁.tapes + M₂.tapes + 3)) :
    (cP (M₁ := M₁) (M₂ := M₂) x).tapes.workTapePos l =
      if l.val = M₁.tapes + 1 then 1 - (M₁.time : ℤ) else 0 := by
  split_ifs with h1
  · exact embed_workTapePos_of _ _ _ _ (j := 0) (Fin.ext (by simp [eP, clk]; omega))
  · by_cases h2 : l.val = M₁.tapes + 2 + M₂.tapes
    · exact embed_workTapePos_of _ _ _ _ (j := 1) (Fin.ext (by simp [eP, flag]; omega))
    · refine embed_workTapePos_of_not _ _ _ _ (fun j hj => ?_)
      have := congrArg Fin.val hj
      fin_cases j <;> simp [eP, clk, flag] at this <;> omega

theorem tapeOfList_nil : tapeOfList ([] : List Bool) = fun _ => none := by
  funext p; cases p <;> rfl

/-- The start of the first phase. -/
def a0 : Config (M₁.tapes + M₂.tapes + 3) Bool (Clock.Control (Fin M₁.states)) (Fin 0) x :=
  (AuxiliaryTape.config (OutputToTape.config (M₁.machine.initialConfig x)) (clkTape M₁.time)
    (1 - M₁.time) false).embed (eA M₁.tapes M₂.tapes) (cP (M₁ := M₁) (M₂ := M₂) x).tapes.workTapes
    (cP (M₁ := M₁) (M₂ := M₂) x).tapes.workTapePos

theorem start_A : Sequential.start (M₁.andThenA M₂) (cP x) = a0 (M₁ := M₁) (M₂ := M₂) x := by
  refine embed_eq _ _ _ rfl rfl rfl (fun j => ?_) (fun j => ?_) <;>
  · refine Fin.lastCases ?_ (fun j => Fin.lastCases ?_ (fun i => ?_) j) j
    all_goals
      try have hi := i.isLt
      simp [Sequential.start, Cfg.withState, cP_w, cP_p, eA, AuxiliaryTape.config,
        OutputToTape.config, MultiTapeTM.outCfg, MultiTapeMachine.initialConfig, tapeOfList_nil]
      try omega
    all_goals rw [if_neg (by omega)]; try rw [if_neg (by omega)]

/-- The end of the first phase, from a final configuration `f` of `M₁`. -/
def aF (f : Config M₁.tapes Bool (Fin M₁.states) (Fin 0) x) :
    Config (M₁.tapes + M₂.tapes + 3) Bool (Clock.Control (Fin M₁.states)) (Fin 0) x :=
  (AuxiliaryTape.stopped (OutputToTape.config f) (clkTape M₁.time)
    (1 - M₁.time + M₁.time)).embed (eA M₁.tapes M₂.tapes)
    (cP (M₁ := M₁) (M₂ := M₂) x).tapes.workTapes (cP (M₁ := M₁) (M₂ := M₂) x).tapes.workTapePos

end AndThen

end SigabaNeo
