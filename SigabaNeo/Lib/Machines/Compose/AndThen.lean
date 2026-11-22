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

@[simp] theorem eA_val (j : Fin (k₁ + 2)) : (eA k₁ k₂ j).val = j.val := rfl
@[simp] theorem eR_val (j : Fin 2) : (eR k₁ k₂ j).val = k₁ + j.val := rfl
@[simp] theorem eB_val (j : Fin (k₂ + 2)) :
    (eB k₁ k₂ j).val = if j.val < k₂ then k₁ + 2 + j else if j.val = k₂ then k₁ else k₁ + 2 + k₂ :=
  eBf_val k₁ k₂ j

end AndThen

open AndThen

@[simp] theorem Sequential.start_workTapes {k : ℕ} {S₀ S₁ : Type} {x : List Bool}
    (M : MultiTapePTM k Bool S₁ (Fin 0)) (c : Config k Bool S₀ (Fin 0) x) :
    (Sequential.start M c).tapes.workTapes = c.tapes.workTapes := rfl

@[simp] theorem Sequential.start_workTapePos {k : ℕ} {S₀ S₁ : Type} {x : List Bool}
    (M : MultiTapePTM k Bool S₁ (Fin 0)) (c : Config k Bool S₀ (Fin 0) x) :
    (Sequential.start M c).tapes.workTapePos = c.tapes.workTapePos := rfl

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

theorem clk_budget (T : ℕ) (i : ℕ) (hi : i < T) : clkTape T (1 - T + i) = some true := by
  simp only [clkW]; rw [if_pos (by omega)]

theorem clk_stop (T : ℕ) : clkTape T (1 - T + T) ≠ some true := by
  simp only [clkW]; rw [if_neg (by omega)]; simp

/-- **The first phase**: the law of `M₁` after `M₁.time` steps, in exactly `2 M₁.time + 1`
steps. -/
theorem law_A : law (M₁.andThenA M₂) (2 * M₁.time + 1) (a0 x) =
    (law M₁.machine M₁.time (M₁.machine.initialConfig x)).map (aF (M₂ := M₂) x) := by
  rw [a0, Machine.andThenA, law_extendTapes, law_withClock _ _ _ _ _ (clk_budget M₁.time)
    (clk_stop M₁.time), law_outputToTape, PMF.map_comp, PMF.map_comp]
  rfl

theorem exact_A : Exact (M₁.andThenA M₂) (a0 x) (2 * M₁.time + 1) :=
  exact_extendTapes _ _ _ _ _ _
    (exact_withClock _ _ _ _ _ (clk_budget M₁.time) (clk_stop M₁.time))

theorem aF_w (f : Config M₁.tapes Bool (Fin M₁.states) (Fin 0) x)
    (l : Fin (M₁.tapes + M₂.tapes + 3)) (hl : M₁.tapes + 2 ≤ l.val) :
    (aF (M₂ := M₂) x f).tapes.workTapes l = (cP (M₁ := M₁) (M₂ := M₂) x).tapes.workTapes l := by
  refine embed_workTapes_of_not _ _ _ _ (fun j hj => ?_)
  have := congrArg Fin.val hj
  have := j.isLt
  simp only [eA_val] at *; omega

theorem aF_p (f : Config M₁.tapes Bool (Fin M₁.states) (Fin 0) x)
    (l : Fin (M₁.tapes + M₂.tapes + 3)) (hl : M₁.tapes + 2 ≤ l.val) :
    (aF (M₂ := M₂) x f).tapes.workTapePos l = (cP (M₁ := M₁) (M₂ := M₂) x).tapes.workTapePos l := by
  refine embed_workTapePos_of_not _ _ _ _ (fun j hj => ?_)
  have := congrArg Fin.val hj
  have := j.isLt
  simp only [eA_val] at *; omega

/-- The start of the rewinding. -/
def r0 (f : Config M₁.tapes Bool (Fin M₁.states) (Fin 0) x) :
    Config (M₁.tapes + M₂.tapes + 3) Bool (Fin 3) (Fin 0) x :=
  (rewInit M₁.time f.tapes.output f.tapes.inputPos []).embed (eR M₁.tapes M₂.tapes)
    (aF (M₂ := M₂) x f).tapes.workTapes (aF (M₂ := M₂) x f).tapes.workTapePos

theorem start_R (f : Config M₁.tapes Bool (Fin M₁.states) (Fin 0) x) :
    Sequential.start (M₁.andThenR M₂) (aF x f) = r0 (M₂ := M₂) x f := by
  have h0 : eA M₁.tapes M₂.tapes (Fin.last M₁.tapes).castSucc = eR M₁.tapes M₂.tapes 0 :=
    Fin.ext (by simp)
  have h1 : eA M₁.tapes M₂.tapes (Fin.last (M₁.tapes + 1)) = eR M₁.tapes M₂.tapes 1 :=
    Fin.ext (by simp)
  refine embed_eq _ _ _ rfl rfl rfl (fun j => ?_) (fun j => ?_) <;>
    rcases (show j = 0 ∨ j = 1 by fin_cases j <;> simp) with rfl | rfl <;>
    simp only [Sequential.start_workTapes, Sequential.start_workTapePos] <;> unfold aF
  · rw [embed_workTapes_of _ _ _ _ h0]
    simp [AuxiliaryTape.stopped, OutputToTape.config, MultiTapeTM.outCfg, rewInit, pc]
  · rw [embed_workTapes_of _ _ _ _ h1]
    simp [AuxiliaryTape.stopped, rewInit, pc]
  · rw [embed_workTapePos_of _ _ _ _ h0]
    simp [AuxiliaryTape.stopped, OutputToTape.config, MultiTapeTM.outCfg, rewInit, pc]
  · rw [embed_workTapePos_of _ _ _ _ h1]
    simp [AuxiliaryTape.stopped, rewInit, pc]

/-- The end of the rewinding. -/
def rF (f : Config M₁.tapes Bool (Fin M₁.states) (Fin 0) x) :
    Config (M₁.tapes + M₂.tapes + 3) Bool (Fin 3) (Fin 0) x :=
  (rewFin M₁.time f.tapes.output f.tapes.inputPos []).embed (eR M₁.tapes M₂.tapes)
    (aF (M₂ := M₂) x f).tapes.workTapes (aF (M₂ := M₂) x f).tapes.workTapePos

theorem runs_R (f : Config M₁.tapes Bool (Fin M₁.states) (Fin 0) x)
    (hf : f.tapes.output.length ≤ M₁.time) :
    Runs (M₁.andThenR M₂) (r0 x f) (M₁.time + 3) (rF x f) :=
  runs_extendTapes _ _ _ (runs_rew _ _ _ _ hf)

/-- The start of the last phase. -/
def b0 (f : Config M₁.tapes Bool (Fin M₁.states) (Fin 0) x) :
    Config (M₁.tapes + M₂.tapes + 3) Bool (Fin M₂.states) (Fin 0) x :=
  (InputFromTape.config true (M₂.machine.initialConfig f.tapes.output) x f.tapes.inputPos).embed
    (eB M₁.tapes M₂.tapes) (rF (M₂ := M₂) x f).tapes.workTapes (rF (M₂ := M₂) x f).tapes.workTapePos

theorem rF_w (f : Config M₁.tapes Bool (Fin M₁.states) (Fin 0) x)
    (l : Fin (M₁.tapes + M₂.tapes + 3)) (hl : M₁.tapes + 2 ≤ l.val) :
    (rF (M₂ := M₂) x f).tapes.workTapes l = (cP (M₁ := M₁) (M₂ := M₂) x).tapes.workTapes l := by
  refine (embed_workTapes_of_not _ _ _ _ (fun j hj => ?_)).trans (aF_w x f l hl)
  have := congrArg Fin.val hj
  have := j.isLt
  simp only [eR_val] at *; omega

theorem rF_p (f : Config M₁.tapes Bool (Fin M₁.states) (Fin 0) x)
    (l : Fin (M₁.tapes + M₂.tapes + 3)) (hl : M₁.tapes + 2 ≤ l.val) :
    (rF (M₂ := M₂) x f).tapes.workTapePos l = (cP (M₁ := M₁) (M₂ := M₂) x).tapes.workTapePos l := by
  refine (embed_workTapePos_of_not _ _ _ _ (fun j hj => ?_)).trans (aF_p x f l hl)
  have := congrArg Fin.val hj
  have := j.isLt
  simp only [eR_val] at *; omega

theorem start_B (f : Config M₁.tapes Bool (Fin M₁.states) (Fin 0) x) :
    Sequential.start (M₁.andThenB M₂) (rF x f) = b0 (M₂ := M₂) x f := by
  have hv : eB M₁.tapes M₂.tapes (Fin.natAdd M₂.tapes 0) = eR M₁.tapes M₂.tapes 0 :=
    Fin.ext (by simp)
  have hf : (eB M₁.tapes M₂.tapes (Fin.natAdd M₂.tapes 1)).val = M₁.tapes + 2 + M₂.tapes := by
    simp
  have hl : ∀ i : Fin M₂.tapes,
      (eB M₁.tapes M₂.tapes (Fin.castAdd 2 i)).val = M₁.tapes + 2 + i := fun i => by
    simp [i.isLt]
  refine embed_eq _ _ _ rfl rfl rfl (fun j => ?_) (fun j => ?_) <;>
    simp only [Sequential.start_workTapes, Sequential.start_workTapePos] <;>
    induction j using Fin.addCases with
    | left i =>
      have hi := i.isLt
      have h := hl i
      first
      | (rw [rF_w x f (eB M₁.tapes M₂.tapes (Fin.castAdd 2 i)) (by omega), cP_w,
          if_neg (by omega), if_neg (by omega)]
         simp [InputFromTape.config, MultiTapeTM.inCfg, MultiTapeMachine.initialConfig])
      | (rw [rF_p x f (eB M₁.tapes M₂.tapes (Fin.castAdd 2 i)) (by omega), cP_p, if_neg (by omega)]
         simp [InputFromTape.config, MultiTapeTM.inCfg, MultiTapeMachine.initialConfig])
    | right i =>
      rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
      · first
        | (unfold rF; rw [embed_workTapes_of _ _ _ _ hv.symm]; simp [rewFin, pc, InputFromTape.config])
        | (unfold rF; rw [embed_workTapePos_of _ _ _ _ hv.symm]
           simp [rewFin, pc, InputFromTape.config, MultiTapeMachine.initialConfig])
      · first
        | (rw [rF_w x f (eB M₁.tapes M₂.tapes (Fin.natAdd M₂.tapes 1)) (by omega), cP_w,
            if_neg (by omega), if_pos hf]
           simp [InputFromTape.config, flagTape])
        | (rw [rF_p x f (eB M₁.tapes M₂.tapes (Fin.natAdd M₂.tapes 1)) (by omega), cP_p,
            if_neg (by omega)]
           simp [InputFromTape.config, MultiTapeMachine.initialConfig])

end AndThen

end SigabaNeo
