import SigabaNeo.Lib.Machines.Compose.AndThenLin
import SigabaNeo.Lib.Machines.Compose.Shift
import SigabaNeo.Lib.Machines.Compose.Guard

/-!
# Guarded sequential composition

`Machine.andThenGuard M₁ M₂` runs `M₁`; if its output is `true :: w` it runs `M₂` on `w`, and
otherwise (an empty output, or one starting with `false`) it outputs the empty word:

* `Machine.run_andThenGuard`: `(M₁.andThenGuard M₂).run x = (M₁.run x).bind (guardK M₂)`, where
  `guardK M₂ (true :: w) = M₂.run w` and `guardK M₂ y = PMF.pure []` otherwise;
* `Machine.acceptProb_andThenGuard`.

## The machine

It is `Machine.andThenLin M₁ M₂` with a fifth phase between the rewinding and `M₂`: the guard
(`guardTM`) on the buffer and the flag. On `true :: w` it erases the leading `true` and moves the
flag mark and both heads one cell to the right, in exactly `3` steps: the buffer and the flag are
then those `M₂.machine.inputFromTape` starts from on `w`, translated by one cell, and a translation
of tapes commutes with running (`Compose.law_shift`). The first four phases thus run a fixed number
of steps, and the clock stops `M₂` after exactly `M₂.time` of its steps. Otherwise the guard enters
a state it never leaves, and the output tape, never written by the first phases, stays empty.
-/

namespace SigabaNeo

open Cslib Turing MultiTapeMachine Compose _root_.SigabaNeo.AndThen DigitPrep

namespace AndThen

variable (k₁ k₂ : ℕ)

/-- The tapes of the guard (the buffer, the flag). -/
def eG : Fin 2 ↪ Fin (k₁ + k₂ + 3) :=
  ⟨![buf k₁ k₂, flag k₁ k₂], by
    intro a b h; fin_cases a <;> fin_cases b <;> simp_all [buf, flag, Fin.ext_iff] <;> omega⟩

/-- The translation of the tapes of the last phase: by one cell for the buffer and the flag. -/
def dB (j : Fin (k₂ + 2)) : ℤ := if j.val < k₂ then 0 else 1

end AndThen

/-- The guard on the outcome of the first machine: `M₂` on `w` for `true :: w`, the empty word
otherwise. -/
noncomputable def Machine.guardK (M₂ : Machine) : List Bool → PMF (List Bool)
  | true :: w => M₂.run w
  | _ => PMF.pure []

@[simp] theorem Machine.guardK_true (M₂ : Machine) (w : List Bool) :
    M₂.guardK (true :: w) = M₂.run w := rfl

@[simp] theorem Machine.guardK_false (M₂ : Machine) (w : List Bool) :
    M₂.guardK (false :: w) = PMF.pure [] := rfl

@[simp] theorem Machine.guardK_nil (M₂ : Machine) : M₂.guardK [] = PMF.pure [] := rfl

theorem Machine.guardK_of_head (M₂ : Machine) (y : List Bool) (hy : y.head? ≠ some true) :
    M₂.guardK y = PMF.pure [] := by
  rcases y with _ | ⟨_ | _, _⟩ <;> simp_all

variable (M₁ M₂ : Machine)

/-- The guard, on the tapes of the composition. -/
def Machine.andThenG : MultiTapePTM (M₁.tapes + M₂.tapes + 3) Bool (Fin 4) (Fin 0) :=
  guardTM.extendTapes (eG M₁.tapes M₂.tapes)

/-- The state type of the guarded composition. -/
abbrev Machine.AndThenGuardState : Type :=
  DState M₁.tapes M₁.time ⊕ (Clock.Control (Fin M₁.states) ⊕ (Fin 3 ⊕ (Fin 4 ⊕ Fin M₂.states)))

/-- The guarded composed fair-coin machine. -/
def Machine.andThenGuardPTM :
    MultiTapePTM (M₁.tapes + M₂.tapes + 3) Bool (Machine.AndThenGuardState M₁ M₂) (Fin 0) :=
  (M₁.andThenLinP M₂).seq ((M₁.andThenA M₂).seq ((M₁.andThenR M₂).seq
    ((M₁.andThenG M₂).seq (M₁.andThenB M₂))))

/-- The clock of the guarded composition. -/
noncomputable def Machine.andThenGuardTime : ℕ :=
  dprepTime M₁.tapes M₁.time + ((2 * M₁.time + 1) + ((M₁.time + 3) + (3 + M₂.time)))

/-- **Guarded sequential composition**: run `M₁`; on an output `true :: w` run `M₂` on `w`,
otherwise output the empty word. -/
noncomputable def Machine.andThenGuard : Machine :=
  Machine.ofPTMOps (M₁.andThenGuardPTM M₂) (M₁.andThenGuardTime M₂)

namespace AndThen

variable {M₁ M₂} (x : List Bool)

/-- The start of the guard. -/
def g0 (f : Config M₁.tapes Bool (Fin M₁.states) (Fin 0) x) :
    Config (M₁.tapes + M₂.tapes + 3) Bool (Fin 4) (Fin 0) x :=
  (pc (some 0) f.tapes.inputPos [] (tapeOfList f.tapes.output) flagTape 0 0).embed
    (eG M₁.tapes M₂.tapes) (rF (M₂ := M₂) x f).tapes.workTapes (rF (M₂ := M₂) x f).tapes.workTapePos

theorem start_G (f : Config M₁.tapes Bool (Fin M₁.states) (Fin 0) x) :
    Sequential.start (M₁.andThenG M₂) (rF x f) = g0 (M₂ := M₂) x f := by
  have h0 : eG M₁.tapes M₂.tapes 0 = eR M₁.tapes M₂.tapes 0 := Fin.ext (by simp [eG, buf])
  have h1 : (eG M₁.tapes M₂.tapes 1).val = M₁.tapes + 2 + M₂.tapes := by simp [eG, flag]
  refine embed_eq _ _ _ rfl rfl rfl (fun j => ?_) (fun j => ?_) <;>
    rcases (show j = 0 ∨ j = 1 by fin_cases j <;> simp) with rfl | rfl <;>
    simp only [Sequential.start_workTapes, Sequential.start_workTapePos]
  · rw [h0]; unfold rF; rw [embed_workTapes_of _ _ _ _ rfl]; simp [rewFin, pc]
  · rw [rF_w x f _ (by omega), cP_w, if_neg (by omega), if_pos h1]; rfl
  · rw [h0]; unfold rF; rw [embed_workTapePos_of _ _ _ _ rfl]; simp [rewFin, pc]
  · rw [rF_p x f _ (by omega), cP_p, if_neg (by omega)]; rfl

/-- The end of the guard on `true :: w`. -/
def gF (f : Config M₁.tapes Bool (Fin M₁.states) (Fin 0) x) (w : List Bool) :
    Config (M₁.tapes + M₂.tapes + 3) Bool (Fin 4) (Fin 0) x :=
  (guardFin w f.tapes.inputPos []).embed (eG M₁.tapes M₂.tapes) (rF (M₂ := M₂) x f).tapes.workTapes
    (rF (M₂ := M₂) x f).tapes.workTapePos

theorem runs_G (f : Config M₁.tapes Bool (Fin M₁.states) (Fin 0) x) (w : List Bool)
    (hy : f.tapes.output = true :: w) :
    Runs (M₁.andThenG M₂) (g0 x f) 3 (gF x f w) := by
  unfold g0 gF Machine.andThenG
  rw [hy]
  exact runs_extendTapes _ _ _ (runs_guard w _ _)

theorem law_G_rej (f : Config M₁.tapes Bool (Fin M₁.states) (Fin 0) x)
    (hy : f.tapes.output.head? ≠ some true) (n : ℕ) :
    law (M₁.andThenG M₂) (n + 1) (g0 x f) =
      PMF.pure ((pc (some 3) f.tapes.inputPos [] (tapeOfList f.tapes.output) flagTape 0 0).embed
        (eG M₁.tapes M₂.tapes) (rF (M₂ := M₂) x f).tapes.workTapes
        (rF (M₂ := M₂) x f).tapes.workTapePos) := by
  unfold g0 Machine.andThenG
  rw [law_extendTapes, law_guard_rej _ hy, PMF.pure_map]

/-- The start of the last phase of the guarded composition. -/
def b0g (f : Config M₁.tapes Bool (Fin M₁.states) (Fin 0) x) (w : List Bool) :
    Config (M₁.tapes + M₂.tapes + 3) Bool (Fin M₂.states) (Fin 0) x :=
  (shiftCfg (dB M₂.tapes) (InputFromTape.config true (M₂.machine.initialConfig w) x
    f.tapes.inputPos)).embed (eB M₁.tapes M₂.tapes) (gF (M₂ := M₂) x f w).tapes.workTapes
    (gF (M₂ := M₂) x f w).tapes.workTapePos

theorem start_Bg (f : Config M₁.tapes Bool (Fin M₁.states) (Fin 0) x) (w : List Bool) :
    Sequential.start (M₁.andThenB M₂) (gF x f w) = b0g (M₂ := M₂) x f w := by
  have hv : eB M₁.tapes M₂.tapes (Fin.natAdd M₂.tapes 0) = eG M₁.tapes M₂.tapes 0 :=
    Fin.ext (by simp [eG, buf])
  have hf : eB M₁.tapes M₂.tapes (Fin.natAdd M₂.tapes 1) = eG M₁.tapes M₂.tapes 1 :=
    Fin.ext (by simp [eG, flag])
  have hl : ∀ i : Fin M₂.tapes,
      (eB M₁.tapes M₂.tapes (Fin.castAdd 2 i)).val = M₁.tapes + 2 + i := fun i => by
    simp [i.isLt]
  have hng : ∀ i : Fin M₂.tapes, ∀ j, eG M₁.tapes M₂.tapes j ≠ eB M₁.tapes M₂.tapes (Fin.castAdd 2 i) :=
    fun i j hj => by
      have := congrArg Fin.val hj
      rw [hl i] at this
      have := i.isLt
      fin_cases j <;> simp [eG, buf, flag] at this <;> omega
  refine embed_eq _ _ _ rfl rfl rfl (fun j => ?_) (fun j => ?_) <;>
    simp only [Sequential.start_workTapes, Sequential.start_workTapePos] <;>
    induction j using Fin.addCases with
    | left i =>
      have hi := i.isLt
      have h := hl i
      first
      | (unfold gF; rw [embed_workTapes_of_not _ _ _ _ (hng i),
          rF_w x f (eB M₁.tapes M₂.tapes (Fin.castAdd 2 i)) (by omega), cP_w,
          if_neg (by omega), if_neg (by omega)]
         funext p
         simp [shiftCfg, dB, InputFromTape.config, MultiTapeTM.inCfg,
           MultiTapeMachine.initialConfig])
      | (unfold gF; rw [embed_workTapePos_of_not _ _ _ _ (hng i),
          rF_p x f (eB M₁.tapes M₂.tapes (Fin.castAdd 2 i)) (by omega), cP_p, if_neg (by omega)]
         simp [shiftCfg, dB, InputFromTape.config, MultiTapeTM.inCfg,
           MultiTapeMachine.initialConfig])
    | right i =>
      rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
      · first
        | (unfold gF; rw [hv, embed_workTapes_of _ _ _ _ rfl]
           funext p
           simp [guardFin, pc, shiftTape, shiftCfg, dB, InputFromTape.config, MultiTapeTM.inCfg])
        | (unfold gF; rw [hv, embed_workTapePos_of _ _ _ _ rfl]
           simp [guardFin, pc, shiftCfg, dB, InputFromTape.config, MultiTapeTM.inCfg,
             MultiTapeMachine.initialConfig])
      · first
        | (unfold gF; rw [hf, embed_workTapes_of _ _ _ _ rfl]
           funext p
           simp [guardFin, pc, shiftTape, flagTape, shiftCfg, dB, InputFromTape.config,
             MultiTapeTM.inCfg])
        | (unfold gF; rw [hf, embed_workTapePos_of _ _ _ _ rfl]
           simp [guardFin, pc, shiftCfg, dB, InputFromTape.config, MultiTapeTM.inCfg,
             MultiTapeMachine.initialConfig])

end AndThen

/-- The last three phases of the guarded composition, from the end of the first one. -/
theorem AndThen.law_RGB (x : List Bool) (f : Config M₁.tapes Bool (Fin M₁.states) (Fin 0) x)
    (hf : f.tapes.output.length ≤ M₁.time) :
    (law ((M₁.andThenR M₂).seq ((M₁.andThenG M₂).seq (M₁.andThenB M₂)))
        ((M₁.time + 3) + (3 + M₂.time))
        (Sequential.start ((M₁.andThenR M₂).seq ((M₁.andThenG M₂).seq (M₁.andThenB M₂)))
          (aF x f))).map (fun c => c.tapes.output) = M₂.guardK f.tapes.output := by
  rw [start_seq, start_R, law_seq_exact _ _ _ _ _ (runs_R x f hf).1, (runs_R x f hf).2,
    PMF.pure_bind, start_seq, start_G, PMF.map_comp]
  rcases hy : f.tapes.output with _ | ⟨_ | _, w⟩
  rotate_left 2
  · -- `true :: w`
    rw [law_seq_exact _ _ _ _ _ (runs_G x f w hy).1, (runs_G x f w hy).2, PMF.pure_bind,
      start_Bg, b0g, Machine.andThenB, law_extendTapes, law_shift, law_inputFromTape,
      Machine.guardK_true, Machine.run_eq_law, PMF.map_comp, PMF.map_comp, PMF.map_comp,
      PMF.map_comp]
    rfl
  all_goals
    have hh : f.tapes.output.head? ≠ some true := by rw [hy]; simp
    rw [Machine.guardK_of_head _ _ (by simp), law_seq_left _ _ _ _ (fun i _ r hr => ?_),
      show 3 + M₂.time = (2 + M₂.time) + 1 by omega, law_G_rej x f hh, PMF.pure_map,
      PMF.pure_map]
    · rfl
    · rcases i with _ | i
      · rw [Compose.law_zero, PMF.mem_support_pure_iff] at hr; rw [hr]; simp [g0, pc]
      · rw [law_G_rej x f hh, PMF.mem_support_pure_iff] at hr; rw [hr]; simp [pc]

/-- **The output law of the guarded composition**: `M₂` runs on `w` when `M₁` outputs
`true :: w`, each under its own clock; otherwise the output is empty. -/
theorem Machine.run_andThenGuard (x : List Bool) :
    (M₁.andThenGuard M₂).run x = (M₁.run x).bind M₂.guardK := by
  have hinit : (M₁.andThenGuardPTM M₂).initialConfig x =
      Sequential.left ((M₁.andThenA M₂).seq ((M₁.andThenR M₂).seq
        ((M₁.andThenG M₂).seq (M₁.andThenB M₂))))
        ((M₁.andThenLinP M₂).initialConfig x) :=
    Config.ext rfl (funext fun o => o.elim0)
  have hrunsP : Runs (M₁.andThenLinP M₂) ((M₁.andThenLinP M₂).initialConfig x)
      (dprepTime M₁.tapes M₁.time) (AndThen.dE M₁ M₂ x) := by
    rw [Machine.andThenLinP, MultiTapeMachine.initialConfig_extendTapes]
    exact runs_extendTapes _ _ _ (runs_dprep _ _ x)
  rw [Machine.andThenGuard, Machine.run_ofPTMOps', hinit, Machine.andThenGuardTime,
    Machine.andThenGuardPTM, law_seq_exact _ _ _ _ _ hrunsP.1, hrunsP.2, PMF.pure_bind, start_seq,
    AndThen.start_A_lin, law_seq_exact _ _ _ _ _ (exact_A x), law_A, PMF.bind_map, PMF.map_comp,
    PMF.map_bind, Machine.run_eq_law M₁, PMF.bind_map]
  apply Probability.PMF.bind_congr_on_support
  intro f hf
  have hlen := Compose.length_output_of_mem_law _ _ _ _ hf
  simp only [Function.comp_apply, PMF.map_comp]
  rw [← AndThen.law_RGB M₁ M₂ x f (by simpa [MultiTapeMachine.initialConfig] using hlen)]
  rfl

/-- **Acceptance of the guarded composition** on an input law `μ`. -/
theorem Machine.acceptProb_andThenGuard (μ : PMF (List Bool)) :
    (M₁.andThenGuard M₂).acceptProb μ = (((μ.bind M₁.run).bind M₂.guardK) [true]).toReal := by
  unfold Machine.acceptProb
  rw [show (M₁.andThenGuard M₂).run = fun x => (M₁.run x).bind M₂.guardK from
    funext (Machine.run_andThenGuard M₁ M₂), PMF.bind_bind]

end SigabaNeo
