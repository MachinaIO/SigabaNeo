import SigabaNeoStd.Machines.Compose.AndThen
import SigabaNeoStd.Machines.Compose.DigitPrep

/-!
# Sequential composition with a short preparation

`Machine.andThenLin M₁ M₂` is `Machine.andThen M₁ M₂` with its first phase, the writing of the unary
clock of `M₁` by `M₁.time + 5` straight-line states (`prepTM`), replaced by the digit-counter
preparation `DigitPrep.dprepTM M₁.tapes M₁.time`: it has `h + 6` states, where
`h = (clockDigits M₁.tapes M₁.time).length` is the number of digits of `M₁.time` in base
`2 ^ (M₁.tapes + 1)`, and uses the `M₁.tapes` work tapes of `M₁` and the buffer (all blank at the
start, and again at its end) as the `M₁.tapes + 1` tracks of its counter. It ends with the
tapes `prepTM` ends with (`AndThen.dE_w`, `AndThen.dE_p`), after exactly `dprepTime M₁.tapes M₁.time`
steps, so the other three phases are those of `Machine.andThen`:

* `Machine.run_andThenLin`: `(M₁.andThenLin M₂).run x = (M₁.run x).bind M₂.run`;
* `Machine.acceptProb_andThenLin`: `(M₁.andThenLin M₂).acceptProb μ = M₂.acceptProb (μ.bind M₁.run)`.

Bounds are in `Compose.LinCost`.
-/

namespace SigabaNeo

open Cslib Turing MultiTapeMachine Compose _root_.SigabaNeo.AndThen DigitPrep

namespace AndThen

variable (k₁ k₂ : ℕ)

/-- The tapes of the preparation: the work tapes of `M₁`, the buffer and the clock, then the
flag. -/
def eDf (j : Fin (k₁ + 3)) : Fin (k₁ + k₂ + 3) :=
  if j.val < k₁ + 2 then ⟨j, by omega⟩ else ⟨k₁ + 2 + k₂, by omega⟩

theorem eDf_val (j : Fin (k₁ + 3)) :
    (eDf k₁ k₂ j).val = if j.val < k₁ + 2 then j.val else k₁ + 2 + k₂ := by
  unfold eDf; split_ifs <;> rfl

/-- The tapes of the preparation. -/
def eD : Fin (k₁ + 3) ↪ Fin (k₁ + k₂ + 3) :=
  ⟨eDf k₁ k₂, by
    intro a b h
    have := congrArg Fin.val h
    rw [eDf_val, eDf_val] at this
    have ha := a.isLt; have hb := b.isLt
    ext; split_ifs at this <;> omega⟩

@[simp] theorem eD_val (j : Fin (k₁ + 3)) :
    (eD k₁ k₂ j).val = if j.val < k₁ + 2 then j.val else k₁ + 2 + k₂ :=
  eDf_val k₁ k₂ j

end AndThen

variable (M₁ M₂ : Machine)

/-- The state type of the composition with a short preparation. -/
abbrev Machine.AndThenLinState : Type :=
  DState M₁.tapes M₁.time ⊕ (Clock.Control (Fin M₁.states) ⊕ (Fin 3 ⊕ Fin M₂.states))

/-- The short preparation, on the tapes of the composition. -/
def Machine.andThenLinP :
    MultiTapePTM (M₁.tapes + M₂.tapes + 3) Bool (DState M₁.tapes M₁.time) (Fin 0) :=
  (dprepTM M₁.tapes M₁.time).extendTapes (eD M₁.tapes M₂.tapes)

/-- The composed fair-coin machine with a short preparation. -/
def Machine.andThenLinPTM :
    MultiTapePTM (M₁.tapes + M₂.tapes + 3) Bool (Machine.AndThenLinState M₁ M₂) (Fin 0) :=
  (M₁.andThenLinP M₂).seq ((M₁.andThenA M₂).seq ((M₁.andThenR M₂).seq (M₁.andThenB M₂)))

/-- The clock of the composition with a short preparation. -/
noncomputable def Machine.andThenLinTime : ℕ :=
  dprepTime M₁.tapes M₁.time + ((2 * M₁.time + 1) + ((M₁.time + 3) + M₂.time))

/-- **Sequential composition with a short preparation**: run `M₁`, then `M₂` on its output. -/
noncomputable def Machine.andThenLin : Machine :=
  Machine.ofPTMOps (M₁.andThenLinPTM M₂) (M₁.andThenLinTime M₂)

/-- The end of the short preparation, on the tapes of the composition. -/
def AndThen.dE (x : List Bool) :
    Config (M₁.tapes + M₂.tapes + 3) Bool (DState M₁.tapes M₁.time) (Fin 0) x :=
  (dFin (x := x) M₁.tapes M₁.time M₁.time).embed (eD M₁.tapes M₂.tapes) (fun _ _ => none)
    (fun _ => 0)

/-- The short preparation leaves the tapes `prepTM` leaves. -/
theorem AndThen.dE_w (x : List Bool) :
    (AndThen.dE M₁ M₂ x).tapes.workTapes = (cP (M₁ := M₁) (M₂ := M₂) x).tapes.workTapes := by
  funext l
  · rw [cP_w]
    split_ifs with h1 h2
    · rw [AndThen.dE, embed_workTapes_of _ _ _ _ (j := ⟨M₁.tapes + 1, by omega⟩)
        (Fin.ext (by simp; omega))]
      simp [dFin, gc, dF]
    · rw [AndThen.dE, embed_workTapes_of _ _ _ _ (j := ⟨M₁.tapes + 2, by omega⟩)
        (Fin.ext (by simp; omega))]
      simp [dFin, gc, dF]
    · by_cases h3 : l.val < M₁.tapes + 1
      · rw [AndThen.dE, embed_workTapes_of _ _ _ _ (j := ⟨l.val, by omega⟩)
          (Fin.ext (by simp; omega))]
        simp [dFin, gc, dF, h3]
      · refine embed_workTapes_of_not _ _ _ _ (fun j hj => ?_)
        have hv := congrArg Fin.val hj
        have := j.isLt
        simp only [eD_val] at hv
        split_ifs at hv <;> omega

/-- The short preparation leaves the heads where `prepTM` leaves them. -/
theorem AndThen.dE_p (x : List Bool) :
    (AndThen.dE M₁ M₂ x).tapes.workTapePos = (cP (M₁ := M₁) (M₂ := M₂) x).tapes.workTapePos := by
  funext l
  · rw [cP_p]
    split_ifs with h1
    · rw [AndThen.dE, embed_workTapePos_of _ _ _ _ (j := ⟨M₁.tapes + 1, by omega⟩)
        (Fin.ext (by simp; omega))]
      simp [dFin, gc, dP]
    · by_cases h3 : l.val < M₁.tapes + 1
      · rw [AndThen.dE, embed_workTapePos_of _ _ _ _ (j := ⟨l.val, by omega⟩) (Fin.ext (by simp; omega))]
        simp [dFin, gc, dP, h3]
      · by_cases h4 : l.val = M₁.tapes + 2 + M₂.tapes
        · rw [AndThen.dE, embed_workTapePos_of _ _ _ _ (j := ⟨M₁.tapes + 2, by omega⟩)
            (Fin.ext (by simp; omega))]
          simp [dFin, gc, dP]
        · refine embed_workTapePos_of_not _ _ _ _ (fun j hj => ?_)
          have hv := congrArg Fin.val hj
          have := j.isLt
          simp only [eD_val] at hv
          split_ifs at hv <;> omega

/-- The handoff into the simulation of `M₁` is that of `Machine.andThen`. -/
theorem AndThen.start_A_lin (x : List Bool) :
    Sequential.start (M₁.andThenA M₂) (AndThen.dE M₁ M₂ x) = a0 (M₁ := M₁) (M₂ := M₂) x := by
  rw [← start_A x]
  exact Config.ext (Cfg.ext rfl rfl (AndThen.dE_w M₁ M₂ x) (AndThen.dE_p M₁ M₂ x) rfl)
    (funext fun o => o.elim0)

/-- **The output law of the composition with a short preparation**: `M₂` runs on the output of
`M₁`, each under its own clock. -/
theorem Machine.run_andThenLin (x : List Bool) :
    (M₁.andThenLin M₂).run x = (M₁.run x).bind M₂.run := by
  have hinit : (M₁.andThenLinPTM M₂).initialConfig x =
      Sequential.left ((M₁.andThenA M₂).seq ((M₁.andThenR M₂).seq (M₁.andThenB M₂)))
        ((M₁.andThenLinP M₂).initialConfig x) :=
    Config.ext rfl (funext fun o => o.elim0)
  have hrunsP : Runs (M₁.andThenLinP M₂) ((M₁.andThenLinP M₂).initialConfig x)
      (dprepTime M₁.tapes M₁.time) (AndThen.dE M₁ M₂ x) := by
    rw [Machine.andThenLinP, MultiTapeMachine.initialConfig_extendTapes]
    exact runs_extendTapes _ _ _ (runs_dprep _ _ x)
  rw [Machine.andThenLin, Machine.run_ofPTMOps', hinit, Machine.andThenLinTime,
    Machine.andThenLinPTM, law_seq_exact _ _ _ _ _ hrunsP.1, hrunsP.2, PMF.pure_bind, start_seq,
    AndThen.start_A_lin, law_seq_exact _ _ _ _ _ (exact_A x), law_A, PMF.bind_map, PMF.map_comp, PMF.map_bind,
    Machine.run_eq_law M₁, PMF.bind_map]
  apply Probability.PMF.bind_congr_on_support
  intro f hf
  have hlen := Compose.length_output_of_mem_law _ _ _ _ hf
  simp only [Function.comp_apply, PMF.map_comp]
  rw [← AndThen.law_RB M₁ M₂ x f (by simpa [MultiTapeMachine.initialConfig] using hlen)]
  rfl

/-- **Acceptance of the composition with a short preparation** on an input law `μ`: that of `M₂`
on the output law of `M₁`. -/
theorem Machine.acceptProb_andThenLin (μ : PMF (List Bool)) :
    (M₁.andThenLin M₂).acceptProb μ = M₂.acceptProb (μ.bind M₁.run) := by
  unfold Machine.acceptProb
  rw [show (M₁.andThenLin M₂).run = fun x => (M₁.run x).bind M₂.run from
    funext (Machine.run_andThenLin M₁ M₂), PMF.bind_bind]

/-- The two compositions have the same output law. -/
theorem Machine.run_andThenLin_eq_andThen (x : List Bool) :
    (M₁.andThenLin M₂).run x = (M₁.andThen M₂).run x := by
  rw [Machine.run_andThenLin, Machine.run_andThen]

end SigabaNeo
