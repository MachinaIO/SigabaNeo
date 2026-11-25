import SigabaNeo.Trusted.Machine
import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Simulation

/-!
# Machines from closed fair-coin machines

A closed fair-coin machine of cslib-frontier (`MultiTapePTM k Bool S`, with no oracle channels)
with finitely many states becomes a `Machine` with a clock (`Machine.ofPTM`): its states are renamed
into `Fin n` and its (empty) channel type into `Fin 0`. Its output law is that of the closed run
(`Machine.run_ofPTM`).
-/

namespace SigabaNeo

open Cslib Turing

/-- Rename the states and the empty channel type of an instruction. -/
def ptmAction {k n : ℕ} {S : Type} (e : S ≃ Fin n) :
    MultiTapeMachine.Action k Bool S Empty → MultiTapeMachine.Action k Bool (Fin n) (Fin 0)
  | .step action _ _ => .step { action with state := action.state.map e } Fin.elim0 Fin.elim0
  | .query o _ => o.elim

/-- The machine with renamed states and channels. -/
def ptmToFin {k n : ℕ} {S : Type} (m : MultiTapePTM k Bool S) (e : S ≃ Fin n) :
    MultiTapePTM k Bool (Fin n) (Fin 0) where
  initial := e m.initial
  tr q a w _ := fun bit => ptmAction e (m.tr (e.symm q) a w (fun o => o.elim) bit)

/-- The configuration with renamed states and channels. -/
def ptmConfig {k n : ℕ} {S : Type} (e : S ≃ Fin n) {input : List Bool}
    (cfg : MultiTapeMachine.Config k Bool S Empty input) :
    MultiTapeMachine.Config k Bool (Fin n) (Fin 0) input where
  tapes := cfg.tapes.mapState (Option.map e)
  channels := Fin.elim0

theorem ptmToFin_runConfigFrom {k n : ℕ} {S : Type} (m : MultiTapePTM k Bool S) (e : S ≃ Fin n)
    {input : List Bool} (fuel : ℕ) (cfg : MultiTapeMachine.Config k Bool S Empty input) :
    (ptmToFin m e).runConfigFrom (ProbComp.uniform Bool) (fun o => o.elim0) fuel (ptmConfig e cfg) =
      ptmConfig e <$> m.runConfigFrom (ProbComp.uniform Bool) (fun o => o.elim) fuel cfg := by
  apply MultiTapeMachine.runConfigFrom_map
  intro cfg
  cases hs : cfg.tapes.state with
  | none =>
    simp [MultiTapeMachine.runConfigFrom, ptmConfig, Cfg.mapState, hs]
  | some state =>
    simp only [MultiTapeMachine.runConfigFrom, ptmConfig, Cfg.mapState,
      hs, Option.map_some, map_bind, bind_map_left]
    congr 1 with bit : 1
    simp only [ptmToFin, Equiv.symm_apply_apply]
    cases h : m.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols _ bit with
    | step action sym move =>
      have hans : (fun o : Empty => (o.elim : Option Bool)) = cfg.answerSymbols :=
        funext fun o => o.elim
      have h' : m.tr state
          ({ state := some (e state), inputPos := cfg.tapes.inputPos, workTapes := cfg.tapes.workTapes,
              workTapePos := cfg.tapes.workTapePos, output := cfg.tapes.output } :
              Cfg k Bool (Fin n) input).inputSymbol
          ({ state := some (e state), inputPos := cfg.tapes.inputPos, workTapes := cfg.tapes.workTapes,
              workTapePos := cfg.tapes.workTapePos, output := cfg.tapes.output } :
              Cfg k Bool (Fin n) input).workTapeSymbols
          (fun o => o.elim) bit = .step action sym move := by
        rw [hans]; exact h
      rw [h']
      simp only [ptmAction, map_pure]
      congr 1
      ext1
      · rfl
      · funext o; exact o.elim0
    | query o _ => exact o.elim

theorem ptmToFin_initialConfig {k n : ℕ} {S : Type} (m : MultiTapePTM k Bool S) (e : S ≃ Fin n)
    (input : List Bool) :
    (ptmToFin m e).initialConfig input = ptmConfig e (m.initialConfig input) := by
  ext1
  · rfl
  · funext o; exact o.elim0

/-- A closed fair-coin machine with finitely many states, with the clock `time`. -/
noncomputable def Machine.ofPTM {k : ℕ} {S : Type} [Finite S] (m : MultiTapePTM k Bool S)
    (time : ℕ) : Machine :=
  ⟨k, Nat.card S, ptmToFin m (Finite.equivFin S), time⟩

/-- **The output law** of `Machine.ofPTM` is that of the closed run. -/
theorem Machine.run_ofPTM {k : ℕ} {S : Type} [Finite S] (m : MultiTapePTM k Bool S) (time : ℕ)
    (x : List Bool) : (Machine.ofPTM m time).run x = ProbComp.eval (m.runClosed time x) := by
  unfold Machine.run Machine.ofPTM MultiTapePTM.runClosed
  simp only [MultiTapePTM.run, MultiTapePTM.runFrom]
  rw [ptmToFin_initialConfig, ptmToFin_runConfigFrom, Functor.map_map]
  rfl

end SigabaNeo
