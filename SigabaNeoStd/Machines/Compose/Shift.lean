import SigabaNeoStd.Machines.Compose.Steps

/-!
# Translating work tapes

A machine reads and writes only under its heads, so translating a work tape together with its
head commutes with every step. `Compose.shiftCfg d c` translates each work tape `l` of `c` by
`d l` cells (the content of cell `p` moves to cell `p + d l`, the head moves along), and:

* `Compose.law_shift`: `law M n (shiftCfg d c) = (law M n c).map (shiftCfg d)`.
-/

namespace SigabaNeo.Compose

open Cslib Turing MultiTapeMachine

variable {k : ℕ} {S : Type} {x : List Bool}

/-- Translate each work tape `l` (and its head) by `d l` cells. -/
def shiftCfg (d : Fin k → ℤ) (c : Config k Bool S (Fin 0) x) : Config k Bool S (Fin 0) x :=
  ⟨{ c.tapes with
      workTapes := fun l p => c.tapes.workTapes l (p - d l)
      workTapePos := fun l => c.tapes.workTapePos l + d l }, c.channels⟩

@[simp] theorem shiftCfg_state (d : Fin k → ℤ) (c : Config k Bool S (Fin 0) x) :
    (shiftCfg d c).tapes.state = c.tapes.state := rfl

@[simp] theorem shiftCfg_output (d : Fin k → ℤ) (c : Config k Bool S (Fin 0) x) :
    (shiftCfg d c).tapes.output = c.tapes.output := rfl

@[simp] theorem shiftCfg_inputPos (d : Fin k → ℤ) (c : Config k Bool S (Fin 0) x) :
    (shiftCfg d c).tapes.inputPos = c.tapes.inputPos := rfl

@[simp] theorem shiftCfg_workTapes (d : Fin k → ℤ) (c : Config k Bool S (Fin 0) x) (l : Fin k) :
    (shiftCfg d c).tapes.workTapes l = fun p => c.tapes.workTapes l (p - d l) := rfl

@[simp] theorem shiftCfg_workTapePos (d : Fin k → ℤ) (c : Config k Bool S (Fin 0) x)
    (l : Fin k) : (shiftCfg d c).tapes.workTapePos l = c.tapes.workTapePos l + d l := rfl

theorem shiftCfg_workTapeSymbols (d : Fin k → ℤ) (c : Config k Bool S (Fin 0) x) :
    (shiftCfg d c).tapes.workTapeSymbols = c.tapes.workTapeSymbols := by
  funext l
  simp [Cfg.workTapeSymbols, shiftCfg]

theorem shiftCfg_step (d : Fin k → ℤ) (c : Config k Bool S (Fin 0) x)
    (a : Turing.Action k Bool S) (sym : Fin 0 → Option Bool) (mv : Fin 0 → SignType) :
    (shiftCfg d c).step a sym mv = shiftCfg d (c.step a sym mv) := by
  refine Config.ext ?_ (funext fun o => o.elim0)
  refine Cfg.ext rfl rfl (funext fun l => ?_) (funext fun l => ?_) rfl
  · simp only [Config.step, shiftCfg, Turing.Action.apply]
    cases (a.workTapes l).1 with
    | none => rfl
    | some s =>
      funext p
      simp only [Function.update_apply]
      congr 1
      apply propext; omega
  · simp only [Config.step, shiftCfg, Turing.Action.apply]; ring

/-- **Translating work tapes commutes with running.** -/
theorem law_shift (M : MultiTapePTM k Bool S (Fin 0)) (d : Fin k → ℤ) (n : ℕ)
    (c : Config k Bool S (Fin 0) x) :
    law M n (shiftCfg d c) = (law M n c).map (shiftCfg d) := by
  unfold law MultiTapePTM.runConfigFrom
  rw [MultiTapeMachine.runConfigFrom_map M M _ _ _ _ (shiftCfg d) ?_ n c, ProbComp.eval_map]
  intro c
  cases hs : c.tapes.state with
  | none => simp [MultiTapeMachine.runConfigFrom, hs]
  | some q =>
    simp only [MultiTapeMachine.runConfigFrom, shiftCfg_state, hs, shiftCfg_workTapeSymbols,
      map_bind]
    have hi : (shiftCfg d c).tapes.inputSymbol = c.tapes.inputSymbol := rfl
    have ha : (shiftCfg d c).answerSymbols = c.answerSymbols := rfl
    rw [hi, ha]
    congr 1 with a : 1
    cases a with
    | step a sym mv => simp [shiftCfg_step]
    | query o _ => exact o.elim0

end SigabaNeo.Compose
