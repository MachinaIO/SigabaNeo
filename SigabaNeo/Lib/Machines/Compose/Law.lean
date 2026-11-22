import SigabaNeo.Lib.Machines.Inline.OfPTMOps
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Sequential
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Clock
import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.OutputToTape
import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.InputFromTape
import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.ExtendTapes

/-!
# The law of a closed machine on configurations

For a closed fair-coin machine (`MultiTapePTM k Bool S (Fin 0)`), `Compose.law M n c` is the law of
its configuration after `n` steps from `c`. This file collects:

* `law_add`, `law_zero`, `law_halted`: clocks add; a halted configuration stays;
* `law_eq_stateful`: the stateful form used by cslib-frontier's combinator theorems;
* `law_seq_left`, `law_seq_exact`: **sequencing with an exact first phase**. If the first machine
  is live at every step before `t` and halted at `t` (`Exact`), then `t + n` steps of `first.seq
  second` run `first` for `t` steps and `second` for `n` steps from the handoff, whether or not
  `second` halts;
* `Machine.run_ofPTMOps'`: the output law of `Machine.ofPTMOps` through `law`.
-/

namespace SigabaNeo.Compose

open Cslib Turing MultiTapeMachine

/-- The fair coin. -/
noncomputable abbrev coin : ProbComp Bool := ProbComp.uniform Bool

/-- No channels. -/
def noQ : Fin 0 → List Bool → ProbComp (List Bool) := fun o => o.elim0

/-- The uniform oracle, with a trivial private state. -/
noncomputable def uo : (q : ℕ) → StateT Unit PMF (unifSpec q) :=
  fun q s => (fun a => (a, s)) <$> ProbComp.unifOracle q

theorem run_interpret_uo {α : Type} (p : ProbComp α) (s : Unit) :
    (OracleComp.interpret uo p).run s = (ProbComp.eval p).map (fun a => (a, s)) :=
  OracleComp.run_interpret_stateless (m := PMF) ProbComp.unifOracle p s

variable {k : ℕ} {S : Type} {x : List Bool}

/-- The law of the configuration after `n` steps from `c`. -/
noncomputable def law (M : MultiTapePTM k Bool S (Fin 0)) (n : ℕ)
    (c : Config k Bool S (Fin 0) x) : PMF (Config k Bool S (Fin 0) x) :=
  ProbComp.eval (M.runConfigFrom coin noQ n c)

theorem law_eq_stateful (M : MultiTapePTM k Bool S (Fin 0)) (n : ℕ)
    (c : Config k Bool S (Fin 0) x) :
    (OracleComp.interpret uo (M.runConfigFrom coin noQ n c)).run () =
      (law M n c).map (fun a => (a, ())) :=
  run_interpret_uo _ _

theorem law_add (M : MultiTapePTM k Bool S (Fin 0)) (a b : ℕ) (c : Config k Bool S (Fin 0) x) :
    law M (a + b) c = (law M a c).bind (law M b) := by
  unfold law MultiTapePTM.runConfigFrom
  rw [MultiTapeMachine.runConfigFrom_add, ProbComp.eval_bind]

@[simp] theorem law_zero (M : MultiTapePTM k Bool S (Fin 0)) (c : Config k Bool S (Fin 0) x) :
    law M 0 c = PMF.pure c := rfl

theorem law_halted (M : MultiTapePTM k Bool S (Fin 0)) (n : ℕ) (c : Config k Bool S (Fin 0) x)
    (h : c.tapes.state = none) : law M n c = PMF.pure c := by
  unfold law MultiTapePTM.runConfigFrom
  rw [MultiTapeMachine.runConfigFrom_halted _ _ _ _ _ h]
  rfl

/-- A machine is **exactly** `t` steps long from `c`: live before `t`, halted at `t`. -/
def Exact (M : MultiTapePTM k Bool S (Fin 0)) (c : Config k Bool S (Fin 0) x) (t : ℕ) : Prop :=
  (∀ i < t, ∀ r ∈ (law M i c).support, r.tapes.state ≠ none) ∧
    ∀ r ∈ (law M t c).support, r.tapes.state = none

/-- A deterministic run through explicit live configurations is exact. -/
theorem exact_of_pure (M : MultiTapePTM k Bool S (Fin 0)) (c : Config k Bool S (Fin 0) x) (t : ℕ)
    (f : ℕ → Config k Bool S (Fin 0) x) (hf : ∀ i ≤ t, law M i c = PMF.pure (f i))
    (hlive : ∀ i < t, (f i).tapes.state ≠ none) (hhalt : (f t).tapes.state = none) :
    Exact M c t := by
  refine ⟨fun i hi r hr => ?_, fun r hr => ?_⟩
  · rw [hf i hi.le, PMF.mem_support_pure_iff] at hr
    exact hr ▸ hlive i hi
  · rw [hf t le_rfl, PMF.mem_support_pure_iff] at hr
    exact hr ▸ hhalt

/-! ### Sequencing with an exact first phase -/

section Seq

variable {S₀ S₁ : Type} (first : MultiTapePTM k Bool S₀ (Fin 0))
  (second : MultiTapePTM k Bool S₁ (Fin 0))

theorem hchoose {α β : Type} (f : α → β) (choices : ReaderT Bool Id α) :
    (fun choices => choices <$> coin) (f <$> choices) =
      f <$> (fun choices => choices <$> coin) choices := by
  simp only [Functor.map_map]; rfl

theorem law_seq_one (c : Config k Bool S₀ (Fin 0) x) (h : c.tapes.state ≠ none) :
    law (first.seq second) 1 (Sequential.left second c) =
      (law first 1 c).map (Sequential.left second) := by
  unfold law MultiTapePTM.runConfigFrom
  exact (congrArg ProbComp.eval
    (Sequential.runConfigFrom_one first second (fun choices => choices <$> coin) (fun _ _ => hchoose _ _) noQ c h)).trans (ProbComp.eval_map _ _)

theorem law_seq_right (n : ℕ) (c : Config k Bool S₁ (Fin 0) x) :
    law (first.seq second) n (Sequential.right c) = (law second n c).map Sequential.right := by
  unfold law MultiTapePTM.runConfigFrom
  exact (congrArg ProbComp.eval
    (Sequential.runConfigFrom_right first second (fun choices => choices <$> coin) (fun _ _ => hchoose _ _) noQ n c)).trans (ProbComp.eval_map _ _)

theorem law_seq_left (j : ℕ) (c : Config k Bool S₀ (Fin 0) x)
    (hlive : ∀ i < j, ∀ r ∈ (law first i c).support, r.tapes.state ≠ none) :
    law (first.seq second) j (Sequential.left second c) =
      (law first j c).map (Sequential.left second) := by
  induction j with
  | zero => simp [PMF.pure_map]
  | succ j ih =>
    rw [law_add, ih (fun i hi => hlive i (by omega)), PMF.bind_map, law_add first,
      PMF.map_bind]
    apply Probability.PMF.bind_congr_on_support
    intro r hr
    exact law_seq_one first second r (hlive j (by omega) r hr)

theorem start_eq (r : Config k Bool S₀ (Fin 0) x) (h : r.tapes.state = none) :
    Sequential.left second r = Sequential.right (Sequential.start second r) :=
  Sequential.left_halted second r h

/-- **Sequencing with an exact first phase.** -/
theorem law_seq_exact (t n : ℕ) (c : Config k Bool S₀ (Fin 0) x) (hex : Exact first c t) :
    law (first.seq second) (t + n) (Sequential.left second c) =
      (law first t c).bind
        (fun r => (law second n (Sequential.start second r)).map Sequential.right) := by
  rw [law_add, law_seq_left first second t c hex.1, PMF.bind_map]
  apply Probability.PMF.bind_congr_on_support
  intro r hr
  simp only [Function.comp_apply]
  rw [start_eq second r (hex.2 r hr), law_seq_right]

/-- The handoff into a sequence is the handoff into its first phase. -/
theorem start_seq {S₂ S₃ : Type} (A : MultiTapePTM k Bool S₂ (Fin 0))
    (B : MultiTapePTM k Bool S₃ (Fin 0)) (r : Config k Bool S₀ (Fin 0) x) :
    Sequential.start (A.seq B) r = Sequential.left B (Sequential.start A r) := rfl

end Seq

/-! ### Machines -/

theorem _root_.SigabaNeo.Machine.run_eq_law (A : Machine) (x : List Bool) :
    A.run x = (law A.machine A.time (A.machine.initialConfig x)).map (fun c => c.tapes.output) := by
  unfold Machine.run law MultiTapePTM.run MultiTapePTM.runFrom
  rw [ProbComp.eval_map]
  rfl

theorem _root_.SigabaNeo.Machine.run_ofPTMOps' {S : Type} [Fintype S]
    (m : MultiTapePTM k Bool S (Fin 0)) (time : ℕ) (x : List Bool) :
    (Machine.ofPTMOps m time).run x =
      (law m time (m.initialConfig x)).map (fun c => c.tapes.output) := by
  rw [Machine.run_eq_law]
  simp only [Machine.ofPTMOps]
  unfold law
  rw [ptmRename_initialConfig, ptmRename_runConfigFrom, ProbComp.eval_map, PMF.map_comp]
  rfl

end SigabaNeo.Compose
