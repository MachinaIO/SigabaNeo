import SigabaNeo.Lib.Machines.Inline.OfPTMOps

/-!
# Routines: closed machines with an explicit law on their tapes

A `Routine k` bundles a closed fair-coin machine with `k` work tapes and a `Fintype` state type
together with an explicit worst-case clock `time`. `Routine.Runs H ws₀ μ` specifies its effect on
word tapes: started (on the empty input) with the word `ws₀ i` on tape `i` and every head at the
start, on every coin sequence it halts within `time` steps with every head back at the start, and
the joint law of its final tapes is `μ` (words on tapes).

This file also collects the generic run-law algebra of `runOracleConfigFrom` used by the inlining
construction:

* `law_add`: clocks add;
* `law_succ_live`: one live step of a fair-coin machine, with the coin;
* `law_succ_det`: one coin-independent ordinary step;
* `law_simExit`: a machine that simulates another one step by step, and leaves the simulation when
  the simulated machine halts, runs the simulated machine and then its continuation.
-/

namespace SigabaNeo

open Cslib Turing MultiTapeMachine

/-- A closed fair-coin machine with `k` work tapes, finitely many states and a worst-case clock. -/
structure Routine (k : ℕ) where
  /-- The control states. -/
  State : Type
  [fintype : Fintype State]
  [decEq : DecidableEq State]
  /-- The machine. -/
  machine : MultiTapePTM k Bool State
  /-- The worst-case number of steps. -/
  time : ℕ

attribute [instance] Routine.fintype Routine.decEq

namespace Routine

variable {k : ℕ}

/-- The start configuration on the empty input with the word `ws i` on tape `i`. -/
def startCfg (H : Routine k) (ws : Fin k → List Bool) : Config k Bool H.State Empty [] where
  tapes := wordsCfg [] (some H.machine.initial) ws []

/-- The joint law of the configuration after `n` steps from `cfg` (the machine is closed). -/
noncomputable def law (H : Routine k) (n : ℕ) (cfg : Config k Bool H.State Empty []) :
    PMF (Config k Bool H.State Empty [] × Unit) :=
  ProbOracleComp.runWith (fun e : Empty × List Bool => e.1.elim)
    (H.machine.runOracleConfigFrom n cfg) ()

/-- **Specification of a routine.** From the words `ws₀` (heads at the start), on every coin
sequence the routine halts within `time` steps with every head at the start, and the law of its
final tapes is that of the words drawn from `μ`. -/
def Runs (H : Routine k) (ws₀ : Fin k → List Bool) (μ : PMF (Fin k → List Bool)) : Prop :=
  (∀ f ∈ (H.law H.time (H.startCfg ws₀)).support,
      f.1.tapes.state = none ∧ ∀ i, f.1.tapes.workTapePos i = 0) ∧
    (H.law H.time (H.startCfg ws₀)).map (fun f => f.1.tapes.workTapes) =
      μ.map (fun ws i => tapeOfList (ws i))

/-- Number of states. -/
abbrev states (H : Routine k) : ℕ := Fintype.card H.State

end Routine

/-! ### Run-law algebra -/

section Law

variable {k : ℕ} {S O σ : Type} [DecidableEq O] {input : List Bool}
  (M : MultiTapePTM k Bool S O) (oracle : O × List Bool → StateT σ PMF (List Bool))

/-- Clocks add. -/
theorem law_add (a b : ℕ) (cfg : Config k Bool S O input) (s : σ) :
    ProbOracleComp.runWith oracle (M.runOracleConfigFrom (a + b) cfg) s =
      (ProbOracleComp.runWith oracle (M.runOracleConfigFrom a cfg) s).bind
        (fun r => ProbOracleComp.runWith oracle (M.runOracleConfigFrom b r.1) r.2) := by
  simp only [MultiTapePTM.runOracleConfigFrom, MultiTapePTM.runConfigFrom]
  rw [MultiTapeMachine.runConfigFrom_add, ProbOracleComp.runWith_bind]

theorem law_zero (cfg : Config k Bool S O input) (s : σ) :
    ProbOracleComp.runWith oracle (M.runOracleConfigFrom 0 cfg) s = PMF.pure (cfg, s) := by
  simp [MultiTapePTM.runOracleConfigFrom, MultiTapePTM.runConfigFrom]

theorem law_halted (n : ℕ) (cfg : Config k Bool S O input) (s : σ)
    (h : cfg.tapes.state = none) :
    ProbOracleComp.runWith oracle (M.runOracleConfigFrom n cfg) s = PMF.pure (cfg, s) := by
  simp [MultiTapePTM.runOracleConfigFrom, MultiTapePTM.runConfigFrom,
    MultiTapeMachine.runConfigFrom_halted _ _ _ _ _ h]

/-- The law after executing the instruction `act` from `cfg`, then `n` more steps. -/
noncomputable def stepLaw (n : ℕ) (cfg : Config k Bool S O input) (s : σ)
    (act : MultiTapeMachine.Action k Bool S O) : PMF (Config k Bool S O input × σ) :=
  match act with
  | .step action symbol move =>
    ProbOracleComp.runWith oracle (M.runOracleConfigFrom n (cfg.step action symbol move)) s
  | .query op next =>
    (oracle (op, (cfg.channels op).queryBuffer) s).bind fun r =>
      ProbOracleComp.runWith oracle (M.runOracleConfigFrom n (cfg.receive op next r.1)) r.2

/-- One live step of a fair-coin machine: a fair bit selects the instruction. -/
theorem law_succ_live (n : ℕ) (cfg : Config k Bool S O input) (s : σ) {q : S}
    (hq : cfg.tapes.state = some q) :
    ProbOracleComp.runWith oracle (M.runOracleConfigFrom (n + 1) cfg) s =
      (ProbComp.eval (ProbComp.uniform Bool)).bind fun bit =>
        stepLaw M oracle n cfg s
          (M.tr q cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols bit) := by
  dsimp only [MultiTapePTM.runOracleConfigFrom, MultiTapePTM.runConfigFrom]
  rw [MultiTapeMachine.runConfigFrom]
  simp only [hq, bind_map_left, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_sample, PMF.bind_map, Function.comp_def]
  congr 1 with bit : 1
  cases M.tr q cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols bit with
  | step action symbol move => rfl
  | query op next =>
    simp only [stepLaw, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query]
    rfl

/-- One coin-independent ordinary step. -/
theorem law_succ_det (n : ℕ) (cfg : Config k Bool S O input) (s : σ) {q : S}
    (hq : cfg.tapes.state = some q) {action : Turing.Action k Bool S}
    {symbol : O → Option Bool} {move : O → SignType}
    (htr : ∀ bit,
      M.tr q cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols bit =
        .step action symbol move) :
    ProbOracleComp.runWith oracle (M.runOracleConfigFrom (n + 1) cfg) s =
      ProbOracleComp.runWith oracle (M.runOracleConfigFrom n (cfg.step action symbol move)) s :=
  MultiTapePTM.run_interpret_runOracleConfigFrom_succ_step M oracle n cfg s hq htr

/-- Every supported configuration after `a + b` steps is halted when those after `a` steps are. -/
theorem law_add_of_halted (a b : ℕ) (cfg : Config k Bool S O input) (s : σ)
    (h : ∀ f ∈ (ProbOracleComp.runWith oracle (M.runOracleConfigFrom a cfg) s).support,
      f.1.tapes.state = none) :
    ProbOracleComp.runWith oracle (M.runOracleConfigFrom (a + b) cfg) s =
      ProbOracleComp.runWith oracle (M.runOracleConfigFrom a cfg) s :=
  MultiTapePTM.run_interpret_runOracleConfigFrom_add_of_halted M oracle cfg a b s h

end Law

/-! ### Simulation with an exit -/

section SimExit

variable {kS kB : ℕ} {SS SB OB σ : Type} [DecidableEq OB] {xS xB : List Bool}
  (src : MultiTapePTM kS Bool SS) (tgt : MultiTapePTM kB Bool SB OB)
  (oracle : OB × List Bool → StateT σ PMF (List Bool))
  (emb exit : Config kS Bool SS Empty xS → Config kB Bool SB OB xB)

/-- The target configuration for a source configuration: the simulation while the source is live,
the exit once it has halted. -/
def simOrExit (c : Config kS Bool SS Empty xS) : Config kB Bool SB OB xB :=
  if c.tapes.state = none then exit c else emb c

/-- **Simulation with an exit.** Suppose that from the image of every live source configuration
one target step is, in law and preserving the oracle state, one source step followed by the
simulation (or the exit, if the source halted). If the source halts within `n` steps, and the
target halts within `t` steps from every exit, then `n + t` target steps run the source and then
the target from the exit. -/
theorem law_simExit
    (hstep : ∀ c : Config kS Bool SS Empty xS, c.tapes.state ≠ none → ∀ s : σ,
      ProbOracleComp.runWith oracle (tgt.runOracleConfigFrom 1 (emb c)) s =
        (ProbOracleComp.runWith (fun e : Empty × List Bool => e.1.elim)
          (src.runOracleConfigFrom 1 c) ()).map (fun r => (simOrExit emb exit r.1, s)))
    (t : ℕ) (n : ℕ) (c : Config kS Bool SS Empty xS) (s : σ)
    (hhalt : ∀ f ∈ (ProbOracleComp.runWith (fun e : Empty × List Bool => e.1.elim)
      (src.runOracleConfigFrom n c) ()).support, f.1.tapes.state = none)
    (hgood : ∀ f ∈ (ProbOracleComp.runWith (fun e : Empty × List Bool => e.1.elim)
      (src.runOracleConfigFrom n c) ()).support,
      ∀ g ∈ (ProbOracleComp.runWith oracle (tgt.runOracleConfigFrom t (exit f.1)) s).support,
        g.1.tapes.state = none) :
    ProbOracleComp.runWith oracle (tgt.runOracleConfigFrom (n + t) (simOrExit emb exit c)) s =
      (ProbOracleComp.runWith (fun e : Empty × List Bool => e.1.elim)
        (src.runOracleConfigFrom n c) ()).bind
        (fun f => ProbOracleComp.runWith oracle (tgt.runOracleConfigFrom t (exit f.1)) s) := by
  induction n generalizing c with
  | zero =>
    rw [law_zero] at hhalt hgood ⊢
    have hc : c.tapes.state = none := hhalt (c, ()) (by simp)
    simp [simOrExit, hc]
  | succ n ih =>
    by_cases hc : c.tapes.state = none
    · rw [law_halted _ _ _ _ _ hc] at hgood ⊢
      simp only [simOrExit, hc, ite_true, PMF.pure_bind]
      rw [show n + 1 + t = t + (n + 1) by omega,
        law_add_of_halted tgt oracle t (n + 1) (exit c) s
          (fun g hg => hgood (c, ()) (by simp) g hg)]
    · have hsrc : ∀ m, ProbOracleComp.runWith (fun e : Empty × List Bool => e.1.elim)
          (src.runOracleConfigFrom (1 + m) c) () =
          (ProbOracleComp.runWith (fun e : Empty × List Bool => e.1.elim)
            (src.runOracleConfigFrom 1 c) ()).bind (fun r =>
              ProbOracleComp.runWith (fun e : Empty × List Bool => e.1.elim)
                (src.runOracleConfigFrom m r.1) ()) := fun m => by
        rw [law_add]
      rw [show n + 1 = 1 + n by omega] at hhalt hgood ⊢
      rw [hsrc] at hhalt hgood ⊢
      simp only [simOrExit, hc, ite_false]
      rw [show 1 + n + t = 1 + (n + t) by omega, law_add, hstep c hc s, PMF.bind_map,
        PMF.bind_bind]
      apply Probability.PMF.bind_congr_on_support
      rintro ⟨c', u⟩ hc'
      cases u
      simp only [Function.comp_apply]
      apply ih c'
      · intro f hf
        exact hhalt f ((PMF.mem_support_bind_iff _ _ _).mpr ⟨(c', ()), hc', hf⟩)
      · intro f hf
        exact hgood f ((PMF.mem_support_bind_iff _ _ _).mpr ⟨(c', ()), hc', hf⟩)

end SimExit

end SigabaNeo
