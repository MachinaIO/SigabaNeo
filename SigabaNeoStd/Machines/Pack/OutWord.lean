import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Tidy.Redirect
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.SuppCases

/-!
# Redirecting the output of a non-tidy phase to a work tape

cslib-frontier's `Turing.MultiTapePTM.ComputesTidily.outputToWord_of_le` redirects the output of a
*tidy* machine (blank work tapes before and after) to a new last work tape. The same holds for any
`RunsWords` phase: `RunsWords.outputToWord_of_le` takes the words `ws₀` to `ws₁ a` and writes the
emitted word `emit a` on the new last tape (`snocW`). The proof is the one of cslib-frontier, with
the blank tapes replaced by the words of the phase.

This is what makes a phase emitting several words in a row (e.g. transducers reading different
tapes, `inputFromWord`) write their concatenation on a work tape.
-/

namespace Turing.MultiTapePTM

open Cslib Cslib.Probability MultiTapeMachine MultiTapeMachine.Sequential MultiTapeTM

variable {k : ℕ} {State Operation : Type} {x : List Bool} [DecidableEq Operation]

/-- The words `ws` and one more word `w` on a new last tape. -/
def snocW (ws : Fin k → List Bool) (w : List Bool) : Fin (k + 1) → List Bool :=
  Fin.lastCases w ws

@[simp] theorem snocW_last (ws : Fin k → List Bool) (w : List Bool) :
    snocW ws w (Fin.last k) = w := by simp [snocW]

@[simp] theorem snocW_castSucc (ws : Fin k → List Bool) (w : List Bool) (j : Fin k) :
    snocW ws w j.castSucc = ws j := by simp [snocW]

/-- Redirecting the (empty) output of a `wordsCfg` configuration adds a blank last work tape. -/
theorem outCfg_wordsCfg_gen (q : Option State) (ws : Fin k → List Bool) :
    outCfg (wordsCfg x q ws []) = wordsCfg x q (snocW ws []) [] := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> induction l using Fin.lastCases <;>
    simp [outCfg, wordsCfg]

/-- Rewinding the last work tape of `outCfg (wordsCfg x _ ws w)`. -/
theorem runFrom_rewindLast_gen {ws : Fin k → List Bool} {w : List Bool} {r : ℕ}
    (hr : w.length ≤ r) :
    ((rewindWork Bool).extendTapes (tapeEmb (Fin.last k))).runFrom
      (outCfg (wordsCfg x (some (rewindWork Bool).q₀) ws w)) (r + 2) =
      wordsCfg x none (snocW ws w) [] := by
  let cfg := outCfg (wordsCfg x (some (rewindWork Bool).q₀) ws w)
  have hone : oneTapeCfg (Fin.last k) cfg =
      ⟨some (rewindWork Bool).q₀, 1, fun _ => tapeOfList w, fun _ => (w.length : ℤ), []⟩ := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext _ <;> simp [oneTapeCfg, cfg]
  have hrun₀ : (rewindWork Bool).runFrom (oneTapeCfg (Fin.last k) cfg) (w.length + 2) =
      ⟨none, 1, fun _ => tapeOfList w, fun _ => 0, []⟩ := by
    rw [hone]
    exact runFrom_rewindWork_none _ _ _ rfl le_rfl
  have hrun : (rewindWork Bool).runFrom (oneTapeCfg (Fin.last k) cfg) (r + 2) =
      ⟨none, 1, fun _ => tapeOfList w, fun _ => 0, []⟩ := by
    rw [runFrom_eq_of_halt _ _ (by omega : w.length + 2 ≤ r + 2) (by rw [hrun₀]), hrun₀]
  rw [runFrom_tapeEmb, hrun, embed_tapeEmb]
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> induction l using Fin.lastCases <;>
    simp [wordsCfg, cfg, outCfg]

/-- **Redirecting the output of a phase**: if `machine` takes the words `ws₀` to `ws₁ a` emitting
`emit a` (at most `l` long), then `machine.outputToWord` takes `snocW ws₀ []` to
`snocW (ws₁ a) (emit a)` within `time + l + 2` steps and emits nothing. -/
theorem RunsWords.outputToWord_of_le {machine : MultiTapePTM k Bool State Operation}
    {ws₀ : Fin k → List Bool} {time l : ℕ} {α : Type}
    {program : ProbOracleComp (fun _ : Operation × List Bool => List Bool) α}
    {ws₁ : α → Fin k → List Bool} {emit : α → List Bool}
    (h : machine.RunsWords x ws₀ [] time program ws₁ emit)
    (hl : ∀ (OracleState : Type)
      (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
      (s : OracleState) (a : α) (s' : OracleState),
      (a, s') ∈ (ProbOracleComp.runWith oracle program s).support → (emit a).length ≤ l) :
    ∀ out₀, machine.outputToWord.RunsWords x (snocW ws₀ []) out₀ (time + (l + 2)) program
      (fun a => snocW (ws₁ a) (emit a)) (fun _ => []) := by
  intro out₀
  apply RunsWords.of_nil_output
  intro OracleState oracle s cfg htapes hbuf
  let rew : MultiTapePTM (k + 1) Bool RewindWorkState Operation :=
    ofDeterministic ((rewindWork Bool).extendTapes (tapeEmb (Fin.last k)))
  let cfg₀ : Config k Bool State Operation x :=
    { tapes := wordsCfg x (some machine.initial) ws₀ [], channels := cfg.channels }
  have hleft : cfg = Sequential.left rew (OutputToTape.config cfg₀) := by
    refine Config.ext ?_ rfl
    rw [htapes]
    change wordsCfg x (some (Sum.inl machine.initial)) (snocW ws₀ []) [] =
      (outCfg (wordsCfg x (some machine.initial) ws₀ [])).mapState (Option.map Sum.inl)
    rw [outCfg_wordsCfg_gen]
    rfl
  have houtRun :
      machine.outputToTape.runOracleConfigFrom time (OutputToTape.config cfg₀) =
        OutputToTape.config <$> machine.runOracleConfigFrom time cfg₀ :=
    MultiTapePTM.runConfigFrom_outputToTape machine _ _ time cfg₀
  have hhalt₁ : ∀ result ∈ (ProbOracleComp.runWith oracle
      (machine.outputToTape.runOracleConfigFrom time (OutputToTape.config cfg₀)) s).support,
      result.1.tapes.state = none := by
    intro result hres
    supp_cases hres [houtRun, ProbOracleComp.runWith_map] with ⟨⟨mid, s₁⟩, hmid, rfl⟩
    exact h.halted oracle s cfg₀ rfl hbuf (mid, s₁) hmid
  have hstartG : ∀ (mid : Config k Bool State Operation x) (a : α),
      mid.tapes = wordsCfg x none (ws₁ a) ([] ++ emit a) →
      (Sequential.start rew (OutputToTape.config mid)).tapes =
        outCfg (wordsCfg x (some (rewindWork Bool).q₀) (ws₁ a) (emit a)) := by
    intro mid a hmidTapes
    simp only [Sequential.start, OutputToTape.config, outCfg, hmidTapes, id_eq,
      List.nil_append, wordsCfg_state, wordsCfg_inputPos, wordsCfg_output, wordsCfg_workTapePos]
    rfl
  have hhalt₂ : ∀ result ∈ (ProbOracleComp.runWith oracle
      (machine.outputToTape.runOracleConfigFrom time (OutputToTape.config cfg₀)) s).support,
      ∀ final ∈ (ProbOracleComp.runWith oracle
          (rew.runOracleConfigFrom (l + 2) (Sequential.start rew result.1)) result.2).support,
        final.1.tapes.state = none := by
    intro result hres ⟨final₁, final₂⟩ hfinal
    supp_cases hres [houtRun, ProbOracleComp.runWith_map] with ⟨⟨mid, s₁⟩, hmid, rfl⟩
    dsimp only [Prod.map_apply, id_eq] at hfinal
    obtain ⟨⟨a, ha, hmidTapes⟩, _⟩ := h.mem_support oracle s cfg₀ rfl hbuf hmid
    rw [run_interpret_runOracleConfigFrom_ofDeterministic, hstartG mid a hmidTapes,
      runFrom_rewindLast_gen (hl OracleState oracle s a s₁ ha)] at hfinal
    supp_cases hfinal
    rfl
  -- the rewound configuration, read off the tapes of the phase's final configuration
  let G : Cfg k Bool State x → Cfg (k + 1) Bool (State ⊕ RewindWorkState) x := fun c =>
    ⟨none, c.inputPos, Fin.lastCases (tapeOfList c.output) c.workTapes, fun _ => 0, []⟩
  have hG : ∀ (ws : Fin k → List Bool) (e : List Bool),
      G (wordsCfg x none ws ([] ++ e)) = wordsCfg x none (snocW ws e) [] := by
    intro ws e
    refine Cfg.ext rfl rfl ?_ rfl rfl
    funext l
    induction l using Fin.lastCases <;> simp [G, wordsCfg, snocW]
  dsimp only [outputToWord]
  rw [hleft, run_interpret_runOracleConfigFrom_seq _ _ oracle (OutputToTape.config cfg₀)
    time (l + 2) s hhalt₁ hhalt₂]
  constructor
  · rw [houtRun, ProbOracleComp.runWith_map, PMF.bind_map, PMF.map_bind]
    trans ((ProbOracleComp.runWith oracle (machine.runOracleConfigFrom time cfg₀) s).bind
      (fun a => PMF.pure (G a.1.tapes, a.2)))
    · apply PMF.bind_congr_on_support
      intro ⟨mid, s₁⟩ hmid
      dsimp only [Function.comp_def, Prod.map_apply, id_eq]
      obtain ⟨⟨a, ha, hmidTapes⟩, _⟩ := h.mem_support oracle s cfg₀ rfl hbuf hmid
      rw [run_interpret_runOracleConfigFrom_ofDeterministic, hstartG mid a hmidTapes,
        runFrom_rewindLast_gen (hl OracleState oracle s a s₁ ha), hmidTapes, hG]
      simp only [Sequential.right, Cfg.mapState, PMF.pure_map, wordsCfg_state, Option.map_none,
        wordsCfg_inputPos, wordsCfg_output]
      rfl
    · have hlaw := (h OracleState oracle s cfg₀ rfl hbuf).1
      have hmapOut := congrArg
        (PMF.map (fun (p : Cfg k Bool State x × OracleState) => (G p.1, p.2))) hlaw
      change (ProbOracleComp.runWith oracle (machine.runOracleConfigFrom time cfg₀) s).bind
        (PMF.pure ∘ fun a => (G a.1.tapes, a.2)) = _
      rw [PMF.bind_pure_comp]
      simp only [PMF.map_comp, Function.comp_def, hG] at hmapOut
      simpa only [List.nil_append] using hmapOut
  · intro final hfinal op
    supp_cases hfinal [houtRun, ProbOracleComp.runWith_map, rew,
      run_interpret_runOracleConfigFrom_ofDeterministic] with ⟨_, ⟨⟨mid₀, s₁⟩, hmid₀, rfl⟩, rfl⟩
    exact (h.mem_support oracle s cfg₀ rfl hbuf hmid₀).2 op

end Turing.MultiTapePTM
