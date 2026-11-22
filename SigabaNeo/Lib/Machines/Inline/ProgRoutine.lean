import SigabaNeo.Lib.Machines.Inline.Routine
import SigabaNeo.Lib.Machines.Prog.Machine
import SigabaNeo.Lib.Machines.Prog.Frame

/-!
# Tape-language programs as routines

A well-formed program of the tape language (`SigabaNeo.Tape.Prog`), compiled, is a routine
(`Routine.ofProg`) whose specification (`Routine.Runs`) is the law of the program
(`Routine.runs_ofProg`), within the time bound of the compiler. This is how handlers of oracle
inlining (`Machine.inlineOracle`, `Machine.inlineOracleLin`) are written as programs.
-/

namespace SigabaNeo

open Cslib Turing MultiTapeMachine

namespace Routine

variable {k : ℕ}

/-- A program as a routine, with the clock `timeBound p L`. -/
noncomputable def ofProg (p : Tape.Prog k) (L : ℕ) : Routine k where
  State := p.State
  fintype := inferInstance
  decEq := Classical.decEq _
  machine := Tape.Prog.compile p
  time := Tape.Prog.timeBound p L

theorem states_ofProg (p : Tape.Prog k) (L : ℕ) : (ofProg p L).states = Fintype.card p.State := rfl

/-- **A compiled program runs as its law.** -/
theorem runs_ofProg (p : Tape.Prog k) (hp : p.WF) (L : ℕ) (ws₀ : Fin k → List Bool)
    (hL : Tape.maxLen ws₀ ≤ L) : (ofProg p L).Runs ws₀ (Tape.Prog.law p ws₀) := by
  have h := Tape.Prog.compile_runsWords p hp [] L ws₀ [] hL Unit
    (fun e : Empty × List Bool => e.1.elim) () ((ofProg p L).startCfg ws₀) rfl (fun op => op.elim)
  obtain ⟨h1, -⟩ := h
  rw [ProbOracleComp.runWith_sample, PMF.map_comp] at h1
  have key : ((ofProg p L).law (ofProg p L).time ((ofProg p L).startCfg ws₀)).map
      (fun f => f.1.tapes) = (Tape.Prog.law p ws₀).map (fun a => wordsCfg [] none a []) := by
    have := congrArg (PMF.map Prod.fst) h1
    rw [PMF.map_comp, PMF.map_comp] at this
    exact this
  refine ⟨fun f hf => ?_, ?_⟩
  · have hm : f.1.tapes ∈ ((Tape.Prog.law p ws₀).map (fun a => wordsCfg [] none a [])).support := by
      rw [← key]; exact (PMF.mem_support_map_iff _ _ _).mpr ⟨f, hf, rfl⟩
    obtain ⟨a, -, ha⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
    rw [← ha]
    exact ⟨rfl, fun _ => rfl⟩
  · have := congrArg (PMF.map fun t : Cfg k Bool _ [] => t.workTapes) key
    rw [PMF.map_comp, PMF.map_comp] at this
    exact this


/-- A framed program as a routine, with the clock `timeBoundT p ℓ` for per-tape bounds `ℓ`. -/
noncomputable def ofXProg (p : Tape.XProg k) (ℓ : Fin k → ℕ) : Routine k where
  State := p.State
  fintype := inferInstance
  decEq := Classical.decEq _
  machine := Tape.XProg.compile p
  time := Tape.XProg.timeBoundT p ℓ

/-- **A compiled framed program runs as its law**, within its per-tape time bound. -/
theorem runs_ofXProg (p : Tape.XProg k) (hp : p.WF) (ℓ : Fin k → ℕ) (ws₀ : Fin k → List Bool)
    (hℓ : Tape.Fits ws₀ ℓ) : (ofXProg p ℓ).Runs ws₀ (Tape.XProg.law p ws₀) := by
  have h := Tape.XProg.compile_runsWordsT p hp [] ℓ ws₀ [] hℓ Unit
    (fun e : Empty × List Bool => e.1.elim) () ((ofXProg p ℓ).startCfg ws₀) rfl (fun op => op.elim)
  obtain ⟨h1, -⟩ := h
  rw [ProbOracleComp.runWith_sample, PMF.map_comp] at h1
  have key : ((ofXProg p ℓ).law (ofXProg p ℓ).time ((ofXProg p ℓ).startCfg ws₀)).map
      (fun f => f.1.tapes) = (Tape.XProg.law p ws₀).map (fun a => wordsCfg [] none a []) := by
    have := congrArg (PMF.map Prod.fst) h1
    rw [PMF.map_comp, PMF.map_comp] at this
    exact this
  refine ⟨fun f hf => ?_, ?_⟩
  · have hm : f.1.tapes ∈ ((Tape.XProg.law p ws₀).map (fun a => wordsCfg [] none a [])).support := by
      rw [← key]; exact (PMF.mem_support_map_iff _ _ _).mpr ⟨f, hf, rfl⟩
    obtain ⟨a, -, ha⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
    rw [← ha]
    exact ⟨rfl, fun _ => rfl⟩
  · have := congrArg (PMF.map fun t : Cfg k Bool _ [] => t.workTapes) key
    rw [PMF.map_comp, PMF.map_comp] at this
    exact this

end Routine

end SigabaNeo
