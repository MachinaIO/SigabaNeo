import SigabaNeo.Trusted.Machine
import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Deterministic

/-!
# Machines from deterministic Turing machines and polynomial-time certificates

A deterministic multi-tape Turing machine of cslib (`MultiTapeTM k Bool S` with finitely many
states) becomes a `Machine` with a clock (`Machine.ofTM`): its states are renamed into `Fin n` and
it ignores the coin. Its output law is the point mass on the output after `time` steps
(`Machine.run_ofTM`).

From a polynomial-time certificate of cslib-frontier (`ComputableInPolyTime f encIn encOut`), with
a clock at least the time bound on an input, the machine outputs exactly the encoded value of `f`
(`Machine.exists_of_computable`).
-/

namespace SigabaNeo

open Cslib Turing Turing.MultiTapeTM

/-- A deterministic machine with finitely many states, with the clock `time`. -/
noncomputable def Machine.ofTM {k : ℕ} {S : Type} [Finite S] (tm : MultiTapeTM k Bool S)
    (time : ℕ) : Machine :=
  ⟨k, Nat.card S, MultiTapePTM.ofDeterministic (tm.relabel (Finite.equivFin S)), time⟩

/-- The output law of a deterministic machine: the output after `time` steps. -/
theorem Machine.run_ofTM {k : ℕ} {S : Type} [Finite S] (tm : MultiTapeTM k Bool S) (time : ℕ)
    (x : List Bool) :
    (Machine.ofTM tm time).run x = PMF.pure (tm.runFrom (tm.initCfg x) time).output := by
  set tm' := tm.relabel (Finite.equivFin S)
  have h := MultiTapePTM.run_interpret_ofDeterministic (Oracle := Fin 0) tm'
    (ProbComp.uniform Bool) (fun o => o.elim0)
    (fun q (s : Unit) => (fun a => (a, s)) <$> ProbComp.unifOracle q)
    (Probability.PMF.uniformOfFintype Bool)
    (fun s => by
      rw [OracleComp.run_interpret_stateless]
      exact congrArg (PMF.map (fun bit => (bit, s))) (ProbComp.eval_uniform Bool)) time
    ((MultiTapePTM.ofDeterministic (Oracle := Fin 0) tm').initialConfig x) ()
  rw [OracleComp.run_interpret_stateless] at h
  have hout := congrArg (PMF.map Prod.fst) h
  rw [PMF.monad_map_eq_map, PMF.map_comp, PMF.pure_map] at hout
  change PMF.map id _ = _ at hout
  rw [PMF.map_id] at hout
  unfold Machine.run Machine.ofTM
  refine hout.trans ?_
  congr 1
  have hinit : ((MultiTapePTM.ofDeterministic (Oracle := Fin 0) tm').initialConfig x).tapes =
      (tm.initCfg x).mapState (Option.map (Finite.equivFin S)) := rfl
  rw [hinit, MultiTapeTM.runFrom_relabel]
  rfl

/-- **Machines from polynomial-time certificates**: a machine computing `f` within `t` steps,
with the clock `time ≥ t`, outputs exactly the encoded value of `f`. -/
theorem Machine.exists_of_computable {α β : Type*} {f : α → β} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {t s : ℕ → ℕ}
    (h : ComputableInTimeAndSpaceOfLength f encIn encOut t s) :
    ∃ (k : ℕ) (S : Type) (_ : Finite S) (tm : MultiTapeTM k Bool S),
      ∀ (time : ℕ) (a : α), t (encIn a).length ≤ time →
        (Machine.ofTM tm time).run (encIn a) = PMF.pure (encOut (f a)) := by
  obtain ⟨k, S, hS, tm, htm⟩ := h
  refine ⟨k, S, hS, tm, fun time a ht => ?_⟩
  rw [Machine.run_ofTM]
  congr 1
  obtain ⟨⟨u, hu, hout⟩, hrun, -⟩ := htm a
  have hhalt : (tm.runFrom (tm.initCfg (encIn a)) (t (encIn a).length)).Halted :=
    MultiTapeTM.runsInTime_iff_halted.mp hrun
  rw [MultiTapeTM.runFrom_eq_of_halt _ _ ht hhalt]
  rcases le_total u (t (encIn a).length) with hut | htu
  · rw [MultiTapeTM.runFrom_eq_of_halt _ _ hut hu]; exact hout
  · rw [← MultiTapeTM.runFrom_eq_of_halt _ _ htu hhalt]; exact hout

end SigabaNeo
