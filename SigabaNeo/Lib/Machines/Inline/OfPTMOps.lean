import SigabaNeo.Trusted.Machine
import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Simulation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.RunsWords

/-!
# Machines from fair-coin oracle machines with finitely many states

A fair-coin machine of cslib-frontier with `ops` oracle channels (`MultiTapePTM k Bool S (Fin ops)`)
and a `Fintype` state type becomes a `Machine ops` with a clock (`Machine.ofPTMOps`): its states
are renamed into `Fin (Fintype.card S)` through `Fintype.equivFin`. Its description length is
expressed through `Fintype.card S` (`Machine.descLen_ofPTMOps`), and its stateful-oracle law is
that of the original machine (`Machine.runWith_ofPTMOps`).

For `ops = 0` the law of `Machine.run` is the oracle run against any (unused) oracle
(`Machine.run_eq_runWith`).
-/

namespace SigabaNeo

open Cslib Turing MultiTapeMachine

/-- Rename the states of a fair-coin machine along an equivalence, keeping its channels. -/
def ptmRename {k : ℕ} {S S' O : Type} (m : MultiTapePTM k Bool S O) (e : S ≃ S') :
    MultiTapePTM k Bool S' O where
  initial := e m.initial
  tr q a w ans := fun bit => (m.tr (e.symm q) a w ans bit).mapState e

theorem ptmRename_runConfigFrom {k : ℕ} {S S' O Query : Type} [DecidableEq O]
    {spec : OracleSpec.{0, 0} Query} (m : MultiTapePTM k Bool S O) (e : S ≃ S')
    (coin : OracleComp spec Bool) (query : O → List Bool → OracleComp spec (List Bool))
    {input : List Bool} (fuel : ℕ) (cfg : Config k Bool S O input) :
    (ptmRename m e).runConfigFrom coin query fuel (cfg.mapState e) =
      Config.mapState e <$> m.runConfigFrom coin query fuel cfg := by
  unfold MultiTapePTM.runConfigFrom
  apply MultiTapeMachine.runConfigFrom_mapState m (ptmRename m e)
    (fun {α} (choices : ReaderT Bool Id α) => choices <$> coin)
  · intro α β f choices
    rw [Functor.map_map]
    rfl
  · intro state inp work answer
    funext bit
    simp only [ptmRename, Equiv.symm_apply_apply]
    rfl

theorem ptmRename_initialConfig {k : ℕ} {S S' O : Type} (m : MultiTapePTM k Bool S O)
    (e : S ≃ S') (input : List Bool) :
    (ptmRename m e).initialConfig input = (m.initialConfig input).mapState e := rfl

theorem ptmRename_runOracle {k : ℕ} {S S' O : Type} [DecidableEq O] (m : MultiTapePTM k Bool S O)
    (e : S ≃ S') (fuel : ℕ) (input : List Bool) :
    (ptmRename m e).runOracle fuel input = m.runOracle fuel input := by
  simp only [MultiTapePTM.runOracle, MultiTapePTM.run, MultiTapePTM.runFrom,
    ptmRename_initialConfig, ptmRename_runConfigFrom, Functor.map_map]
  rfl

/-- A fair-coin machine with `ops` oracle channels and a finite state type, with the clock
`time`: its states are renamed into `Fin (Fintype.card S)`. -/
noncomputable def Machine.ofPTMOps {ops k : ℕ} {S : Type} [Fintype S]
    (m : MultiTapePTM k Bool S (Fin ops)) (time : ℕ) : Machine ops :=
  ⟨k, Fintype.card S, ptmRename m (Fintype.equivFin S), time⟩

@[simp] theorem Machine.tapes_ofPTMOps {ops k : ℕ} {S : Type} [Fintype S]
    (m : MultiTapePTM k Bool S (Fin ops)) (time : ℕ) : (Machine.ofPTMOps m time).tapes = k := rfl

@[simp] theorem Machine.states_ofPTMOps {ops k : ℕ} {S : Type} [Fintype S]
    (m : MultiTapePTM k Bool S (Fin ops)) (time : ℕ) :
    (Machine.ofPTMOps m time).states = Fintype.card S := rfl

@[simp] theorem Machine.time_ofPTMOps {ops k : ℕ} {S : Type} [Fintype S]
    (m : MultiTapePTM k Bool S (Fin ops)) (time : ℕ) : (Machine.ofPTMOps m time).time = time :=
  rfl

/-- The description length of `Machine.ofPTMOps`, through the number of states. -/
theorem Machine.descLen_ofPTMOps {ops k : ℕ} {S : Type} [Fintype S]
    (m : MultiTapePTM k Bool S (Fin ops)) (time : ℕ) :
    (Machine.ofPTMOps m time).descLen =
      6 * Fintype.card S * 3 ^ k * 3 ^ ops * Machine.entryBits k (Fintype.card S) ops := rfl

/-- **The stateful-oracle law** of `Machine.ofPTMOps` is that of the original machine. -/
theorem Machine.runWith_ofPTMOps {ops k : ℕ} {S σ : Type} [Fintype S]
    (m : MultiTapePTM k Bool S (Fin ops)) (time : ℕ)
    (oracle : Fin ops × List Bool → StateT σ PMF (List Bool)) (x : List Bool) (s : σ) :
    (Machine.ofPTMOps m time).runWith oracle x s =
      ProbOracleComp.runWith oracle (m.runOracle time x) s := by
  unfold Machine.runWith Machine.ofPTMOps
  rw [ptmRename_runOracle]

/-- Without channels, the oracle run of a fair-coin machine samples its closed run. -/
theorem MultiTapePTM.runOracle_fin_zero {k : ℕ} {S : Type} (m : MultiTapePTM k Bool S (Fin 0))
    (fuel : ℕ) (input : List Bool) :
    m.runOracle fuel input =
      ProbOracleComp.sample (m.run (ProbComp.uniform Bool) (fun o => o.elim0) fuel input) := by
  simp only [MultiTapePTM.runOracle, MultiTapePTM.run, MultiTapePTM.runFrom,
    MultiTapePTM.runConfigFrom, ProbOracleComp.sample, OracleComp.interpret_map,
    MultiTapeMachine.interpret_runConfigFrom]
  congr 2 with o : 1
  exact o.elim0

/-- The output law of a machine without oracles is its oracle run against any oracle. -/
theorem Machine.run_eq_runWith {σ : Type} (A : Machine)
    (oracle : Fin 0 × List Bool → StateT σ PMF (List Bool)) (x : List Bool) (s : σ) :
    A.run x = (A.runWith oracle x s).map Prod.fst := by
  unfold Machine.run Machine.runWith
  rw [MultiTapePTM.runOracle_fin_zero, ProbOracleComp.runWith_sample, PMF.map_comp]
  exact (PMF.map_id _).symm

end SigabaNeo
