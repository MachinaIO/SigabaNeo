import SigabaNeoStd.Machines.Inline.Oracle

/-!
# Inlining an oracle handler: the simulation part on its own

The simulation, query and handler phases of `Inline.machine` never enter a preparation state. So
they form a machine `Inline.simM` on the control states `Ctl SA H` alone, and every machine whose
transitions on `Sum.inr c` are those of `simM` (relabelled) runs, from a simulation configuration,
like `simM`. This transfers the correctness of the simulation (`lawR_embA`) to inlined machines
with a different preparation (`Inline.LinDefs`).

* `Inline.simM`: the simulation part, with state type `Ctl SA H`;
* `Inline.tr_inr_mapState`: the transitions of `Inline.machine` from simulation states lead to
  simulation states;
* `Inline.law_mapState_inr`: the transfer of run laws along `Sum.inr`.
-/

namespace SigabaNeo.Inline

open Cslib Turing MultiTapeMachine

variable {kA ops m : ℕ} {SA : Type} (H : Fin ops → Routine (m + 3))
  (M : MultiTapePTM kA Bool SA (Fin ops)) (T : ℕ) (w : List Bool) {x : List Bool}

/-- The initial simulation state. -/
def ctl0 : Ctl SA H := ((M.initial, fun _ => .empty), none)

/-- Back from the states of `Inline.machine` to the simulation states (the preparation states, never
reached from a simulation state, go to the initial one). -/
def toCtl : RState SA H T w → Ctl SA H := Sum.elim (fun _ => ctl0 H M) id

/-- **The simulation part** of the inlined machine. -/
def simM : MultiTapePTM (nTapes kA ops m) Bool (Ctl SA H) (Fin 0) where
  initial := ctl0 H M
  tr c inp work ans := fun bit => ((machine H M T w).tr (.inr c) inp work ans bit).mapState
    (toCtl H M T w)

theorem mapState_stepR_mkAct {S S' : Type} (e : S → S') (d : SignType)
    (W : Tape kA ops m → Option (Option Bool) × SignType) (o : Option Bool) (q : Option S) :
    (stepR (mkAct d W o q)).mapState e = stepR (mkAct d W o (q.map e)) := rfl

/-- The transitions of `Inline.machine` from simulation states stay in simulation states. -/
theorem tr_inr_mapState (c : Ctl SA H) inp work ans bit :
    ((machine H M T w).tr (.inr c) inp work ans bit).mapState
      (Sum.inr ∘ toCtl H M T w) = (machine H M T w).tr (.inr c) inp work ans bit := by
  rcases c with ⟨⟨q, fl⟩, _ | ⟨o, ph | h⟩⟩
  · simp only [machine, simAct]
    split_ifs
    · rfl
    · cases M.tr q inp (fun i => work (Tape.work i).idx) (fun o => work (Tape.ans o).idx) bit with
      | step act sy mv =>
        simp only [mapState_stepR_mkAct, Option.map_map]
        rfl
      | query o nx => rfl
  · simp only [machine]
    cases ph <;> simp only [qAct] <;> (try split_ifs) <;> rfl
  · simp only [machine, hAct]
    cases (H o).machine.tr h none (fun j => work (hTape o j).idx) (fun e => e.elim) bit with
    | step a _ _ =>
      simp only [mapState_stepR_mkAct]
      cases a.state <;> rfl
    | query e _ => exact e.elim

/-- The run law of a channel-free fair-coin machine. -/
noncomputable def lawM {k : ℕ} {S : Type} (Mc : MultiTapePTM k Bool S (Fin 0)) (N : ℕ)
    (cfg : Config k Bool S (Fin 0) x) : PMF (Config k Bool S (Fin 0) x × Unit) :=
  ProbOracleComp.runWith (fun e : Fin 0 × List Bool => e.1.elim0) (Mc.runOracleConfigFrom N cfg) ()

/-- **Transfer of run laws** along a relabelling of states that commutes with the transitions. -/
theorem lawM_mapState {k : ℕ} {S S' : Type} (Ms : MultiTapePTM k Bool S (Fin 0))
    (Mt : MultiTapePTM k Bool S' (Fin 0)) (f : S → S')
    (htr : ∀ q inp work ans bit, Mt.tr (f q) inp work ans bit = (Ms.tr q inp work ans bit).mapState f)
    (N : ℕ) (cfg : Config k Bool S (Fin 0) x) :
    lawM Mt N (cfg.mapState f) = (lawM Ms N cfg).map (fun r => (r.1.mapState f, r.2)) := by
  unfold lawM
  have h : Mt.runOracleConfigFrom N (Config.mapState f cfg) =
      Config.mapState f <$> Ms.runOracleConfigFrom N cfg :=
    MultiTapeMachine.runConfigFrom_mapState
      (Choose := ReaderT Bool Id)
      (spec := probOracleSpec (fun _ : Fin 0 × List Bool => List Bool))
      Ms Mt
      (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
      (fun _ _ => by simp only [Functor.map_map]; rfl)
      (fun op word => ProbOracleComp.query (op, word)) f
      (fun q inp work answer => funext (htr q inp work answer))
      N cfg
  rw [h, ProbOracleComp.runWith_map]
  rfl

theorem lawR_eq_lawM (N : ℕ) (cfg : Config (nTapes kA ops m) Bool (RState SA H T w) (Fin 0) x) :
    lawR H M T w N cfg = lawM (machine H M T w) N cfg := rfl

/-- The run law of `Inline.machine` from a simulation configuration is that of `simM`. -/
theorem lawR_mapState_inr (N : ℕ) (cfg : Config (nTapes kA ops m) Bool (Ctl SA H) (Fin 0) x) :
    lawR H M T w N (cfg.mapState Sum.inr) =
      (lawM (simM H M T w) N cfg).map (fun r => (r.1.mapState Sum.inr, r.2)) := by
  rw [lawR_eq_lawM]
  apply lawM_mapState
  intro q inp work ans bit
  simp only [simM]
  rw [← tr_inr_mapState H M T w q inp work ans bit]
  cases (machine H M T w).tr (.inr q) inp work ans bit with
  | step a sy mv =>
    simp only [MultiTapeMachine.Action.mapState, Option.map_map]
    rfl
  | query o nx => rfl

end SigabaNeo.Inline
