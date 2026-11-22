import SigabaNeo.Lib.Machines.Inline.LinPrep

/-!
# Inlining an oracle handler with a short preparation

`Machine.inlineOracleLin A H Q L` runs the oracle machine `A : Machine ops` with its queries answered
by the handlers `H` as one closed `Machine`, like `Machine.inlineOracle A H w Q L`, but the handler
state starts blank (`w = []`) and the clock of `A.time` cells is written by a counting loop from the
`h = (clockDigits A.tapes A.time).length` digits of `A.time` in base `2 ^ (A.tapes + 1)`
(`Inline.machineLin`). Its number of states is `h + 4 + A.states * 3 ^ ops * Z`, so its cost is
linear in that of `A`.

## Main results

* `Machine.law_inlineOracleLin`, `Machine.run_inlineOracleLin`: the laws, as for
  `Machine.inlineOracle`, when the initial handler state is encoded by the empty word;
In `Inline.LinCost`:

* `Machine.tapes_inlineOracleLin`, `Machine.states_inlineOracleLin`, `Machine.time_inlineOracleLin`:
  `A.tapes + 2 ops + 2 + m` tapes, `h + 4 + A.states * 3 ^ ops * (1 + ∑ o, (9 + (H o).states))`
  states with `h ≤ Nat.size A.time` (`clockDigits_length_le_size`), the clock
  `4 T + 4 h + 4 + (T * (Q + 2 L + 4 ops + 9) + 1)`;
* `Machine.time_inlineOracleLin_le`: `time ≤ A.time * (Q + 2 L + 4 ops + 17) + 5`;
* `Machine.cost_inlineOracleLin_le`: `cost ≤ linFactor H Q L * A.cost`, where `linFactor H Q L`
  depends only on `ops`, `m`, the numbers of states of the handlers, `Q` and `L`.
-/

namespace SigabaNeo

open Cslib Turing MultiTapeMachine Inline

variable {ops m : ℕ}

/-- The clock of the inlined machine with a short preparation: the preparation (at most
`4 T + 4 h + 4` steps), then the simulation. -/
def inlineTimeLin (T h Q L ops : ℕ) : ℕ := (4 * T + 4 * h + 4) + (T * (Q + 2 * L + 4 * ops + 9) + 1)

/-- **The inlined machine with a short preparation**: `A` with its queries answered by the handlers
`H`, the handler state initially blank. -/
noncomputable def Machine.inlineOracleLin (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (Q L : ℕ) : Machine :=
  Machine.ofPTMOps (machineLin H A.machine A.time)
    (inlineTimeLin A.time (clockDigits A.tapes A.time).length Q L ops)

section Law

variable {kA : ℕ} {SA : Type} (H : Fin ops → Routine (m + 3)) (M : MultiTapePTM kA Bool SA (Fin ops))
  (T : ℕ) {x : List Bool}

/-- The start of the simulation, as a configuration of `Inline.simM`. -/
def startS (c : Config kA Bool SA (Fin ops) x) :
    Config (nTapes kA ops m) Bool (Ctl SA H) (Fin 0) x :=
  mkR (some (ctl0 H M)) c.tapes.inputPos (frameF T c []) (frameP c T) c.tapes.output

theorem embA_start :
    embA H T [] (M.initialConfig x) (fun _ => .empty) [] T =
      (startS H M T (M.initialConfig x)).mapState Sum.inr := by
  simp only [embA, startS, MultiTapeMachine.initialConfig, Cfg.init, Option.map_some]
  rfl

theorem finCfg_start :
    finCfg (x := x) H M T T = (startS H M T (M.initialConfig x)).mapState Sum.inr := by
  have hF : lF (kA := kA) (ops := ops) (m := m) [] T = frameF T (M.initialConfig x) [] := by
    funext t
    rcases t with i | o | o | _ | _ | j <;>
      simp [lF, frameF, MultiTapeMachine.initialConfig, Cfg.init]
  have hP : lP (kA := kA) (ops := ops) (m := m) 0 ((T : ℤ) - 1) = frameP (M.initialConfig x) T := by
    funext t
    rcases t with i | o | o | _ | _ | j <;>
      simp [lP, frameP, MultiTapeMachine.initialConfig, Cfg.init]
  simp only [finCfg, startS, hF, hP, MultiTapeMachine.initialConfig, Cfg.init]
  rfl

theorem projR_mapState {S S' : Type} (f : S → S')
    (r : Config (nTapes kA ops m) Bool S (Fin 0) x × Unit) :
    projR (r.1.mapState f, r.2) = projR r := rfl

/-- From the start of the simulation, the machine with the short preparation runs as
`Inline.machine` (with the same clock and a blank handler state). -/
theorem lawLin_start (N : ℕ) :
    (lawM (machineLin H M T) N (finCfg (x := x) H M T T)).map projR =
      (lawR H M T [] N (embA H T [] (M.initialConfig x) (fun _ => .empty) [] T)).map projR := by
  rw [finCfg_start, embA_start, lawR_mapState_inr,
    lawM_mapState (simM H M T []) (machineLin H M T) Sum.inr (fun _ _ _ _ _ => rfl),
    PMF.map_comp, PMF.map_comp]
  rfl

end Law

/-- **The law of the inlined machine with a short preparation**: when the initial handler state is
encoded by the empty word, the output and the state tape of its final configuration are distributed
as the output and the encoded final state of `A` against the oracle. -/
theorem Machine.law_inlineOracleLin {σ : Type} (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (oracle : Fin ops × List Bool → StateT σ PMF (List Bool)) (enc : σ → List Bool)
    (InvS : σ → Prop) (Q L : ℕ) (hH : Handles A H oracle enc InvS Q L) (s₀ : σ) (hs₀ : InvS s₀)
    (henc : enc s₀ = []) (x : List Bool) :
    (lawM (machineLin H A.machine A.time)
        (inlineTimeLin A.time (clockDigits A.tapes A.time).length Q L ops)
        ((machineLin H A.machine A.time).initialConfig x)).map projR =
      (A.runWith oracle x s₀).map (fun r => (r.1, tapeOfList (enc r.2))) := by
  obtain ⟨t, ht, hprep⟩ := lawLin_prep (x := x) H A.machine A.time
  unfold inlineTimeLin
  rw [show 4 * A.time + 4 * (clockDigits A.tapes A.time).length + 4 +
      (A.time * (Q + 2 * L + 4 * ops + 9) + 1) =
      t + ((4 * A.time + 4 * (clockDigits A.tapes A.time).length + 4 - t) +
        (A.time * (Q + 2 * L + 4 * ops + 9) + 1)) by omega,
    hprep, lawLin_start]
  have hgood : Good A.time L InvS A.time (A.machine.initialConfig x) s₀ (fun _ => .empty) :=
    ⟨le_rfl, fun o => by simp [MultiTapeMachine.initialConfig],
      fun o => by simp [MultiTapeMachine.initialConfig],
      fun o => by simp [MultiTapeMachine.initialConfig], hs₀⟩
  have hpot : pot (A.machine.initialConfig x) = 0 := by
    simp [pot, MultiTapeMachine.initialConfig]
  have := (lawR_embA H A.machine A.time [] oracle enc InvS L Q hH.time_le hH.runs hH.inv
    A.time _ s₀ _ hgood
    ((4 * A.time + 4 * (clockDigits A.tapes A.time).length + 4 - t) +
      (A.time * (Q + 2 * L + 4 * ops + 9) + 1)) (by rw [hpot]; omega)).2
  rw [henc] at this
  rw [this]
  unfold Machine.runWith lawA
  rw [MultiTapePTM.runOracle_eq_map, ProbOracleComp.runWith_map, PMF.map_comp]
  rfl

/-- **The output law of the inlined machine with a short preparation** is that of `A` against the
oracle, when the initial handler state is encoded by the empty word. -/
theorem Machine.run_inlineOracleLin {σ : Type} (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (oracle : Fin ops × List Bool → StateT σ PMF (List Bool)) (enc : σ → List Bool)
    (InvS : σ → Prop) (Q L : ℕ) (hH : Handles A H oracle enc InvS Q L) (s₀ : σ) (hs₀ : InvS s₀)
    (henc : enc s₀ = []) (x : List Bool) :
    (A.inlineOracleLin H Q L).run x = (A.runWith oracle x s₀).map Prod.fst := by
  have h := congrArg (PMF.map Prod.fst)
    (A.law_inlineOracleLin H oracle enc InvS Q L hH s₀ hs₀ henc x)
  rw [PMF.map_comp, PMF.map_comp] at h
  rw [Machine.run_eq_runWith _ (fun e : Fin 0 × List Bool => e.1.elim0) x (),
    Machine.inlineOracleLin, Machine.runWith_ofPTMOps, MultiTapePTM.runOracle_eq_map,
    ProbOracleComp.runWith_map, PMF.map_comp]
  exact h

end SigabaNeo
