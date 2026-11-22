import SigabaNeo.Lib.Machines.Compose.Steps

/-!
# A clocked phase is exact

`M.withClock` (cslib-frontier) runs `M` under a unary budget of `T` cells on a last work tape: from
`AuxiliaryTape.config c tape pos false`, with `T` cells of budget at `pos, …, pos + T - 1` and none
at `pos + T`, it runs exactly `2 T + 1` steps (`exact_withClock`), and its final configuration is
that of `T` steps of `M` (`law_withClock`), halted, with the clock head at `pos + T`. Running exactly
`2 T + 1` steps, whatever `M` does, is what lets a later phase start at a fixed time.

`exact_of_last`: a run is exact as soon as it is live one step before its end and halted at its end
(halted configurations are fixed points).
-/

namespace SigabaNeo.Compose

open Cslib Turing MultiTapeMachine

variable {k : ℕ} {S : Type} {x : List Bool}

/-- A halted configuration reached at step `i` is still there at step `j ≥ i`. -/
theorem mem_support_law_of_halted (M : MultiTapePTM k Bool S (Fin 0))
    (c : Config k Bool S (Fin 0) x) {i j : ℕ} (hij : i ≤ j) {r : Config k Bool S (Fin 0) x}
    (hr : r ∈ (law M i c).support) (hh : r.tapes.state = none) : r ∈ (law M j c).support := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [law_add, PMF.mem_support_bind_iff]
  exact ⟨r, hr, by rw [law_halted M d r hh]; simp⟩

/-- **Exactness from the last two steps.** -/
theorem exact_of_last (M : MultiTapePTM k Bool S (Fin 0)) (c : Config k Bool S (Fin 0) x) (t : ℕ)
    (hlive : ∀ r ∈ (law M t c).support, r.tapes.state = none →
      ∀ i < t, ∀ r ∈ (law M i c).support, r.tapes.state ≠ none)
    (hhalt : ∀ r ∈ (law M t c).support, r.tapes.state = none) : Exact M c t := by
  refine ⟨fun i hi r hr => ?_, hhalt⟩
  obtain ⟨r₀, hr₀⟩ := (law M t c).support_nonempty
  exact hlive r₀ hr₀ (hhalt r₀ hr₀) i hi r hr

/-- Liveness at the step before the end gives liveness before. -/
theorem live_of_live_pred (M : MultiTapePTM k Bool S (Fin 0)) (c : Config k Bool S (Fin 0) x)
    (t : ℕ) (h : ∀ r ∈ (law M t c).support, r.tapes.state ≠ none) :
    ∀ i ≤ t, ∀ r ∈ (law M i c).support, r.tapes.state ≠ none := by
  intro i hi r hr hh
  exact h r (mem_support_law_of_halted M c hi hr hh) hh

variable (M : MultiTapePTM k Bool S (Fin 0))

theorem hpure_uo {α : Type} (a : α) (s : Unit) :
    (OracleComp.interpret uo ((fun choices : ReaderT Bool Id α => choices <$> coin) (pure a))).run s =
      PMF.pure (a, s) := by
  change (OracleComp.interpret uo ((fun _ : Bool => a) <$> coin)).run s = _
  rw [run_interpret_uo, ProbComp.eval_map, PMF.map_comp]
  exact PMF.map_const _ _

theorem hcoin_uo (s : Unit) :
    (OracleComp.interpret uo coin).run s = (ProbComp.eval coin).map (fun bit => (bit, s)) :=
  run_interpret_uo _ _

theorem map_pair_inj {α : Type} {p q : PMF α} (h : p.map (fun a => (a, ())) = q.map (fun a => (a, ()))) :
    p = q := by
  have := congrArg (PMF.map Prod.fst) h
  simp only [PMF.map_comp, Function.comp_def] at this
  have e : ∀ r : PMF α, r.map (fun x => x) = r := PMF.map_id
  rwa [e, e] at this

/-- **The clocked run.** -/
theorem law_withClock (c : Config k Bool S (Fin 0) x) (tape : ℤ → Option Bool) (pos : ℤ) (T : ℕ)
    (hbudget : ∀ i : ℕ, i < T → tape (pos + i) = some true) (hstop : tape (pos + T) ≠ some true) :
    law M.withClock (2 * T + 1) (AuxiliaryTape.config c tape pos false) =
      (law M T c).map (fun f => AuxiliaryTape.stopped f tape (pos + T)) := by
  have h := MultiTapePTM.run_interpret_runConfigFrom_withClock_add M coin noQ uo
    (ProbComp.eval coin) hcoin_uo c tape pos T 0 () hbudget hstop
  simp only [Nat.add_zero] at h
  rw [law_eq_stateful, law_eq_stateful, PMF.map_comp] at h
  apply map_pair_inj
  rw [h, PMF.map_comp]
  rfl

/-- The clocked run, `j` source steps in. -/
theorem law_withClock_prefix (c : Config k Bool S (Fin 0) x) (tape : ℤ → Option Bool) (pos : ℤ)
    (j : ℕ) (hbudget : ∀ i : ℕ, i < j → tape (pos + i) = some true) :
    law M.withClock (2 * j) (AuxiliaryTape.config c tape pos false) =
      (law M j c).map (fun f => AuxiliaryTape.config f tape (pos + j) false) := by
  have h := Clock.run_interpret_prefix M (fun choices => choices <$> coin) (fun _ _ => hchoose _ _)
    noQ uo (fun a s => hpure_uo a s) c tape pos j () hbudget
  have e1 := law_eq_stateful M.withClock (2 * j) (AuxiliaryTape.config c tape pos false)
  have e2 := law_eq_stateful M j c
  unfold MultiTapePTM.runConfigFrom at e1 e2
  rw [e1, e2, PMF.map_comp] at h
  apply map_pair_inj
  rw [h, PMF.map_comp]
  rfl

/-- **The clocked run is exact.** -/
theorem exact_withClock (c : Config k Bool S (Fin 0) x) (tape : ℤ → Option Bool) (pos : ℤ) (T : ℕ)
    (hbudget : ∀ i : ℕ, i < T → tape (pos + i) = some true) (hstop : tape (pos + T) ≠ some true) :
    Exact M.withClock (AuxiliaryTape.config c tape pos false) (2 * T + 1) := by
  refine ⟨fun i hi r hr => ?_, fun r hr => ?_⟩
  · refine live_of_live_pred _ _ (2 * T) (fun r hr => ?_) i (by omega) r hr
    rw [law_withClock_prefix M c tape pos T hbudget, PMF.mem_support_map_iff] at hr
    obtain ⟨f, -, rfl⟩ := hr
    simp
  · rw [law_withClock M c tape pos T hbudget hstop, PMF.mem_support_map_iff] at hr
    obtain ⟨f, -, rfl⟩ := hr
    rfl

end SigabaNeo.Compose
