import SigabaNeo.Lib.Machines.Inline.PerQuery
import SigabaNeo.Lib.Machines.Inline.InitCost

/-!
# Inlining per-query handlers

With handlers whose time depends on the query (`HandlesP A H oracle enc InvS q₀ q₁ L`: the handler
of a query `b` halts within `q₀ + q₁ |b|` steps), the inlined machines built for the uniform bound
`Q = q₀ + q₁ * ops` have the laws of `A` against the oracle (`Inline.lawR_embAP'`: each query bit
written by `A` prepays `q₁` steps of the handler). Since `A` writes at most one bit per channel per
step, the total time is linear in `A.time`, and the cost of the inlined machine for reductions is
at most a factor independent of `A` times `A.cost`.

## Main results

* `Machine.law_inlineOracleP`, `Machine.run_inlineOracleP` (`Machine.inlineOracle`);
* `Machine.law_inlineOracleLinP`, `Machine.run_inlineOracleLinP` (`Machine.inlineOracleLin`);
* `Machine.law_inlineOracleInitP`, `Machine.run_inlineOracleInitP` (`Machine.inlineOracleInit`);
* `Machine.time_inlineOracleInitP_le`:
  `time ≤ A.time * (q₀ + q₁ * ops + 2 L + 4 ops + 17) + 4 E + 21`;
* `Machine.cost_inlineOracleInitP_le`: `cost ≤ initFactorP H q₀ q₁ L |w₀| E * A.cost`, the factor
  depending only on `ops`, `m`, the numbers of states of the handlers, `q₀`, `q₁`, `L`, `|w₀|`
  and `E`.

In all of them the machine is the one of the uniform bound `Q = q₀ + q₁ * ops`.
-/

namespace SigabaNeo.Inline

open Cslib Turing MultiTapeMachine

variable {kA ops m : ℕ} {x : List Bool}

section Sim

variable {SA : Type} (H : Fin ops → Routine (m + 3)) (M : MultiTapePTM kA Bool SA (Fin ops))
  (T : ℕ) (w : List Bool)

/-- **Correctness of the simulation with per-query handlers.** -/
theorem lawR_embAP {σ : Type} (oracle : Fin ops × List Bool → StateT σ PMF (List Bool))
    (enc : σ → List Bool) (InvS : σ → Prop) (L q₀ q₁ : ℕ)
    (hH : ∀ o b s, b.length ≤ T → InvS s → (H o).RunsIn (q₀ + q₁ * b.length) (layout b [] (enc s))
      ((oracle (o, b) s).map (fun r => layout b r.1 (enc r.2))))
    (hInv : ∀ o b s, b.length ≤ T → InvS s → ∀ r ∈ (oracle (o, b) s).support,
      InvS r.2 ∧ r.1.length ≤ L) :
    ∀ n (c : Config kA Bool SA (Fin ops) x) s fl, Good T L InvS n c s fl →
      ∀ N, n * (q₀ + q₁ * ops + 2 * L + 4 * ops + 9) + potP q₁ c + 1 ≤ N →
      (∀ g ∈ (lawR H M T w N (embA H T w c fl (enc s) n)).support, g.1.tapes.state = none) ∧
      (lawR H M T w N (embA H T w c fl (enc s) n)).map projR =
        (lawA M oracle n c s).map (projA enc) := by
  intro n c s fl hg N hN
  obtain ⟨h1, h2⟩ := lawR_embAP' H M T w oracle enc InvS L q₀ q₁ hH hInv n c s fl hg N hN
  refine ⟨h1, ?_⟩
  have := congrArg (PMF.map (fun t : List Bool × (ℤ → Option Bool) × ℤ => (t.1, t.2.1))) h2
  rw [PMF.map_comp, PMF.map_comp] at this
  exact this

theorem potP_initialConfig (q₁ : ℕ) : potP q₁ (M.initialConfig x) = 0 := by
  simp [potP, pot, MultiTapeMachine.initialConfig]

/-- **The simulation phase**: it halts, and its output, `st` tape and `st` head are those of the
oracle machine run on `x`, the handler state starting as `x = enc s₀`. -/
theorem lawM_simP {σ : Type} (oracle : Fin ops × List Bool → StateT σ PMF (List Bool))
    (enc : σ → List Bool) (InvS : σ → Prop) (L q₀ q₁ : ℕ)
    (hH : ∀ o b s, b.length ≤ T → InvS s → (H o).RunsIn (q₀ + q₁ * b.length) (layout b [] (enc s))
      ((oracle (o, b) s).map (fun r => layout b r.1 (enc r.2))))
    (hInv : ∀ o b s, b.length ≤ T → InvS s → ∀ r ∈ (oracle (o, b) s).support,
      InvS r.2 ∧ r.1.length ≤ L) (s₀ : σ) (hs₀ : InvS s₀) (henc : enc s₀ = x) :
    (∀ r ∈ (lawM (simM H M T []) (simTime T (q₀ + q₁ * ops) L ops) (simStart (x := x) H M T)).support,
      r.1.tapes.state = none) ∧
    (lawM (simM H M T []) (simTime T (q₀ + q₁ * ops) L ops) (simStart (x := x) H M T)).map projRP =
      (lawA M oracle T (M.initialConfig x) s₀).map (projAP enc) := by
  have hgood : Good T L InvS T (M.initialConfig x) s₀ (fun _ => .empty) :=
    ⟨le_rfl, fun o => by simp [MultiTapeMachine.initialConfig],
      fun o => by simp [MultiTapeMachine.initialConfig],
      fun o => by simp [MultiTapeMachine.initialConfig], hs₀⟩
  have hpot : potP q₁ (M.initialConfig x) = 0 := by
    simp [potP, pot, MultiTapeMachine.initialConfig]
  obtain ⟨h1, h2⟩ := lawR_embAP' H M T [] oracle enc InvS L q₀ q₁ hH hInv T _ s₀ _ hgood
    (simTime T (q₀ + q₁ * ops) L ops) (by rw [hpot])
  rw [henc, ← simStart_eq, lawR_mapState_inr] at h1 h2
  refine ⟨fun r hr => ?_, ?_⟩
  · have := h1 (r.1.mapState Sum.inr, r.2) ((PMF.mem_support_map_iff _ _ _).mpr ⟨r, hr, rfl⟩)
    simpa using this
  · rw [PMF.map_comp] at h2
    exact h2


end Sim

section Main

variable {SA : Type} (H : Fin ops → Routine (m + 3)) (M : MultiTapePTM kA Bool SA (Fin ops))
  (T : ℕ)

/-- **The law of the inlined machine for reductions**, for a machine `M` and a clock `T`. -/
theorem lawM_initMP {σ : Type} (oracle : Fin ops × List Bool → StateT σ PMF (List Bool))
    (enc : σ → List Bool) (InvS : σ → Prop) (L q₀ q₁ E : ℕ)
    (hH : ∀ o b s, b.length ≤ T → InvS s → (H o).RunsIn (q₀ + q₁ * b.length) (layout b [] (enc s))
      ((oracle (o, b) s).map (fun r => layout b r.1 (enc r.2))))
    (hInv : ∀ o b s, b.length ≤ T → InvS s → ∀ r ∈ (oracle (o, b) s).support,
      InvS r.2 ∧ r.1.length ≤ L) (hE : ∀ s, InvS s → (enc s).length ≤ E)
    (s₀ : σ) (hs₀ : InvS s₀) (henc : enc s₀ = x) :
    (lawM (initM H M T) (inlineTimeInit T (clockDigits kA (T + 1)).length (q₀ + q₁ * ops) L ops E)
        ((initM H M T).initialConfig x)).map projR =
      (lawA M oracle T (M.initialConfig x) s₀).map
        (fun a => (pairOut a.1.tapes.output (enc a.2), tapeOfList (enc a.2))) := by
  have hx : x.length ≤ E := henc ▸ hE s₀ hs₀
  obtain ⟨hsim1, hsim2⟩ := lawM_simP H M T oracle enc InvS L q₀ q₁ hH hInv s₀ hs₀ henc
  -- the simulation ends with a state word of length at most `E` on `st`, its head at `0`
  have hend : ∀ r ∈ (lawM (simM H M T []) (simTime T (q₀ + q₁ * ops) L ops) (simStart (x := x) H M T)).support,
      ∃ u, u.length ≤ E ∧ projRP r = (r.1.tapes.output, tapeOfList u, 0) := by
    intro r hr
    have hm : projRP r ∈ ((lawA M oracle T (M.initialConfig x) s₀).map (projAP enc)).support := by
      rw [← hsim2]; exact (PMF.mem_support_map_iff _ _ _).mpr ⟨r, hr, rfl⟩
    obtain ⟨a, ha, hpa⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
    have hinv := lawA_inv M oracle InvS T (fun o b s hb hs r hr => (hInv o b s hb hs r hr).1) T
      _ s₀ hs₀ (fun o => by simp [MultiTapeMachine.initialConfig]) a ha
    refine ⟨enc a.2, hE _ hinv, ?_⟩
    rw [← hpa]
    simp only [projAP, Prod.mk.injEq, and_true]
    exact congrArg Prod.fst hpa
  -- the output phase from the end of the simulation
  have hout : ∀ r ∈ (lawM (simM H M T []) (simTime T (q₀ + q₁ * ops) L ops) (simStart (x := x) H M T)).support,
      ∃ f, f.1.tapes.state = none ∧ projR f = finProj (projRP r) ∧
        lawM (outM (kA := kA) (ops := ops) (m := m)) (2 * E + 3)
          (Sequential.start outM r.1) = PMF.pure f := by
    intro r hr
    obtain ⟨u, hu, hp⟩ := hend r hr
    simp only [projRP, Prod.mk.injEq] at hp
    obtain ⟨-, hst, hpos⟩ := hp
    rw [mkR_eta r.1, start_mkR, show (outM (kA := kA) (ops := ops) (m := m)).initial = .s0 from rfl,
      show 2 * E + 3 = 2 * u.length + 3 + (2 * E - 2 * u.length) by omega,
      lawM_out _ _ _ u hst _ _ hpos]
    refine ⟨_, rfl, ?_, rfl⟩
    simp [projR, finProj, projRP, mkR_workTapes, hst, tapeWord_tapeOfList]
  -- the simulation, then the output
  set μ := lawM (simM H M T []) (simTime T (q₀ + q₁ * ops) L ops) (simStart (x := x) H M T) with hμ
  have hK : ∀ r ∈ μ.support, ∀ f ∈ (lawM (outM (kA := kA) (ops := ops) (m := m)) (2 * E + 3)
      (Sequential.start outM r.1)).support, f.1.tapes.state = none := by
    intro r hr f hf
    obtain ⟨g, hg, -, hl⟩ := hout r hr
    rw [hl, PMF.mem_support_pure_iff] at hf
    rw [hf]; exact hg
  have hS := lawM_seq (simM H M T []) (outM (kA := kA) (ops := ops) (m := m)) (simTime T (q₀ + q₁ * ops) L ops)
    (2 * E + 3) (simStart (x := x) H M T) hsim1 hK
  have hS1 := halted_of_bind (S₀ := Ctl SA H) μ _ hK
  rw [← hS] at hS1
  -- the copy
  have hcp : lawM (copyM (kA := kA) (ops := ops) (m := m)) (2 * E + 4)
      (Sequential.start copyM (clkCfg (x := x) (S := LState Unit H (clockDigits kA (T + 1)).length)
        T)) = PMF.pure (cpEnd T, ()) := by
    rw [show 2 * E + 4 = 2 * x.length + 4 + (2 * E - 2 * x.length) by omega, lawM_copy,
      lawM_halted' _ _ _ rfl]
  have hC := lawM_seq (copyM (kA := kA) (ops := ops) (m := m)) ((simM H M T []).seq outM)
    (2 * E + 4) (simTime T (q₀ + q₁ * ops) L ops + (2 * E + 3))
    (Sequential.start copyM (clkCfg (x := x) (S := LState Unit H (clockDigits kA (T + 1)).length) T))
    (by rw [hcp]; intro r hr; rw [PMF.mem_support_pure_iff] at hr; subst hr; rfl)
    (by rw [hcp]; intro r hr; rw [PMF.mem_support_pure_iff] at hr; subst hr; exact hS1)
  rw [hcp, PMF.pure_bind] at hC
  have hC1 := halted_of_bind (S₀ := CStep) (PMF.pure ((cpEnd (x := x) (kA := kA) (ops := ops)
    (m := m) T), ())) (fun r => lawM ((simM H M T []).seq outM) (simTime T (q₀ + q₁ * ops) L ops + (2 * E + 3))
      (Sequential.start ((simM H M T []).seq outM) r.1))
    (by intro r hr; rw [PMF.mem_support_pure_iff] at hr; subst hr; exact hS1)
  rw [PMF.pure_bind, ← hC] at hC1
  -- the clock
  have hclk := lawM_clock (kA := kA) (x := x) (m := m) H T
  have hP := lawM_seq (machineLin H (haltM (kA := kA) (ops := ops)) (T + 1))
    ((copyM (kA := kA) (ops := ops) (m := m)).seq ((simM H M T []).seq outM))
    (clkTime kA T) ((2 * E + 4) + (simTime T (q₀ + q₁ * ops) L ops + (2 * E + 3)))
    ((machineLin H (haltM (kA := kA) (ops := ops)) (T + 1)).initialConfig x)
    (by rw [hclk]; intro r hr; rw [PMF.mem_support_pure_iff] at hr; subst hr; rfl)
    (by rw [hclk]; intro r hr; rw [PMF.mem_support_pure_iff] at hr; subst hr; exact hC1)
  rw [hclk, PMF.pure_bind] at hP
  -- assemble
  have htime : inlineTimeInit T (clockDigits kA (T + 1)).length (q₀ + q₁ * ops) L ops E =
      clkTime kA T + ((2 * E + 4) + (simTime T (q₀ + q₁ * ops) L ops + (2 * E + 3))) := rfl
  rw [htime]
  unfold initM
  rw [show ((machineLin H (haltM (kA := kA) (ops := ops)) (T + 1)).seq
      ((copyM (kA := kA) (ops := ops) (m := m)).seq ((simM H M T []).seq outM))).initialConfig x =
      Sequential.left _ ((machineLin H (haltM (kA := kA) (ops := ops)) (T + 1)).initialConfig x)
      from rfl, hP]
  erw [hC, hS]
  simp only [PMF.map_comp, PMF.map_bind]
  rw [← hμ]
  calc _ = μ.bind (PMF.pure ∘ (finProj ∘ projRP)) := by
        apply Probability.PMF.bind_congr_on_support
        intro a ha
        obtain ⟨f, -, hf, hl⟩ := hout a ha
        rw [hl, PMF.pure_map]
        exact congrArg PMF.pure hf
    _ = (μ.map projRP).map finProj := by rw [PMF.bind_pure_comp, PMF.map_comp]
    _ = _ := by
        rw [hsim2, PMF.map_comp]
        congr 1
        funext a
        simp [finProj, projAP, tapeWord_tapeOfList]


end Main

end SigabaNeo.Inline

namespace SigabaNeo

open Cslib Turing MultiTapeMachine Inline

variable {ops m : ℕ}

/-! ### `Machine.inlineOracle` -/

/-- **The law of the inlined machine with per-query handlers.** -/
theorem Machine.law_inlineOracleP {σ : Type} (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (oracle : Fin ops × List Bool → StateT σ PMF (List Bool)) (enc : σ → List Bool)
    (InvS : σ → Prop) (q₀ q₁ L : ℕ) (hH : HandlesP A H oracle enc InvS q₀ q₁ L) (s₀ : σ)
    (hs₀ : InvS s₀) (x : List Bool) :
    (lawR H A.machine A.time (enc s₀) (inlineTime A.time (enc s₀).length (q₀ + q₁ * ops) L ops)
        ((Inline.machine H A.machine A.time (enc s₀)).initialConfig x)).map projR =
      (A.runWith oracle x s₀).map (fun r => (r.1, tapeOfList (enc r.2))) := by
  unfold inlineTime
  rw [lawR_prep]
  have hgood : Good A.time L InvS A.time (A.machine.initialConfig x) s₀ (fun _ => .empty) :=
    ⟨le_rfl, fun o => by simp [MultiTapeMachine.initialConfig],
      fun o => by simp [MultiTapeMachine.initialConfig],
      fun o => by simp [MultiTapeMachine.initialConfig], hs₀⟩
  rw [(lawR_embAP H A.machine A.time (enc s₀) oracle enc InvS L q₀ q₁ hH.runs hH.inv
    A.time _ s₀ _ hgood _ (by rw [potP_initialConfig])).2]
  unfold Machine.runWith lawA
  rw [MultiTapePTM.runOracle_eq_map, ProbOracleComp.runWith_map, PMF.map_comp]
  rfl

/-- **The output law of the inlined machine with per-query handlers** is that of `A` against the
oracle. -/
theorem Machine.run_inlineOracleP {σ : Type} (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (oracle : Fin ops × List Bool → StateT σ PMF (List Bool)) (enc : σ → List Bool)
    (InvS : σ → Prop) (q₀ q₁ L : ℕ) (hH : HandlesP A H oracle enc InvS q₀ q₁ L) (s₀ : σ)
    (hs₀ : InvS s₀) (x : List Bool) :
    (A.inlineOracle H (enc s₀) (q₀ + q₁ * ops) L).run x = (A.runWith oracle x s₀).map Prod.fst := by
  have h := congrArg (PMF.map Prod.fst) (A.law_inlineOracleP H oracle enc InvS q₀ q₁ L hH s₀ hs₀ x)
  rw [PMF.map_comp, PMF.map_comp] at h
  rw [Machine.run_eq_runWith _ (fun e : Fin 0 × List Bool => e.1.elim0) x (),
    Machine.inlineOracle, Machine.runWith_ofPTMOps, MultiTapePTM.runOracle_eq_map,
    ProbOracleComp.runWith_map, PMF.map_comp]
  exact h

/-! ### `Machine.inlineOracleLin` -/

/-- **The law of the inlined machine with a short preparation, per-query handlers.** -/
theorem Machine.law_inlineOracleLinP {σ : Type} (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (oracle : Fin ops × List Bool → StateT σ PMF (List Bool)) (enc : σ → List Bool)
    (InvS : σ → Prop) (q₀ q₁ L : ℕ) (hH : HandlesP A H oracle enc InvS q₀ q₁ L) (s₀ : σ)
    (hs₀ : InvS s₀) (henc : enc s₀ = []) (x : List Bool) :
    (lawM (machineLin H A.machine A.time)
        (inlineTimeLin A.time (clockDigits A.tapes A.time).length (q₀ + q₁ * ops) L ops)
        ((machineLin H A.machine A.time).initialConfig x)).map projR =
      (A.runWith oracle x s₀).map (fun r => (r.1, tapeOfList (enc r.2))) := by
  obtain ⟨t, ht, hprep⟩ := lawLin_prep (x := x) H A.machine A.time
  unfold inlineTimeLin
  rw [show 4 * A.time + 4 * (clockDigits A.tapes A.time).length + 4 +
      (A.time * (q₀ + q₁ * ops + 2 * L + 4 * ops + 9) + 1) =
      t + ((4 * A.time + 4 * (clockDigits A.tapes A.time).length + 4 - t) +
        (A.time * (q₀ + q₁ * ops + 2 * L + 4 * ops + 9) + 1)) by omega,
    hprep, lawLin_start]
  have hgood : Good A.time L InvS A.time (A.machine.initialConfig x) s₀ (fun _ => .empty) :=
    ⟨le_rfl, fun o => by simp [MultiTapeMachine.initialConfig],
      fun o => by simp [MultiTapeMachine.initialConfig],
      fun o => by simp [MultiTapeMachine.initialConfig], hs₀⟩
  have := (lawR_embAP H A.machine A.time [] oracle enc InvS L q₀ q₁ hH.runs hH.inv
    A.time _ s₀ _ hgood
    ((4 * A.time + 4 * (clockDigits A.tapes A.time).length + 4 - t) +
      (A.time * (q₀ + q₁ * ops + 2 * L + 4 * ops + 9) + 1))
    (by rw [potP_initialConfig]; omega)).2
  rw [henc] at this
  rw [this]
  unfold Machine.runWith lawA
  rw [MultiTapePTM.runOracle_eq_map, ProbOracleComp.runWith_map, PMF.map_comp]
  rfl

/-- **The output law of the inlined machine with a short preparation, per-query handlers.** -/
theorem Machine.run_inlineOracleLinP {σ : Type} (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (oracle : Fin ops × List Bool → StateT σ PMF (List Bool)) (enc : σ → List Bool)
    (InvS : σ → Prop) (q₀ q₁ L : ℕ) (hH : HandlesP A H oracle enc InvS q₀ q₁ L) (s₀ : σ)
    (hs₀ : InvS s₀) (henc : enc s₀ = []) (x : List Bool) :
    (A.inlineOracleLin H (q₀ + q₁ * ops) L).run x = (A.runWith oracle x s₀).map Prod.fst := by
  have h := congrArg (PMF.map Prod.fst)
    (A.law_inlineOracleLinP H oracle enc InvS q₀ q₁ L hH s₀ hs₀ henc x)
  rw [PMF.map_comp, PMF.map_comp] at h
  rw [Machine.run_eq_runWith _ (fun e : Fin 0 × List Bool => e.1.elim0) x (),
    Machine.inlineOracleLin, Machine.runWith_ofPTMOps, MultiTapePTM.runOracle_eq_map,
    ProbOracleComp.runWith_map, PMF.map_comp]
  exact h

/-! ### `Machine.inlineOracleInit` -/

/-- **The law of the inlined machine for reductions, per-query handlers.** -/
theorem Machine.law_inlineOracleInitP {σ : Type} (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (w₀ : List Bool) (oracle : Fin ops × List Bool → StateT σ PMF (List Bool))
    (enc : σ → List Bool) (InvS : σ → Prop) (E q₀ q₁ L : ℕ)
    (hH : HandlesP A H oracle enc InvS q₀ q₁ L)
    (hE : ∀ s, InvS s → (enc s).length ≤ E) (s₀ : σ) (hs₀ : InvS s₀) (x : List Bool)
    (henc : enc s₀ = x) :
    (lawM (initM H (Inline.fixInput A.machine w₀) A.time)
        (inlineTimeInit A.time (clockDigits A.tapes (A.time + 1)).length (q₀ + q₁ * ops) L ops E)
        ((initM H (Inline.fixInput A.machine w₀) A.time).initialConfig x)).map projR =
      (A.runWith oracle w₀ s₀).map (fun r => (pairOut r.1 (enc r.2), tapeOfList (enc r.2))) := by
  rw [lawM_initMP H (Inline.fixInput A.machine w₀) A.time oracle enc InvS L q₀ q₁ E hH.runs
    hH.inv hE s₀ hs₀ henc, ← fixCfg_initial, lawA_fixInput, PMF.map_comp]
  unfold Machine.runWith
  rw [MultiTapePTM.runOracle_eq_map, ProbOracleComp.runWith_map, PMF.map_comp]
  rfl

/-- **The output law of the inlined machine for reductions, per-query handlers**: `A`'s output on
`w₀` against the oracle from `s₀` (with `enc s₀ = x`), paired with the encoded final state. -/
theorem Machine.run_inlineOracleInitP {σ : Type} (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (w₀ : List Bool) (oracle : Fin ops × List Bool → StateT σ PMF (List Bool))
    (enc : σ → List Bool) (InvS : σ → Prop) (E q₀ q₁ L : ℕ)
    (hH : HandlesP A H oracle enc InvS q₀ q₁ L)
    (hE : ∀ s, InvS s → (enc s).length ≤ E) (s₀ : σ) (hs₀ : InvS s₀) (x : List Bool)
    (henc : enc s₀ = x) :
    (A.inlineOracleInit H w₀ E (q₀ + q₁ * ops) L).run x =
      (A.runWith oracle w₀ s₀).map (fun r => pairOut r.1 (enc r.2)) := by
  have h := congrArg (PMF.map Prod.fst)
    (A.law_inlineOracleInitP H w₀ oracle enc InvS E q₀ q₁ L hH hE s₀ hs₀ x henc)
  rw [PMF.map_comp, PMF.map_comp] at h
  rw [Machine.run_eq_runWith _ (fun e : Fin 0 × List Bool => e.1.elim0) x (),
    Machine.inlineOracleInit, Machine.runWith_ofPTMOps, MultiTapePTM.runOracle_eq_map,
    ProbOracleComp.runWith_map, PMF.map_comp]
  exact h

/-- **The clock for per-query handlers**: linear in `A.time`, with slope
`q₀ + q₁ * ops + 2 L + 4 ops + 17`. -/
theorem Machine.time_inlineOracleInitP_le (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (w₀ : List Bool) (E q₀ q₁ L : ℕ) :
    (A.inlineOracleInit H w₀ E (q₀ + q₁ * ops) L).time ≤
      A.time * (q₀ + q₁ * ops + 2 * L + 4 * ops + 17) + 4 * E + 21 :=
  A.time_inlineOracleInit_le H w₀ E _ L

/-- The factor of the cost bound for per-query handlers: it depends only on `ops`, `m`, the
numbers of states of the handlers, `q₀`, `q₁`, `L`, `|w₀|` and `E`. -/
def initFactorP (H : Fin ops → Routine (m + 3)) (q₀ q₁ L wl E : ℕ) : ℕ :=
  initFactor H (q₀ + q₁ * ops) L wl E

/-- **Cost of the inlined machine for reductions, per-query handlers**:
`cost ≤ initFactorP H q₀ q₁ L |w₀| E * A.cost`. -/
theorem Machine.cost_inlineOracleInitP_le (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (w₀ : List Bool) (E q₀ q₁ L : ℕ) :
    (A.inlineOracleInit H w₀ E (q₀ + q₁ * ops) L).cost ≤
      initFactorP H q₀ q₁ L w₀.length E * A.cost :=
  A.cost_inlineOracleInit_le H w₀ E _ L

end SigabaNeo
