import SigabaNeoStd.Machines.Inline.InitPhases

/-!
# Inlining an oracle handler for a reduction

`Machine.inlineOracleInit A H w₀ E Q L` (`Inline.InitDefs`): on the input `x`, the oracle machine
`A` runs on the fixed word `w₀`, its queries answered by the handlers `H`, the handler state
starting as `x`; the output is `pairOut o u`, `o` the output of `A` and `u` the final state word.

## Main results

* `Machine.law_inlineOracleInit`: for every initial state `s₀` with `enc s₀ = x` and `InvS s₀`, the
  output and the `st` tape of the final configuration are distributed as
  `(pairOut o (enc s), tapeOfList (enc s))` for `(o, s)` drawn from `A.runWith oracle w₀ s₀`;
* `Machine.run_inlineOracleInit`: the output law is that of `pairOut o (enc s)`;
* `pairOut_injective` (`Inline.InitDefs`): the pairing is injective.

The hypotheses are those of `Machine.inlineOracleLin` (`Handles A H oracle enc InvS Q L`), and
`E` bounds the lengths of the encoded states satisfying `InvS`.
-/

namespace SigabaNeo.Inline

open Cslib Turing MultiTapeMachine

variable {kA ops m : ℕ} {x : List Bool}

/-! ### The invariant along the run of the oracle machine -/

section Inv

variable {SA σ : Type} (M : MultiTapePTM kA Bool SA (Fin ops))
  (oracle : Fin ops × List Bool → StateT σ PMF (List Bool)) (InvS : σ → Prop) (T : ℕ)
  (hInv : ∀ o b s, b.length ≤ T → InvS s → ∀ r ∈ (oracle (o, b) s).support, InvS r.2)
include hInv

/-- **The oracle keeps the invariant** along a run whose queries stay within `T`. -/
theorem lawA_inv : ∀ n (c : Config kA Bool SA (Fin ops) x) s, InvS s →
    (∀ o, (c.channels o).queryBuffer.length + n ≤ T) →
    ∀ r ∈ (lawA M oracle n c s).support, InvS r.2 := by
  intro n
  induction n with
  | zero =>
    intro c s hs _ r hr
    unfold lawA at hr
    rw [law_zero, PMF.mem_support_pure_iff] at hr
    subst hr; exact hs
  | succ n ih =>
    intro c s hs hbuf r hr
    unfold lawA at hr
    cases hc : c.tapes.state with
    | none =>
      rw [law_halted _ _ _ _ _ hc, PMF.mem_support_pure_iff] at hr
      subst hr; exact hs
    | some q =>
      rw [law_succ_live _ _ _ _ _ hc] at hr
      obtain ⟨bit, -, hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
      cases hM : M.tr q c.tapes.inputSymbol c.tapes.workTapeSymbols c.answerSymbols bit with
      | step act sy mv =>
        rw [hM] at hr
        refine ih _ s hs (fun o => ?_) r hr
        have := hbuf o
        have : (sy o).toList.length ≤ 1 := by cases sy o <;> simp
        simp only [Config.step, List.length_append]
        omega
      | query o nx =>
        rw [hM] at hr
        obtain ⟨r', hr', hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
        have hb := hbuf o
        refine ih _ r'.2 (hInv o _ s (by omega) hs r' hr') (fun o' => ?_) r hr
        by_cases ho : o' = o
        · subst ho; simp [Config.receive]; omega
        · have := hbuf o'
          simp only [Config.receive, Function.update_of_ne ho]
          omega

end Inv

/-! ### The simulation phase -/

section Sim

variable {SA : Type} (H : Fin ops → Routine (m + 3)) (M : MultiTapePTM kA Bool SA (Fin ops))
  (T : ℕ)

theorem mkR_mapState {S S' : Type} (f : S → S') (q : Option S) (ip : Fin (x.length + 2))
    (F : Tape kA ops m → ℤ → Option Bool) (P : Tape kA ops m → ℤ) (out : List Bool) :
    (mkR q ip F P out).mapState f = mkR (q.map f) ip F P out := rfl

/-- The start of the simulation. -/
abbrev simStart : Config (nTapes kA ops m) Bool (Ctl SA H) (Fin 0) x :=
  Sequential.start (simM H M T []) (cpEnd (x := x) T)

theorem simStart_eq :
    (simStart (x := x) H M T).mapState Sum.inr =
      embA H T [] (M.initialConfig x) (fun _ => .empty) x T := by
  rw [simStart, start_mkR, mkR_mapState]
  unfold embA
  congr 1
  · funext t
    rcases t with i | o | o | _ | _ | j <;>
      simp [cpF, frameF, MultiTapeMachine.initialConfig, Cfg.init]
  · funext t
    rcases t with i | o | o | _ | _ | j <;>
      simp [cpP, frameP, MultiTapeMachine.initialConfig, Cfg.init]

theorem projRP_mapState {S S' : Type} (f : S → S')
    (r : Config (nTapes kA ops m) Bool S (Fin 0) x × Unit) :
    projRP (r.1.mapState f, r.2) = projRP r := rfl

/-- The number of steps of the simulation phase. -/
abbrev simTime (T Q L ops : ℕ) : ℕ := T * (Q + 2 * L + 4 * ops + 9) + 1

/-- **The simulation phase**: it halts, and its output, `st` tape and `st` head are those of the
oracle machine run on `x`, the handler state starting as `x = enc s₀`. -/
theorem lawM_sim {σ : Type} (oracle : Fin ops × List Bool → StateT σ PMF (List Bool))
    (enc : σ → List Bool) (InvS : σ → Prop) (L Q : ℕ) (hQ : ∀ o, (H o).time ≤ Q)
    (hH : ∀ o b s, b.length ≤ T → InvS s → (H o).Runs (layout b [] (enc s))
      ((oracle (o, b) s).map (fun r => layout b r.1 (enc r.2))))
    (hInv : ∀ o b s, b.length ≤ T → InvS s → ∀ r ∈ (oracle (o, b) s).support,
      InvS r.2 ∧ r.1.length ≤ L) (s₀ : σ) (hs₀ : InvS s₀) (henc : enc s₀ = x) :
    (∀ r ∈ (lawM (simM H M T []) (simTime T Q L ops) (simStart (x := x) H M T)).support,
      r.1.tapes.state = none) ∧
    (lawM (simM H M T []) (simTime T Q L ops) (simStart (x := x) H M T)).map projRP =
      (lawA M oracle T (M.initialConfig x) s₀).map (projAP enc) := by
  have hgood : Good T L InvS T (M.initialConfig x) s₀ (fun _ => .empty) :=
    ⟨le_rfl, fun o => by simp [MultiTapeMachine.initialConfig],
      fun o => by simp [MultiTapeMachine.initialConfig],
      fun o => by simp [MultiTapeMachine.initialConfig], hs₀⟩
  have hpot : pot (M.initialConfig x) = 0 := by
    simp [pot, MultiTapeMachine.initialConfig]
  obtain ⟨h1, h2⟩ := lawR_embA' H M T [] oracle enc InvS L Q hQ hH hInv T _ s₀ _ hgood
    (simTime T Q L ops) (by rw [hpot])
  rw [henc, ← simStart_eq, lawR_mapState_inr] at h1 h2
  refine ⟨fun r hr => ?_, ?_⟩
  · have := h1 (r.1.mapState Sum.inr, r.2) ((PMF.mem_support_map_iff _ _ _).mpr ⟨r, hr, rfl⟩)
    simpa using this
  · rw [PMF.map_comp] at h2
    exact h2

end Sim

/-! ### Reading back a word -/

open Classical in
/-- The word on a tape holding a word (`[]` otherwise). -/
noncomputable def tapeWord (f : ℤ → Option Bool) : List Bool :=
  if h : ∃ u, tapeOfList u = f then h.choose else []

theorem tapeWord_tapeOfList (u : List Bool) : tapeWord (tapeOfList u) = u := by
  have h : ∃ v, tapeOfList v = tapeOfList u := ⟨u, rfl⟩
  rw [tapeWord, dite_eq_left_of_eq_true (eq_true h)]
  exact MultiTapePTM.tapeOfList_injective h.choose_spec

/-! ### The whole run -/

section Main

variable {SA : Type} (H : Fin ops → Routine (m + 3)) (M : MultiTapePTM kA Bool SA (Fin ops))
  (T : ℕ)

/-- The final output and `st` tape, from those of the simulation. -/
noncomputable def finProj (p : List Bool × (ℤ → Option Bool) × ℤ) : List Bool × (ℤ → Option Bool) :=
  (pairOut p.1 (tapeWord p.2.1), p.2.1)

theorem projR_right {S₀ S₁ : Type} (f : Config (nTapes kA ops m) Bool S₁ (Fin 0) x × Unit) :
    projR (Sequential.right (State₀ := S₀) f.1, f.2) = projR f := rfl

/-- **The law of the inlined machine for reductions**, for a machine `M` and a clock `T`. -/
theorem lawM_initM {σ : Type} (oracle : Fin ops × List Bool → StateT σ PMF (List Bool))
    (enc : σ → List Bool) (InvS : σ → Prop) (L Q E : ℕ) (hQ : ∀ o, (H o).time ≤ Q)
    (hH : ∀ o b s, b.length ≤ T → InvS s → (H o).Runs (layout b [] (enc s))
      ((oracle (o, b) s).map (fun r => layout b r.1 (enc r.2))))
    (hInv : ∀ o b s, b.length ≤ T → InvS s → ∀ r ∈ (oracle (o, b) s).support,
      InvS r.2 ∧ r.1.length ≤ L) (hE : ∀ s, InvS s → (enc s).length ≤ E)
    (s₀ : σ) (hs₀ : InvS s₀) (henc : enc s₀ = x) :
    (lawM (initM H M T) (inlineTimeInit T (clockDigits kA (T + 1)).length Q L ops E)
        ((initM H M T).initialConfig x)).map projR =
      (lawA M oracle T (M.initialConfig x) s₀).map
        (fun a => (pairOut a.1.tapes.output (enc a.2), tapeOfList (enc a.2))) := by
  have hx : x.length ≤ E := henc ▸ hE s₀ hs₀
  obtain ⟨hsim1, hsim2⟩ := lawM_sim H M T oracle enc InvS L Q hQ hH hInv s₀ hs₀ henc
  -- the simulation ends with a state word of length at most `E` on `st`, its head at `0`
  have hend : ∀ r ∈ (lawM (simM H M T []) (simTime T Q L ops) (simStart (x := x) H M T)).support,
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
  have hout : ∀ r ∈ (lawM (simM H M T []) (simTime T Q L ops) (simStart (x := x) H M T)).support,
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
  set μ := lawM (simM H M T []) (simTime T Q L ops) (simStart (x := x) H M T) with hμ
  have hK : ∀ r ∈ μ.support, ∀ f ∈ (lawM (outM (kA := kA) (ops := ops) (m := m)) (2 * E + 3)
      (Sequential.start outM r.1)).support, f.1.tapes.state = none := by
    intro r hr f hf
    obtain ⟨g, hg, -, hl⟩ := hout r hr
    rw [hl, PMF.mem_support_pure_iff] at hf
    rw [hf]; exact hg
  have hS := lawM_seq (simM H M T []) (outM (kA := kA) (ops := ops) (m := m)) (simTime T Q L ops)
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
    (2 * E + 4) (simTime T Q L ops + (2 * E + 3))
    (Sequential.start copyM (clkCfg (x := x) (S := LState Unit H (clockDigits kA (T + 1)).length) T))
    (by rw [hcp]; intro r hr; rw [PMF.mem_support_pure_iff] at hr; subst hr; rfl)
    (by rw [hcp]; intro r hr; rw [PMF.mem_support_pure_iff] at hr; subst hr; exact hS1)
  rw [hcp, PMF.pure_bind] at hC
  have hC1 := halted_of_bind (S₀ := CStep) (PMF.pure ((cpEnd (x := x) (kA := kA) (ops := ops)
    (m := m) T), ())) (fun r => lawM ((simM H M T []).seq outM) (simTime T Q L ops + (2 * E + 3))
      (Sequential.start ((simM H M T []).seq outM) r.1))
    (by intro r hr; rw [PMF.mem_support_pure_iff] at hr; subst hr; exact hS1)
  rw [PMF.pure_bind, ← hC] at hC1
  -- the clock
  have hclk := lawM_clock (kA := kA) (x := x) (m := m) H T
  have hP := lawM_seq (machineLin H (haltM (kA := kA) (ops := ops)) (T + 1))
    ((copyM (kA := kA) (ops := ops) (m := m)).seq ((simM H M T []).seq outM))
    (clkTime kA T) ((2 * E + 4) + (simTime T Q L ops + (2 * E + 3)))
    ((machineLin H (haltM (kA := kA) (ops := ops)) (T + 1)).initialConfig x)
    (by rw [hclk]; intro r hr; rw [PMF.mem_support_pure_iff] at hr; subst hr; rfl)
    (by rw [hclk]; intro r hr; rw [PMF.mem_support_pure_iff] at hr; subst hr; exact hC1)
  rw [hclk, PMF.pure_bind] at hP
  -- assemble
  have htime : inlineTimeInit T (clockDigits kA (T + 1)).length Q L ops E =
      clkTime kA T + ((2 * E + 4) + (simTime T Q L ops + (2 * E + 3))) := rfl
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

/-- **The law of the inlined machine for reductions**: when the input `x` encodes an initial
handler state `s₀` satisfying `InvS`, the output and the `st` tape of its final configuration are
`pairOut o (enc s)` and the tape of `enc s`, for `(o, s)` drawn from `A` on the fixed word `w₀`
against the oracle from `s₀`. -/
theorem Machine.law_inlineOracleInit {σ : Type} (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (w₀ : List Bool) (oracle : Fin ops × List Bool → StateT σ PMF (List Bool))
    (enc : σ → List Bool) (InvS : σ → Prop) (E Q L : ℕ) (hH : Handles A H oracle enc InvS Q L)
    (hE : ∀ s, InvS s → (enc s).length ≤ E) (s₀ : σ) (hs₀ : InvS s₀) (x : List Bool)
    (henc : enc s₀ = x) :
    (lawM (initM H (Inline.fixInput A.machine w₀) A.time)
        (inlineTimeInit A.time (clockDigits A.tapes (A.time + 1)).length Q L ops E)
        ((initM H (Inline.fixInput A.machine w₀) A.time).initialConfig x)).map projR =
      (A.runWith oracle w₀ s₀).map (fun r => (pairOut r.1 (enc r.2), tapeOfList (enc r.2))) := by
  rw [lawM_initM H (Inline.fixInput A.machine w₀) A.time oracle enc InvS L Q E hH.time_le hH.runs
    hH.inv hE s₀ hs₀ henc, ← fixCfg_initial, lawA_fixInput, PMF.map_comp]
  unfold Machine.runWith
  rw [MultiTapePTM.runOracle_eq_map, ProbOracleComp.runWith_map, PMF.map_comp]
  rfl

/-- **The output law of the inlined machine for reductions**: `A`'s output on `w₀` against the
oracle from `s₀` (with `enc s₀ = x`), paired with the encoded final state. -/
theorem Machine.run_inlineOracleInit {σ : Type} (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (w₀ : List Bool) (oracle : Fin ops × List Bool → StateT σ PMF (List Bool))
    (enc : σ → List Bool) (InvS : σ → Prop) (E Q L : ℕ) (hH : Handles A H oracle enc InvS Q L)
    (hE : ∀ s, InvS s → (enc s).length ≤ E) (s₀ : σ) (hs₀ : InvS s₀) (x : List Bool)
    (henc : enc s₀ = x) :
    (A.inlineOracleInit H w₀ E Q L).run x =
      (A.runWith oracle w₀ s₀).map (fun r => pairOut r.1 (enc r.2)) := by
  have h := congrArg (PMF.map Prod.fst)
    (A.law_inlineOracleInit H w₀ oracle enc InvS E Q L hH hE s₀ hs₀ x henc)
  rw [PMF.map_comp, PMF.map_comp] at h
  rw [Machine.run_eq_runWith _ (fun e : Fin 0 × List Bool => e.1.elim0) x (),
    Machine.inlineOracleInit, Machine.runWith_ofPTMOps, MultiTapePTM.runOracle_eq_map,
    ProbOracleComp.runWith_map, PMF.map_comp]
  exact h

end SigabaNeo
