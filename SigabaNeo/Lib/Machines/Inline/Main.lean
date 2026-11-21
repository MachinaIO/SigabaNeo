import SigabaNeo.Lib.Machines.Inline.Sim

/-!
# Inlining an oracle handler: correctness of the simulation

`lawR_embA`: from the simulation of a configuration `c` of the oracle machine with `n` steps left
on the clock, the inlined machine halts within `n * K + pot c + 1` steps, where
`K = Q + 2 L + 4 ops + 9` (`Q` bounds the handlers' clocks, `L` the answer lengths) and `pot c` is
three times the query lengths plus the answer head distances; and the joint law of its output and
of its `st` tape is that of the output and of the encoded final handler state of the oracle
machine run for `n` steps against the oracle.
-/

namespace SigabaNeo.Inline

open Cslib Turing MultiTapeMachine

variable {kA ops m : ℕ} {SA : Type} (H : Fin ops → Routine (m + 3))
  (M : MultiTapePTM kA Bool SA (Fin ops)) (T : ℕ) (w : List Bool) {x : List Bool}

/-- The potential of a configuration: thrice the length of each query, plus the distance of each
answer head from the start of a nonempty answer. -/
def pot (c : Config kA Bool SA (Fin ops) x) : ℕ :=
  ∑ o, (3 * (c.channels o).queryBuffer.length +
    (if (c.channels o).answer = [] then 0 else (c.channels o).answerPos.natAbs))

/-- The law of the oracle machine. -/
noncomputable def lawA {σ : Type} (oracle : Fin ops × List Bool → StateT σ PMF (List Bool))
    (n : ℕ) (c : Config kA Bool SA (Fin ops) x) (s : σ) :
    PMF (Config kA Bool SA (Fin ops) x × σ) :=
  ProbOracleComp.runWith oracle (M.runOracleConfigFrom n c) s

/-- The output and the `st` tape of the inlined machine. -/
def projR {S : Type} (r : Config (nTapes kA ops m) Bool S (Fin 0) x × Unit) :
    List Bool × (ℤ → Option Bool) :=
  (r.1.tapes.output, r.1.tapes.workTapes (Tape.st (kA := kA) (ops := ops) (m := m)).idx)

/-- The output and the encoded handler state of the oracle machine. -/
def projA {σ : Type} (enc : σ → List Bool) (r : Config kA Bool SA (Fin ops) x × σ) :
    List Bool × (ℤ → Option Bool) :=
  (r.1.tapes.output, tapeOfList (enc r.2))

/-- The invariant of the simulation. -/
structure Good {σ : Type} (L : ℕ) (InvS : σ → Prop) (n : ℕ) (c : Config kA Bool SA (Fin ops) x)
    (s : σ) (fl : Fin ops → AFlag) : Prop where
  n_le : n ≤ T
  buf_le : ∀ o, (c.channels o).queryBuffer.length + n ≤ T
  ans_le : ∀ o, (c.channels o).answer.length ≤ L
  flags : FlagOK c fl
  inv : InvS s

theorem pot_receive (c : Config kA Bool SA (Fin ops) x) (o : Fin ops) (nx : SA) (a : List Bool) :
    pot (c.receive o nx a) + (3 * (c.channels o).queryBuffer.length +
      (if (c.channels o).answer = [] then 0 else (c.channels o).answerPos.natAbs)) = pot c := by
  unfold pot
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ o),
    ← Finset.add_sum_erase _ (fun o' => 3 * (c.channels o').queryBuffer.length +
      (if (c.channels o').answer = [] then 0 else (c.channels o').answerPos.natAbs))
      (Finset.mem_univ o)]
  have h0 : 3 * ((c.receive o nx a).channels o).queryBuffer.length +
      (if ((c.receive o nx a).channels o).answer = [] then 0
        else ((c.receive o nx a).channels o).answerPos.natAbs) = 0 := by
    simp [Config.receive]
  rw [h0, Finset.sum_congr rfl (g := fun o' => 3 * (c.channels o').queryBuffer.length +
      (if (c.channels o').answer = [] then 0 else (c.channels o').answerPos.natAbs))]
  · ring
  · intro o' ho'
    have : o' ≠ o := Finset.ne_of_mem_erase ho'
    simp [Config.receive, Function.update_of_ne this]

theorem pot_step (c : Config kA Bool SA (Fin ops) x) (act : Turing.Action kA Bool SA)
    (sy : Fin ops → Option Bool) (mv : Fin ops → SignType) :
    pot (c.step act sy mv) ≤ pot c + 4 * ops := by
  unfold pot
  calc ∑ o, (3 * ((c.step act sy mv).channels o).queryBuffer.length +
        (if ((c.step act sy mv).channels o).answer = [] then 0
          else ((c.step act sy mv).channels o).answerPos.natAbs))
      ≤ ∑ o : Fin ops, ((3 * (c.channels o).queryBuffer.length +
        (if (c.channels o).answer = [] then 0 else (c.channels o).answerPos.natAbs)) + 4) := by
        apply Finset.sum_le_sum
        intro o _
        simp only [Config.step, List.length_append]
        have h1 : (sy o).toList.length ≤ 1 := by cases sy o <;> simp
        have h2 : ((c.channels o).answerPos + (mv o : ℤ)).natAbs ≤
            (c.channels o).answerPos.natAbs + 1 := by
          rcases mv o with _ | _ | _ <;> simp <;> omega
        by_cases ha : (c.channels o).answer = [] <;> simp only [ha, if_true, if_false] <;> omega
    _ = _ := by rw [Finset.sum_add_distrib]; simp [mul_comm]

theorem symbols_embA (c : Config kA Bool SA (Fin ops) x) (fl : Fin ops → AFlag) (s : List Bool)
    (n : ℕ) (t : Tape kA ops m) :
    (embA H T w c fl s n).tapes.workTapeSymbols t.idx = frameF T c s t (frameP c n t) := by
  simp [embA]

theorem projR_embA (c : Config kA Bool SA (Fin ops) x) (fl : Fin ops → AFlag) (s : List Bool)
    (n : ℕ) : projR (embA H T w c fl s n, ()) = (c.tapes.output, tapeOfList s) := by
  simp [projR, embA, mkR_workTapes, frameF]

theorem lawR_of_halted (cfg : Config (nTapes kA ops m) Bool (RState SA H T w) (Fin 0) x)
    (h : cfg.tapes.state = none) (N : ℕ) : lawR H M T w N cfg = PMF.pure (cfg, ()) :=
  law_halted _ _ _ _ _ h

theorem lawR_embA_halted (c : Config kA Bool SA (Fin ops) x) (hc : c.tapes.state = none)
    (fl : Fin ops → AFlag) (s : List Bool) (n N : ℕ) :
    lawR H M T w N (embA H T w c fl s n) = PMF.pure (embA H T w c fl s n, ()) :=
  law_halted _ _ _ _ _ (by simp [embA, hc])

/-- **Correctness of the simulation.** -/
theorem lawR_embA {σ : Type} (oracle : Fin ops × List Bool → StateT σ PMF (List Bool))
    (enc : σ → List Bool) (InvS : σ → Prop) (L Q : ℕ) (hQ : ∀ o, (H o).time ≤ Q)
    (hH : ∀ o b s, b.length ≤ T → InvS s → (H o).Runs (layout b [] (enc s))
      ((oracle (o, b) s).map (fun r => layout b r.1 (enc r.2))))
    (hInv : ∀ o b s, b.length ≤ T → InvS s → ∀ r ∈ (oracle (o, b) s).support,
      InvS r.2 ∧ r.1.length ≤ L) :
    ∀ n (c : Config kA Bool SA (Fin ops) x) s fl, Good T L InvS n c s fl →
      ∀ N, n * (Q + 2 * L + 4 * ops + 9) + pot c + 1 ≤ N →
      (∀ g ∈ (lawR H M T w N (embA H T w c fl (enc s) n)).support, g.1.tapes.state = none) ∧
      (lawR H M T w N (embA H T w c fl (enc s) n)).map projR =
        (lawA M oracle n c s).map (projA enc) := by
  intro n
  induction n with
  | zero =>
    intro c s fl hg N hN
    unfold lawA
    rw [law_zero, PMF.pure_map]
    cases hc : c.tapes.state with
    | none =>
      rw [lawR_embA_halted H M T w c hc, PMF.pure_map, projR_embA]
      refine ⟨fun g hg' => ?_, rfl⟩
      rw [PMF.mem_support_pure_iff] at hg'; subst hg'; simp [embA, hc]
    | some q =>
      obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
      have hstep : lawR H M T w (N' + 1) (embA H T w c fl (enc s) 0) =
          lawR H M T w N' (mkR none (moveInputPos c.tapes.inputPos 0)
            (fun t => wr (frameF T c (enc s) t) (frameP c 0 t) ((noop t).1))
            (fun t => frameP c 0 t + (noop t).2) (c.tapes.output ++ (none : Option Bool).toList)) := by
        unfold embA
        rw [hc, Option.map_some]
        apply lawR_det
        intro bit
        simp only [machine, simS, simAct]
        rw [if_pos (by
          simp only [kind_idx, frameF, frameP, Nat.cast_zero, zero_sub]
          rw [show tapeOfList (List.replicate T true) (-1) = none from tapeOfList_negSucc _ 0]
          simp)]
      rw [hstep, lawR_of_halted H M T w _ rfl, PMF.pure_map]
      refine ⟨fun g hg' => by rw [PMF.mem_support_pure_iff] at hg'; subst hg'; rfl, ?_⟩
      simp [projR, projA, mkR_workTapes, noop, frameF]
  | succ n ih =>
    intro c s fl hg N hN
    cases hc : c.tapes.state with
    | none =>
      unfold lawA
      rw [lawR_embA_halted H M T w c hc, law_halted _ _ _ _ _ hc, PMF.pure_map, PMF.pure_map,
        projR_embA]
      refine ⟨fun g hg' => ?_, rfl⟩
      rw [PMF.mem_support_pure_iff] at hg'; subst hg'; simp [embA, hc]
    | some q =>
      obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
      have hlt : n < T := by have := hg.n_le; omega
      -- the reads of the simulation are those of the oracle machine
      have hinp : (embA H T w c fl (enc s) (n + 1)).tapes.inputSymbol = c.tapes.inputSymbol :=
        inputSymbol_congr rfl
      have hwork : (fun i => (embA H T w c fl (enc s) (n + 1)).tapes.workTapeSymbols
          (Tape.work i).idx) = c.tapes.workTapeSymbols := by
        funext i; rw [symbols_embA]; rfl
      have hans : (fun o => (embA H T w c fl (enc s) (n + 1)).tapes.workTapeSymbols
          (Tape.ans o).idx) = c.answerSymbols := by
        funext o; simp only [symbols_embA, frameF, frameP]; exact answer_read' _
      have hclock : (embA H T w c fl (enc s) (n + 1)).tapes.workTapeSymbols
          (Tape.clock (kA := kA) (ops := ops) (m := m)).idx = some true := by
        rw [symbols_embA]
        simp only [frameF, frameP, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
        rw [tapeOfList_ofNat]; simp [hlt]
      have hR : lawR H M T w (N' + 1) (embA H T w c fl (enc s) (n + 1)) =
          (ProbComp.eval (ProbComp.uniform Bool)).bind fun bit =>
            lawR H M T w N' ((embA H T w c fl (enc s) (n + 1)).step
              (simAct H M T w q fl (embA H T w c fl (enc s) (n + 1)).tapes.inputSymbol
                (embA H T w c fl (enc s) (n + 1)).tapes.workTapeSymbols bit)
              (fun _ => none) (fun _ => 0)) := by
        unfold lawR
        rw [law_succ_live _ _ N' _ () (q := simS H T w q fl) (by simp [embA, hc])]
        rfl
      have hA : lawA M oracle (n + 1) c s = (ProbComp.eval (ProbComp.uniform Bool)).bind fun bit =>
          stepLaw M oracle n c s
            (M.tr q c.tapes.inputSymbol c.tapes.workTapeSymbols c.answerSymbols bit) := by
        unfold lawA
        exact law_succ_live M oracle n c s hc
      -- each coin
      have hbit : ∀ bit,
          (∀ g ∈ (lawR H M T w N' ((embA H T w c fl (enc s) (n + 1)).step
              (simAct H M T w q fl (embA H T w c fl (enc s) (n + 1)).tapes.inputSymbol
                (embA H T w c fl (enc s) (n + 1)).tapes.workTapeSymbols bit)
              (fun _ => none) (fun _ => 0))).support, g.1.tapes.state = none) ∧
          (lawR H M T w N' ((embA H T w c fl (enc s) (n + 1)).step
              (simAct H M T w q fl (embA H T w c fl (enc s) (n + 1)).tapes.inputSymbol
                (embA H T w c fl (enc s) (n + 1)).tapes.workTapeSymbols bit)
              (fun _ => none) (fun _ => 0))).map projR =
            (stepLaw M oracle n c s
              (M.tr q c.tapes.inputSymbol c.tapes.workTapeSymbols c.answerSymbols bit)).map
              (projA enc) := by
        intro bit
        simp only [simAct, hclock, ne_eq, not_true_eq_false, if_false, hinp]
        rw [hwork, hans]
        cases hM : M.tr q c.tapes.inputSymbol c.tapes.workTapeSymbols c.answerSymbols bit with
        | step act sy mv =>
          simp only [stepLaw]
          have hrd : (fun o => (embA H T w c fl (enc s) (n + 1)).tapes.workTapeSymbols
              (Tape.ans (kA := kA) (m := m) o).idx) = fun o => tapeOfList (c.channels o).answer
                (if (c.channels o).answer = [] then 0 else (c.channels o).answerPos) := by
            funext o; simp [symbols_embA, frameF, frameP]
          rw [show c.answerSymbols = _ from hans.symm.trans hrd]
          have hemb := embA_step H T w (some (simS H T w q fl)) c fl (fun o => (hg.flags o).1)
            (enc s) n act sy mv (newFl fl (fun o => tapeOfList (c.channels o).answer
                (if (c.channels o).answer = [] then 0 else (c.channels o).answerPos)) mv)
          have hemb' : (embA H T w c fl (enc s) (n + 1)) = mkR (some (simS H T w q fl))
              c.tapes.inputPos (frameF T c (enc s)) (frameP c (n + 1)) c.tapes.output := by
            simp [embA, hc]
          rw [hemb', hemb]
          apply ih
          · refine ⟨by omega, fun o => ?_, fun o => ?_, hg.flags.step act sy mv, hg.inv⟩
            · have := hg.buf_le o
              simp only [Config.step, List.length_append]
              have : (sy o).toList.length ≤ 1 := by cases sy o <;> simp
              omega
            · simpa [Config.step] using hg.ans_le o
          · have := pot_step c act sy mv
            nlinarith
        | query op nx =>
          simp only [stepLaw]
          set b := (c.channels op).queryBuffer with hb
          have hblen : b.length + (n + 1) ≤ T := hg.buf_le op
          have hcfg : (embA H T w c fl (enc s) (n + 1)).step
              (mkAct 0 (mv1 .clock none (-1)) none (some (qS H T w nx fl op .cleanStart)))
              (fun _ => none) (fun _ => 0) =
              mkR (some (qS H T w nx fl op .cleanStart)) c.tapes.inputPos (frameF T c (enc s))
                (frameP c n) c.tapes.output := by
            simp only [embA, hc, Option.map_some, step_mkR, wr_mv1, pos_mv1, moveInputPos_zero,
              Option.toList_none, List.append_nil, wr_none]
            congr 1
            · exact update_self_eq _ _
            · funext t
              by_cases ht : t = .clock
              · subst ht; simp [frameP]; ring
              · rw [Function.update_of_ne ht]
                rcases t with i | o | o | _ | _ | j <;> simp_all [frameP]
          rw [hcfg]
          obtain ⟨j, hj, hq⟩ := lawR_query H M T w oracle enc s c fl n op nx hg.flags
            (hH op b s (by omega) hg.inv)
          -- the remaining clock after the query
          have hpot := pot_receive c op nx
          have hNj : j ≤ N' := by
            have := hQ op
            have := hg.ans_le op
            split_ifs at hj with ha <;> simp only [ha, if_true, if_false] at hpot <;>
              nlinarith [hpot []]
          obtain ⟨N'', rfl⟩ : ∃ N'', N' = j + N'' := ⟨N' - j, by omega⟩
          have hgood' : ∀ r ∈ (oracle (op, b) s).support,
              Good T L InvS n (c.receive op nx r.1) r.2
                (Function.update fl op (if r.1 = [] then .empty else .right)) ∧
              n * (Q + 2 * L + 4 * ops + 9) + pot (c.receive op nx r.1) + 1 ≤ N'' := by
            intro r hr
            obtain ⟨hinv, hlen⟩ := hInv op b s (by omega) hg.inv r hr
            have := hg.n_le
            refine ⟨⟨by omega, fun o => ?_, fun o => ?_, fun o => ?_, hinv⟩, ?_⟩
            · by_cases ho : o = op
              · subst ho; simp [Config.receive]; omega
              · have := hg.buf_le o
                simp [Config.receive, Function.update_of_ne ho]; omega
            · by_cases ho : o = op
              · subst ho; simpa [Config.receive] using hlen
              · simpa [Config.receive, Function.update_of_ne ho] using hg.ans_le o
            · by_cases ho : o = op
              · subst ho
                simp only [Config.receive, Function.update_self]
                refine ⟨by split_ifs <;> simp_all, fun ha hz => ?_⟩
                rw [tapeOfList_zero] at hz
                cases hra : r.1 <;> simp_all
              · simp only [Config.receive, Function.update_of_ne ho]
                exact hg.flags o
            · have h1 := hpot r.1
              have := hQ op
              have := hg.ans_le op
              split_ifs at hj with ha <;> simp only [ha, if_true, if_false] at h1 <;> nlinarith
          rw [hq N'' (fun r hr => (ih _ _ _ (hgood' r hr).1 N'' (hgood' r hr).2).1)]
          refine ⟨fun g hg' => ?_, ?_⟩
          · obtain ⟨r, hr, hg''⟩ := (PMF.mem_support_bind_iff _ _ _).mp hg'
            exact (ih _ _ _ (hgood' r hr).1 N'' (hgood' r hr).2).1 g hg''
          · rw [PMF.map_bind, PMF.map_bind]
            apply Probability.PMF.bind_congr_on_support
            intro r hr
            exact (ih _ _ _ (hgood' r hr).1 N'' (hgood' r hr).2).2
      rw [hR, hA]
      refine ⟨fun g hg' => ?_, ?_⟩
      · obtain ⟨bit, _, hg''⟩ := (PMF.mem_support_bind_iff _ _ _).mp hg'
        exact (hbit bit).1 g hg''
      · rw [PMF.map_bind, PMF.map_bind]
        congr 1
        funext bit
        exact (hbit bit).2

end SigabaNeo.Inline
