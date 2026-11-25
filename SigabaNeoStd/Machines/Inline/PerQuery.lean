import SigabaNeoStd.Machines.Inline.Oracle

/-!
# Inlining an oracle handler with per-query time bounds

`Routine.Runs` asks a routine to halt within its clock `time`. The inlined machine
(`Inline.machine`) runs a handler until it halts (it has no clock of its own for the handler), so
only the halting bound matters for the time accounting. `Routine.RunsIn H t ws₀ μ` is
`Routine.Runs` with an explicit halting bound `t` instead of `H.time`.

`HandlesP A H oracle enc InvS q₀ q₁ L` asks the handler of a query `b` to halt within
`q₀ + q₁ * |b|` steps (instead of a uniform bound `Q`). The time of the queries is then paid by
a potential `potP q₁ c = pot c + q₁ * ∑ₒ |queryBuffer o|`: each step of the oracle machine appends
at most one bit to each query buffer, so the potential grows by at most `q₁ * ops` per step, and
a query `b` releases `q₁ * |b|` of it.

## Main results

* `Routine.RunsIn.mono`, `Routine.runs_iff_runsIn`;
* `Inline.lawR_handlerP`, `Inline.lawR_queryP`: the handler and query phases with a halting
  bound `t`;
* `Inline.lawR_embAP'`: the correctness of the simulation where each simulated step costs
  `q₀ + q₁ * ops + 2 L + 4 ops + 9` steps — the same as `Inline.lawR_embA'` with
  `Q = q₀ + q₁ * ops`, so the inlined machines with the clock for `Q = q₀ + ops * q₁` serve
  per-query handlers (`Inline.InitPerQuery`).
-/

namespace SigabaNeo

open Cslib Turing MultiTapeMachine

namespace Routine

variable {k : ℕ}

/-- **Specification of a routine with the halting bound `t`.** From the words `ws₀` (heads at
the start), on every coin sequence the routine halts within `t` steps with every head at the
start, and the law of its final tapes is that of the words drawn from `μ`. -/
def RunsIn (H : Routine k) (t : ℕ) (ws₀ : Fin k → List Bool) (μ : PMF (Fin k → List Bool)) :
    Prop :=
  (∀ f ∈ (H.law t (H.startCfg ws₀)).support,
      f.1.tapes.state = none ∧ ∀ i, f.1.tapes.workTapePos i = 0) ∧
    (H.law t (H.startCfg ws₀)).map (fun f => f.1.tapes.workTapes) =
      μ.map (fun ws i => tapeOfList (ws i))

theorem runs_iff_runsIn (H : Routine k) (ws₀ : Fin k → List Bool) (μ : PMF (Fin k → List Bool)) :
    H.Runs ws₀ μ ↔ H.RunsIn H.time ws₀ μ := Iff.rfl

/-- A larger halting bound. -/
theorem RunsIn.mono {H : Routine k} {t t' : ℕ} {ws₀ : Fin k → List Bool}
    {μ : PMF (Fin k → List Bool)} (h : H.RunsIn t ws₀ μ) (ht : t ≤ t') : H.RunsIn t' ws₀ μ := by
  have e : H.law t' (H.startCfg ws₀) = H.law t (H.startCfg ws₀) := by
    unfold Routine.law
    rw [show t' = t + (t' - t) by omega]
    exact law_add_of_halted _ _ t (t' - t) _ () (fun f hf => (h.1 f hf).1)
  unfold RunsIn
  rw [e]
  exact h

end Routine

namespace Inline

variable {kA ops m : ℕ} {SA : Type} (H : Fin ops → Routine (m + 3))
  (M : MultiTapePTM kA Bool SA (Fin ops)) (T : ℕ) (w : List Bool) {x : List Bool}

/-! ### The handler and query phases with a halting bound -/

section

variable (q : SA) (fl : Fin ops → AFlag) (o : Fin ops) (ip : Fin (x.length + 2))
  (F : Tape kA ops m → ℤ → Option Bool) (P : Tape kA ops m → ℤ) (out : List Bool)

/-- **The handler phase**, with the halting bound `t`. -/
theorem lawR_handlerP (t : ℕ) (b s : List Bool) (μ : PMF (Fin (m + 3) → List Bool))
    (hspec : (H o).RunsIn t (layout b [] s) μ)
    (hF : ∀ j, F (hTape o j) = tapeOfList (layout b [] s j)) (hP : ∀ j, P (hTape o j) = 0)
    (N : ℕ)
    (hgood : ∀ ws ∈ μ.support, ∀ g ∈ (lawR H M T w N (mkR (some (qS H T w q fl o .qToEnd)) ip
      (withH o F (fun j => tapeOfList (ws j))) (withHP o P (fun _ => 0)) out)).support,
        g.1.tapes.state = none) :
    lawR H M T w (t + N) (mkR (some (hS H T w q fl o (H o).machine.initial)) ip F P out) =
      μ.bind (fun ws => lawR H M T w N (mkR (some (qS H T w q fl o .qToEnd)) ip
        (withH o F (fun j => tapeOfList (ws j))) (withHP o P (fun _ => 0)) out)) := by
  have hstart : mkR (some (hS H T w q fl o (H o).machine.initial)) ip F P out =
      simOrExit (embH H T w q fl o ip F P out) (exitH H T w q fl o ip F P out)
        ((H o).startCfg (layout b [] s)) := by
    simp only [simOrExit, Routine.startCfg, wordsCfg_state, reduceCtorEq, ite_false, embH,
      Option.map_some]
    congr 1
    · funext t
      simp only [withH]
      cases hp : hPre o t with
      | none => rfl
      | some j => rw [← hTape_of_hPre hp, hF]; rfl
    · funext t
      simp only [withHP, wordsCfg_workTapePos]
      cases hp : hPre o t with
      | none => rfl
      | some j => rw [← hTape_of_hPre hp, hP]
  -- the exit depends only on the final words, the heads being at the start
  have hexit : ∀ f ∈ ((H o).law t ((H o).startCfg (layout b [] s))).support,
      exitH H T w q fl o ip F P out f.1 = mkR (some (qS H T w q fl o .qToEnd)) ip
        (withH o F f.1.tapes.workTapes) (withHP o P (fun _ => 0)) out := by
    intro f hf
    simp only [exitH]
    rw [show f.1.tapes.workTapePos = fun _ => 0 from funext (hspec.1 f hf).2]
  have hwords : ∀ f ∈ ((H o).law t ((H o).startCfg (layout b [] s))).support,
      ∃ ws ∈ μ.support, f.1.tapes.workTapes = fun j => tapeOfList (ws j) := by
    intro f hf
    have : f.1.tapes.workTapes ∈ (μ.map (fun ws i => tapeOfList (ws i))).support := by
      rw [← hspec.2]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨f, hf, rfl⟩
    obtain ⟨ws, hws, he⟩ := (PMF.mem_support_map_iff _ _ _).mp this
    exact ⟨ws, hws, he.symm⟩
  rw [hstart]
  unfold lawR
  rw [law_simExit (H o).machine (machine H M T w)
    (fun e : Fin 0 × List Bool => e.1.elim0) (embH H T w q fl o ip F P out)
    (exitH H T w q fl o ip F P out)
    (fun c hc s => lawR_embH_one H M T w q fl o ip F P out c hc s) N t _ ()
    (fun f hf => (hspec.1 f hf).1) (by
      intro f hf g hg
      obtain ⟨ws, hws, he⟩ := hwords f hf
      rw [hexit f hf, he] at hg
      exact hgood ws hws g hg)]
  calc ((H o).law t ((H o).startCfg (layout b [] s))).bind
        (fun f => lawR H M T w N (exitH H T w q fl o ip F P out f.1))
      = ((H o).law t ((H o).startCfg (layout b [] s))).bind
        (fun f => lawR H M T w N (mkR (some (qS H T w q fl o .qToEnd)) ip
          (withH o F f.1.tapes.workTapes) (withHP o P (fun _ => 0)) out)) := by
        apply Probability.PMF.bind_congr_on_support
        intro f hf
        rw [hexit f hf]
    _ = (((H o).law t ((H o).startCfg (layout b [] s))).map
          (fun f => f.1.tapes.workTapes)).bind
        (fun tp => lawR H M T w N (mkR (some (qS H T w q fl o .qToEnd)) ip
          (withH o F tp) (withHP o P (fun _ => 0)) out)) := by
        rw [PMF.bind_map]; rfl
    _ = _ := by
        rw [hspec.2, PMF.bind_map]; rfl


end

/-- **A query** on `o` with next state `nx`, from the configuration `c` that submits it, is answered
within `|p| + 2 |a| + 3 |b| + 7 + time` steps (`p` the answer head, `a` the old answer, `b` the
query) by the law of the handler, after which the simulation resumes from `c` having received the
answer. -/
theorem lawR_queryP (t : ℕ) {σ : Type} (oracle : Fin ops × List Bool → StateT σ PMF (List Bool))
    (enc : σ → List Bool) (s : σ) (c : Config kA Bool SA (Fin ops) x) (fl : Fin ops → AFlag)
    (n : ℕ) (o : Fin ops) (nx : SA) (hfl : FlagOK c fl)
    (hspec : (H o).RunsIn t (layout (c.channels o).queryBuffer [] (enc s))
      ((oracle (o, (c.channels o).queryBuffer) s).map
        (fun r => layout (c.channels o).queryBuffer r.1 (enc r.2)))) :
    ∃ j ≤ (if (c.channels o).answer = [] then 0 else (c.channels o).answerPos.natAbs) +
        2 * (c.channels o).answer.length + 3 * (c.channels o).queryBuffer.length + 7 + t,
      ∀ N, (∀ r ∈ (oracle (o, (c.channels o).queryBuffer) s).support,
        ∀ g ∈ (lawR H M T w N (embA H T w (c.receive o nx r.1)
          (Function.update fl o (if r.1 = [] then .empty else .right)) (enc r.2) n)).support,
          g.1.tapes.state = none) →
      lawR H M T w (j + N) (mkR (some (qS H T w nx fl o .cleanStart)) c.tapes.inputPos
          (frameF T c (enc s)) (frameP c n) c.tapes.output) =
        (oracle (o, (c.channels o).queryBuffer) s).bind (fun r => lawR H M T w N
          (embA H T w (c.receive o nx r.1)
            (Function.update fl o (if r.1 = [] then .empty else .right)) (enc r.2) n)) := by
  obtain ⟨jc, hjc, hclean⟩ := lawR_clean H M T w nx fl o c.tapes.inputPos (frameF T c (enc s))
    (frameP c n) c.tapes.output (c.channels o).answer (c.channels o).answerPos rfl rfl
    (hfl o).1 (hfl o).2
  set b := (c.channels o).queryBuffer with hb
  refine ⟨jc + (b.length + 2 + (t + (2 * b.length + 2))), by omega, fun N hgood => ?_⟩
  rw [show jc + (b.length + 2 + (t + (2 * b.length + 2))) + N =
    jc + (b.length + 2 + (t + (2 * b.length + 2 + N))) by omega, hclean]
  rw [lawR_rewind H M T w nx fl o _ _ _ _ b (by simp [frameF, hb]) (by simp [frameP, hb])]
  have key : ∀ r : List Bool × σ, lawR H M T w (2 * b.length + 2 + N)
      (mkR (some (qS H T w nx fl o .qToEnd)) c.tapes.inputPos
        (withH o (Function.update (frameF T c (enc s)) (Tape.ans o) (fun _ => none))
          (fun j => tapeOfList (layout b r.1 (enc r.2) j)))
        (withHP o (Function.update (Function.update (frameP c n) (Tape.ans o) 0) (Tape.qry o) 0)
          (fun _ => 0)) c.tapes.output) =
      lawR H M T w N (embA H T w (c.receive o nx r.1)
        (Function.update fl o (if r.1 = [] then .empty else .right)) (enc r.2) n) := by
    intro r
    rw [lawR_eraseQuery H M T w nx fl o _ _ _ _ b (by simp [withH, hPre])
      (by simp [withHP, hPre])]
    exact congrArg _ (after_query H T w c fl n o nx (enc s) r.1 (enc r.2))
  have hF : ∀ j, Function.update (frameF (m := m) T c (enc s)) (Tape.ans o) (fun _ => none)
      (hTape o j) =
      tapeOfList (layout b [] (enc s) j) := by
    intro j
    unfold hTape layout
    split_ifs with h0 h1 h2 <;> simp [frameF, hb]
  have hP : ∀ j, Function.update (Function.update (frameP (m := m) c n) (Tape.ans o) 0)
      (Tape.qry o) 0
      (hTape o j) = 0 := by
    intro j
    unfold hTape
    split_ifs with h0 h1 h2 <;> simp [frameP]
  rw [lawR_handlerP H M T w nx fl o _ _ _ _ t b (enc s) _ hspec hF hP _ (by
    intro ws hws g hg
    obtain ⟨r, hr, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hws
    rw [key r] at hg
    exact hgood r hr g hg)]
  rw [PMF.bind_map]
  congr 1
  funext r
  exact key r

/-! ### The weighted potential -/

/-- The potential with the per-bit price `q₁` of the queries. -/
def potP (q₁ : ℕ) (c : Config kA Bool SA (Fin ops) x) : ℕ :=
  pot c + q₁ * ∑ o, (c.channels o).queryBuffer.length

theorem qlen_receive (c : Config kA Bool SA (Fin ops) x) (o : Fin ops) (nx : SA) (a : List Bool) :
    ∑ o', ((c.receive o nx a).channels o').queryBuffer.length +
      (c.channels o).queryBuffer.length = ∑ o', (c.channels o').queryBuffer.length := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ o),
    ← Finset.add_sum_erase _ (fun o' => (c.channels o').queryBuffer.length) (Finset.mem_univ o)]
  have h0 : ((c.receive o nx a).channels o).queryBuffer.length = 0 := by simp [Config.receive]
  rw [h0, Finset.sum_congr rfl (g := fun o' => (c.channels o').queryBuffer.length)]
  · ring
  · intro o' ho'
    have : o' ≠ o := Finset.ne_of_mem_erase ho'
    simp [Config.receive, Function.update_of_ne this]

theorem potP_receive (q₁ : ℕ) (c : Config kA Bool SA (Fin ops) x) (o : Fin ops) (nx : SA)
    (a : List Bool) :
    potP q₁ (c.receive o nx a) + (3 * (c.channels o).queryBuffer.length +
      (if (c.channels o).answer = [] then 0 else (c.channels o).answerPos.natAbs) +
      q₁ * (c.channels o).queryBuffer.length) = potP q₁ c := by
  have h1 := pot_receive c o nx a
  have h2 := qlen_receive c o nx a
  unfold potP
  rw [← h1, ← h2]
  ring

theorem qlen_step (c : Config kA Bool SA (Fin ops) x) (act : Turing.Action kA Bool SA)
    (sy : Fin ops → Option Bool) (mv : Fin ops → SignType) :
    ∑ o, ((c.step act sy mv).channels o).queryBuffer.length ≤
      ∑ o, (c.channels o).queryBuffer.length + ops := by
  calc ∑ o, ((c.step act sy mv).channels o).queryBuffer.length
      ≤ ∑ o : Fin ops, ((c.channels o).queryBuffer.length + 1) := by
        apply Finset.sum_le_sum
        intro o _
        simp only [Config.step, List.length_append]
        have : (sy o).toList.length ≤ 1 := by cases sy o <;> simp
        omega
    _ = _ := by rw [Finset.sum_add_distrib]; simp

theorem potP_step (q₁ : ℕ) (c : Config kA Bool SA (Fin ops) x) (act : Turing.Action kA Bool SA)
    (sy : Fin ops → Option Bool) (mv : Fin ops → SignType) :
    potP q₁ (c.step act sy mv) ≤ potP q₁ c + (4 * ops + q₁ * ops) := by
  have h1 := pot_step c act sy mv
  have h2 := Nat.mul_le_mul_left q₁ (qlen_step c act sy mv)
  unfold potP
  rw [Nat.mul_add] at h2
  omega

theorem potP_zero (c : Config kA Bool SA (Fin ops) x) : potP 0 c = pot c := by simp [potP]

/-! ### The simulation -/

/-- **Correctness of the simulation with per-query handlers**, with the position of the `st` head
(back at `0`): the handler of a query `b` halts within `q₀ + q₁ |b|` steps. -/
theorem lawR_embAP' {σ : Type} (oracle : Fin ops × List Bool → StateT σ PMF (List Bool))
    (enc : σ → List Bool) (InvS : σ → Prop) (L q₀ q₁ : ℕ)
    (hH : ∀ o b s, b.length ≤ T → InvS s → (H o).RunsIn (q₀ + q₁ * b.length) (layout b [] (enc s))
      ((oracle (o, b) s).map (fun r => layout b r.1 (enc r.2))))
    (hInv : ∀ o b s, b.length ≤ T → InvS s → ∀ r ∈ (oracle (o, b) s).support,
      InvS r.2 ∧ r.1.length ≤ L) :
    ∀ n (c : Config kA Bool SA (Fin ops) x) s fl, Good T L InvS n c s fl →
      ∀ N, n * (q₀ + q₁ * ops + 2 * L + 4 * ops + 9) + potP q₁ c + 1 ≤ N →
      (∀ g ∈ (lawR H M T w N (embA H T w c fl (enc s) n)).support, g.1.tapes.state = none) ∧
      (lawR H M T w N (embA H T w c fl (enc s) n)).map projRP =
        (lawA M oracle n c s).map (projAP enc) := by
  intro n
  induction n with
  | zero =>
    intro c s fl hg N hN
    unfold lawA
    rw [law_zero, PMF.pure_map]
    cases hc : c.tapes.state with
    | none =>
      rw [lawR_embA_halted H M T w c hc, PMF.pure_map, projRP_embA]
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
        rw [ite_eq_left (by
          simp only [kind_idx, frameF, frameP, Nat.cast_zero, zero_sub]
          rw [show tapeOfList (List.replicate T true) (-1) = none from tapeOfList_negSucc _ 0]
          simp)]
      rw [hstep, lawR_of_halted H M T w _ rfl, PMF.pure_map]
      refine ⟨fun g hg' => by rw [PMF.mem_support_pure_iff] at hg'; subst hg'; rfl, ?_⟩
      simp [projRP, projAP, noop, frameF, mkR, frameP]
  | succ n ih =>
    intro c s fl hg N hN
    cases hc : c.tapes.state with
    | none =>
      unfold lawA
      rw [lawR_embA_halted H M T w c hc, law_halted _ _ _ _ _ hc, PMF.pure_map, PMF.pure_map,
        projRP_embA]
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
              (fun _ => none) (fun _ => 0))).map projRP =
            (stepLaw M oracle n c s
              (M.tr q c.tapes.inputSymbol c.tapes.workTapeSymbols c.answerSymbols bit)).map
              (projAP enc) := by
        intro bit
        simp only [simAct, hclock, ne_eq, not_true_eq_false, ite_false, hinp]
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
          · have := potP_step q₁ c act sy mv
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
          obtain ⟨j, hj, hq⟩ := lawR_queryP H M T w _ oracle enc s c fl n op nx hg.flags
            (hH op b s (by omega) hg.inv)
          -- the remaining clock after the query
          have hpot := potP_receive q₁ c op nx
          rw [← hb] at hpot hj
          rw [Nat.add_mul, one_mul] at hN
          have hNj : j ≤ N' := by
            have := hg.ans_le op
            have := hpot []
            omega
          obtain ⟨N'', rfl⟩ : ∃ N'', N' = j + N'' := ⟨N' - j, by omega⟩
          have hgood' : ∀ r ∈ (oracle (op, b) s).support,
              Good T L InvS n (c.receive op nx r.1) r.2
                (Function.update fl op (if r.1 = [] then .empty else .right)) ∧
              n * (q₀ + q₁ * ops + 2 * L + 4 * ops + 9) + potP q₁ (c.receive op nx r.1) + 1 ≤ N'' := by
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
              have h2 := hpot []
              have := hg.ans_le op
              omega
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

end Inline

open Inline

variable {ops m : ℕ}

/-- **The handlers realize the oracle with per-query halting bounds**: on the encoded states
satisfying `InvS`, the handler of a query `b` (of at most `A.time` bits) halts within
`q₀ + q₁ |b|` steps; answers have length at most `L`. -/
structure HandlesP {σ : Type} (A : Machine ops) (H : Fin ops → Routine (m + 3))
    (oracle : Fin ops × List Bool → StateT σ PMF (List Bool)) (enc : σ → List Bool)
    (InvS : σ → Prop) (q₀ q₁ L : ℕ) : Prop where
  runs : ∀ o b s, b.length ≤ A.time → InvS s →
    (H o).RunsIn (q₀ + q₁ * b.length) (layout b [] (enc s))
      ((oracle (o, b) s).map (fun r => layout b r.1 (enc r.2)))
  inv : ∀ o b s, b.length ≤ A.time → InvS s → ∀ r ∈ (oracle (o, b) s).support,
    InvS r.2 ∧ r.1.length ≤ L

/-- A uniform bound is a per-query bound with `q₁ = 0`. -/
theorem Handles.handlesP {σ : Type} {A : Machine ops} {H : Fin ops → Routine (m + 3)}
    {oracle : Fin ops × List Bool → StateT σ PMF (List Bool)} {enc : σ → List Bool}
    {InvS : σ → Prop} {Q L : ℕ} (h : Handles A H oracle enc InvS Q L) :
    HandlesP A H oracle enc InvS Q 0 L where
  runs o b s hb hs := (Routine.RunsIn.mono (h.runs o b s hb hs) (h.time_le o)).mono (by simp)
  inv := h.inv

end SigabaNeo
