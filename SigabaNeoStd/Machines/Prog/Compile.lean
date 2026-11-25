import SigabaNeoStd.Machines.Prog.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Tidy
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Loop

/-!
# Compiling tape programs to fair-coin multi-tape machines

`compile p : MultiTapePTM k Bool (State p)` is built by structural recursion from cslib-frontier's
explicit combinators: a primitive is its column machine (`colTM`, deterministic), `seq` is
`MultiTapePTM.seq`, `ifBlank` is `MultiTapePTM.branch`, `ifBit` is `branchBit` (the same, reading
the first bit), and `loop i b` is `branch i (repeatUntilBlank i (tail i ; b)) halt`. A coin clears
its tape and then writes one coin bit (`coinPTM`).

## Main results

* `compile_runsWords`: **correctness and time**. From any store `s` whose words are at most `L` long,
  the machine realizes the law of `denote p s` on its tapes, halting within `timeBound p L` steps on
  every coin sequence (the `RunsWords` specification of cslib-frontier), for a well-formed `p`.
* `card_state`: the machine has exactly `size p` states.
-/

namespace SigabaNeo.Tape

open Cslib Turing MultiTapeMachine MultiTapePTM

variable {k : ℕ}

/-! ### Small machines -/

/-- The machine that halts in one step, changing nothing. -/
def haltTM (k : ℕ) : MultiTapeTM k Bool Unit :=
  MultiTapeTM.ofTr () fun _ _ _ => RepeatUntilBlank.idle none

theorem haltTM_runFrom (x : List Bool) (s : Store k) (out : List Bool) :
    (haltTM k).runFrom (wordsCfg x (some (haltTM k).q₀) s out) 1 = wordsCfg x none s out := by
  show (haltTM k).step _ = _
  rw [MultiTapeTM.step_of_state rfl, haltTM, MultiTapeTM.tr_ofTr]
  exact RepeatUntilBlank.apply_idle_wordsCfg _ _ s out

/-- The action writing the bit `b` under the head of tape `i` and halting. -/
def coinAct (i : Fin k) (b : Bool) : Action k Bool Unit where
  inputTape := 0
  workTapes t := (if t = i then some (some b) else none, 0)
  output := none
  state := none

/-- Write one fair coin under the head of tape `i`, and halt. -/
def coinPTM (i : Fin k) : MultiTapePTM k Bool Unit Empty where
  initial := ()
  tr _ _ _ _ bit := .step (coinAct i bit) (fun _ => none) (fun _ => 0)

theorem apply_coinAct (i : Fin k) (b : Bool) (x : List Bool) (q : Option Unit) (s : Store k)
    (hs : s i = []) (out : List Bool) :
    (coinAct i b).apply (wordsCfg x q s out) = wordsCfg x none (Function.update s i [b]) out := by
  refine Cfg.ext rfl (by simp [Action.apply, coinAct, wordsCfg]) ?_ (by
    funext t; simp [Action.apply, coinAct, wordsCfg]) (by simp [Action.apply, coinAct, wordsCfg])
  funext t
  by_cases ht : t = i
  · subst ht
    have := tapeOfList_append_single ([] : List Bool) b
    simp only [List.nil_append, List.length_nil, Nat.cast_zero] at this
    simp [Action.apply, coinAct, wordsCfg, hs, this]
  · simp [Action.apply, coinAct, wordsCfg, ht]

/-- On a blank tape `i`, the coin machine writes a fair coin there in one step. -/
theorem coinPTM_runsWords (i : Fin k) (x : List Bool) (s : Store k) (hs : s i = [])
    (out₀ : List Bool) :
    (coinPTM i).RunsWords x s out₀ 1
      (ProbOracleComp.sample ((fun b => Function.update s i [b]) <$> ProbComp.uniform Bool))
      id (fun _ => []) := by
  intro OracleState oracle st cfg htapes hbuf
  have hstate : cfg.tapes.state = some () := by rw [htapes]; rfl
  have hrun : ProbOracleComp.runWith oracle ((coinPTM i).runOracleConfigFrom 1 cfg) st =
      (Probability.PMF.uniformOfFintype Bool).map (fun b =>
        ((cfg.step (coinAct i b) (fun _ => none) (fun _ => 0)), st)) := by
    dsimp only [runOracleConfigFrom, MultiTapePTM.runConfigFrom]
    rw [MultiTapeMachine.runConfigFrom]
    simp only [hstate, bind_map_left, ProbOracleComp.runWith_bind,
      run_interpret_sample_uniform_bool, PMF.bind_map, Function.comp_def]
    simp [coinPTM, MultiTapeMachine.runConfigFrom_zero, PMF.map, Function.comp_def]
  have hstep : ∀ b, (cfg.step (coinAct i b) (fun _ => none) (fun _ => 0)).tapes =
      wordsCfg x none (Function.update s i [b]) out₀ := by
    intro b
    rw [Config.step, htapes, apply_coinAct i b x _ s hs out₀]
  dsimp only
  rw [hrun]
  constructor
  · rw [PMF.map_comp, ProbOracleComp.runWith_sample, ProbComp.eval_map, ProbComp.eval_uniform,
      PMF.map_comp, PMF.map_comp]
    refine congrArg (fun f => PMF.map f _) ?_
    funext b
    simp [hstep, Function.comp_def]
  · intro final hfinal op
    exact op.elim

/-- Read the first cell of tape `i`, moving no head and writing nothing, then run `tm₁` if it holds
`true` and `tm₂` otherwise. -/
def branchBit {S₁ S₂ : Type} (i : Fin k) (tm₁ : MultiTapePTM k Bool S₁ Empty)
    (tm₂ : MultiTapePTM k Bool S₂ Empty) : MultiTapePTM k Bool (Option (S₁ ⊕ S₂)) Empty where
  initial := none
  tr q inp work answer bit :=
    match q with
    | none => .step
      { inputTape := 0, workTapes := fun _ => (none, 0), output := none,
        state := some (some (if work i = some true then .inl tm₁.initial else .inr tm₂.initial)) }
      (fun _ => none) (fun _ => 0)
    | some (.inl q) =>
      MultiTapeMachine.Action.mapState (fun s => some (Sum.inl s)) (tm₁.tr q inp work answer bit)
    | some (.inr q) =>
      MultiTapeMachine.Action.mapState (fun s => some (Sum.inr s)) (tm₂.tr q inp work answer bit)

theorem RunsWords.branchBit_true {S₁ S₂ : Type} (i : Fin k) {tm₁ : MultiTapePTM k Bool S₁ Empty}
    (tm₂ : MultiTapePTM k Bool S₂ Empty) {x : List Bool} {ws₀ : Store k} {out₀ : List Bool}
    {t : ℕ} {α : Type} {program : ProbOracleComp (fun _ : Empty × List Bool => List Bool) α}
    {ws₁ : α → Store k} {emit : α → List Bool}
    (hi : (ws₀ i).head? = some true) (h₁ : tm₁.RunsWords x ws₀ out₀ t program ws₁ emit) :
    (branchBit i tm₁ tm₂).RunsWords x ws₀ out₀ (t + 1) program ws₁ emit :=
  RunsWords.of_first_step_mapState (f := fun s => some (Sum.inl s))
    (fun _ _ => by simp [branchBit, Cfg.workTapeSymbols, wordsCfg, tapeOfList_zero, hi])
    (fun _ _ _ _ _ => rfl) h₁

theorem RunsWords.branchBit_false {S₁ S₂ : Type} (i : Fin k) (tm₁ : MultiTapePTM k Bool S₁ Empty)
    {tm₂ : MultiTapePTM k Bool S₂ Empty} {x : List Bool} {ws₀ : Store k} {out₀ : List Bool}
    {t : ℕ} {α : Type} {program : ProbOracleComp (fun _ : Empty × List Bool => List Bool) α}
    {ws₁ : α → Store k} {emit : α → List Bool}
    (hi : (ws₀ i).head? ≠ some true) (h₂ : tm₂.RunsWords x ws₀ out₀ t program ws₁ emit) :
    (branchBit i tm₁ tm₂).RunsWords x ws₀ out₀ (t + 1) program ws₁ emit :=
  RunsWords.of_first_step_mapState (f := fun s => some (Sum.inr s))
    (fun _ _ => by simp [branchBit, Cfg.workTapeSymbols, wordsCfg, tapeOfList_zero, hi])
    (fun _ _ _ _ _ => rfl) h₂

/-! ### Sequencing store phases -/

theorem mem_support_of_runWith_sample {α OracleState : Type}
    {oracle : Empty × List Bool → StateT OracleState PMF (List Bool)} {A : ProbComp α} {st st' : OracleState}
    {a : α} (h : (a, st') ∈ (ProbOracleComp.runWith oracle
      (ProbOracleComp.sample (spec := fun _ : Empty × List Bool => List Bool) A) st).support) :
    a ∈ (ProbComp.eval A).support := by
  rw [ProbOracleComp.runWith_sample, PMF.support_map] at h
  obtain ⟨b, hb, he⟩ := h
  cases he
  exact hb

/-- Sequence two phases on stores, each realizing a closed program. -/
theorem RunsWords.seqStore {S₁ S₂ : Type} {M₁ : MultiTapePTM k Bool S₁ Empty}
    {M₂ : MultiTapePTM k Bool S₂ Empty} {x : List Bool} {s : Store k} {out₀ : List Bool}
    {t₁ t₂ : ℕ} {A : ProbComp (Store k)} {B : Store k → ProbComp (Store k)}
    (h₁ : M₁.RunsWords x s out₀ t₁ (ProbOracleComp.sample A) id (fun _ => []))
    (h₂ : ∀ a ∈ (ProbComp.eval A).support,
      M₂.RunsWords x a out₀ t₂ (ProbOracleComp.sample (B a)) id (fun _ => [])) :
    (M₁.seq M₂).RunsWords x s out₀ (t₁ + t₂) (ProbOracleComp.sample (A >>= B)) id
      (fun _ => []) := by
  have h := (h₁.seq_bind (prog₂ := fun a => ProbOracleComp.sample (B a))
    (ws₂ := fun _ => id) (emit₂ := fun _ _ => [])
    (fun a b hab => by simpa using hab)
    (fun a _ _ _ _ ha => by
      rw [List.append_nil]
      exact h₂ a (mem_support_of_runWith_sample ha))).of_map Prod.snd id (fun _ => [])
  have heq : (Prod.snd <$> (ProbOracleComp.sample A >>= fun a =>
      (fun b => (a, b)) <$> ProbOracleComp.sample (B a)) :
        ProbOracleComp (fun _ : Empty × List Bool => List Bool) (Store k)) =
      ProbOracleComp.sample (A >>= B) := by
    rw [ProbOracleComp.sample_bind]
    simp [map_bind, Functor.map_map]
  rwa [heq] at h

theorem sample_iterate {σ : Type} (n : ℕ) (f : σ → ProbComp σ) (s : σ) :
    (ProbOracleComp.sample (spec := fun _ : Empty × List Bool => List Bool)
      (OracleComp.iterate n f s)) =
      OracleComp.iterate n (fun t => ProbOracleComp.sample (f t)) s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [OracleComp.iterate_succ, ProbOracleComp.sample_bind, ih]; rfl

/-! ### The compiler -/

namespace Prog

/-- The control states of the compiled machine. -/
def State : Prog k → Type
  | prim p => CQ p.spec.e
  | coin i => CQ (clearSpec i).e ⊕ Unit
  | seq p q => State p ⊕ State q
  | ifBlank _ p q => Option (State q ⊕ State p)
  | ifBit _ p q => Option (State p ⊕ State q)
  | loop i body => Option (((CQ (tailSpec i).e ⊕ State body) ⊕ Unit) ⊕ Unit)

/-- The states are finite. -/
@[instance_reducible] def instFintypeState : (p : Prog k) → Fintype p.State
  | prim p => inferInstanceAs (Fintype (CQ p.spec.e))
  | coin i => inferInstanceAs (Fintype (CQ (clearSpec i).e ⊕ Unit))
  | seq p q =>
    letI := instFintypeState p; letI := instFintypeState q
    inferInstanceAs (Fintype (State p ⊕ State q))
  | ifBlank _ p q =>
    letI := instFintypeState p; letI := instFintypeState q
    inferInstanceAs (Fintype (Option (State q ⊕ State p)))
  | ifBit _ p q =>
    letI := instFintypeState p; letI := instFintypeState q
    inferInstanceAs (Fintype (Option (State p ⊕ State q)))
  | loop i body =>
    letI := instFintypeState body
    inferInstanceAs (Fintype (Option (((CQ (tailSpec i).e ⊕ State body) ⊕ Unit) ⊕ Unit)))

instance (p : Prog k) : Fintype p.State := instFintypeState p

/-- The number of states of the compiled machine. -/
def size : Prog k → ℕ
  | prim p => (3 + 2 * p.pad) * 12
  | coin _ => 37
  | seq p q => size p + size q
  | ifBlank _ p q => size p + size q + 1
  | ifBit _ p q => size p + size q + 1
  | loop _ body => size body + 39

/-- **The state count** of the compiled machine. -/
theorem card_state (p : Prog k) : Fintype.card p.State = p.size := by
  induction p with
  | prim p => exact (card_CQ _).trans (by rw [p.spec_e]; rfl)
  | coin i =>
    rw [show Fintype.card (coin i).State = Fintype.card (CQ (clearSpec i).e ⊕ Unit) from
      Fintype.card_congr (Equiv.refl _), Fintype.card_sum, card_CQ]
    rfl
  | seq p q ihp ihq =>
    rw [show Fintype.card (seq p q).State = Fintype.card (p.State ⊕ q.State) from
      Fintype.card_congr (Equiv.refl _), Fintype.card_sum, ihp, ihq]
    rfl
  | ifBlank _ p q ihp ihq =>
    rw [show Fintype.card (ifBlank _ p q).State = Fintype.card (Option (q.State ⊕ p.State)) from
      Fintype.card_congr (Equiv.refl _), Fintype.card_option, Fintype.card_sum, ihp, ihq, size]
    ring
  | ifBit _ p q ihp ihq =>
    rw [show Fintype.card (ifBit _ p q).State = Fintype.card (Option (p.State ⊕ q.State)) from
      Fintype.card_congr (Equiv.refl _), Fintype.card_option, Fintype.card_sum, ihp, ihq, size]
  | loop i body ih =>
    rw [show Fintype.card (loop i body).State =
        Fintype.card (Option (((CQ (tailSpec i).e ⊕ body.State) ⊕ Unit) ⊕ Unit)) from
      Fintype.card_congr (Equiv.refl _), Fintype.card_option, Fintype.card_sum, Fintype.card_sum,
      Fintype.card_sum, card_CQ, Fintype.card_unit, ih, size]
    simp only [tailSpec, bwdSpec]
    ring

/-- The round of a loop: drop the first bit of the counter, then run the body. -/
noncomputable def loopRound (i : Fin k) {S : Type} (body : MultiTapePTM k Bool S Empty) :
    MultiTapePTM k Bool (CQ (tailSpec i).e ⊕ S) Empty :=
  (ofDeterministic (colTM (tailSpec i))).seq body

/-- **The compiler**, by structural recursion from cslib-frontier's combinators. -/
noncomputable def compile : (p : Prog k) → MultiTapePTM k Bool p.State Empty
  | prim p => ofDeterministic (colTM p.spec)
  | coin i => (ofDeterministic (colTM (clearSpec i))).seq (coinPTM i)
  | seq p q => (compile p).seq (compile q)
  | ifBlank i p q => branch i (compile q) (compile p)
  | ifBit i p q => branchBit i (compile p) (compile q)
  | loop i body =>
    branch i (repeatUntilBlank i (loopRound i (compile body))) (ofDeterministic (haltTM k))

theorem roundTime_le_sup (body : Prog k) (L : ℕ) {j : ℕ} (hj : j < L) :
    roundTime (timeBound body) ((lenBound body)^[j] L) ≤
      (Finset.range L).sup (fun j => roundTime (timeBound body) ((lenBound body)^[j] L)) :=
  Finset.le_sup (f := fun j => roundTime (timeBound body) ((lenBound body)^[j] L))
    (Finset.mem_range.mpr hj)

/-- **Correctness and time of the compiled machine.** From any store `s` whose words are at most
`L` long, the compiled machine of a well-formed program realizes the law of `denote p s` on its
work tapes (jointly with any external oracle state), emits nothing, and halts within
`timeBound p L` steps on every coin sequence. -/
theorem compile_runsWords (p : Prog k) (hp : p.WF) (x : List Bool) :
    ∀ (L : ℕ) (s : Store k) (out₀ : List Bool), maxLen s ≤ L →
      (compile p).RunsWords x s out₀ (timeBound p L) (ProbOracleComp.sample (denote p s)) id
        (fun _ => []) := by
  induction p with
  | prim p =>
    intro L s out₀ hs
    exact colTM_runsWords p.spec x s (p.apply s) out₀ (by rw [p.spec_e]; simp only [timeBound]; omega)
      (p.result s)
  | coin i =>
    intro L s out₀ hs
    have h := RunsWords.seqStore (A := pure (Function.update s i []))
      (B := fun a => (fun b => Function.update a i [b]) <$> ProbComp.uniform Bool)
      (colTM_runsWords (clearSpec i) x s (Function.update s i []) out₀
        (t := 2 * L + 3) (by simp only [clearSpec, bwdSpec]; omega) (clear_result i s))
      (fun a ha => by
        simp only [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at ha
        subst ha
        exact coinPTM_runsWords i x _ (by simp) out₀)
    have heq : (pure (Function.update s i []) >>= fun a =>
        (fun b => Function.update a i [b]) <$> ProbComp.uniform Bool) = denote (coin i) s := by
      simp [denote, Function.update_idem]
    rw [heq] at h
    exact h.mono (by simp only [timeBound]; omega)
  | seq p q ihp ihq =>
    intro L s out₀ hs
    exact RunsWords.seqStore (ihp hp.1 L s out₀ hs)
      (fun a ha => ihq hp.2 _ a out₀ (lenBound_spec p L s hs a ha))
  | ifBlank i p q ihp ihq =>
    intro L s out₀ hs
    by_cases hi : s i = []
    · have h := RunsWords.branch_nil i (compile q) hi (ihp hp.1 L s out₀ hs)
      simp only [denote, hi, ↓reduceIte]
      exact h.mono (by simp only [timeBound]; omega)
    · have h := RunsWords.branch_ne_nil i (compile p) hi (ihq hp.2 L s out₀ hs)
      simp only [denote, hi, ↓reduceIte]
      exact h.mono (by simp only [timeBound]; omega)
  | ifBit i p q ihp ihq =>
    intro L s out₀ hs
    by_cases hi : (s i).head? = some true
    · have h := RunsWords.branchBit_true i (compile q) hi (ihp hp.1 L s out₀ hs)
      simp only [denote, hi, ↓reduceIte]
      exact h.mono (by simp only [timeBound]; omega)
    · have h := RunsWords.branchBit_false i (compile p) hi (ihq hp.2 L s out₀ hs)
      simp only [denote, hi, ↓reduceIte]
      exact h.mono (by simp only [timeBound]; omega)
  | loop i body ih =>
    intro L s out₀ hs
    set g := lenBound body with hg
    set T := (Finset.range L).sup (fun j => roundTime (timeBound body) (g^[j] L)) with hT
    -- one round, from words at most `L'` long
    have hround : ∀ (L' : ℕ) (t : Store k), maxLen t ≤ L' →
        (loopRound i (compile body)).RunsWords x t out₀ (roundTime (timeBound body) L')
          (ProbOracleComp.sample (denote body (tailAt i t))) id (fun _ => []) := by
      intro L' t ht
      have h := RunsWords.seqStore (A := pure (tailAt i t)) (B := denote body)
        (colTM_runsWords (tailSpec i) x t (tailAt i t) out₀ (t := 2 * L' + 3)
          (by simp only [tailSpec, bwdSpec]; omega) (tail_result i t))
        (fun a ha => by
          simp only [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at ha
          subst ha
          exact ih hp.1 L' _ out₀ ((maxLen_tailAt i t).trans ht))
      rw [pure_bind] at h
      exact h
    have hn : (s i).length ≤ L := (length_le_maxLen s i).trans hs
    by_cases h0 : s i = []
    · have hhalt : (ofDeterministic (haltTM k) : MultiTapePTM k Bool Unit Empty).RunsWords x s out₀ 1
          (pure s) id (fun _ => []) := runsWords_of_runFrom (haltTM_runFrom x s out₀)
      have h := RunsWords.branch_nil i (repeatUntilBlank i (loopRound i (compile body))) h0 hhalt
      simp only [denote, h0, List.length_nil, OracleComp.iterate_zero]
      exact h.mono (by simp only [timeBound]; omega)
    · set n := (s i).length with hn'
      have hpos : 0 < n := List.length_pos_iff.mpr h0
      have hloop := RunsWords.repeatUntilBlank i (body := loopRound i (compile body))
        (x := x) (out₀ := out₀) (t := T) (rounds := n - 1) (s₀ := s) (ws := id) Function.injective_id
        (step := fun t => ProbOracleComp.sample (denote body (tailAt i t)))
        (last := fun t => ProbOracleComp.sample (denote body (tailAt i t)))
        (fun m t => (t i).length = n - m ∧ maxLen t ≤ g^[m] L) ⟨by simp [hn'], hs⟩
        (fun m hm t ht => (hround _ t ht.2).mono (roundTime_le_sup body L (by omega)))
        (fun t ht => (hround _ t ht.2).mono (roundTime_le_sup body L (by omega)))
        (fun m hm t ht OS oracle st st' t' ht' => by
          have ht'' := mem_support_of_runWith_sample ht'
          have hi := preserves_spec i body hp.2 _ t' ht''
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · rw [hi]; simp [tailAt, ht.1]; omega
          · rw [Function.iterate_succ_apply']
            exact lenBound_spec body _ _ ((maxLen_tailAt i t).trans ht.2) t' ht''
          · show t' i ≠ []
            rw [hi]
            simp only [tailAt, Function.update_self, ne_eq]
            rw [← List.length_eq_zero_iff, List.length_tail, ht.1]
            omega)
        (fun t ht OS oracle st st' t' ht' => by
          have hi := preserves_spec i body hp.2 _ t' (mem_support_of_runWith_sample ht')
          show t' i = []
          rw [hi]
          simp only [tailAt, Function.update_self]
          rw [← List.length_eq_zero_iff, List.length_tail, ht.1]
          omega)
      have h := RunsWords.branch_ne_nil i (ofDeterministic (haltTM k)) h0 hloop
      have hprog : (OracleComp.iterate (n - 1)
          (fun t => ProbOracleComp.sample (denote body (tailAt i t))) s >>=
            fun t => ProbOracleComp.sample (denote body (tailAt i t)) :
            ProbOracleComp (fun _ : Empty × List Bool => List Bool) (Store k)) =
          ProbOracleComp.sample (denote (loop i body) s) := by
        rw [← OracleComp.iterate_succ, Nat.sub_add_cancel hpos, denote, sample_iterate]
      rw [hprog] at h
      refine h.mono ?_
      show (n - 1 + 1) * (T + 1) + 1 ≤ L * (T + 1) + 2
      have : (n - 1 + 1) * (T + 1) ≤ L * (T + 1) := Nat.mul_le_mul_right _ (by omega)
      omega

end Prog

end SigabaNeo.Tape
