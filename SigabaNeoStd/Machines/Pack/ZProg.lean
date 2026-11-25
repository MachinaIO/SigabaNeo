import SigabaNeoStd.Machines.Prog.Frame

/-!
# Framed programs with certified native phases

`ZProg k` extends the framed programs `XProg k` by **phases**: a `Phase k` is any machine with a
store function `f`, a precondition and a per-store time, together with its `RunsWords`
specification. Phases let a program use machines that the column primitives cannot express
efficiently (e.g. transducer passes that move a word between two positions of the tapes in linear
time), while the control constructs (`seq`, `ifBlank`, `ifBit`, `loop`) and the `XProg` leaves are
compiled exactly as in `SigabaNeoStd.Machines.Prog.Frame`.

Time is certified by a **Hoare-style judgment** `HT p Pre t`: from every store satisfying `Pre`,
the compiled machine halts within `t` steps on every coin sequence. Sequencing goes through an
intermediate predicate, a loop through an invariant; leaves use `XProg.timeBoundT` from a `Fits`
bound, phases their own time. Unlike the static per-tape bounds of `XProg.timeBoundT`, the
predicates can carry semantic information (e.g. *tape `0` encodes a store whose words fit `ℓ`*).

## Main results

* `ZProg.compile_runsWords`: from `HT p Pre t` and `Pre s`, the compiled machine realizes
  `denote p s` within `t` steps.
* `ZProg.toMachineZ`, `ZProg.run_toMachineZ`: the explicit machine (load the input onto a tape,
  run, emit a tape) and its output law; `ZProg.states_toMachineZ`: its states.
-/

namespace SigabaNeo.Tape

open Cslib Turing MultiTapeMachine MultiTapePTM

/-- A **certified phase** on `k` tapes: a machine computing the store function `f` from every store
satisfying `pre`, within `time s` steps, emitting nothing. -/
structure Phase (k : ℕ) where
  /-- The control states. -/
  State : Type
  /-- They are finite. -/
  fintype : Fintype State
  /-- The machine. -/
  machine : MultiTapePTM k Bool State Empty
  /-- The store function. -/
  f : Store k → Store k
  /-- The precondition. -/
  pre : Store k → Prop
  /-- The time, per store. -/
  time : Store k → ℕ
  /-- The specification. -/
  runs : ∀ (x : List Bool) (s : Store k) (out₀ : List Bool), pre s →
    machine.RunsWords x s out₀ (time s) (ProbOracleComp.sample (pure (f s))) id (fun _ => [])

attribute [instance] Phase.fintype

/-- Framed programs with native phases. -/
inductive ZProg (k : ℕ) : Type 1
  /-- A framed program. -/
  | xp (p : XProg k) : ZProg k
  /-- A certified phase. -/
  | ph (P : Phase k) : ZProg k
  /-- `p`, then `q`. -/
  | seq (p q : ZProg k) : ZProg k
  /-- `p` if tape `i` is blank, otherwise `q`. -/
  | ifBlank (i : Fin k) (p q : ZProg k) : ZProg k
  /-- `p` if the first bit of tape `i` is `true`, otherwise `q`. -/
  | ifBit (i : Fin k) (p q : ZProg k) : ZProg k
  /-- Repeat `|s i|` times: drop the first bit of tape `i`, then run `body`. -/
  | loop (i : Fin k) (body : ZProg k) : ZProg k

namespace ZProg

variable {k : ℕ}

/-- The denotation: a randomized store transformation. -/
noncomputable def denote : ZProg k → Store k → ProbComp (Store k)
  | xp p, s => p.denote s
  | ph P, s => pure (P.f s)
  | seq p q, s => denote p s >>= denote q
  | ifBlank i p q, s => if s i = [] then denote p s else denote q s
  | ifBit i p q, s => if (s i).head? = some true then denote p s else denote q s
  | loop i body, s => OracleComp.iterate (s i).length (fun t => denote body (tailAt i t)) s
termination_by structural p => p

/-- The output law of a program on a store. -/
noncomputable def law (p : ZProg k) (s : Store k) : PMF (Store k) := ProbComp.eval (p.denote s)

theorem law_xp (p : XProg k) (s : Store k) : (xp p).law s = p.law s := rfl

theorem law_ph (P : Phase k) (s : Store k) : (ph P).law s = PMF.pure (P.f s) := by
  simp [law, denote]

theorem law_seq (p q : ZProg k) (s : Store k) : (seq p q).law s = (p.law s).bind q.law := by
  simp [law, denote]; rfl

theorem law_ifBlank (i : Fin k) (p q : ZProg k) (s : Store k) :
    (ifBlank i p q).law s = if s i = [] then p.law s else q.law s := by
  simp only [law, denote]; split_ifs <;> rfl

theorem law_ifBit (i : Fin k) (p q : ZProg k) (s : Store k) :
    (ifBit i p q).law s = if (s i).head? = some true then p.law s else q.law s := by
  simp only [law, denote]; split_ifs <;> rfl

/-! ### The time judgment -/

/-- **The time judgment** `HT p Pre t`: from every store satisfying `Pre`, the compiled machine of
`p` halts within `t` steps (`compile_runsWords`). It also carries the side conditions the compiler
needs (well-formed leaves, the counter of a loop is shortened by exactly one bit per round). -/
def HT : ZProg k → (Store k → Prop) → ℕ → Prop
  | xp p, Pre, t => p.WF ∧ ∃ ℓ : Fin k → ℕ, (∀ s, Pre s → Fits s ℓ) ∧ p.timeBoundT ℓ ≤ t
  | ph P, Pre, t => ∀ s, Pre s → P.pre s ∧ P.time s ≤ t
  | seq p q, Pre, t => ∃ (Mid : Store k → Prop) (t₁ t₂ : ℕ), HT p Pre t₁ ∧
      (∀ s, Pre s → ∀ s' ∈ (p.law s).support, Mid s') ∧ HT q Mid t₂ ∧ t₁ + t₂ ≤ t
  | ifBlank i p q, Pre, t => ∃ t', HT p (fun s => Pre s ∧ s i = []) t' ∧
      HT q (fun s => Pre s ∧ s i ≠ []) t' ∧ t' + 1 ≤ t
  | ifBit i p q, Pre, t => ∃ t', HT p (fun s => Pre s ∧ (s i).head? = some true) t' ∧
      HT q (fun s => Pre s ∧ (s i).head? ≠ some true) t' ∧ t' + 1 ≤ t
  | loop i body, Pre, t => ∃ (Inv : Store k → Prop) (n L R : ℕ),
      (∀ s, Pre s → Inv s ∧ (s i).length ≤ n) ∧ (∀ s, Inv s → maxLen s ≤ L) ∧
      HT body (fun u => ∃ s, Inv s ∧ s i ≠ [] ∧ u = tailAt i s) R ∧
      (∀ s, Inv s → s i ≠ [] → ∀ s' ∈ (body.law (tailAt i s)).support,
        Inv s' ∧ s' i = (s i).tail) ∧
      n * ((2 * L + 3) + R + 1) + 2 ≤ t

/-- A weaker precondition and a larger clock keep the judgment. -/
theorem HT.mono : ∀ {p : ZProg k} {Pre Pre' : Store k → Prop} {t t' : ℕ}, HT p Pre t →
    (∀ s, Pre' s → Pre s) → t ≤ t' → HT p Pre' t'
  | xp _, _, _, _, _, ⟨hw, ℓ, hℓ, ht⟩, hP, htt => ⟨hw, ℓ, fun s hs => hℓ s (hP s hs), ht.trans htt⟩
  | ph _, _, _, _, _, h, hP, htt => fun s hs => ⟨(h s (hP s hs)).1, (h s (hP s hs)).2.trans htt⟩
  | seq _ _, _, _, _, _, ⟨Mid, t₁, t₂, h₁, hm, h₂, ht⟩, hP, htt =>
    ⟨Mid, t₁, t₂, h₁.mono hP le_rfl, fun s hs => hm s (hP s hs), h₂, ht.trans htt⟩
  | ifBlank _ _ _, _, _, _, _, ⟨t₀, h₁, h₂, ht⟩, hP, htt =>
    ⟨t₀, h₁.mono (fun s hs => ⟨hP s hs.1, hs.2⟩) le_rfl,
      h₂.mono (fun s hs => ⟨hP s hs.1, hs.2⟩) le_rfl, ht.trans htt⟩
  | ifBit _ _ _, _, _, _, _, ⟨t₀, h₁, h₂, ht⟩, hP, htt =>
    ⟨t₀, h₁.mono (fun s hs => ⟨hP s hs.1, hs.2⟩) le_rfl,
      h₂.mono (fun s hs => ⟨hP s hs.1, hs.2⟩) le_rfl, ht.trans htt⟩
  | loop _ _, _, _, _, _, ⟨Inv, n, L, R, h0, hL, hb, hinv, ht⟩, hP, htt =>
    ⟨Inv, n, L, R, fun s hs => h0 s (hP s hs), hL, hb, hinv, ht.trans htt⟩

/-! ### The compiler -/

/-- The control states of the compiled machine. -/
def State : ZProg k → Type
  | xp p => p.State
  | ph P => P.State
  | seq p q => State p ⊕ State q
  | ifBlank _ p q => Option (State q ⊕ State p)
  | ifBit _ p q => Option (State p ⊕ State q)
  | loop i body => Option (((CQ (tailSpec i).e ⊕ State body) ⊕ Unit) ⊕ Unit)
termination_by structural p => p

/-- The states are finite. -/
@[instance_reducible] def instFintypeState : (p : ZProg k) → Fintype p.State
  | xp p => inferInstanceAs (Fintype p.State)
  | ph P => P.fintype
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
termination_by structural p => p

instance (p : ZProg k) : Fintype p.State := instFintypeState p

/-- **The compiler.** -/
noncomputable def compile : (p : ZProg k) → MultiTapePTM k Bool p.State Empty
  | xp p => p.compile
  | ph P => P.machine
  | seq p q => (compile p).seq (compile q)
  | ifBlank i p q => branch i (compile q) (compile p)
  | ifBit i p q => branchBit i (compile p) (compile q)
  | loop i body =>
    branch i (repeatUntilBlank i (Prog.loopRound i (compile body)))
      (ofDeterministic (haltTM _))
termination_by structural p => p

/-- **Correctness and time of the compiled machine.** -/
theorem compile_runsWords (x : List Bool) :
    ∀ (p : ZProg k) (Pre : Store k → Prop) (t : ℕ), HT p Pre t →
      ∀ (s : Store k) (out₀ : List Bool), Pre s →
      (compile p).RunsWords x s out₀ t (ProbOracleComp.sample (denote p s)) id (fun _ => []) := by
  intro p
  induction p with
  | xp p =>
    rintro Pre t ⟨hw, ℓ, hℓ, ht⟩ s out₀ hs
    exact (XProg.compile_runsWordsT p hw x ℓ s out₀ (hℓ s hs)).mono ht
  | ph P =>
    intro Pre t h s out₀ hs
    exact (P.runs x s out₀ (h s hs).1).mono (h s hs).2
  | seq p q ihp ihq =>
    rintro Pre t ⟨Mid, t₁, t₂, h₁, hm, h₂, ht⟩ s out₀ hs
    exact (RunsWords.seqStore (ihp Pre t₁ h₁ s out₀ hs)
      (fun a ha => ihq Mid t₂ h₂ a out₀ (hm s hs a ha))).mono ht
  | ifBlank i p q ihp ihq =>
    rintro Pre t ⟨t₀, h₁, h₂, ht⟩ s out₀ hs
    by_cases hi : s i = []
    · have h := RunsWords.branch_nil i (compile q) hi (ihp _ t₀ h₁ s out₀ ⟨hs, hi⟩)
      simp only [denote, hi, ↓reduceIte]
      exact h.mono ht
    · have h := RunsWords.branch_ne_nil i (compile p) hi (ihq _ t₀ h₂ s out₀ ⟨hs, hi⟩)
      simp only [denote, hi, ↓reduceIte]
      exact h.mono ht
  | ifBit i p q ihp ihq =>
    rintro Pre t ⟨t₀, h₁, h₂, ht⟩ s out₀ hs
    by_cases hi : (s i).head? = some true
    · have h := RunsWords.branchBit_true i (compile q) hi (ihp _ t₀ h₁ s out₀ ⟨hs, hi⟩)
      simp only [denote, hi, ↓reduceIte]
      exact h.mono ht
    · have h := RunsWords.branchBit_false i (compile p) hi (ihq _ t₀ h₂ s out₀ ⟨hs, hi⟩)
      simp only [denote, hi, ↓reduceIte]
      exact h.mono ht
  | loop i body ih =>
    rintro Pre t ⟨Inv, n, L, R, h0, hL, hb, hinv, ht⟩ s out₀ hs
    set T := (2 * L + 3) + R with hT
    have hround : ∀ u : Store _, Inv u → u i ≠ [] →
        (Prog.loopRound i (compile body)).RunsWords x u out₀ T
          (ProbOracleComp.sample (denote body (tailAt i u))) id (fun _ => []) := by
      intro u hu hne
      have hML := hL u hu
      have h := RunsWords.seqStore (A := pure (tailAt i u)) (B := denote body)
        (colTM_runsWords (tailSpec i) x u (tailAt i u) out₀ (t := 2 * L + 3)
          (by simp only [tailSpec, bwdSpec]; omega) (tail_result i u))
        (fun a ha => by
          simp only [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at ha
          subst ha
          exact ih _ R hb _ out₀ ⟨u, hu, hne, rfl⟩)
      rw [pure_bind] at h
      exact h
    obtain ⟨hInv, hn⟩ := h0 s hs
    by_cases h0 : s i = []
    · have hhalt : (ofDeterministic (haltTM _) : MultiTapePTM _ Bool Unit Empty).RunsWords x s out₀
          1 (pure s) id (fun _ => []) := runsWords_of_runFrom (haltTM_runFrom x s out₀)
      have h := RunsWords.branch_nil i (repeatUntilBlank i (Prog.loopRound i (compile body))) h0
        hhalt
      simp only [denote, h0, List.length_nil, OracleComp.iterate_zero]
      exact h.mono (by omega)
    · set m := (s i).length with hm'
      have hpos : 0 < m := List.length_pos_iff.mpr h0
      have hloop := RunsWords.repeatUntilBlank i (body := Prog.loopRound i (compile body))
        (x := x) (out₀ := out₀) (t := T) (rounds := m - 1) (s₀ := s) (ws := id)
        Function.injective_id
        (step := fun t => ProbOracleComp.sample (denote body (tailAt i t)))
        (last := fun t => ProbOracleComp.sample (denote body (tailAt i t)))
        (fun r u => (u i).length = m - r ∧ Inv u) ⟨by simp [hm'], hInv⟩
        (fun r hr u hu => hround u hu.2 (by
          rw [← List.length_pos_iff, hu.1]; omega))
        (fun u hu => hround u hu.2 (by rw [← List.length_pos_iff, hu.1]; omega))
        (fun r hr u hu OS oracle st st' u' hu' => by
          have hne : u i ≠ [] := by rw [← List.length_pos_iff, hu.1]; omega
          obtain ⟨hI, hi⟩ := hinv u hu.2 hne u' (mem_support_of_runWith_sample hu')
          refine ⟨⟨?_, hI⟩, ?_⟩
          · rw [hi, List.length_tail, hu.1]; omega
          · show u' i ≠ []
            rw [hi, ← List.length_pos_iff, List.length_tail, hu.1]
            omega)
        (fun u hu OS oracle st st' u' hu' => by
          have hne : u i ≠ [] := by rw [← List.length_pos_iff, hu.1]; omega
          obtain ⟨-, hi⟩ := hinv u hu.2 hne u' (mem_support_of_runWith_sample hu')
          show u' i = []
          rw [hi, ← List.length_eq_zero_iff, List.length_tail, hu.1]
          omega)
      have h := RunsWords.branch_ne_nil i (ofDeterministic (haltTM _)) h0 hloop
      have hprog : (OracleComp.iterate (m - 1)
          (fun t => ProbOracleComp.sample (denote body (tailAt i t))) s >>=
            fun t => ProbOracleComp.sample (denote body (tailAt i t)) :
            ProbOracleComp (fun _ : Empty × List Bool => List Bool) (Store _)) =
          ProbOracleComp.sample (denote (loop i body) s) := by
        rw [← OracleComp.iterate_succ, Nat.sub_add_cancel hpos, denote, sample_iterate]
      rw [hprog] at h
      refine h.mono ?_
      show (m - 1 + 1) * (T + 1) + 1 ≤ t
      have : (m - 1 + 1) * (T + 1) ≤ n * (T + 1) := Nat.mul_le_mul_right _ (by omega)
      have : n * (T + 1) = n * ((2 * L + 3) + R + 1) := by rw [hT]
      omega

/-! ### The explicit machine -/

/-- The machine of a program: load the input onto tape `i₀`, run, emit tape `o`. -/
noncomputable def toPTM (p : ZProg k) (i₀ o : Fin k) :
    MultiTapePTM k Bool ((Bool ⊕ p.State) ⊕ Bool) Empty :=
  ((ofDeterministic (loadTM i₀)).seq (compile p)).seq (ofDeterministic (emitTM o))

/-- The clock of the machine, from a time judgment `HT p (· = inputStore i₀ x) t` holding for
every input `x` at most `n` long and a bound `lo` on the length of the emitted word. -/
def totalTime (n t lo : ℕ) : ℕ := (2 * n + 2) + t + (2 * lo + 2)

theorem toPTM_runsWords (p : ZProg k) (i₀ o : Fin k) (n t lo : ℕ) (x : List Bool)
    (hx : x.length ≤ n) (hT : HT p (fun s => s = inputStore i₀ x) t)
    (hlo : ∀ s ∈ (p.law (inputStore i₀ x)).support, (s o).length ≤ lo) :
    (p.toPTM i₀ o).RunsWords x (fun _ => []) [] (totalTime n t lo)
      (ProbOracleComp.sample (denote p (inputStore i₀ x))) id (fun s => s o) := by
  have hload : (ofDeterministic (loadTM i₀) : MultiTapePTM k Bool Bool Empty).RunsWords x
      (fun _ => []) [] (2 * n + 2) (ProbOracleComp.sample (pure (inputStore i₀ x))) id
      (fun _ => []) :=
    (runsWords_of_runFrom (loadTM_runFrom i₀ x _ rfl [])).mono (by omega)
  have h₁ := RunsWords.seqStore hload (fun a ha => by
    simp only [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at ha
    subst ha
    exact compile_runsWords x p _ t hT _ [] rfl)
  rw [pure_bind] at h₁
  have h₂ := h₁.seq_bind (t₂ := 2 * lo + 2)
    (prog₂ := fun a => pure a) (ws₂ := fun _ => id)
    (emit₂ := fun _ b => b o) (fun a b hab => by simpa using hab)
    (fun a _ _ _ _ ha => by
      have hlen := hlo a (mem_support_of_runWith_sample ha)
      refine (runsWords_of_runFrom_emit (e := fun b => b o)
        (emitTM_runFrom o x a ([] ++ []))).mono ?_
      omega)
  have h₃ := h₂.of_map Prod.snd id (fun s => s o)
  have heq : (Prod.snd <$> (ProbOracleComp.sample (denote p (inputStore i₀ x)) >>= fun a =>
      (fun b => (a, b)) <$> (pure a : ProbOracleComp (fun _ : Empty × List Bool => List Bool) _))) =
      ProbOracleComp.sample (denote p (inputStore i₀ x)) := by
    simp
  rw [heq] at h₃
  exact h₃

/-- The explicit machine (no oracles) of a program, with the clock `totalTime n t lo`. -/
noncomputable def toMachineZ (p : ZProg k) (i₀ o : Fin k) (n t lo : ℕ) : Machine :=
  Machine.ofPTM (p.toPTM i₀ o) (totalTime n t lo)

/-- **The output law of the machine.** -/
theorem run_toMachineZ (p : ZProg k) (i₀ o : Fin k) (n t lo : ℕ) (x : List Bool)
    (hx : x.length ≤ n) (hT : HT p (fun s => s = inputStore i₀ x) t)
    (hlo : ∀ s ∈ (p.law (inputStore i₀ x)).support, (s o).length ≤ lo) :
    (p.toMachineZ i₀ o n t lo).run x = (p.law (inputStore i₀ x)).map (fun s => s o) := by
  rw [toMachineZ, Machine.run_ofPTM]
  exact Prog.eval_runClosed_of_runsWords (toPTM_runsWords p i₀ o n t lo x hx hT hlo)

theorem states_toMachineZ (p : ZProg k) (i₀ o : Fin k) (n t lo : ℕ) :
    (p.toMachineZ i₀ o n t lo).states = Fintype.card p.State + 4 := by
  show Nat.card ((Bool ⊕ p.State) ⊕ Bool) = _
  rw [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_bool]
  ring

theorem tapes_toMachineZ (p : ZProg k) (i₀ o : Fin k) (n t lo : ℕ) :
    (p.toMachineZ i₀ o n t lo).tapes = k := rfl

theorem time_toMachineZ (p : ZProg k) (i₀ o : Fin k) (n t lo : ℕ) :
    (p.toMachineZ i₀ o n t lo).time = totalTime n t lo := rfl

end ZProg

end SigabaNeo.Tape
