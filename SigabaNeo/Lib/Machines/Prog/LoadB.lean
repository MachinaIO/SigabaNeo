import SigabaNeo.Lib.Machines.Prog.DetX

/-!
# A bounded loader and machines with one clock for every input

`toMachineT p i₀ o n` loads its whole input, so its clock covers only inputs at most `n` long. The
**bounded loader** `loadBTM i₀ n` copies only the first `min |x| (n + 1)` input bits onto tape `i₀`
(at most `2 (n + 1) + 2` steps on every input), so the machine

  `XProg.toMachineB p i₀ o n` (load at most `n + 1` bits, run `p`, emit tape `o`)

runs within its clock on **every** input: `run_toMachineB` gives its output law on every `x` as the
law of `p` on `x.take (n + 1)`. A program can then detect inputs longer than `n` (its input tape
has `n + 1` bits) and answer them by a fixed word. Coin-free programs give deterministic machines
(`deterministic_toMachineB`).
-/

namespace SigabaNeo.Tape

open Cslib Turing MultiTapeMachine MultiTapePTM

variable {k : ℕ}

/-! ### The bounded loader -/

/-- The action of the loader: move the input head by `di` and the head of tape `i₀` by `d`, writing
`w` there. -/
def lbAct {S : Type} (i₀ : Fin k) (di : SignType) (w : Option (Option Bool)) (d : SignType)
    (q : Option S) : Action k Bool S where
  inputTape := di
  workTapes t := if t = i₀ then (w, d) else (none, 0)
  output := none
  state := q

/-- The transitions: in state `some i` (`i` bits copied) copy while `i ≤ n`, in state `none` move
both heads back. -/
def lbTr (i₀ : Fin k) (n : ℕ) : Option (Fin (n + 2)) → Option Bool → (Fin k → Option Bool) →
    Action k Bool (Option (Fin (n + 2)))
  | some i, some a, _ =>
    if h : i.val < n + 1 then lbAct i₀ 1 (some (some a)) 1 (some (some ⟨i.val + 1, by omega⟩))
    else lbAct i₀ (-1) none (-1) (some none)
  | some _, none, _ => lbAct i₀ (-1) none (-1) (some none)
  | none, some _, _ => lbAct i₀ (-1) none (-1) (some none)
  | none, none, _ => lbAct i₀ 1 none 1 none

/-- **The bounded loader**: copy at most `n + 1` input bits to the blank tape `i₀` and rewind. -/
def loadBTM (i₀ : Fin k) (n : ℕ) : MultiTapeTM k Bool (Option (Fin (n + 2))) :=
  MultiTapeTM.ofTr (some ⟨0, by omega⟩) (lbTr i₀ n)

/-- A configuration of the loader. -/
def lbCfg {S : Type} (i₀ : Fin k) (x : List Bool) (q : Option S) (p : ℕ) (hp : p < x.length + 2)
    (s : Store k) (w : List Bool) (h : ℤ) (out : List Bool) : Cfg k Bool S x :=
  ⟨q, ⟨p, hp⟩, fun t => tapeOfList (Function.update s i₀ w t),
    Function.update (fun _ => 0) i₀ h, out⟩

theorem loadBTM_step (i₀ : Fin k) (n : ℕ) (x : List Bool) (q : Option (Fin (n + 2))) (p : ℕ)
    (hp : p < x.length + 2) (s : Store k) (w : List Bool) (h : ℤ) (out : List Bool) :
    (loadBTM i₀ n).step (lbCfg i₀ x (some q) p hp s w h out) =
      (lbTr i₀ n q (lbCfg i₀ x (some q) p hp s w h out).inputSymbol
        (lbCfg i₀ x (some q) p hp s w h out).workTapeSymbols).apply
        (lbCfg i₀ x (some q) p hp s w h out) := by
  rw [MultiTapeTM.step_of_state rfl, loadBTM, MultiTapeTM.tr_ofTr]

theorem apply_lbAct {S : Type} (i₀ : Fin k) (x : List Bool) (q : Option S) (p : ℕ)
    (hp : p < x.length + 2) (s : Store k) (w : List Bool) (h : ℤ) (out : List Bool)
    (di : SignType) (d : SignType) (q' : Option S) (p' : ℕ) (hp' : p' < x.length + 2)
    (hmove : moveInputPos (⟨p, hp⟩ : Fin (x.length + 2)) di = ⟨p', hp'⟩)
    (wr : Option (Option Bool)) (w' : List Bool)
    (hw : (match wr with
      | none => tapeOfList w
      | some c => Function.update (tapeOfList w) h c) = tapeOfList w') :
    (lbAct i₀ di wr d q').apply (lbCfg i₀ x q p hp s w h out) =
      lbCfg i₀ x q' p' hp' s w' (h + d) out := by
  refine Cfg.ext rfl ?_ ?_ ?_ (by simp [Action.apply, lbAct, lbCfg])
  · simpa [Action.apply, lbAct, lbCfg] using hmove
  · funext t
    by_cases ht : t = i₀
    · subst ht
      simp only [Action.apply, lbAct, lbCfg, ↓reduceIte, Function.update_self]
      rw [← hw]
      cases wr <;> rfl
    · simp [Action.apply, lbAct, lbCfg, ht]
  · funext t
    by_cases ht : t = i₀
    · subst ht; simp [Action.apply, lbAct, lbCfg]
    · simp [Action.apply, lbAct, lbCfg, ht]

theorem loadBTM_runFrom_add (i₀ : Fin k) (n : ℕ) (x : List Bool)
    (c : Cfg k Bool (Option (Fin (n + 2))) x) (a b : ℕ) :
    (loadBTM i₀ n).runFrom c (a + b) = (loadBTM i₀ n).runFrom ((loadBTM i₀ n).runFrom c a) b := by
  show (loadBTM i₀ n).step^[a + b] c = (loadBTM i₀ n).step^[b] ((loadBTM i₀ n).step^[a] c)
  rw [← Function.iterate_add_apply, Nat.add_comm b a]

theorem loadBTM_runFrom_one (i₀ : Fin k) (n : ℕ) (x : List Bool)
    (c : Cfg k Bool (Option (Fin (n + 2))) x) :
    (loadBTM i₀ n).runFrom c 1 = (loadBTM i₀ n).step c := rfl

/-- The copying phase. -/
theorem loadB_copy (i₀ : Fin k) (n : ℕ) (x : List Bool) (s : Store k) (out : List Bool) :
    ∀ m (hm : m ≤ x.length) (hmn : m ≤ n + 1),
      (loadBTM i₀ n).runFrom (lbCfg i₀ x (some (some ⟨0, by omega⟩)) 1 (by omega) s [] 0 out) m =
        lbCfg i₀ x (some (some ⟨m, by omega⟩)) (1 + m) (by omega) s (x.take m) m out := by
  intro m
  induction m with
  | zero => intro _ _; rfl
  | succ m ih =>
    intro _hm _hmn
    rw [loadBTM_runFrom_add, ih (by omega) (by omega), loadBTM_runFrom_one, loadBTM_step]
    have hsym : (lbCfg i₀ x (some (some (⟨m, by omega⟩ : Fin (n + 2)))) (1 + m) (by omega) s
        (x.take m) m out).inputSymbol = some x[m] :=
      inputSymbolInner m (by simp [lbCfg] <;> omega) (by omega)
    rw [hsym]
    simp only [lbTr, dite_eq_left_of_eq_true (eq_true (show m < n + 1 by omega))]
    refine (apply_lbAct i₀ x _ _ _ s _ _ out 1 1 _ (1 + (m + 1)) (by omega) ?_ _
      (x.take (m + 1)) ?_).trans ?_
    · apply Fin.ext
      have h := val_moveInputPos_eq (⟨1 + m, by omega⟩ : Fin (x.length + 2)) 1
      simp only [SignType.coe_one] at h
      simp only
      omega
    · simp only
      have := tapeOfList_append_single (x.take m) x[m]
      rw [List.length_take, min_eq_left (by omega)] at this
      rw [← this, List.take_succ_eq_append_getElem (by omega)]
    · simp

/-- The rewinding phase. -/
theorem loadB_back (i₀ : Fin k) (n : ℕ) (x : List Bool) (s : Store k) (w : List Bool)
    (out : List Bool) : ∀ j (hj : j ≤ x.length),
      (loadBTM i₀ n).runFrom (lbCfg i₀ x (some (none : Option (Fin (n + 2)))) j (by omega) s w
        ((j : ℤ) - 1) out) (j + 1) = lbCfg i₀ x none 1 (by omega) s w 0 out := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [loadBTM_runFrom_one, loadBTM_step]
    have hsym : (lbCfg i₀ x (some (none : Option (Fin (n + 2)))) 0 (by omega) s w ((0 : ℕ) - 1)
        out).inputSymbol = none := inputSymbol_eq_none_of_boundary (Or.inl rfl)
    rw [hsym]
    simp only [lbTr]
    refine (apply_lbAct i₀ x _ _ _ s _ _ out 1 1 _ 1 (by omega) ?_ none w rfl).trans ?_
    · apply Fin.ext
      have h := val_moveInputPos_eq (⟨0, by omega⟩ : Fin (x.length + 2)) 1
      simp only [SignType.coe_one] at h
      simp only
      omega
    · simp
  | succ j ih =>
    intro hj
    rw [show j + 1 + 1 = 1 + (j + 1) by omega, loadBTM_runFrom_add, loadBTM_runFrom_one,
      loadBTM_step]
    have hsym : (lbCfg i₀ x (some (none : Option (Fin (n + 2)))) (j + 1) (by omega) s w
        (((j + 1 : ℕ) : ℤ) - 1) out).inputSymbol = some x[j] :=
      inputSymbolInner j (by simp [lbCfg] <;> omega) (by omega)
    rw [hsym]
    simp only [lbTr]
    refine (congrArg (fun c => (loadBTM i₀ n).runFrom c (j + 1))
      (apply_lbAct i₀ x _ _ _ s _ _ out (-1) (-1) _ j (by omega) ?_ none w rfl)).trans ?_
    · apply Fin.ext
      have h := val_moveInputPos_eq (⟨j + 1, by omega⟩ : Fin (x.length + 2)) (-1)
      simp only [SignType.coe_neg, SignType.coe_one] at h
      simp only
      omega
    · rw [← ih (by omega)]
      congr 2
      simp only [SignType.coe_neg, SignType.coe_one]
      push_cast; ring

/-- **The bounded loader**: after `2 m + 2` steps, `m = min |x| (n + 1)`, the first `m` input bits
are on tape `i₀`, all heads at the start. -/
theorem loadBTM_runFrom (i₀ : Fin k) (n : ℕ) (x : List Bool) (s : Store k) (hs : s i₀ = [])
    (out : List Bool) :
    (loadBTM i₀ n).runFrom (wordsCfg x (some (loadBTM i₀ n).q₀) s out)
        (2 * min x.length (n + 1) + 2) =
      wordsCfg x none (Function.update s i₀ (x.take (n + 1))) out := by
  set m := min x.length (n + 1) with hm
  have hm1 : m ≤ x.length := min_le_left _ _
  have hm2 : m ≤ n + 1 := min_le_right _ _
  have htk : x.take m = x.take (n + 1) := by
    rcases le_total x.length (n + 1) with h | h
    · rw [hm, min_eq_left h, List.take_length, List.take_of_length_le h]
    · rw [hm, min_eq_right h]
  have hstart : (wordsCfg x (some (loadBTM i₀ n).q₀) s out : Cfg k Bool _ x) =
      lbCfg i₀ x (some (some ⟨0, by omega⟩)) 1 (by omega) s [] 0 out := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext t
      by_cases ht : t = i₀
      · subst ht; simp [lbCfg, hs, wordsCfg]
      · simp [lbCfg, ht, wordsCfg]
    · funext t
      by_cases ht : t = i₀
      · subst ht; simp [lbCfg, wordsCfg]
      · simp [lbCfg, ht, wordsCfg]
  have hend : lbCfg i₀ x (none : Option (Option (Fin (n + 2)))) 1 (by omega) s (x.take m) 0 out =
      wordsCfg x none (Function.update s i₀ (x.take (n + 1))) out := by
    rw [htk]
    refine Cfg.ext rfl rfl rfl ?_ rfl
    funext t
    by_cases ht : t = i₀
    · subst ht; simp [lbCfg]
    · simp [lbCfg, ht]
  rw [hstart, show 2 * m + 2 = m + (1 + (m + 1)) by omega, loadBTM_runFrom_add,
    loadB_copy i₀ n x s out m hm1 hm2, loadBTM_runFrom_add, loadBTM_runFrom_one, loadBTM_step]
  have hstop : lbTr i₀ n (some ⟨m, by omega⟩) (lbCfg i₀ x (some (some (⟨m, by omega⟩ :
      Fin (n + 2)))) (1 + m) (by omega) s (x.take m) m out).inputSymbol
      (lbCfg i₀ x (some (some (⟨m, by omega⟩ : Fin (n + 2)))) (1 + m) (by omega) s (x.take m) m
        out).workTapeSymbols = lbAct i₀ (-1) none (-1) (some none) := by
    rcases Nat.lt_or_ge m x.length with h | h
    · have hmn : m = n + 1 := by omega
      have hsym : (lbCfg i₀ x (some (some (⟨m, by omega⟩ : Fin (n + 2)))) (1 + m) (by omega) s
          (x.take m) m out).inputSymbol = some x[m] :=
        inputSymbolInner m (by simp [lbCfg] <;> omega) (by omega)
      rw [hsym]
      simp only [lbTr, dite_eq_right_of_eq_false (eq_false (show ¬ m < n + 1 by omega))]
    · have hsym : (lbCfg i₀ x (some (some (⟨m, by omega⟩ : Fin (n + 2)))) (1 + m) (by omega) s
          (x.take m) m out).inputSymbol = none :=
        inputSymbol_eq_none_of_boundary (Or.inr (by simp [lbCfg] <;> omega))
      rw [hsym]
      simp only [lbTr]
  rw [hstop, apply_lbAct i₀ x _ _ _ s _ _ out (-1) (-1) _ m (by omega) ?_ none (x.take m) rfl,
    ← hend]
  · rw [← loadB_back i₀ n x s (x.take m) out m hm1]
    congr 2 <;> simp
  · apply Fin.ext
    have h := val_moveInputPos_eq (⟨1 + m, by omega⟩ : Fin (x.length + 2)) (-1)
    simp only [SignType.coe_neg, SignType.coe_one] at h
    simp only
    omega


/-! ### The machine of a framed program with a bounded loader -/

namespace XProg

/-- The machine of a framed program: load at most `n + 1` input bits onto tape `i₀`, run, emit
tape `o`. -/
noncomputable def toPTMB (p : XProg k) (i₀ o : Fin k) (n : ℕ) :
    MultiTapePTM k Bool ((Option (Fin (n + 2)) ⊕ p.State) ⊕ Bool) Empty :=
  ((ofDeterministic (loadBTM i₀ n)).seq (compile p)).seq (ofDeterministic (emitTM o))

/-- The clock: load at most `n + 1` bits, run from the input bound `n + 1`, emit. -/
def totalTimeB (p : XProg k) (i₀ o : Fin k) (n : ℕ) : ℕ :=
  (2 * (n + 1) + 2) + timeBoundT p (Prog.inputBound i₀ (n + 1)) +
    (2 * lenBoundT p (Prog.inputBound i₀ (n + 1)) o + 2)

theorem toPTMB_runsWords (p : XProg k) (hp : p.WF) (i₀ o : Fin k) (n : ℕ) (x : List Bool) :
    (p.toPTMB i₀ o n).RunsWords x (fun _ => []) [] (totalTimeB p i₀ o n)
      (ProbOracleComp.sample (denote p (inputStore i₀ (x.take (n + 1))))) id (fun s => s o) := by
  have hx : (x.take (n + 1)).length ≤ n + 1 := by simp
  have hload : (ofDeterministic (loadBTM i₀ n) : MultiTapePTM k Bool _ Empty).RunsWords x
      (fun _ => []) [] (2 * (n + 1) + 2)
      (ProbOracleComp.sample (pure (inputStore i₀ (x.take (n + 1))))) id (fun _ => []) :=
    (runsWords_of_runFrom (loadBTM_runFrom i₀ n x _ rfl [])).mono
      (by have := min_le_right x.length (n + 1); omega)
  have h₁ := RunsWords.seqStore hload (fun a ha => by
    simp only [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at ha
    subst ha
    exact compile_runsWordsT p hp x _ _ [] (Prog.fits_inputStore i₀ hx))
  rw [pure_bind] at h₁
  have h₂ := h₁.seq_bind (t₂ := 2 * lenBoundT p (Prog.inputBound i₀ (n + 1)) o + 2)
    (prog₂ := fun a => pure a) (ws₂ := fun _ => id)
    (emit₂ := fun _ b => b o) (fun a b hab => by simpa using hab)
    (fun a _ _ _ _ ha => by
      have hlen := lenBoundT_spec p _ _ (Prog.fits_inputStore i₀ hx) a
        (mem_support_of_runWith_sample ha) o
      refine (runsWords_of_runFrom_emit (e := fun b => b o)
        (emitTM_runFrom o x a ([] ++ []))).mono ?_
      omega)
  have h₃ := h₂.of_map Prod.snd id (fun s => s o)
  have heq : (Prod.snd <$> (ProbOracleComp.sample (denote p (inputStore i₀ (x.take (n + 1)))) >>=
      fun a => (fun b => (a, b)) <$>
        (pure a : ProbOracleComp (fun _ : Empty × List Bool => List Bool) _))) =
      ProbOracleComp.sample (denote p (inputStore i₀ (x.take (n + 1)))) := by
    simp
  rw [heq] at h₃
  exact h₃

/-- **The explicit machine of a framed program with a bounded loader.** -/
noncomputable def toMachineB (p : XProg k) (i₀ o : Fin k) (n : ℕ) : Machine :=
  Machine.ofPTM (p.toPTMB i₀ o n) (totalTimeB p i₀ o n)

/-- **Its output law, on every input**: the law of tape `o` after `p` from the first `n + 1` input
bits on tape `i₀`. -/
theorem run_toMachineB (p : XProg k) (hp : p.WF) (i₀ o : Fin k) (n : ℕ) (x : List Bool) :
    (p.toMachineB i₀ o n).run x =
      (p.law (inputStore i₀ (x.take (n + 1)))).map (fun s => s o) := by
  rw [toMachineB, Machine.run_ofPTM]
  exact Prog.eval_runClosed_of_runsWords (toPTMB_runsWords p hp i₀ o n x)

theorem time_toMachineB (p : XProg k) (i₀ o : Fin k) (n : ℕ) :
    (p.toMachineB i₀ o n).time = totalTimeB p i₀ o n := rfl

theorem tapes_toMachineB (p : XProg k) (i₀ o : Fin k) (n : ℕ) :
    (p.toMachineB i₀ o n).tapes = k := rfl

theorem states_toMachineB (p : XProg k) (i₀ o : Fin k) (n : ℕ) :
    (p.toMachineB i₀ o n).states = Fintype.card p.State + (n + 3) + 2 := by
  show Nat.card ((Option (Fin (n + 2)) ⊕ p.State) ⊕ Bool) = _
  rw [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_bool,
    Fintype.card_option, Fintype.card_fin]
  ring

/-- **The description length of the machine.** -/
theorem descLen_toMachineB (p : XProg k) (i₀ o : Fin k) (n : ℕ) :
    (p.toMachineB i₀ o n).descLen =
      6 * (Fintype.card p.State + (n + 3) + 2) * 3 ^ k * 3 ^ 0 *
        Machine.entryBits k (Fintype.card p.State + (n + 3) + 2) 0 := by
  rw [Machine.descLen, states_toMachineB]
  rfl

/-- **Coin-free programs give deterministic machines.** -/
theorem deterministic_toMachineB (p : XProg k) (hc : p.CoinFree) (i₀ o : Fin k) (n : ℕ) :
    (p.toMachineB i₀ o n).Deterministic :=
  deterministic_ofPTM (((coinIndep_ofDeterministic _).seq (coinIndep_compile p hc)).seq
    (coinIndep_ofDeterministic _)) _

end XProg

end SigabaNeo.Tape
