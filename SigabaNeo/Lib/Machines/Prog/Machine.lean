import SigabaNeo.Lib.Machines.Prog.Compile
import SigabaNeo.Lib.Machines.FromPTM

/-!
# Tape programs as explicit machines

`Prog.toMachine p i₀ o n` is a `SigabaNeo.Machine` (no oracles) that loads its input onto tape `i₀`
(`loadTM`, `2 |x| + 2` steps), runs the compiled program, and emits the word of tape `o`
(`emitTM`, `2 |w| + 2` steps). Its clock `totalTime p n` covers every input of length at most `n`.

## Main results

* `Prog.run_toMachine`: on an input `x` with `|x| ≤ n`, the output law is the law of the word on
  tape `o` after `p`, started from the store with `x` on tape `i₀` and blank tapes elsewhere.
* `Prog.cost_toMachine`: the cost, explicitly: `totalTime p n` plus the description length of a
  machine with `k` tapes and `p.size + 4` states.
-/

namespace SigabaNeo.Tape

open Cslib Turing MultiTapeMachine MultiTapePTM

variable {k : ℕ}

/-! ### Loading the input -/

/-- The action of the loader: move the input head by `di` and the head of tape `i₀` by `d`, writing
`w` there. -/
def ldAct (i₀ : Fin k) (di : SignType) (w : Option (Option Bool)) (d : SignType)
    (q : Option Bool) : Action k Bool Bool where
  inputTape := di
  workTapes t := if t = i₀ then (w, d) else (none, 0)
  output := none
  state := q

/-- The transitions of the loader: in state `false` copy the input to tape `i₀`, in state `true`
move both heads back. -/
def ldTr (i₀ : Fin k) : Bool → Option Bool → (Fin k → Option Bool) → Action k Bool Bool
  | false, some a, _ => ldAct i₀ 1 (some (some a)) 1 (some false)
  | false, none, _ => ldAct i₀ (-1) none (-1) (some true)
  | true, some _, _ => ldAct i₀ (-1) none (-1) (some true)
  | true, none, _ => ldAct i₀ 1 none 1 none

/-- Copy the input to the blank tape `i₀` and rewind. -/
def loadTM (i₀ : Fin k) : MultiTapeTM k Bool Bool := MultiTapeTM.ofTr false (ldTr i₀)

/-- A configuration of the loader: input head at `p`, the word `w` on tape `i₀` with its head at
`h`, the store `s` elsewhere. -/
def ldCfg (i₀ : Fin k) (x : List Bool) (q : Option Bool) (p : ℕ) (hp : p < x.length + 2)
    (s : Store k) (w : List Bool) (h : ℤ) (out : List Bool) : Cfg k Bool Bool x :=
  ⟨q, ⟨p, hp⟩, fun t => tapeOfList (Function.update s i₀ w t),
    Function.update (fun _ => 0) i₀ h, out⟩

theorem loadTM_step (i₀ : Fin k) (x : List Bool) (q : Bool) (p : ℕ) (hp : p < x.length + 2)
    (s : Store k) (w : List Bool) (h : ℤ) (out : List Bool) :
    (loadTM i₀).step (ldCfg i₀ x (some q) p hp s w h out) =
      (ldTr i₀ q (ldCfg i₀ x (some q) p hp s w h out).inputSymbol
        (ldCfg i₀ x (some q) p hp s w h out).workTapeSymbols).apply
        (ldCfg i₀ x (some q) p hp s w h out) := by
  rw [MultiTapeTM.step_of_state rfl, loadTM, MultiTapeTM.tr_ofTr]

theorem apply_ldAct (i₀ : Fin k) (x : List Bool) (q : Option Bool) (p : ℕ) (hp : p < x.length + 2)
    (s : Store k) (w : List Bool) (h : ℤ) (out : List Bool) (di : SignType) (d : SignType)
    (q' : Option Bool) (p' : ℕ) (hp' : p' < x.length + 2)
    (hmove : moveInputPos (⟨p, hp⟩ : Fin (x.length + 2)) di = ⟨p', hp'⟩)
    (wr : Option (Option Bool)) (w' : List Bool)
    (hw : (match wr with
      | none => tapeOfList w
      | some c => Function.update (tapeOfList w) h c) = tapeOfList w') :
    (ldAct i₀ di wr d q').apply (ldCfg i₀ x q p hp s w h out) =
      ldCfg i₀ x q' p' hp' s w' (h + d) out := by
  refine Cfg.ext rfl ?_ ?_ ?_ (by simp [Action.apply, ldAct, ldCfg])
  · simpa [Action.apply, ldAct, ldCfg] using hmove
  · funext t
    by_cases ht : t = i₀
    · subst ht
      simp only [Action.apply, ldAct, ldCfg, ↓reduceIte, Function.update_self]
      rw [← hw]
      cases wr <;> rfl
    · simp [Action.apply, ldAct, ldCfg, ht]
  · funext t
    by_cases ht : t = i₀
    · subst ht; simp [Action.apply, ldAct, ldCfg]
    · simp [Action.apply, ldAct, ldCfg, ht]

theorem loadTM_runFrom_add (i₀ : Fin k) (x : List Bool) (c : Cfg k Bool Bool x) (a b : ℕ) :
    (loadTM i₀).runFrom c (a + b) = (loadTM i₀).runFrom ((loadTM i₀).runFrom c a) b := by
  show (loadTM i₀).step^[a + b] c = (loadTM i₀).step^[b] ((loadTM i₀).step^[a] c)
  rw [Nat.add_comm, Function.iterate_add_apply]

theorem loadTM_runFrom_one (i₀ : Fin k) (x : List Bool) (c : Cfg k Bool Bool x) :
    (loadTM i₀).runFrom c 1 = (loadTM i₀).step c := rfl

theorem ldCfg_workTapeSymbols (i₀ : Fin k) (x : List Bool) (q : Option Bool) (p : ℕ)
    (hp : p < x.length + 2) (s : Store k) (w : List Bool) (h : ℤ) (out : List Bool) :
    (ldCfg i₀ x q p hp s w h out).workTapeSymbols i₀ = tapeOfList w h := by
  simp [Cfg.workTapeSymbols, ldCfg]

/-- The copying phase. -/
theorem load_copy (i₀ : Fin k) (x : List Bool) (s : Store k) (out : List Bool) :
    ∀ m (hm : m ≤ x.length),
      (loadTM i₀).runFrom (ldCfg i₀ x (some false) 1 (by omega) s [] 0 out) m =
        ldCfg i₀ x (some false) (1 + m) (by omega) s (x.take m) m out := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro _hm
    rw [loadTM_runFrom_add, ih (by omega), loadTM_runFrom_one, loadTM_step]
    have hsym : (ldCfg i₀ x (some false) (1 + m) (by omega) s (x.take m) m out).inputSymbol =
        some x[m] := inputSymbolInner m (by simp [ldCfg] <;> omega) (by omega)
    rw [hsym]
    simp only [ldTr]
    refine (apply_ldAct i₀ x _ _ _ s _ _ out 1 1 _ (1 + (m + 1)) (by omega) ?_ _
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
theorem load_back (i₀ : Fin k) (x : List Bool) (s : Store k) (out : List Bool) :
    ∀ j (hj : j ≤ x.length),
      (loadTM i₀).runFrom (ldCfg i₀ x (some true) j (by omega) s x ((j : ℤ) - 1) out) (j + 1) =
        ldCfg i₀ x none 1 (by omega) s x 0 out := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [loadTM_runFrom_one, loadTM_step]
    have hsym : (ldCfg i₀ x (some true) 0 (by omega) s x ((0 : ℕ) - 1) out).inputSymbol = none :=
      inputSymbol_eq_none_of_boundary (Or.inl rfl)
    rw [hsym]
    simp only [ldTr]
    refine (apply_ldAct i₀ x _ _ _ s _ _ out 1 1 _ 1 (by omega) ?_ none x rfl).trans ?_
    · apply Fin.ext
      have h := val_moveInputPos_eq (⟨0, by omega⟩ : Fin (x.length + 2)) 1
      simp only [SignType.coe_one] at h
      simp only
      omega
    · simp
  | succ j ih =>
    intro hj
    rw [show j + 1 + 1 = 1 + (j + 1) by omega, loadTM_runFrom_add, loadTM_runFrom_one, loadTM_step]
    have hsym : (ldCfg i₀ x (some true) (j + 1) (by omega) s x (((j + 1 : ℕ) : ℤ) - 1)
        out).inputSymbol = some x[j] := inputSymbolInner j (by simp [ldCfg] <;> omega) (by omega)
    rw [hsym]
    simp only [ldTr]
    refine (congrArg (fun c => (loadTM i₀).runFrom c (j + 1))
      (apply_ldAct i₀ x _ _ _ s _ _ out (-1) (-1) _ j (by omega) ?_ none x rfl)).trans ?_
    · apply Fin.ext
      have h := val_moveInputPos_eq (⟨j + 1, by omega⟩ : Fin (x.length + 2)) (-1)
      simp only [SignType.coe_neg, SignType.coe_one] at h
      simp only
      omega
    · rw [← ih (by omega)]
      congr 2
      simp only [SignType.coe_neg, SignType.coe_one]
      push_cast; ring

/-- **The loader**: after `2 |x| + 2` steps the input is on tape `i₀`, all heads at the start. -/
theorem loadTM_runFrom (i₀ : Fin k) (x : List Bool) (s : Store k) (hs : s i₀ = [])
    (out : List Bool) :
    (loadTM i₀).runFrom (wordsCfg x (some (loadTM i₀).q₀) s out) (2 * x.length + 2) =
      wordsCfg x none (Function.update s i₀ x) out := by
  have hstart : (wordsCfg x (some (loadTM i₀).q₀) s out : Cfg k Bool Bool x) =
      ldCfg i₀ x (some false) 1 (by omega) s [] 0 out := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext t
      by_cases ht : t = i₀
      · subst ht; simp [ldCfg, hs, wordsCfg]
      · simp [ldCfg, ht, wordsCfg]
    · funext t
      by_cases ht : t = i₀
      · subst ht; simp [ldCfg, wordsCfg]
      · simp [ldCfg, ht, wordsCfg]
  have hend : ldCfg i₀ x none 1 (by omega) s x 0 out = wordsCfg x none (Function.update s i₀ x) out := by
    refine Cfg.ext rfl rfl rfl ?_ rfl
    funext t
    by_cases ht : t = i₀
    · subst ht; simp [ldCfg]
    · simp [ldCfg, ht]
  rw [hstart, show 2 * x.length + 2 = x.length + (1 + (x.length + 1)) by omega, loadTM_runFrom_add,
    load_copy i₀ x s out x.length le_rfl, loadTM_runFrom_add, loadTM_runFrom_one, loadTM_step]
  have hsym : (ldCfg i₀ x (some false) (1 + x.length) (by omega) s (x.take x.length) x.length
      out).inputSymbol = none := inputSymbol_eq_none_of_boundary (Or.inr (by simp [ldCfg] <;> omega))
  rw [hsym, List.take_length]
  simp only [ldTr]
  rw [apply_ldAct i₀ x _ _ _ s _ _ out (-1) (-1) _ x.length (by omega) ?_ none x rfl, ← hend]
  · rw [← load_back i₀ x s out x.length le_rfl]
    congr 2 <;> simp
  · apply Fin.ext
    have h := val_moveInputPos_eq (⟨1 + x.length, by omega⟩ : Fin (x.length + 2)) (-1)
    simp only [SignType.coe_neg, SignType.coe_one] at h
    simp only
    omega

/-! ### Emitting the output -/

/-- The action of the emitter: move the head of tape `o` by `d`, emitting `e`. -/
def emAct (o : Fin k) (d : SignType) (e : Option Bool) (q : Option Bool) : Action k Bool Bool where
  inputTape := 0
  workTapes t := (none, if t = o then d else 0)
  output := e
  state := q

/-- The transitions of the emitter: in state `false` emit the word of tape `o`, in state `true`
move back. -/
def emTr (o : Fin k) : Bool → Option Bool → (Fin k → Option Bool) → Action k Bool Bool
  | false, _, w => match w o with
    | some a => emAct o 1 (some a) (some false)
    | none => emAct o (-1) none (some true)
  | true, _, w => match w o with
    | some _ => emAct o (-1) none (some true)
    | none => emAct o 1 none none

/-- Emit the word of tape `o` and rewind. -/
def emitTM (o : Fin k) : MultiTapeTM k Bool Bool := MultiTapeTM.ofTr false (emTr o)

/-- A configuration of the emitter: the store `s`, the head of tape `o` at `h`. -/
def emCfg (o : Fin k) (x : List Bool) (q : Option Bool) (s : Store k) (h : ℤ) (out : List Bool) :
    Cfg k Bool Bool x :=
  ⟨q, 1, fun t => tapeOfList (s t), Function.update (fun _ => 0) o h, out⟩

theorem emitTM_step (o : Fin k) (x : List Bool) (q : Bool) (s : Store k) (h : ℤ)
    (out : List Bool) :
    (emitTM o).step (emCfg o x (some q) s h out) =
      (emTr o q (emCfg o x (some q) s h out).inputSymbol (fun t => tapeOfList (s t)
        (Function.update (fun _ => (0 : ℤ)) o h t))).apply (emCfg o x (some q) s h out) := by
  rw [MultiTapeTM.step_of_state rfl, emitTM, MultiTapeTM.tr_ofTr]
  rfl

theorem apply_emAct (o : Fin k) (x : List Bool) (q : Option Bool) (s : Store k) (h : ℤ)
    (out : List Bool) (d : SignType) (e : Option Bool) (q' : Option Bool) :
    (emAct o d e q').apply (emCfg o x q s h out) = emCfg o x q' s (h + d) (out ++ e.toList) := by
  refine Cfg.ext rfl (by simp [Action.apply, emAct, emCfg]) rfl ?_ rfl
  funext t
  by_cases ht : t = o
  · subst ht; simp [Action.apply, emAct, emCfg]
  · simp [Action.apply, emAct, emCfg, ht]

theorem emitTM_runFrom_add (o : Fin k) (x : List Bool) (c : Cfg k Bool Bool x) (a b : ℕ) :
    (emitTM o).runFrom c (a + b) = (emitTM o).runFrom ((emitTM o).runFrom c a) b := by
  show (emitTM o).step^[a + b] c = (emitTM o).step^[b] ((emitTM o).step^[a] c)
  rw [Nat.add_comm, Function.iterate_add_apply]

theorem emitTM_runFrom_one (o : Fin k) (x : List Bool) (c : Cfg k Bool Bool x) :
    (emitTM o).runFrom c 1 = (emitTM o).step c := rfl

/-- The emitting phase. -/
theorem emit_fwd (o : Fin k) (x : List Bool) (s : Store k) (out : List Bool) :
    ∀ m (hm : m ≤ (s o).length),
      (emitTM o).runFrom (emCfg o x (some false) s 0 out) m =
        emCfg o x (some false) s m (out ++ (s o).take m) := by
  intro m
  induction m with
  | zero => intro _; simp; rfl
  | succ m ih =>
    intro _hm
    rw [emitTM_runFrom_add, ih (by omega), emitTM_runFrom_one, emitTM_step]
    have hsym : tapeOfList (s o) (Function.update (fun _ => (0 : ℤ)) o (m : ℤ) o) =
        some (s o)[m] := by simp
    simp only [emTr, hsym]
    rw [apply_emAct]
    have h1 : ((m : ℤ) + ((1 : SignType) : ℤ)) = ((m + 1 : ℕ) : ℤ) := by push_cast; simp
    rw [h1, List.take_succ_eq_append_getElem (by omega : m < (s o).length)]
    simp

/-- The rewinding phase. -/
theorem emit_back (o : Fin k) (x : List Bool) (s : Store k) (out : List Bool) :
    ∀ j (hj : j ≤ (s o).length),
      (emitTM o).runFrom (emCfg o x (some true) s ((j : ℤ) - 1) out) (j + 1) =
        emCfg o x none s 0 out := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [emitTM_runFrom_one, emitTM_step]
    have hsym : tapeOfList (s o) (Function.update (fun _ => (0 : ℤ)) o (((0 : ℕ) : ℤ) - 1) o) =
        none := by rw [Function.update_self]; rfl
    simp only [emTr, hsym]
    rw [apply_emAct]
    simp
  | succ j ih =>
    intro hj
    rw [show j + 1 + 1 = 1 + (j + 1) by omega, emitTM_runFrom_add, emitTM_runFrom_one, emitTM_step]
    have hsym : tapeOfList (s o) (Function.update (fun _ => (0 : ℤ)) o (((j + 1 : ℕ) : ℤ) - 1) o) =
        some (s o)[j] := by simp
    simp only [emTr, hsym]
    rw [apply_emAct, Option.toList_none, List.append_nil, ← ih (by omega)]
    congr 2
    simp only [SignType.coe_neg, SignType.coe_one]; push_cast; ring

/-- **The emitter**: after `2 |s o| + 2` steps it has emitted the word of tape `o`, all heads back
at the start. -/
theorem emitTM_runFrom (o : Fin k) (x : List Bool) (s : Store k) (out : List Bool) :
    (emitTM o).runFrom (wordsCfg x (some (emitTM o).q₀) s out) (2 * (s o).length + 2) =
      wordsCfg x none s (out ++ s o) := by
  have hstart : (wordsCfg x (some (emitTM o).q₀) s out : Cfg k Bool Bool x) =
      emCfg o x (some false) s 0 out := by
    refine Cfg.ext rfl rfl rfl ?_ rfl
    funext t
    by_cases ht : t = o
    · subst ht; simp [emCfg]
    · simp [emCfg, ht]
  have hend : emCfg o x none s 0 (out ++ s o) = wordsCfg x none s (out ++ s o) := by
    refine Cfg.ext rfl rfl rfl ?_ rfl
    funext t
    by_cases ht : t = o
    · subst ht; simp [emCfg]
    · simp [emCfg, ht]
  rw [hstart, show 2 * (s o).length + 2 = (s o).length + (1 + ((s o).length + 1)) by omega,
    emitTM_runFrom_add, emit_fwd o x s out _ le_rfl, emitTM_runFrom_add, emitTM_runFrom_one,
    emitTM_step]
  have hsym : tapeOfList (s o) (Function.update (fun _ => (0 : ℤ)) o ((s o).length : ℤ) o) =
      none := by simp
  simp only [emTr, hsym, List.take_length]
  rw [apply_emAct, ← hend, ← emit_back o x s _ (s o).length le_rfl]
  congr 2 <;> simp

/-! ### The machine of a program -/

/-- A deterministic run from words to words, emitting `e`, is a `RunsWords` phase. -/
theorem runsWords_of_runFrom_emit {S : Type} {tm : MultiTapeTM k Bool S} {x : List Bool}
    {ws ws' : Store k} {out₀ : List Bool} {e : Store k → List Bool} {t : ℕ}
    (h : tm.runFrom (wordsCfg x (some tm.q₀) ws out₀) t = wordsCfg x none ws' (out₀ ++ e ws')) :
    (MultiTapePTM.ofDeterministic tm : MultiTapePTM k Bool S Empty).RunsWords x ws out₀ t
      (pure ws') id e := by
  intro OracleState oracle st cfg htapes hbuf
  have htapes' : cfg.tapes = wordsCfg x (some tm.q₀) ws out₀ := htapes
  dsimp only
  rw [MultiTapePTM.run_interpret_runOracleConfigFrom_ofDeterministic, htapes', h]
  simp only [ProbOracleComp.runWith_pure, PMF.pure_map, PMF.support_pure, Set.mem_singleton_iff,
    forall_eq, true_and, id]
  exact hbuf

/-- The store holding the input `x` on tape `i₀` and blank tapes elsewhere. -/
def inputStore (i₀ : Fin k) (x : List Bool) : Store k := Function.update (fun _ => []) i₀ x

theorem maxLen_inputStore (i₀ : Fin k) (x : List Bool) : maxLen (inputStore i₀ x) ≤ x.length :=
  maxLen_update_le _ i₀ x (by simp [maxLen]) le_rfl

namespace Prog

/-- The machine of a program: load the input onto tape `i₀`, run the program, emit tape `o`. -/
noncomputable def toPTM (p : Prog k) (i₀ o : Fin k) :
    MultiTapePTM k Bool ((Bool ⊕ p.State) ⊕ Bool) Empty :=
  ((ofDeterministic (loadTM i₀)).seq (compile p)).seq (ofDeterministic (emitTM o))

/-- The clock of the machine of a program, for inputs at most `n` long. -/
def totalTime (p : Prog k) (n : ℕ) : ℕ := (2 * n + 2) + timeBound p n + (2 * lenBound p n + 2)

/-- **The machine of a program as a phase**: on an input at most `n` long, from blank tapes, it
emits the word on tape `o` after `p`, within `totalTime p n` steps. -/
theorem toPTM_runsWords (p : Prog k) (hp : p.WF) (i₀ o : Fin k) (n : ℕ) (x : List Bool)
    (hx : x.length ≤ n) :
    (p.toPTM i₀ o).RunsWords x (fun _ => []) [] (totalTime p n)
      (ProbOracleComp.sample (denote p (inputStore i₀ x))) id (fun s => s o) := by
  have hload : (ofDeterministic (loadTM i₀) : MultiTapePTM k Bool Bool Empty).RunsWords x
      (fun _ => []) [] (2 * n + 2) (ProbOracleComp.sample (pure (inputStore i₀ x))) id
      (fun _ => []) :=
    (runsWords_of_runFrom (loadTM_runFrom i₀ x _ rfl [])).mono (by omega)
  have h₁ := RunsWords.seqStore hload (fun a ha => by
    simp only [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at ha
    subst ha
    exact compile_runsWords p hp x n _ [] ((maxLen_inputStore i₀ x).trans hx))
  rw [pure_bind] at h₁
  have h₂ := h₁.seq_bind (t₂ := 2 * lenBound p n + 2) (prog₂ := fun a => pure a)
    (ws₂ := fun _ => id)
    (emit₂ := fun _ b => b o) (fun a b hab => by simpa using hab)
    (fun a _ _ _ _ ha => by
      have hlen := lenBound_spec p n _ ((maxLen_inputStore i₀ x).trans hx) a
        (mem_support_of_runWith_sample ha)
      refine (runsWords_of_runFrom_emit (e := fun b => b o)
        (emitTM_runFrom o x a ([] ++ []))).mono ?_
      have := (length_le_maxLen a o).trans hlen
      omega)
  have h₃ := h₂.of_map Prod.snd id (fun s => s o)
  have heq : (Prod.snd <$> (ProbOracleComp.sample (denote p (inputStore i₀ x)) >>= fun a =>
      (fun b => (a, b)) <$> (pure a : ProbOracleComp (fun _ : Empty × List Bool => List Bool) _))) =
      ProbOracleComp.sample (denote p (inputStore i₀ x)) := by
    simp
  rw [heq] at h₃
  exact h₃

/-- The output law of a closed machine realizing a `RunsWords` phase from blank tapes. -/
theorem eval_runClosed_of_runsWords {S : Type} {M : MultiTapePTM k Bool S Empty} {x : List Bool}
    {t : ℕ} {A : ProbComp (Store k)} {ws : Store k → Store k} {emit : Store k → List Bool}
    (h : M.RunsWords x (fun _ => []) [] t (ProbOracleComp.sample A) ws emit) :
    ProbComp.eval (M.runClosed t x) = (ProbComp.eval A).map emit := by
  have hlaw := (h Unit (fun q => q.1.elim) () (M.initialConfig x)
    (Cfg.init_eq_wordsCfg M.initial x) (fun op => op.elim)).1
  have hrun : ProbOracleComp.runWith (fun q => q.1.elim) (M.runOracle t x) () =
      (ProbComp.eval (M.runClosed t x)).map (·, ()) := by
    rw [runOracle_eq_sample_runClosed, ProbOracleComp.runWith_sample]
  rw [runOracle_eq_map, ProbOracleComp.runWith_map] at hrun
  calc ProbComp.eval (M.runClosed t x)
      = ((ProbComp.eval (M.runClosed t x)).map (·, ())).map Prod.fst := by
        rw [PMF.map_comp]; exact (PMF.map_id _).symm
    _ = ((ProbOracleComp.runWith (fun q => q.1.elim)
          (M.runOracleConfigFrom t (M.initialConfig x)) ()).map
            (fun (final, s') => (final.tapes, s'))).map (fun p => p.1.output) := by
        rw [← hrun, PMF.map_comp, PMF.map_comp]; rfl
    _ = (ProbComp.eval A).map emit := by
        rw [hlaw, ProbOracleComp.runWith_sample, PMF.map_comp, PMF.map_comp]
        rfl

/-- The explicit machine (no oracles) of a program, with input on tape `i₀`, output on tape `o`,
and a clock for inputs at most `n` long. -/
noncomputable def toMachine (p : Prog k) (i₀ o : Fin k) (n : ℕ) : Machine :=
  Machine.ofPTM (p.toPTM i₀ o) (totalTime p n)

/-- **The output law of the machine of a program**: on an input at most `n` long, the law of the
word on tape `o` after `p`, started with `x` on tape `i₀` and blank tapes elsewhere. -/
theorem run_toMachine (p : Prog k) (hp : p.WF) (i₀ o : Fin k) (n : ℕ) (x : List Bool)
    (hx : x.length ≤ n) :
    (p.toMachine i₀ o n).run x = (p.law (inputStore i₀ x)).map (fun s => s o) := by
  rw [toMachine, Machine.run_ofPTM]
  exact eval_runClosed_of_runsWords (toPTM_runsWords p hp i₀ o n x hx)

/-- The number of states of the machine of a program. -/
theorem states_toMachine (p : Prog k) (i₀ o : Fin k) (n : ℕ) :
    (p.toMachine i₀ o n).states = p.size + 4 := by
  show Nat.card ((Bool ⊕ p.State) ⊕ Bool) = _
  rw [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_bool,
    show Fintype.card p.State = p.size from p.card_state]
  ring

/-- **The cost of the machine of a program**, explicitly: its clock plus the description length
of a machine with `k` tapes and `p.size + 4` states. -/
theorem cost_toMachine (p : Prog k) (i₀ o : Fin k) (n : ℕ) :
    (p.toMachine i₀ o n).cost =
      totalTime p n + 6 * (p.size + 4) * 3 ^ k * 3 ^ 0 * Machine.entryBits k (p.size + 4) 0 := by
  rw [Machine.cost, Machine.descLen, states_toMachine]
  rfl

end Prog

end SigabaNeo.Tape
