import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.RunsWords
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option

/-!
# Column machines

The primitives of the tape language (`SigabaNeoStd.Machines.Prog.Basic`) are instances of one
deterministic machine shape, the *column machine* `colTM S` of a `ColSpec S`. It moves the heads of
all `k` work tapes in lockstep, so at each step it reads one *column*: the cells at one position of
all tapes. On the store `s` (a word on each tape), with `P = maxLen s` the length of the longest
word and `e = S.e` extra (padding) columns, it

1. moves right over the columns `0, …, P + e - 1`, replacing each column `c` by `(S.fwd u c).2` and
   updating the forward state `u` (the forward pass; it only replaces nonblank columns by nonblank
   ones, so the end of the words stays detectable);
2. moves back left over the same columns, replacing each column `c` by `(S.bwd u c).2`, starting
   from the final forward state (the backward pass); it detects the left end by the blank column
   at cell `-1`;
3. replaces column `0` by `S.post u (column 0)`, `u` the final backward state, and halts.

It takes exactly `2 (P + e) + 3` steps (`colTM_runFrom`). Its final tapes are read off the columns
computed by the list functions `fwdRun`, `bwdRun` (`colResult`). The states are
`CQ e = scan | pad | back | main | post`, each with a control value in `U = Bool × Bool × Option
Bool`, so `Fintype.card (CQ e) = (3 + 2 e) * 12`.

## Main definitions

* `Store k`, `Col k`, `cols`, `tapesOf`, `maxLen`: stores, columns and the tapes they describe.
* `ColSpec`, `colTM`, `colResult`: the column machine of a specification and its list semantics.

## Main results

* `colTM_runFrom`: the run of the column machine, step-exactly.
* `colTM_runsWords`: its `RunsWords` specification within any clock `≥ 2 (maxLen s + e) + 3`.
-/

namespace SigabaNeo.Tape

open Cslib Turing

/-- A store: a word on each of the `k` work tapes. -/
abbrev Store (k : ℕ) := Fin k → List Bool

/-- A column: the cells at one position of the `k` tapes (`none` is blank). -/
abbrev Col (k : ℕ) := Fin k → Option Bool

variable {k : ℕ}

/-- The blank column. -/
def blankCol : Col k := fun _ => none

/-- Whether a column is blank. -/
def isBlank (c : Col k) : Bool := decide (∀ i, c i = none)

theorem isBlank_eq_true_iff (c : Col k) : isBlank c = true ↔ c = blankCol := by
  simp [isBlank, blankCol, funext_iff]

@[simp] theorem isBlank_blankCol : isBlank (blankCol : Col k) = true :=
  (isBlank_eq_true_iff _).mpr rfl

/-- Column `p` of a store. -/
def colAt (s : Store k) (p : ℕ) : Col k := fun i => (s i)[p]?

/-- The first `n` columns of a store. -/
def cols (s : Store k) (n : ℕ) : List (Col k) := (List.range n).map (colAt s)

@[simp] theorem length_cols (s : Store k) (n : ℕ) : (cols s n).length = n := by simp [cols]

theorem getElem_cols (s : Store k) (n p : ℕ) (h : p < (cols s n).length) :
    (cols s n)[p] = colAt s p := by simp [cols]

theorem cols_add (s : Store k) (n m : ℕ) :
    cols s (n + m) = cols s n ++ (List.range m).map (fun p => colAt s (n + p)) := by
  simp [cols, List.range_add, List.map_append, Function.comp_def]

/-- The tapes described by a list of columns: cell `n ≥ 0` of tape `i` is entry `i` of column `n`,
blank beyond the list and at negative cells. -/
def tapesOf (cs : List (Col k)) (i : Fin k) : ℤ → Option Bool
  | .ofNat n => (cs[n]?).bind (fun c => c i)
  | .negSucc _ => none

/-- The length of the longest word. -/
def maxLen (s : Store k) : ℕ := Finset.univ.sup fun i => (s i).length

theorem length_le_maxLen (s : Store k) (i : Fin k) : (s i).length ≤ maxLen s :=
  Finset.le_sup (f := fun i => (s i).length) (Finset.mem_univ i)

theorem maxLen_le_iff (s : Store k) (L : ℕ) : maxLen s ≤ L ↔ ∀ i, (s i).length ≤ L := by
  simp [maxLen]

/-- Enough columns describe the words of the store. -/
theorem tapesOf_cols (s : Store k) {n : ℕ} (hn : maxLen s ≤ n) (i : Fin k) :
    tapesOf (cols s n) i = tapeOfList (s i) := by
  have hi := (length_le_maxLen s i).trans hn
  funext z
  cases z with
  | negSucc m => rfl
  | ofNat m =>
    simp only [tapesOf, tapeOfList, cols, List.getElem?_map]
    by_cases hm : m < n
    · simp [List.getElem?_range hm, colAt]
    · rw [List.getElem?_eq_none (by simp; omega)]
      exact (List.getElem?_eq_none (by omega)).symm

/-- A column before the end of the longest word is not blank. -/
theorem colAt_ne_blank (s : Store k) {p : ℕ} (hp : p < maxLen s) : isBlank (colAt s p) = false := by
  have : ∃ i, p < (s i).length := by
    by_contra h
    push Not at h
    exact absurd ((maxLen_le_iff s p).mpr h) (by omega)
  obtain ⟨i, hi⟩ := this
  rw [Bool.eq_false_iff, ne_eq, isBlank_eq_true_iff]
  intro h
  have := congrFun h i
  simp [colAt, blankCol, hi] at this

/-- The columns from the end of the longest word on are blank. -/
theorem colAt_blank (s : Store k) {p : ℕ} (hp : maxLen s ≤ p) : colAt s p = blankCol := by
  funext i
  have := (length_le_maxLen s i).trans hp
  simp [colAt, blankCol, List.getElem?_eq_none (by omega : (s i).length ≤ p)]

/-- Beyond the longest word, the columns are blank. -/
theorem cols_eq_append (s : Store k) {n : ℕ} (hn : maxLen s ≤ n) (m : ℕ) :
    cols s (n + m) = cols s n ++ List.replicate m blankCol := by
  rw [cols_add]
  congr 1
  apply List.ext_getElem (by simp)
  intro p h₁ h₂
  simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
  exact colAt_blank s (by omega)

theorem tapesOf_set (cs : List (Col k)) {n : ℕ} (hn : n < cs.length) (w : Col k) (i : Fin k) :
    tapesOf (cs.set n w) i = Function.update (tapesOf cs i) (n : ℤ) (w i) := by
  funext z
  cases z with
  | negSucc m => simp [tapesOf, Function.update, show Int.negSucc m ≠ (n : ℤ) by omega]
  | ofNat m =>
    by_cases hm : m = n
    · subst hm
      simp [tapesOf, hn]
    · have : (Int.ofNat m) ≠ (n : ℤ) := by simp [hm]
      simp only [tapesOf]
      rw [List.getElem?_set_ne (fun h => hm h.symm)]
      simp [Function.update, hm, tapesOf]

theorem tapesOf_neg (cs : List (Col k)) (i : Fin k) (c : Option Bool) :
    Function.update (tapesOf cs i) (-1) c = Function.update (tapesOf cs i) (-1) c := rfl

theorem update_tapesOf_neg_one (cs : List (Col k)) (i : Fin k) :
    Function.update (tapesOf cs i) (-1) none = tapesOf cs i := by
  funext z
  by_cases hz : z = -1
  · subst hz; rfl
  · simp [Function.update, hz]

/-- The forward/backward control values: two flags and an optional bit. -/
abbrev U := Bool × Bool × Option Bool

/-- Specification of a column machine. -/
structure ColSpec (k : ℕ) where
  /-- Number of padding columns processed after the longest word. -/
  e : ℕ
  /-- Initial forward state. -/
  u₀ : U
  /-- Forward pass: from a state and a column, the next state and the new column. -/
  fwd : U → Col k → U × Col k
  /-- Backward pass: from a state and a column, the next state and the new column. -/
  bwd : U → Col k → U × Col k
  /-- Final rewrite of column `0`. -/
  post : U → Col k → Col k
  /-- The forward pass keeps nonblank columns nonblank. -/
  fwd_ne : ∀ u c, isBlank c = false → isBlank (fwd u c).2 = false

namespace ColSpec

variable (S : ColSpec k)

/-- The forward pass over a list of columns, from the left. -/
def fwdRun : U → List (Col k) → U × List (Col k)
  | u, [] => (u, [])
  | u, c :: cs => ((fwdRun (S.fwd u c).1 cs).1, (S.fwd u c).2 :: (fwdRun (S.fwd u c).1 cs).2)

/-- The backward pass over a list of columns, from the right. -/
def bwdRun : U → List (Col k) → U × List (Col k)
  | u, [] => (u, [])
  | u, c :: cs =>
    ((S.bwd (bwdRun u cs).1 c).1, (S.bwd (bwdRun u cs).1 c).2 :: (bwdRun u cs).2)

@[simp] theorem fwdRun_nil (u : U) : S.fwdRun u [] = (u, []) := rfl
@[simp] theorem bwdRun_nil (u : U) : S.bwdRun u [] = (u, []) := rfl

theorem length_fwdRun (u : U) (cs : List (Col k)) : (S.fwdRun u cs).2.length = cs.length := by
  induction cs generalizing u with
  | nil => rfl
  | cons c cs ih => simp [fwdRun, ih]

theorem length_bwdRun (u : U) (cs : List (Col k)) : (S.bwdRun u cs).2.length = cs.length := by
  induction cs generalizing u with
  | nil => rfl
  | cons c cs ih => simp [bwdRun, ih]

theorem fwdRun_append (u : U) (a b : List (Col k)) :
    S.fwdRun u (a ++ b) =
      ((S.fwdRun (S.fwdRun u a).1 b).1, (S.fwdRun u a).2 ++ (S.fwdRun (S.fwdRun u a).1 b).2) := by
  induction a generalizing u with
  | nil => rfl
  | cons c a ih => simp [fwdRun, ih]

theorem bwdRun_append (u : U) (a b : List (Col k)) :
    S.bwdRun u (a ++ b) =
      ((S.bwdRun (S.bwdRun u b).1 a).1, (S.bwdRun (S.bwdRun u b).1 a).2 ++ (S.bwdRun u b).2) := by
  induction a generalizing u with
  | nil => rfl
  | cons c a ih => simp [bwdRun, ih]

theorem bwdRun_concat (u : U) (a : List (Col k)) (c : Col k) :
    S.bwdRun u (a ++ [c]) =
      ((S.bwdRun (S.bwd u c).1 a).1, (S.bwdRun (S.bwd u c).1 a).2 ++ [(S.bwd u c).2]) := by
  rw [bwdRun_append]; rfl

theorem fwdRun_ne_blank (u : U) (cs : List (Col k)) (h : ∀ c ∈ cs, isBlank c = false) :
    ∀ c ∈ (S.fwdRun u cs).2, isBlank c = false := by
  induction cs generalizing u with
  | nil => simp
  | cons c cs ih =>
    simp only [fwdRun, List.mem_cons, forall_eq_or_imp]
    exact ⟨S.fwd_ne u c (h c (by simp)), ih _ fun c' hc' => h c' (by simp [hc'])⟩

/-- Column `0` rewritten by `f` (the list is unchanged when empty). -/
def setHead (f : Col k → Col k) : List (Col k) → List (Col k)
  | [] => []
  | c :: cs => f c :: cs

/-- The final columns of the column machine on a store with longest word `P`: the forward pass over
`cols s (P + e)`, the backward pass over its result, and the rewrite of column `0`, followed by one
blank column. -/
def colResult (s : Store k) : List (Col k) :=
  let F := S.fwdRun S.u₀ (cols s (maxLen s + S.e))
  let B := S.bwdRun F.1 F.2
  setHead (S.post B.1) (B.2 ++ [blankCol])

end ColSpec

/-- States of the column machine: the forward pass over the words (`scan`) and over the padding
(`pad j`, at cell `P + j + 1`), the backward pass over the padding (`back j`, at cell `P + j`) and
over the words (`main`), and the final rewrite of column `0` (`post`). -/
inductive CQ (e : ℕ) where
  | scan (u : U)
  | pad (j : Fin e) (u : U)
  | back (j : Fin e) (u : U)
  | main (u : U)
  | post (u : U)
  deriving DecidableEq

/-- `CQ e` as a sum type. -/
def CQ.equiv (e : ℕ) : CQ e ≃ U ⊕ (Fin e × U) ⊕ (Fin e × U) ⊕ U ⊕ U where
  toFun
    | .scan u => .inl u
    | .pad j u => .inr (.inl (j, u))
    | .back j u => .inr (.inr (.inl (j, u)))
    | .main u => .inr (.inr (.inr (.inl u)))
    | .post u => .inr (.inr (.inr (.inr u)))
  invFun
    | .inl u => .scan u
    | .inr (.inl (j, u)) => .pad j u
    | .inr (.inr (.inl (j, u))) => .back j u
    | .inr (.inr (.inr (.inl u))) => .main u
    | .inr (.inr (.inr (.inr u))) => .post u
  left_inv q := by cases q <;> rfl
  right_inv q := by rcases q with _ | _ | _ | _ | _ <;> rfl

instance (e : ℕ) : Fintype (CQ e) := Fintype.ofEquiv _ (CQ.equiv e).symm

theorem card_CQ (e : ℕ) : Fintype.card (CQ e) = (3 + 2 * e) * 12 := by
  rw [Fintype.card_congr (CQ.equiv e)]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    Fintype.card_option]
  ring

/-- The action that writes the column `w` at the heads, moves all work heads by `d`, keeps the input
head, emits nothing and enters `q`. -/
def colAct {S : Type} (w : Col k) (d : SignType) (q : Option S) : Action k Bool S where
  inputTape := 0
  workTapes i := (some (w i), d)
  output := none
  state := q

namespace ColSpec

variable (S : ColSpec k)

/-- The transitions of the column machine. -/
def tr : CQ S.e → Option Bool → Col k → Action k Bool (CQ S.e)
  | .scan u, _, c =>
    if isBlank c then
      if h : 0 < S.e then colAct (S.fwd u c).2 1 (some (.pad ⟨0, h⟩ (S.fwd u c).1))
      else colAct c (-1) (some (.main u))
    else colAct (S.fwd u c).2 1 (some (.scan (S.fwd u c).1))
  | .pad j u, _, c =>
    if h : j.val + 1 < S.e then colAct (S.fwd u c).2 1 (some (.pad ⟨j.val + 1, h⟩ (S.fwd u c).1))
    else colAct c (-1) (some (.back j u))
  | .back j u, _, c =>
    colAct (S.bwd u c).2 (-1)
      (some (if h : j.val = 0 then .main (S.bwd u c).1 else .back ⟨j.val - 1, by omega⟩ (S.bwd u c).1))
  | .main u, _, c =>
    if isBlank c then colAct c 1 (some (.post u))
    else colAct (S.bwd u c).2 (-1) (some (.main (S.bwd u c).1))
  | .post u, _, c => colAct (S.post u c) 0 none

end ColSpec

/-- The column machine of a specification. -/
def colTM (S : ColSpec k) : MultiTapeTM k Bool (CQ S.e) :=
  MultiTapeTM.ofTr (.scan S.u₀) S.tr

/-- A configuration of the column machine: the tapes described by `cs`, all work heads at `p`, the
input head at the start. -/
def ccfg {S : Type} (x : List Bool) (q : Option S) (cs : List (Col k)) (p : ℤ) (out : List Bool) :
    Cfg k Bool S x :=
  ⟨q, 1, tapesOf cs, fun _ => p, out⟩

theorem wordsCfg_eq_ccfg {S : Type} (x : List Bool) (q : Option S) (s : Store k) {n : ℕ}
    (hn : maxLen s ≤ n) (out : List Bool) :
    (wordsCfg x q s out : Cfg k Bool S x) = ccfg x q (cols s n) 0 out := by
  refine Cfg.ext rfl rfl ?_ rfl rfl
  funext i
  exact (tapesOf_cols s hn i).symm

theorem ccfg_eq_wordsCfg {S : Type} (x : List Bool) (q : Option S) (cs : List (Col k))
    (s : Store k) (h : ∀ i, tapesOf cs i = tapeOfList (s i)) (out : List Bool) :
    (ccfg x q cs 0 out : Cfg k Bool S x) = wordsCfg x q s out := by
  refine Cfg.ext rfl rfl ?_ rfl rfl
  funext i
  exact h i

theorem apply_colAct {S : Type} (x : List Bool) (q : Option S) (cs : List (Col k)) (n : ℕ)
    (hn : n < cs.length) (out : List Bool) (w : Col k) (d : SignType) (q' : Option S) :
    (colAct w d q').apply (ccfg x q cs n out) = ccfg x q' (cs.set n w) (n + d) out := by
  refine Cfg.ext rfl ?_ ?_ rfl ?_
  · simp [Action.apply, colAct, ccfg]
  · funext i
    simp only [Action.apply, colAct, ccfg]
    exact (tapesOf_set cs hn w i).symm
  · simp [Action.apply, colAct, ccfg]

theorem apply_colAct_neg {S : Type} (x : List Bool) (q : Option S) (cs : List (Col k))
    (out : List Bool) (d : SignType) (q' : Option S) :
    (colAct blankCol d q').apply (ccfg x q cs (-1) out) = ccfg x q' cs (-1 + d) out := by
  refine Cfg.ext rfl ?_ ?_ rfl ?_
  · simp [Action.apply, colAct, ccfg]
  · funext i
    simp only [Action.apply, colAct, ccfg, blankCol]
    exact update_tapesOf_neg_one cs i
  · simp [Action.apply, colAct, ccfg]

theorem workTapeSymbols_ccfg {S : Type} (x : List Bool) (q : Option S) (cs : List (Col k)) (n : ℕ)
    (hn : n < cs.length) (out : List Bool) :
    (ccfg x q cs n out).workTapeSymbols = cs[n] := by
  funext i
  simp [Cfg.workTapeSymbols, ccfg, tapesOf, hn]

theorem workTapeSymbols_ccfg_neg {S : Type} (x : List Bool) (q : Option S) (cs : List (Col k))
    (out : List Bool) : (ccfg x q cs (-1) out).workTapeSymbols = blankCol := by
  funext i
  rfl

namespace ColSpec

variable (S : ColSpec k) (x : List Bool) (out : List Bool)

theorem step_ccfg (q : CQ S.e) (cs : List (Col k)) (n : ℕ) (hn : n < cs.length) :
    (colTM S).step (ccfg x (some q) cs n out) =
      (S.tr q (ccfg x (some q) cs n out).inputSymbol cs[n]).apply (ccfg x (some q) cs n out) := by
  rw [MultiTapeTM.step_of_state rfl, colTM, MultiTapeTM.tr_ofTr, workTapeSymbols_ccfg x _ cs n hn]

theorem step_ccfg' (q : CQ S.e) (cs : List (Col k)) (p : ℤ) (n : ℕ) (hp : p = n)
    (hn : n < cs.length) :
    (colTM S).step (ccfg x (some q) cs p out) =
      (S.tr q (ccfg x (some q) cs n out).inputSymbol cs[n]).apply (ccfg x (some q) cs n out) := by
  subst hp
  exact S.step_ccfg x out q cs n hn

theorem runFrom_succ (c : Cfg k Bool (CQ S.e) x) (t : ℕ) :
    (colTM S).runFrom c (t + 1) = (colTM S).runFrom ((colTM S).step c) t := by
  show (colTM S).step^[t + 1] c = (colTM S).step^[t] ((colTM S).step c)
  rw [Function.iterate_succ_apply]

theorem runFrom_add (c : Cfg k Bool (CQ S.e) x) (a b : ℕ) :
    (colTM S).runFrom c (a + b) = (colTM S).runFrom ((colTM S).runFrom c a) b := by
  show (colTM S).step^[a + b] c = (colTM S).step^[b] ((colTM S).step^[a] c)
  rw [Nat.add_comm, Function.iterate_add_apply]

theorem runFrom_one (c : Cfg k Bool (CQ S.e) x) : (colTM S).runFrom c 1 = (colTM S).step c := rfl

theorem runFrom_zero (c : Cfg k Bool (CQ S.e) x) : (colTM S).runFrom c 0 = c := rfl

/-- The forward pass over nonblank columns. -/
theorem run_scan (pre rest tail : List (Col k)) (u : U) (hrest : ∀ c ∈ rest, isBlank c = false)
    (_htail : tail ≠ []) :
    (colTM S).runFrom (ccfg x (some (.scan u)) (pre ++ rest ++ tail) pre.length out) rest.length =
      ccfg x (some (.scan (S.fwdRun u rest).1)) (pre ++ (S.fwdRun u rest).2 ++ tail)
        (pre.length + rest.length) out := by
  induction rest generalizing pre u with
  | nil => simp [runFrom_zero]
  | cons c rest ih =>
    have hlen : pre.length < (pre ++ c :: rest ++ tail).length := by simp
    have hget : (pre ++ c :: rest ++ tail)[pre.length] = c := by simp
    have hc : isBlank c = false := hrest c (by simp)
    rw [List.length_cons, runFrom_succ, step_ccfg S x out _ _ _ hlen, hget]
    simp only [tr, hc, Bool.false_eq_true, ↓reduceIte]
    rw [apply_colAct x _ _ _ hlen]
    have hset : (pre ++ c :: rest ++ tail).set pre.length (S.fwd u c).2 =
        (pre ++ [(S.fwd u c).2]) ++ rest ++ tail := by simp
    rw [hset]
    have := ih (pre ++ [(S.fwd u c).2]) (S.fwd u c).1 (fun c' hc' => hrest c' (by simp [hc']))
    simp only [List.length_append, List.length_singleton] at this
    simp only [SignType.coe_one, Nat.cast_add, Nat.cast_one]
    rw [show (pre.length : ℤ) + 1 = ((pre.length + 1 : ℕ) : ℤ) by push_cast; rfl, this]
    simp only [fwdRun, List.append_assoc, List.cons_append, List.singleton_append]
    congr 1
    push_cast; ring

/-- The forward pass over the padding columns, ending with the turn. -/
theorem run_pad (pre : List (Col k)) (u : U) (m : ℕ) (j : Fin S.e) (hj : j.val + 1 + m = S.e) :
    (colTM S).runFrom (ccfg x (some (.pad j u)) (pre ++ List.replicate (m + 1) blankCol)
      pre.length out) (m + 1) =
      ccfg x (some (.back ⟨S.e - 1, by omega⟩ (S.fwdRun u (List.replicate m blankCol)).1))
        (pre ++ (S.fwdRun u (List.replicate m blankCol)).2 ++ [blankCol])
        (pre.length + m - 1) out := by
  induction m generalizing pre u j with
  | zero =>
    have hlen : pre.length < (pre ++ List.replicate 1 blankCol).length := by simp
    rw [runFrom_succ, runFrom_zero, step_ccfg S x out _ _ _ hlen]
    have hget : (pre ++ List.replicate 1 blankCol)[pre.length] = blankCol := by simp
    rw [hget]
    have hnot : ¬ j.val + 1 < S.e := by omega
    simp only [tr, hnot, ↓reduceDIte]
    rw [apply_colAct x _ _ _ hlen]
    have hj' : (⟨S.e - 1, by omega⟩ : Fin S.e) = j := Fin.ext (by simp; omega)
    simp only [hj', fwdRun_nil, List.append_nil, Nat.add_zero, SignType.coe_neg, SignType.coe_one]
    congr 1
    simp
  | succ m ih =>
    have hlen : pre.length < (pre ++ List.replicate (m + 1 + 1) blankCol).length := by simp
    rw [runFrom_succ, step_ccfg S x out _ _ _ hlen]
    have hget : (pre ++ List.replicate (m + 1 + 1) blankCol)[pre.length] = blankCol := by simp
    rw [hget]
    have hlt : j.val + 1 < S.e := by omega
    simp only [tr, hlt, ↓reduceDIte]
    rw [apply_colAct x _ _ _ hlen]
    have hset : (pre ++ List.replicate (m + 1 + 1) blankCol).set pre.length
        (S.fwd u blankCol).2 = (pre ++ [(S.fwd u blankCol).2]) ++ List.replicate (m + 1) blankCol := by
      simp [List.replicate_succ]
    rw [hset]
    have := ih (pre ++ [(S.fwd u blankCol).2]) (S.fwd u blankCol).1 ⟨j.val + 1, hlt⟩ (by simp; omega)
    simp only [List.length_append, List.length_singleton] at this
    simp only [SignType.coe_one]
    rw [show (pre.length : ℤ) + 1 = ((pre.length + 1 : ℕ) : ℤ) by push_cast; rfl, this]
    simp only [List.replicate_succ, fwdRun, List.append_assoc, List.cons_append,
      List.singleton_append]
    congr 1
    omega

/-- The backward pass over the padding columns. -/
theorem run_back (pre mid suffix : List (Col k)) (u : U) (j : ℕ) (hj : j < S.e)
    (hmid : mid.length = j + 1) :
    (colTM S).runFrom (ccfg x (some (.back ⟨j, hj⟩ u)) (pre ++ mid ++ suffix)
      ((pre.length + j : ℕ) : ℤ) out) (j + 1) =
      ccfg x (some (.main (S.bwdRun u mid).1)) (pre ++ (S.bwdRun u mid).2 ++ suffix)
        ((pre.length : ℤ) - 1) out := by
  induction j generalizing mid u suffix with
  | zero =>
    obtain ⟨c, rfl⟩ : ∃ c, mid = [c] := by
      match mid, hmid with
      | [c], _ => exact ⟨c, rfl⟩
    have hlen : pre.length + 0 < (pre ++ [c] ++ suffix).length := by simp
    rw [runFrom_succ, runFrom_zero, step_ccfg S x out _ _ _ hlen]
    have hget : (pre ++ [c] ++ suffix)[pre.length + 0] = c := by simp
    rw [hget]
    simp only [tr, ↓reduceDIte]
    rw [apply_colAct x _ _ _ hlen]
    simp [bwdRun, sub_eq_add_neg]
  | succ j ih =>
    obtain ⟨mid₀, c, rfl⟩ : ∃ mid₀ c, mid = mid₀ ++ [c] := by
      rcases List.eq_nil_or_concat mid with h | ⟨mid₀, c, h⟩
      · simp [h] at hmid
      · exact ⟨mid₀, c, by simpa using h⟩
    have hmid₀ : mid₀.length = j + 1 := by simpa using hmid
    have hlen : pre.length + (j + 1) < (pre ++ (mid₀ ++ [c]) ++ suffix).length := by simp; omega
    rw [runFrom_succ, step_ccfg S x out _ _ _ hlen]
    have hget : (pre ++ (mid₀ ++ [c]) ++ suffix)[pre.length + (j + 1)] = c := by
      simp [List.getElem_append_right, hmid₀]
    rw [hget]
    simp only [tr, show j + 1 ≠ 0 by omega, ↓reduceDIte, Nat.add_sub_cancel]
    rw [apply_colAct x _ _ _ hlen]
    have hset : (pre ++ (mid₀ ++ [c]) ++ suffix).set (pre.length + (j + 1)) (S.bwd u c).2 =
        pre ++ mid₀ ++ ((S.bwd u c).2 :: suffix) := by
      rw [List.set_append_left _ _ (by simp; omega)]
      simp [List.set_append_right, hmid₀]
    rw [hset]
    have := ih (mid := mid₀) (u := (S.bwd u c).1) (suffix := (S.bwd u c).2 :: suffix) (by omega)
      hmid₀
    simp only [SignType.coe_neg, SignType.coe_one]
    rw [show ((pre.length + (j + 1) : ℕ) : ℤ) + -1 = ((pre.length + j : ℕ) : ℤ) by push_cast; ring,
      this, bwdRun_concat]
    simp

/-- The backward pass over nonblank columns, up to the blank column at cell `-1`. -/
theorem run_main (pre suffix : List (Col k)) (u : U) (hpre : ∀ c ∈ pre, isBlank c = false) :
    (colTM S).runFrom (ccfg x (some (.main u)) (pre ++ suffix) ((pre.length : ℤ) - 1) out)
      pre.length =
      ccfg x (some (.main (S.bwdRun u pre).1)) ((S.bwdRun u pre).2 ++ suffix) (-1) out := by
  induction pre using List.reverseRecOn generalizing suffix u with
  | nil => simp [runFrom_zero]
  | append_singleton pre c ih =>
    have hlen : pre.length < (pre ++ [c] ++ suffix).length := by simp
    have hc : isBlank c = false := hpre c (by simp)
    rw [List.length_append, List.length_singleton, runFrom_succ,
      step_ccfg' S x out _ _ _ pre.length (by simp) hlen]
    have hget : (pre ++ [c] ++ suffix)[pre.length] = c := by simp
    rw [hget]
    simp only [tr, hc, Bool.false_eq_true, ↓reduceIte]
    rw [apply_colAct x _ _ _ hlen]
    have hset : (pre ++ [c] ++ suffix).set pre.length (S.bwd u c).2 =
        pre ++ ((S.bwd u c).2 :: suffix) := by simp
    rw [hset, SignType.coe_neg, SignType.coe_one, ← sub_eq_add_neg,
      ih _ _ (fun c' hc' => hpre c' (by simp [hc'])), bwdRun_concat]
    simp

/-- The step at cell `-1` and the final rewrite of column `0`. -/
theorem run_end (cs : List (Col k)) (hcs : cs ≠ []) (u : U) :
    (colTM S).runFrom (ccfg x (some (.main u)) cs (-1) out) 2 =
      ccfg x none (setHead (S.post u) cs) 0 out := by
  have h1 : (colTM S).step (ccfg x (some (.main u)) cs (-1) out) =
      ccfg x (some (.post u)) cs 0 out := by
    rw [MultiTapeTM.step_of_state rfl, colTM, MultiTapeTM.tr_ofTr, workTapeSymbols_ccfg_neg]
    simp only [tr, isBlank_blankCol, ↓reduceIte]
    rw [apply_colAct_neg]
    simp
  rw [show (colTM S).runFrom (ccfg x (some (.main u)) cs (-1) out) 2 =
    (colTM S).step ((colTM S).step (ccfg x (some (.main u)) cs (-1) out)) from rfl, h1]
  have hlen : (0 : ℕ) < cs.length := List.length_pos_iff.mpr hcs
  rw [step_ccfg' S x out _ _ _ 0 (by simp) hlen]
  simp only [tr]
  rw [apply_colAct x _ _ _ hlen]
  obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil hcs
  simp [setHead]

/-- **The run of the column machine**: after exactly `2 (P + e) + 3` steps it has halted, its tapes
described by `colResult s`. -/
theorem colTM_runFrom (s : Store k) :
    (colTM S).runFrom (wordsCfg x (some (colTM S).q₀) s out) (2 * (maxLen s + S.e) + 3) =
      ccfg x none (S.colResult s) 0 out := by
  set P := maxLen s with hP
  have hq : (colTM S).q₀ = .scan S.u₀ := rfl
  have horig : ∀ c ∈ cols s P, isBlank c = false := by
    intro c hc
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
    exact colAt_ne_blank s (List.mem_range.mp hp)
  rw [hq, wordsCfg_eq_ccfg x _ s (show maxLen s ≤ P + (S.e + 1) by omega),
    cols_eq_append s le_rfl]
  -- the forward pass over the words
  have hscan := S.run_scan x out [] (cols s P) (List.replicate (S.e + 1) blankCol) S.u₀ horig
    (by simp)
  simp only [List.nil_append, List.length_nil, length_cols, Nat.cast_zero, zero_add,
    CharP.cast_eq_zero] at hscan
  set F₁ := S.fwdRun S.u₀ (cols s P) with hF₁
  have hF₁ne := S.fwdRun_ne_blank S.u₀ (cols s P) horig
  have hF₁len : F₁.2.length = P := by rw [hF₁, length_fwdRun, length_cols]
  have hcolsE : cols s (P + S.e) = cols s P ++ List.replicate S.e blankCol :=
    cols_eq_append s le_rfl S.e
  have hlenP : P < (F₁.2 ++ List.replicate (S.e + 1) blankCol).length := by simp [hF₁len]
  have hgetP : (F₁.2 ++ List.replicate (S.e + 1) blankCol)[P] = blankCol := by
    simp [List.getElem_append_right, hF₁len]
  unfold colResult
  rcases Nat.eq_zero_or_pos S.e with he | he
  · -- no padding
    rw [show 2 * (P + S.e) + 3 = P + (1 + (P + 2)) by omega, runFrom_add, hscan, runFrom_add,
      runFrom_one, step_ccfg' S x out _ _ _ P rfl hlenP, hgetP]
    have hnot : ¬ 0 < S.e := by omega
    simp only [tr, isBlank_blankCol, ↓reduceIte, hnot, ↓reduceDIte]
    rw [apply_colAct x _ _ _ hlenP]
    have hset : (F₁.2 ++ List.replicate (S.e + 1) blankCol).set P blankCol =
        F₁.2 ++ [blankCol] := by
      simp [List.set_append_right, hF₁len, he]
    rw [hset, SignType.coe_neg, SignType.coe_one, ← sub_eq_add_neg]
    have hmain := S.run_main x out F₁.2 [blankCol] F₁.1 hF₁ne
    rw [hF₁len] at hmain
    rw [runFrom_add, hmain, S.run_end x out _ (by simp)]
    rw [hcolsE, he, List.replicate_zero, List.append_nil]
  · -- padding: the forward pass over it, then the backward pass over it
    set F₂ := S.fwdRun (S.fwd F₁.1 blankCol).1 (List.replicate (S.e - 1) blankCol) with hF₂
    have hF : S.fwdRun S.u₀ (cols s (P + S.e)) =
        (F₂.1, F₁.2 ++ ((S.fwd F₁.1 blankCol).2 :: F₂.2)) := by
      rw [hcolsE, fwdRun_append, ← hF₁, show S.e = (S.e - 1) + 1 by omega,
        List.replicate_succ]
      simp [fwdRun, hF₂]
    have hF₂len : ((S.fwd F₁.1 blankCol).2 :: F₂.2).length = S.e := by
      simp [hF₂, length_fwdRun]; omega
    rw [show 2 * (P + S.e) + 3 = P + (1 + ((S.e - 1 + 1) + ((S.e - 1 + 1) + (P + 2)))) by omega,
      runFrom_add, hscan, runFrom_add, runFrom_one, step_ccfg' S x out _ _ _ P rfl hlenP, hgetP]
    simp only [tr, isBlank_blankCol, ↓reduceIte, he, ↓reduceDIte]
    rw [apply_colAct x _ _ _ hlenP]
    have hset : (F₁.2 ++ List.replicate (S.e + 1) blankCol).set P (S.fwd F₁.1 blankCol).2 =
        (F₁.2 ++ [(S.fwd F₁.1 blankCol).2]) ++ List.replicate (S.e - 1 + 1) blankCol := by
      rw [show S.e + 1 = (S.e - 1 + 1) + 1 by omega, List.replicate_succ]
      simp [List.set_append_right, hF₁len]
    rw [hset]
    have hpad := S.run_pad x out (F₁.2 ++ [(S.fwd F₁.1 blankCol).2]) (S.fwd F₁.1 blankCol).1
      (S.e - 1) ⟨0, he⟩ (by simp; omega)
    simp only [List.length_append, List.length_singleton, hF₁len] at hpad
    rw [runFrom_add, show ((P : ℤ) + ((1 : SignType) : ℤ)) = ((P + 1 : ℕ) : ℤ) by simp, hpad,
      ← hF₂]
    have hback := S.run_back x out F₁.2 ((S.fwd F₁.1 blankCol).2 :: F₂.2) [blankCol] F₂.1
      (S.e - 1) (by omega) (by rw [hF₂len]; omega)
    rw [hF₁len] at hback
    have hpos : ((P + 1 : ℕ) : ℤ) + ((S.e - 1 : ℕ) : ℤ) - 1 = ((P + (S.e - 1) : ℕ) : ℤ) := by
      omega
    have hpre : F₁.2 ++ [(S.fwd F₁.1 blankCol).2] ++ F₂.2 ++ [blankCol] =
        F₁.2 ++ ((S.fwd F₁.1 blankCol).2 :: F₂.2) ++ [blankCol] := by simp
    rw [runFrom_add, hpos, hpre, hback, runFrom_add]
    set M := S.bwdRun F₂.1 ((S.fwd F₁.1 blankCol).2 :: F₂.2) with hM
    have hmain := S.run_main x out F₁.2 (M.2 ++ [blankCol]) M.1 hF₁ne
    rw [hF₁len] at hmain
    rw [List.append_assoc, hmain, S.run_end x out _ (by simp), hF, bwdRun_append, ← hM]
    simp

end ColSpec

open MultiTapeMachine in
/-- A deterministic run from words to words is a `RunsWords` phase of the embedded machine. -/
theorem runsWords_of_runFrom {S Operation : Type} [DecidableEq Operation] {tm : MultiTapeTM k Bool S}
    {x : List Bool} {ws ws' : Store k} {out₀ : List Bool} {t : ℕ}
    (h : tm.runFrom (wordsCfg x (some tm.q₀) ws out₀) t = wordsCfg x none ws' out₀) :
    (MultiTapePTM.ofDeterministic tm : MultiTapePTM k Bool S Operation).RunsWords x ws out₀ t
      (pure ws') id (fun _ => []) := by
  intro OracleState oracle st cfg htapes hbuf
  have htapes' : cfg.tapes = wordsCfg x (some tm.q₀) ws out₀ := htapes
  dsimp only
  rw [MultiTapePTM.run_interpret_runOracleConfigFrom_ofDeterministic, htapes', h]
  simp only [ProbOracleComp.runWith_pure, PMF.pure_map, PMF.support_pure, Set.mem_singleton_iff,
    forall_eq, true_and, id, List.append_nil]
  exact hbuf

/-- **The column machine as a phase**: if the final columns describe the store `s'`, the column
machine takes `s` to `s'` within any clock `t ≥ 2 (maxLen s + e) + 3`, emitting nothing. -/
theorem colTM_runsWords {Operation : Type} [DecidableEq Operation] (S : ColSpec k) (x : List Bool)
    (s s' : Store k) (out₀ : List Bool) {t : ℕ} (ht : 2 * (maxLen s + S.e) + 3 ≤ t)
    (hres : ∀ i, tapesOf (S.colResult s) i = tapeOfList (s' i)) :
    (MultiTapePTM.ofDeterministic (colTM S) : MultiTapePTM k Bool (CQ S.e) Operation).RunsWords
      x s out₀ t (pure s') id (fun _ => []) := by
  apply runsWords_of_runFrom
  have hrun := S.colTM_runFrom x out₀ s
  rw [MultiTapeTM.runFrom_eq_of_halt _ _ ht (by rw [hrun]; rfl), hrun]
  exact ccfg_eq_wordsCfg x none _ s' hres out₀

end SigabaNeo.Tape
