import SigabaNeo.Lib.Machines.Prog.Columns

/-!
# The primitive column machines

Each primitive of the tape language is a column machine (`SigabaNeo.Tape.colTM`) whose final tapes
hold the words of an explicit store transformation (`*_result` below). A *backward* primitive only
uses the backward pass (with a carry from the right: the least significant bit of a big-endian word
comes last) and the final rewrite of column `0`; a *forward* primitive only uses the forward pass
(with a carry from the left) over one padding column.

Words are big-endian: `bitsVal [b₀, …, bₙ₋₁] = Σ bᵢ 2^(n-1-i)`.

| primitive | effect | pass |
|---|---|---|
| `clear i` | `i := []` | backward |
| `copy i j` | `i := s j` | backward |
| `add i j` | `i := s i + s j mod 2^|s i|` (`addC`) | backward |
| `sub i j` | `i := s i - s j mod 2^|s i|` (`subC`) | backward |
| `tail i` | `i := (s i).tail` | backward |
| `pop i j` | `i := (s i).tail`, then `j := (s i).take 1` | backward |
| `eq i j f` | `f := [decide (s i = s j)]` | backward |
| `cons i b` | `i := b :: s i` | forward |
| `snoc i b` | `i := s i ++ [b]` | forward |
| `consHead i j` | `i := (s j).take 1 ++ s i` | forward |
| `snocHead i j` | `i := s i ++ (s j).take 1` | forward |
-/

namespace SigabaNeo.Tape

open Turing

variable {k : ℕ}

/-! ### Stores, column by column -/

/-- Drop the first symbol of every word. -/
def tails (s : Store k) : Store k := fun i => (s i).tail

theorem colAt_zero (s : Store k) : colAt s 0 = fun i => (s i).head? := by
  funext i; simp [colAt, List.head?_eq_getElem?]

theorem colAt_succ (s : Store k) (p : ℕ) : colAt s (p + 1) = colAt (tails s) p := by
  funext i; simp [colAt, tails]

theorem cols_succ (s : Store k) (n : ℕ) : cols s (n + 1) = colAt s 0 :: cols (tails s) n := by
  simp only [cols, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  exact colAt_succ s p

theorem maxLen_tails_le (s : Store k) {n : ℕ} (h : maxLen s ≤ n + 1) : maxLen (tails s) ≤ n := by
  rw [maxLen_le_iff] at h ⊢
  intro i
  simp only [tails, List.length_tail]
  have := h i
  omega

theorem eq_nil_of_maxLen (s : Store k) (h : maxLen s ≤ 0) (i : Fin k) : s i = [] := by
  have := (length_le_maxLen s i).trans h
  exact List.eq_nil_of_length_eq_zero (by omega)

theorem tails_update (s : Store k) (i : Fin k) (w : List Bool) :
    tails (Function.update s i w) = Function.update (tails s) i w.tail := by
  funext t
  by_cases h : t = i
  · subst h; simp [tails]
  · simp [tails, h]

theorem colAt_update (s : Store k) (i : Fin k) (w : List Bool) (p : ℕ) :
    colAt (Function.update s i w) p = Function.update (colAt s p) i w[p]? := by
  funext t
  by_cases h : t = i
  · subst h; simp [colAt]
  · simp [colAt, h]

theorem length_tail_le_maxLen (s : Store k) (i : Fin k) : (s i).tail.length ≤ maxLen s := by
  have := length_le_maxLen s i
  simp only [List.length_tail]
  omega

@[simp] theorem colAt_zero_apply (s : Store k) (t : Fin k) : colAt s 0 t = (s t).head? := by
  simp [colAt, List.head?_eq_getElem?]

@[simp] theorem tails_apply (s : Store k) (t : Fin k) : tails s t = (s t).tail := rfl

theorem cols_append_blank (s : Store k) {n : ℕ} (h : maxLen s ≤ n) :
    cols s n ++ [blankCol] = cols s (n + 1) := by
  rw [cols_eq_append s h 1]; rfl

/-! ### Backward and forward primitives -/

namespace ColSpec

variable (S : ColSpec k)

/-- The backward pass over the columns of a store, from functions describing its state and result
on every store. -/
theorem bwdRun_cols (u : U) (σ : Store k → U) (τ : Store k → Store k)
    (h0 : ∀ s, maxLen s ≤ 0 → σ s = u)
    (h1 : ∀ s, S.bwd (σ (tails s)) (colAt s 0) = (σ s, colAt (τ s) 0))
    (h2 : ∀ s, tails (τ s) = τ (tails s)) :
    ∀ n (s : Store k), maxLen s ≤ n → S.bwdRun u (cols s n) = (σ s, cols (τ s) n) := by
  intro n
  induction n with
  | zero => intro s hs; simp [cols, h0 s hs]
  | succ n ih =>
    intro s hs
    rw [cols_succ, bwdRun, ih (tails s) (maxLen_tails_le s hs), h1, cols_succ, h2]

/-- The forward pass over the columns of a store, from a function describing its result. -/
theorem fwdRun_cols (τ : U → Store k → Store k)
    (h1 : ∀ u s, (S.fwd u (colAt s 0)).2 = colAt (τ u s) 0)
    (h2 : ∀ u s, tails (τ u s) = τ (S.fwd u (colAt s 0)).1 (tails s)) :
    ∀ n (s : Store k) u, (S.fwdRun u (cols s n)).2 = cols (τ u s) n := by
  intro n
  induction n with
  | zero => intro s u; simp [cols]
  | succ n ih =>
    intro s u
    rw [cols_succ, fwdRun, ih, h1, cols_succ, ← h2]

theorem fwdRun_id (hfwd : ∀ u c, S.fwd u c = (u, c)) (u : U) (cs : List (Col k)) :
    S.fwdRun u cs = (u, cs) := by
  induction cs generalizing u with
  | nil => rfl
  | cons c cs ih => simp [fwdRun, hfwd, ih]

theorem bwdRun_id (hbwd : ∀ u c, S.bwd u c = (u, c)) (u : U) (cs : List (Col k)) :
    S.bwdRun u cs = (u, cs) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [bwdRun, hbwd, ih]

/-- **A backward primitive** (no padding, identity forward pass) leaves the store `s'` whose column
`0` is the final rewrite of the backward result and which agrees with it elsewhere. -/
theorem bwdPrim_result (he : S.e = 0) (hfwd : ∀ u c, S.fwd u c = (u, c))
    (σ : Store k → U) (τ : Store k → Store k)
    (h0 : ∀ s, maxLen s ≤ 0 → σ s = S.u₀)
    (h1 : ∀ s, S.bwd (σ (tails s)) (colAt s 0) = (σ s, colAt (τ s) 0))
    (h2 : ∀ s, tails (τ s) = τ (tails s))
    (s s' : Store k) (hτ : maxLen (τ s) ≤ maxLen s)
    (hpost : colAt s' 0 = S.post (σ s) (colAt (τ s) 0)) (htails : tails s' = tails (τ s))
    (hs' : maxLen s' ≤ maxLen s + 1) :
    ∀ i, tapesOf (S.colResult s) i = tapeOfList (s' i) := by
  intro i
  have hres : S.colResult s = cols s' (maxLen s + 1) := by
    simp only [colResult, he, Nat.add_zero, S.fwdRun_id hfwd,
      S.bwdRun_cols S.u₀ σ τ h0 h1 h2 _ s le_rfl, cols_append_blank _ hτ, cols_succ, setHead,
      hpost, htails]
  rw [hres, tapesOf_cols s' hs']

/-- **A forward primitive** (one padding column, identity backward pass and final rewrite) leaves
the store `τ u₀ s`. -/
theorem fwdPrim_result (he : S.e = 1) (hbwd : ∀ u c, S.bwd u c = (u, c))
    (hpost : ∀ u c, S.post u c = c) (τ : U → Store k → Store k)
    (h1 : ∀ u s, (S.fwd u (colAt s 0)).2 = colAt (τ u s) 0)
    (h2 : ∀ u s, tails (τ u s) = τ (S.fwd u (colAt s 0)).1 (tails s))
    (s : Store k) (hτ : maxLen (τ S.u₀ s) ≤ maxLen s + 1) :
    ∀ i, tapesOf (S.colResult s) i = tapeOfList (τ S.u₀ s i) := by
  intro i
  have hres : S.colResult s = cols (τ S.u₀ s) (maxLen s + 1 + 1) := by
    have hpost' : S.post = fun _ c => c := funext fun u => funext fun c => hpost u c
    have hF := S.fwdRun_cols τ h1 h2 (maxLen s + 1) s S.u₀
    simp only [colResult, he, S.bwdRun_id hbwd, hpost']
    rw [hF, cols_append_blank _ hτ]
    cases cols (τ S.u₀ s) (maxLen s + 1 + 1) <;> rfl
  rw [hres, tapesOf_cols _ (by omega)]

end ColSpec

/-! ### The primitives -/

/-- The control value with only the first flag set to `b`. -/
abbrev flagU (b : Bool) : U := (b, false, none)

/-- The control value carrying the optional bit `o`. -/
abbrev bitU (o : Option Bool) : U := (false, false, o)

/-- A backward specification, with no padding and an identity forward pass. -/
def bwdSpec (bwd : U → Col k → U × Col k) (post : U → Col k → Col k) : ColSpec k where
  e := 0
  u₀ := (false, false, none)
  fwd u c := (u, c)
  bwd := bwd
  post := post
  fwd_ne _ _ h := h

/-- A forward specification, with one padding column and identity backward pass and rewrite. -/
def fwdSpec (u₀ : U) (fwd : U → Col k → U × Col k)
    (fwd_ne : ∀ u c, isBlank c = false → isBlank (fwd u c).2 = false) : ColSpec k where
  e := 1
  u₀ := u₀
  fwd := fwd
  bwd u c := (u, c)
  post _ c := c
  fwd_ne := fwd_ne

theorem update_col_self (c : Col k) (i : Fin k) : Function.update c i (c i) = c :=
  Function.update_eq_self i c

theorem maxLen_update_le (s : Store k) (i : Fin k) (w : List Bool) {L : ℕ} (hs : maxLen s ≤ L)
    (hw : w.length ≤ L) : maxLen (Function.update s i w) ≤ L := by
  rw [maxLen_le_iff] at hs ⊢
  intro t
  by_cases h : t = i
  · subst h; simpa using hw
  · simpa [h] using hs t

theorem isBlank_update_of_none (c : Col k) (i : Fin k) (v : Option Bool) (h : isBlank c = false)
    (hi : c i = none) : isBlank (Function.update c i v) = false := by
  rw [Bool.eq_false_iff, ne_eq, isBlank_eq_true_iff] at h ⊢
  intro h'
  apply h
  funext t
  by_cases ht : t = i
  · subst ht; exact hi
  · have := congrFun h' t
    simpa [ht] using this

/-! #### Clearing and copying -/

/-- `clear i`: erase tape `i`. -/
def clearSpec (i : Fin k) : ColSpec k :=
  bwdSpec (fun u c => (u, Function.update c i none)) (fun _ c => c)

theorem clear_result (i : Fin k) (s : Store k) :
    ∀ t, tapesOf ((clearSpec i).colResult s) t = tapeOfList (Function.update s i [] t) := by
  have hτ : maxLen (Function.update s i []) ≤ maxLen s :=
    maxLen_update_le s i [] le_rfl (by simp)
  refine ColSpec.bwdPrim_result _ rfl (fun _ _ => rfl) (fun _ => (false, false, none))
    (fun s => Function.update s i []) (fun _ _ => rfl) (fun s => ?_) (fun s => ?_) s _ hτ ?_ rfl
    (by omega)
  · simp [clearSpec, bwdSpec, colAt_update]
  · simp [tails_update]
  · simp [clearSpec, bwdSpec]

/-- `copy i j`: tape `i` gets the word of tape `j`. -/
def copySpec (i j : Fin k) : ColSpec k :=
  bwdSpec (fun u c => (u, Function.update c i (c j))) (fun _ c => c)

theorem copy_result (i j : Fin k) (s : Store k) :
    ∀ t, tapesOf ((copySpec i j).colResult s) t = tapeOfList (Function.update s i (s j) t) := by
  have hτ : maxLen (Function.update s i (s j)) ≤ maxLen s :=
    maxLen_update_le s i _ le_rfl (length_le_maxLen s j)
  refine ColSpec.bwdPrim_result _ rfl (fun _ _ => rfl) (fun _ => (false, false, none))
    (fun s => Function.update s i (s j)) (fun _ _ => rfl) (fun s => ?_) (fun s => ?_) s _ hτ ?_ rfl
    (by omega)
  · simp [copySpec, bwdSpec, colAt_update, colAt]
  · simp [tails_update, tails]
  · simp [copySpec, bwdSpec]

/-! #### Carry operations: addition and subtraction -/

/-- A digit operation with a carry: from two digits and the incoming carry, the result digit and
the outgoing carry. -/
abbrev DigitOp := Bool → Bool → Bool → Bool × Bool

/-- Big-endian addition: result digit and carry. -/
def addBit : DigitOp := fun x y c => (xor (xor x y) c, (x && y) || (c && xor x y))

/-- Big-endian subtraction: result digit and borrow. -/
def subBit : DigitOp := fun x y c => (xor (xor x y) c, (!x && y) || (c && !(xor x y)))

/-- Combine the word `a` with `b`, aligned at their first (most significant) digit, digit by digit
from the last: the outgoing carry and the result, of the length of `a`. Missing digits of `b` are
`false`; digits of `b` beyond `a` are ignored. -/
def carryOp (f : DigitOp) : List Bool → List Bool → Bool × List Bool
  | [], _ => (false, [])
  | x :: xs, ys =>
    ((f x (ys.headD false) (carryOp f xs ys.tail).1).2,
      (f x (ys.headD false) (carryOp f xs ys.tail).1).1 :: (carryOp f xs ys.tail).2)

@[simp] theorem carryOp_nil (f : DigitOp) (ys : List Bool) : carryOp f [] ys = (false, []) := rfl

@[simp] theorem length_carryOp (f : DigitOp) (xs ys : List Bool) :
    (carryOp f xs ys).2.length = xs.length := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih => simp [carryOp, ih]

theorem carryOp_tail (f : DigitOp) (xs ys : List Bool) :
    (carryOp f xs ys).2.tail = (carryOp f xs.tail ys.tail).2 := by
  cases xs <;> rfl

/-- `carry f i j`: tape `i` becomes `carryOp f (s i) (s j)`. -/
def carrySpec (f : DigitOp) (i j : Fin k) : ColSpec k :=
  bwdSpec (fun u c => match c i with
    | none => (flagU false, c)
    | some x => (flagU (f x ((c j).getD false) u.1).2,
        Function.update c i (some (f x ((c j).getD false) u.1).1))) (fun _ c => c)

theorem carry_result (f : DigitOp) (i j : Fin k) (s : Store k) :
    ∀ t, tapesOf ((carrySpec f i j).colResult s) t =
      tapeOfList (Function.update s i (carryOp f (s i) (s j)).2 t) := by
  have hτ : maxLen (Function.update s i (carryOp f (s i) (s j)).2) ≤ maxLen s :=
    maxLen_update_le s i _ le_rfl (by simpa using length_le_maxLen s i)
  refine ColSpec.bwdPrim_result _ rfl (fun _ _ => rfl) (fun s => flagU (carryOp f (s i) (s j)).1)
    (fun s => Function.update s i (carryOp f (s i) (s j)).2) (fun s hs => ?_) (fun s => ?_)
    (fun s => ?_) s _ hτ ?_ rfl (by omega)
  · simp [eq_nil_of_maxLen s hs i, carrySpec, bwdSpec]
  · rw [colAt_zero, colAt_update, colAt_zero]
    simp only [carrySpec, bwdSpec, tails]
    cases h : s i with
    | nil => simp [Function.update_eq_self_iff, h]
    | cons x xs => simp [carryOp]
  · simp [tails_update, carryOp_tail, tails]
  · simp [carrySpec, bwdSpec]

/-! #### Taking a word apart -/

/-- `tail i`: drop the first symbol of tape `i`. -/
def tailSpec (i : Fin k) : ColSpec k :=
  bwdSpec (fun u c => (bitU (c i), Function.update c i u.2.2)) (fun _ c => c)

theorem tail_result (i : Fin k) (s : Store k) :
    ∀ t, tapesOf ((tailSpec i).colResult s) t =
      tapeOfList (Function.update s i (s i).tail t) := by
  have hτ : maxLen (Function.update s i (s i).tail) ≤ maxLen s :=
    maxLen_update_le s i _ le_rfl (length_tail_le_maxLen s i)
  refine ColSpec.bwdPrim_result _ rfl (fun _ _ => rfl) (fun s => bitU (s i).head?)
    (fun s => Function.update s i (s i).tail) (fun s hs => ?_) (fun s => ?_)
    (fun s => ?_) s _ hτ ?_ rfl (by omega)
  · simp [eq_nil_of_maxLen s hs i, tailSpec, bwdSpec]
  · rw [colAt_zero, colAt_update, colAt_zero]
    simp [tailSpec, bwdSpec, tails, List.head?_eq_getElem?]
  · simp [tails_update, tails]
  · simp [tailSpec, bwdSpec]

/-- `pop i j`: drop the first symbol of tape `i` and put it (as a word of length at most one) on
tape `j`. -/
def popSpec (i j : Fin k) : ColSpec k :=
  bwdSpec (fun u c => (bitU (c i), Function.update (Function.update c i u.2.2) j none))
    (fun u c => Function.update c j u.2.2)

theorem pop_result (i j : Fin k) (s : Store k) :
    ∀ t, tapesOf ((popSpec i j).colResult s) t =
      tapeOfList (Function.update (Function.update s i (s i).tail) j ((s i).take 1) t) := by
  have hτ : maxLen (Function.update (Function.update s i (s i).tail) j []) ≤ maxLen s :=
    maxLen_update_le _ j _ (maxLen_update_le s i _ le_rfl (length_tail_le_maxLen s i)) (by simp)
  refine ColSpec.bwdPrim_result _ rfl (fun _ _ => rfl) (fun s => bitU (s i).head?)
    (fun s => Function.update (Function.update s i (s i).tail) j []) (fun s hs => ?_)
    (fun s => ?_) (fun s => ?_) s _ hτ ?_ ?_ ?_
  · simp [eq_nil_of_maxLen s hs i, popSpec, bwdSpec]
  · rw [colAt_zero, colAt_update, colAt_update, colAt_zero]
    simp [popSpec, bwdSpec, tails, List.head?_eq_getElem?]
  · simp [tails_update, tails]
  · rw [colAt_update, colAt_update, colAt_update, colAt_update]
    simp [popSpec, bwdSpec, List.head?_eq_getElem?]
  · have : ((s i).take 1).tail = [] := by cases s i <;> rfl
    simp [tails_update, this]
  · exact maxLen_update_le _ j _ (maxLen_update_le s i _ (by omega)
      (length_tail_le_maxLen s i |>.trans (by omega))) (by simp only [List.length_take]; omega)

/-! #### Comparing words -/

theorem ne_iff_head?_tail (a b : List Bool) : a ≠ b ↔ a.head? ≠ b.head? ∨ a.tail ≠ b.tail := by
  constructor
  · intro h
    by_contra h'
    push Not at h'
    apply h
    cases a <;> cases b <;> simp_all
  · rintro (h | h) rfl <;> exact h rfl

/-- `eq i j f`: tape `f` gets the word `[decide (s i = s j)]`. -/
def eqSpec (i j f : Fin k) : ColSpec k :=
  bwdSpec (fun u c => (flagU (u.1 || decide (c i ≠ c j)), Function.update c f none))
    (fun u c => Function.update c f (some (!u.1)))

theorem eq_result (i j f : Fin k) (s : Store k) :
    ∀ t, tapesOf ((eqSpec i j f).colResult s) t =
      tapeOfList (Function.update s f [decide (s i = s j)] t) := by
  have hτ : maxLen (Function.update s f []) ≤ maxLen s := maxLen_update_le s f [] le_rfl (by simp)
  refine ColSpec.bwdPrim_result _ rfl (fun _ _ => rfl) (fun s => flagU (decide (s i ≠ s j)))
    (fun s => Function.update s f []) (fun s hs => ?_) (fun s => ?_) (fun s => ?_) s _ hτ ?_ ?_
    (maxLen_update_le s f _ (by omega) (by simp))
  · simp [eq_nil_of_maxLen s hs i, eq_nil_of_maxLen s hs j, eqSpec, bwdSpec]
  · rw [colAt_update, colAt_zero]
    simp only [eqSpec, bwdSpec, tails, Prod.mk.injEq, and_true]
    refine ⟨?_, by simp⟩
    congr 1
    have := ne_iff_head?_tail (s i) (s j)
    by_cases h₁ : (s i).head? = (s j).head? <;> by_cases h₂ : (s i).tail = (s j).tail <;>
      simp_all
  · simp [tails_update]
  · rw [colAt_update, colAt_update]
    simp [eqSpec, bwdSpec]
  · simp [tails_update]

/-! #### Growing a word -/

/-- The symbols put in front of `a` by a pending carry: the carried bit, or with no carry the first
symbol of `a` (which only happens before the first symbol is read). -/
def pre : Option Bool → List Bool → List Bool
  | none, a => a.take 1
  | some v, _ => [v]

/-- One step of the shift to the right: write the carried bit, carry the old one. -/
def consStep (i : Fin k) (cy : Option Bool) (c : Col k) : U × Col k :=
  ((true, false, c i), match cy with
    | none => c
    | some v => Function.update c i (some v))

theorem consStep_ne (i : Fin k) (cy : Option Bool) (c : Col k) (h : isBlank c = false) :
    isBlank (consStep i cy c).2 = false := by
  cases cy with
  | none => exact h
  | some v =>
    rw [Bool.eq_false_iff, ne_eq, isBlank_eq_true_iff]
    intro h'
    have := congrFun h' i
    simp [consStep, blankCol] at this

/-- The store after the shift to the right with pending carry `cy`. -/
def consStore (i : Fin k) (cy : Option Bool) (s : Store k) : Store k :=
  Function.update s i (pre cy (s i) ++ s i)

theorem consStep_col (i : Fin k) (cy : Option Bool) (s : Store k) :
    (consStep i cy (colAt s 0)).2 = colAt (consStore i cy s) 0 := by
  simp only [consStore]
  rw [colAt_update, colAt_zero]
  cases cy with
  | none =>
    simp only [consStep, pre]
    cases h : s i <;> simp [h, Function.update_eq_self_iff]
  | some v => simp [consStep, pre]

theorem consStep_tails (i : Fin k) (cy : Option Bool) (s : Store k) :
    tails (consStore i cy s) = consStore i (consStep i cy (colAt s 0)).1.2.2 (tails s) := by
  simp only [consStore, tails_update, consStep, colAt_zero]
  congr 1
  simp only [tails]
  cases cy <;> cases s i <;> simp [pre]

/-- `cons i b`: put `b` in front of tape `i`. -/
def consSpec (i : Fin k) (b : Bool) : ColSpec k :=
  fwdSpec (bitU (some b)) (fun u c => consStep i u.2.2 c) (fun u c h => consStep_ne i _ c h)

theorem cons_result (i : Fin k) (b : Bool) (s : Store k) :
    ∀ t, tapesOf ((consSpec i b).colResult s) t =
      tapeOfList (Function.update s i (b :: s i) t) :=
  ColSpec.fwdPrim_result (consSpec i b) rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun u s => consStore i u.2.2 s) (fun u s => consStep_col i _ s)
    (fun u s => consStep_tails i _ s) s
    (maxLen_update_le s i _ (by omega)
      (by simp [consSpec, fwdSpec, pre]; exact length_le_maxLen s i))

/-- `consHead i j`: put the first symbol of tape `j` (if any) in front of tape `i`. The control
value is (started, idle, carry). -/
def consHeadSpec (i j : Fin k) : ColSpec k :=
  fwdSpec (false, false, none)
    (fun u c => if !u.1 then (if (c j).isNone then ((true, true, none), c) else consStep i (c j) c)
      else if u.2.1 then (u, c) else consStep i u.2.2 c)
    (fun u c h => by
      split_ifs
      · exact h
      · exact consStep_ne i _ c h
      · exact h
      · exact consStep_ne i _ c h)

/-- The store after `consHead` from the control value `u`. -/
def consHeadStore (i j : Fin k) (u : U) (s : Store k) : Store k :=
  if !u.1 then Function.update s i ((s j).take 1 ++ s i)
  else if u.2.1 then s else consStore i u.2.2 s

theorem consHead_result (i j : Fin k) (s : Store k) :
    ∀ t, tapesOf ((consHeadSpec i j).colResult s) t =
      tapeOfList (Function.update s i ((s j).take 1 ++ s i) t) := by
  have hstarted : ∀ cy (s : Store k), consHeadStore i j (true, false, cy) s = consStore i cy s :=
    fun _ _ => rfl
  refine ColSpec.fwdPrim_result (consHeadSpec i j) rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (consHeadStore i j) (fun u s => ?_) (fun u s => ?_) s
    (maxLen_update_le s i _ (by omega) (by have := length_le_maxLen s i; simp; omega))
  · obtain ⟨st, idle, cy⟩ := u
    cases st
    · cases hj : s j with
      | nil =>
        have e1 : (consHeadSpec i j).fwd (false, idle, cy) (colAt s 0) =
            ((true, true, none), colAt s 0) := by simp [consHeadSpec, fwdSpec, hj]
        have e2 : consHeadStore i j (false, idle, cy) s = s := by
          simp [consHeadStore, hj]
        rw [e1, e2]
      | cons v vs =>
        have e1 : (consHeadSpec i j).fwd (false, idle, cy) (colAt s 0) =
            consStep i (some v) (colAt s 0) := by simp [consHeadSpec, fwdSpec, hj]
        have e2 : consHeadStore i j (false, idle, cy) s = consStore i (some v) s := by
          simp [consHeadStore, consStore, pre, hj]
        rw [e1, e2]
        exact consStep_col i _ s
    · cases idle
      · have e1 : (consHeadSpec i j).fwd (true, false, cy) (colAt s 0) =
            consStep i cy (colAt s 0) := by simp [consHeadSpec, fwdSpec]
        rw [e1, hstarted]
        exact consStep_col i _ s
      · rfl
  · obtain ⟨st, idle, cy⟩ := u
    cases st
    · cases hj : s j with
      | nil =>
        have e1 : (consHeadSpec i j).fwd (false, idle, cy) (colAt s 0) =
            ((true, true, none), colAt s 0) := by simp [consHeadSpec, fwdSpec, hj]
        have e2 : consHeadStore i j (false, idle, cy) s = s := by
          simp [consHeadStore, hj]
        rw [e1, e2]
        rfl
      | cons v vs =>
        have e1 : (consHeadSpec i j).fwd (false, idle, cy) (colAt s 0) =
            consStep i (some v) (colAt s 0) := by simp [consHeadSpec, fwdSpec, hj]
        have e2 : consHeadStore i j (false, idle, cy) s = consStore i (some v) s := by
          simp [consHeadStore, consStore, pre, hj]
        rw [e1, e2, show (consStep i (some v) (colAt s 0)).1 = (true, false, colAt s 0 i) from rfl,
          hstarted]
        exact consStep_tails i _ s
    · cases idle
      · have e1 : (consHeadSpec i j).fwd (true, false, cy) (colAt s 0) =
            consStep i cy (colAt s 0) := by simp [consHeadSpec, fwdSpec]
        rw [e1, hstarted, show (consStep i cy (colAt s 0)).1 = (true, false, colAt s 0 i) from rfl,
          hstarted]
        exact consStep_tails i _ s
      · rfl

/-- `snoc i b`: append `b` to tape `i`. The first flag records that it was written. -/
def snocSpec (i : Fin k) (b : Bool) : ColSpec k :=
  fwdSpec (flagU false)
    (fun u c => if !u.1 && (c i).isNone then (flagU true, Function.update c i (some b))
      else (flagU u.1, c))
    (fun u c h => by
      split_ifs
      · rw [Bool.eq_false_iff, ne_eq, isBlank_eq_true_iff]
        intro h'
        have := congrFun h' i
        simp [blankCol] at this
      · exact h)

theorem snoc_result (i : Fin k) (b : Bool) (s : Store k) :
    ∀ t, tapesOf ((snocSpec i b).colResult s) t =
      tapeOfList (Function.update s i (s i ++ [b]) t) := by
  refine ColSpec.fwdPrim_result (snocSpec i b) rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun u s => if u.1 then s else Function.update s i (s i ++ [b])) (fun u s => ?_)
    (fun u s => ?_) s
    (maxLen_update_le s i _ (by omega) (by simpa using length_le_maxLen s i))
  · obtain ⟨d, _, _⟩ := u
    cases d
    · funext t
      by_cases ht : t = i
      · subst ht; cases h : s t <;> simp [snocSpec, fwdSpec, h]
      · cases h : s i <;> simp [snocSpec, fwdSpec, h, ht]
    · simp [snocSpec, fwdSpec]
  · obtain ⟨d, _, _⟩ := u
    cases d
    · funext t
      by_cases ht : t = i
      · subst ht; cases h : s t <;> simp [snocSpec, fwdSpec, h]
      · cases h : s i <;> simp [snocSpec, fwdSpec, h, ht]
    · simp [snocSpec, fwdSpec]

/-- `snocHead i j`: append the first symbol of tape `j` (if any) to tape `i`. The control value is
(started, done, bit). -/
def snocHeadSpec (i j : Fin k) : ColSpec k :=
  fwdSpec (false, false, none)
    (fun u c =>
      if !(if u.1 then u.2.1 else (c j).isNone) && (c i).isNone then
        ((true, true, if u.1 then u.2.2 else c j), Function.update c i (if u.1 then u.2.2 else c j))
      else ((true, if u.1 then u.2.1 else (c j).isNone, if u.1 then u.2.2 else c j), c))
    (fun u c h => by
      generalize (if u.1 then u.2.2 else c j) = b
      generalize (if u.1 then u.2.1 else (c j).isNone) = d
      split
      · rename_i h₁
        simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at h₁
        exact isBlank_update_of_none c i _ h h₁.2
      · exact h)

/-- The store after `snocHead` from the control value `u`. -/
def snocHeadStore (i j : Fin k) (u : U) (s : Store k) : Store k :=
  if (if u.1 then u.2.1 else (s j).head?.isNone) then s
  else Function.update s i (s i ++ (if u.1 then u.2.2 else (s j).head?).toList)

theorem snocHead_result (i j : Fin k) (s : Store k) :
    ∀ t, tapesOf ((snocHeadSpec i j).colResult s) t =
      tapeOfList (Function.update s i (s i ++ (s j).take 1) t) := by
  have hfin : snocHeadStore i j (false, false, none) s =
      Function.update s i (s i ++ (s j).take 1) := by
    unfold snocHeadStore
    cases hj : s j <;> simp [hj]
  rw [← hfin]
  refine ColSpec.fwdPrim_result (snocHeadSpec i j) rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (snocHeadStore i j) (fun u s => ?_) (fun u s => ?_) s ?_
  · obtain ⟨st, d, bt⟩ := u
    funext t
    by_cases ht : t = i
    · subst ht
      cases st <;> cases d <;> cases hi : s t <;> cases hj : s j <;> cases bt <;>
        simp [snocHeadSpec, fwdSpec, snocHeadStore, hi, hj]
    · cases st <;> cases d <;> cases hi : s i <;> cases hj : s j <;> cases bt <;>
        simp [snocHeadSpec, fwdSpec, snocHeadStore, hi, hj, ht]
  · obtain ⟨st, d, bt⟩ := u
    funext t
    by_cases ht : t = i
    · subst ht
      cases st <;> cases d <;> cases hi : s t <;> cases hj : s j <;> cases bt <;>
        simp [snocHeadSpec, fwdSpec, snocHeadStore, hi, hj]
    · cases st <;> cases d <;> cases hi : s i <;> cases hj : s j <;> cases bt <;>
        simp [snocHeadSpec, fwdSpec, snocHeadStore, hi, hj, ht]
  · show maxLen (snocHeadStore i j (false, false, none) s) ≤ _
    rw [hfin]
    exact maxLen_update_le s i _ (by omega)
      (by have := length_le_maxLen s i; simp; omega)

end SigabaNeo.Tape
