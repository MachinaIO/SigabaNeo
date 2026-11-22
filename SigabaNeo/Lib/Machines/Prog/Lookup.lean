import SigabaNeo.Lib.Machines.Prog.Pass
import SigabaNeo.Lib.Machines.Prog.Stream
import SigabaNeo.Lib.Machines.Inline.Regions

/-!
# Constant words, table lookups and cutting a long word, as tape programs

Coin-free programs of the tape language (`Prog.CoinFree`), so their law is the point mass at their
pure semantics `Prog.run` (`Prog.law_eq_run_of_coinFree`). They lengthen words (`cons`, `snoc`),
so they are outside the fragment `NoGrow`; they are loop-free (`Prog.LoopFree`), so their time is
read off the number of primitives (`Prog.timeBoundT_le_pcount`).

* `putW o w`: `o := w` (`run_putW`), `|w| + 1` primitives.
* `lookupP d sc f o tbl dv`: `o :=` the value of the first entry of the table `tbl` whose key is
  the word of tape `d`, `dv` if there is none (`lookupV`, `run_lookupP`); the scratch tapes `sc`,
  `f` end blank. `lookCount tbl dv + 2` primitives (`pcount_lookupP`). With all values equal
  (`lookupV_const`) or determined by the key (`lookupV_det`), the lookup is a membership test or a
  partial function given by its graph.
* `cutP n : Prog 5`: the front end for a long input `C` on tape `0`: tape `3 :=`
  `replicate (n + 1) (decide (|C| ≤ n))` (the length test, `shortOp`) and tape `4 :=`
  `padW n C = takeD (n + 1) (C ++ [true])` (`takeOp`), with a template of `n + 1` bits on tape `2`;
  tapes `0`, `1`, `2` end blank (`run_cutP`). It has `11` primitives, each one sweep (`cutCore`),
  plus the template, written on its own tape (`cutX n : XProg 5`, a frame), so its time is
  `11 · (2 (|C| + 1 + n + 1) + 5)` plus a term in `n` only (`timeBoundT_cutX`). For `|C| ≤ n` the key
  determines `C` (`unpad_padW`, `padW_inj`), so everything after the cut runs on words of at most
  `n + 1` bits, in a time independent of `|C|`.
* `appendP i j m`: append the first `m` bits of tape `j` to tape `i`, dropping them from `j`
  (`run_appendP`).
-/

namespace SigabaNeo.Tape

open Cslib

namespace Prog

variable {k : ℕ}

/-! ### Constant words -/

/-- `o := w`. -/
def putW (o : Fin k) : List Bool → Prog k
  | [] => prim (.clear o)
  | b :: w => seq (putW o w) (prim (.cons o b))

theorem run_putW (o : Fin k) : ∀ (w : List Bool) (s : Store k),
    run (putW o w) s = Function.update s o w
  | [], s => rfl
  | b :: w, s => by
    rw [putW, run_seq, run_putW o w s, run_prim]
    simp [Prim.apply]

theorem coinFree_putW (o : Fin k) : ∀ w, (putW o w).CoinFree
  | [] => rfl
  | b :: w => by
    simp only [CoinFree, putW, coinFreeB, Bool.and_eq_true]
    exact ⟨coinFree_putW o w, trivial⟩

theorem loopFree_putW (o : Fin k) : ∀ w, (putW o w).LoopFree
  | [] => trivial
  | _ :: w => ⟨loopFree_putW o w, trivial⟩

theorem wf_putW (o : Fin k) : ∀ w, (putW o w).WF
  | [] => trivial
  | _ :: w => ⟨wf_putW o w, trivial⟩

@[simp] theorem pcount_putW (o : Fin k) : ∀ w, pcount (putW o w) = w.length + 1
  | [] => rfl
  | _ :: w => by simp only [putW, pcount, pcount_putW o w, List.length_cons]

theorem lenBoundT_putW (o : Fin k) : ∀ (w : List Bool) (ℓ : Fin k → ℕ),
    lenBoundT (putW o w) ℓ = Function.update ℓ o w.length
  | [], ℓ => rfl
  | b :: w, ℓ => by
    simp only [putW, lenBoundT, lenBoundT_putW o w ℓ, Prim.lenT]
    simp

/-! ### Table lookups -/

/-- The value of the first entry whose key is `x`, or `dv`. -/
def lookupV : List (List Bool × List Bool) → List Bool → List Bool → List Bool
  | [], dv, _ => dv
  | e :: t, dv, x => if x = e.1 then e.2 else lookupV t dv x

/-- A table with one value: a membership test. -/
theorem lookupV_const {α : Type} (K : α → List Bool) (v dv x : List Bool) :
    ∀ l : List α, lookupV (l.map fun a => (K a, v)) dv x = if ∃ a ∈ l, K a = x then v else dv
  | [] => by simp [lookupV]
  | a :: l => by
    simp only [List.map_cons, lookupV, lookupV_const K v dv x l, List.mem_cons, exists_eq_or_imp]
    by_cases h : x = K a
    · simp [h]
    · simp only [h, ite_false]
      have h' : ¬ K a = x := fun e => h e.symm
      simp [h']

/-- A table whose value is determined by its key. -/
theorem lookupV_det {α : Type} (K V : α → List Bool) (dv x v : List Bool) :
    ∀ l : List α, (∀ a ∈ l, K a = x → V a = v) → (∃ a ∈ l, K a = x) →
      lookupV (l.map fun a => (K a, V a)) dv x = v
  | [], _, ⟨a, ha, _⟩ => absurd ha (by simp)
  | a :: l, hV, ⟨b, hb, hbx⟩ => by
    simp only [List.map_cons, lookupV]
    by_cases h : x = K a
    · rw [if_pos h]; exact hV a (by simp) h.symm
    · rw [if_neg h]
      rcases List.mem_cons.mp hb with rfl | hb
      · exact absurd hbx.symm h
      · exact lookupV_det K V dv x v l (fun c hc => hV c (by simp [hc])) ⟨b, hb, hbx⟩

/-- No entry has the key `x`. -/
theorem lookupV_none {α : Type} (K V : α → List Bool) (dv x : List Bool) :
    ∀ l : List α, (∀ a ∈ l, K a ≠ x) → lookupV (l.map fun a => (K a, V a)) dv x = dv
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.map_cons, lookupV]
    rw [if_neg (fun e => h a (by simp) e.symm)]
    exact lookupV_none K V dv x l (fun c hc => h c (by simp [hc]))

/-- The comparisons and writes of the table. -/
def lookC (d sc f o : Fin k) : List (List Bool × List Bool) → List Bool → Prog k
  | [], dv => putW o dv
  | e :: t, dv => seq (putW sc e.1) (seq (prim (.eq d sc f))
      (ifBit f (putW o e.2) (lookC d sc f o t dv)))

/-- **The table lookup**: `o := lookupV tbl dv (s d)`, then the scratch tapes `sc`, `f` are
cleared. -/
def lookupP (d sc f o : Fin k) (tbl : List (List Bool × List Bool)) (dv : List Bool) : Prog k :=
  seq (lookC d sc f o tbl dv) (seq (prim (.clear sc)) (prim (.clear f)))

section Lookup

variable {d sc f o : Fin k}

theorem run_lookC (hd1 : d ≠ sc) (hd2 : d ≠ f) :
    ∀ (tbl : List (List Bool × List Bool)) (dv : List Bool) (s : Store k) (t : Fin k),
      t ≠ sc → t ≠ f →
      run (lookC d sc f o tbl dv) s t = Function.update s o (lookupV tbl dv (s d)) t
  | [], dv, s, t, _, _ => by rw [lookC, run_putW]; rfl
  | e :: tb, dv, s, t, h1, h2 => by
    simp only [lookC, run_seq, run_putW, run_ifBit, run_prim, Prim.apply]
    simp only [Function.update_self, Function.update_of_ne hd1, Function.update_of_ne hd2, hd_cons,
      decide_eq_true_eq, lookupV]
    split_ifs with he
    · simp only [Function.update_apply, h1, h2, ite_false]
    · rw [run_lookC hd1 hd2 tb dv _ t h1 h2]
      simp only [Function.update_apply, h1, h2, ite_false, hd1, hd2]

/-- **The lookup.** -/
theorem run_lookupP (hd1 : d ≠ sc) (hd2 : d ≠ f) (h12 : sc ≠ f) (ho1 : o ≠ sc) (ho2 : o ≠ f)
    (tbl : List (List Bool × List Bool)) (dv : List Bool) (s : Store k) :
    run (lookupP d sc f o tbl dv) s =
      Function.update (Function.update (Function.update s o (lookupV tbl dv (s d))) sc []) f [] := by
  simp only [lookupP, run_seq, run_prim, Prim.apply]
  funext t
  by_cases hf : t = f
  · subst hf; simp
  · by_cases hs : t = sc
    · subst hs; simp [hf]
    · simp only [Function.update_apply, hf, hs, ite_false]
      rw [run_lookC hd1 hd2 tbl dv s t hs hf]
      simp only [Function.update_apply]

theorem coinFree_lookC : ∀ (tbl : List (List Bool × List Bool)) (dv : List Bool),
    (lookC d sc f o tbl dv).CoinFree
  | [], dv => coinFree_putW o dv
  | e :: tb, dv => by
    simp only [CoinFree, lookC, coinFreeB, Bool.and_eq_true]
    exact ⟨coinFree_putW sc e.1, trivial, coinFree_putW o e.2, coinFree_lookC tb dv⟩

theorem coinFree_lookupP (tbl : List (List Bool × List Bool)) (dv : List Bool) :
    (lookupP d sc f o tbl dv).CoinFree := by
  simp only [CoinFree, lookupP, coinFreeB, Bool.and_eq_true]
  exact ⟨coinFree_lookC tbl dv, trivial, trivial⟩

theorem loopFree_lookC : ∀ (tbl : List (List Bool × List Bool)) (dv : List Bool),
    (lookC d sc f o tbl dv).LoopFree
  | [], dv => loopFree_putW o dv
  | e :: tb, dv => ⟨loopFree_putW sc e.1, trivial, loopFree_putW o e.2, loopFree_lookC tb dv⟩

theorem loopFree_lookupP (tbl : List (List Bool × List Bool)) (dv : List Bool) :
    (lookupP d sc f o tbl dv).LoopFree :=
  ⟨loopFree_lookC tbl dv, trivial, trivial⟩

theorem wf_lookC : ∀ (tbl : List (List Bool × List Bool)) (dv : List Bool),
    (lookC d sc f o tbl dv).WF
  | [], dv => wf_putW o dv
  | e :: tb, dv => ⟨wf_putW sc e.1, trivial, wf_putW o e.2, wf_lookC tb dv⟩

theorem wf_lookupP (tbl : List (List Bool × List Bool)) (dv : List Bool) :
    (lookupP d sc f o tbl dv).WF :=
  ⟨wf_lookC tbl dv, trivial, trivial⟩

/-- The number of primitives and branchings of the comparisons and writes. -/
def lookCount : List (List Bool × List Bool) → List Bool → ℕ
  | [], dv => dv.length + 1
  | e :: tb, dv => e.1.length + e.2.length + 4 + lookCount tb dv

theorem pcount_lookC : ∀ (tbl : List (List Bool × List Bool)) (dv : List Bool),
    pcount (lookC d sc f o tbl dv) = lookCount tbl dv
  | [], dv => pcount_putW o dv
  | e :: tb, dv => by
    simp only [lookC, pcount, pcount_putW, pcount_lookC tb dv, lookCount]; ring

theorem pcount_lookupP (tbl : List (List Bool × List Bool)) (dv : List Bool) :
    pcount (lookupP d sc f o tbl dv) = lookCount tbl dv + 2 := by
  simp only [lookupP, pcount, pcount_lookC]

/-- **The time of the lookup**, for tapes of at most `M` bits. -/
theorem timeBoundT_lookupP (tbl : List (List Bool × List Bool)) (dv : List Bool)
    (ℓ : Fin k → ℕ) {M : ℕ} (hM : ∀ t, ℓ t ≤ M) :
    timeBoundT (lookupP d sc f o tbl dv) ℓ ≤
      (lookCount tbl dv + 2) * (2 * (M + (lookCount tbl dv + 2)) + 5) := by
  have := timeBoundT_le_pcount _ (loopFree_lookupP (d := d) (sc := sc) (f := f) (o := o) tbl dv) ℓ hM
  rwa [pcount_lookupP] at this

end Lookup

/-! ### Appending a prefix of a tape -/

/-- Append the first `m` bits of tape `j` to tape `i`, dropping them from `j`. -/
def appendP (i j : Fin k) : ℕ → Prog k
  | 0 => prim (.copy i i)
  | m + 1 => seq (prim (.snocHead i j)) (seq (prim (.tail j)) (appendP i j m))

theorem run_appendP {i j : Fin k} (hij : i ≠ j) : ∀ (m : ℕ) (s : Store k),
    run (appendP i j m) s =
      Function.update (Function.update s i (s i ++ (s j).take m)) j ((s j).drop m)
  | 0, s => by
    simp only [appendP, run_prim, Prim.apply, List.take_zero, List.append_nil, List.drop_zero]
    simp
  | m + 1, s => by
    simp only [appendP, run_seq, run_prim, Prim.apply]
    rw [run_appendP hij m]
    simp only [Function.update_self, Function.update_of_ne hij, Function.update_of_ne hij.symm,
      List.append_assoc, take_one_append_take_tail, List.drop_tail]
    funext t
    simp only [Function.update_apply]
    split_ifs <;> simp_all [Nat.add_comm]

theorem coinFree_appendP (i j : Fin k) : ∀ m, (appendP i j m).CoinFree
  | 0 => rfl
  | m + 1 => by
    simp only [CoinFree, appendP, coinFreeB, Bool.and_eq_true]
    exact ⟨trivial, trivial, coinFree_appendP i j m⟩

theorem loopFree_appendP (i j : Fin k) : ∀ m, (appendP i j m).LoopFree
  | 0 => trivial
  | m + 1 => ⟨trivial, trivial, loopFree_appendP i j m⟩

theorem wf_appendP (i j : Fin k) : ∀ m, (appendP i j m).WF
  | 0 => trivial
  | m + 1 => ⟨trivial, trivial, wf_appendP i j m⟩

@[simp] theorem pcount_appendP (i j : Fin k) : ∀ m, pcount (appendP i j m) = 2 * m + 1
  | 0 => rfl
  | m + 1 => by simp only [appendP, pcount, pcount_appendP i j m]; ring

/-! ### Digit operations for the cut -/

/-- Every digit `true`. -/
def allTOp : DigitOp := fun _ _ _ => (true, false)

/-- The carry from the last digit: some digit of the second word at or after this one is
missing (or `false`). -/
def shortOp : DigitOp := fun _ y c => (c || !y, c || !y)

/-- The digit of the second word (`false` when missing). -/
def takeOp : DigitOp := fun _ y _ => (y, false)

theorem carryOp_allTOp : ∀ xs ys : List Bool,
    (carryOp allTOp xs ys).2 = List.replicate xs.length true
  | [], _ => rfl
  | x :: xs, ys => by
    simp only [carryOp, allTOp, List.length_cons, List.replicate_succ]
    rw [carryOp_allTOp xs]

theorem carryOp_takeOp : ∀ xs ys : List Bool, (carryOp takeOp xs ys).2 = takeD xs.length ys
  | [], _ => rfl
  | x :: xs, ys => by
    simp only [carryOp, takeOp, List.length_cons, takeD]
    rw [carryOp_takeOp xs]
    rfl

theorem carryOp_shortOp : ∀ (xs : List Bool) (r : ℕ),
    carryOp shortOp xs (List.replicate r true) =
      (decide (r < xs.length), List.replicate xs.length (decide (r < xs.length)))
  | [], r => by simp
  | x :: xs, 0 => by
    have ih := carryOp_shortOp xs 0
    simp only [List.replicate_zero, List.headD_nil, List.tail_nil] at ih ⊢
    simp only [carryOp, shortOp, List.headD_nil, List.tail_nil, ih, List.length_cons]
    rcases xs with _ | ⟨a, xs⟩
    · simp
    · simp [List.replicate_succ]
  | x :: xs, r + 1 => by
    have ih := carryOp_shortOp xs r
    simp only [carryOp, shortOp, List.replicate_succ, List.headD_cons, List.tail_cons, ih,
      List.length_cons, Bool.not_true, Bool.or_false]
    simp

/-! ### The cut -/

/-- The key of a word cut at `n + 1` bits: the word, a `true`, then `false` up to `n + 1` bits
(when `|C| ≤ n`). -/
def padW (n : ℕ) (C : List Bool) : List Bool := takeD (n + 1) (C ++ [true])

@[simp] theorem length_padW (n : ℕ) (C : List Bool) : (padW n C).length = n + 1 := length_takeD _ _

/-- Strip the trailing `false` bits and the last `true`. -/
def unpad (w : List Bool) : List Bool := ((w.reverse.dropWhile (· = false)).tail).reverse

theorem takeD_of_le : ∀ (n : ℕ) (w : List Bool), w.length ≤ n →
    takeD n w = w ++ List.replicate (n - w.length) false
  | 0, w, h => by simp [takeD, List.length_eq_zero_iff.mp (Nat.le_zero.mp h)]
  | n + 1, [], _ => by simp [takeD_nil]
  | n + 1, b :: w, h => by
    simp only [takeD, hd_cons, List.tail_cons, List.cons_append, List.length_cons]
    rw [takeD_of_le n w (by simp at h; omega), Nat.add_sub_add_right]

theorem dropWhile_replicate_false (m : ℕ) (l : List Bool) :
    (List.replicate m false ++ true :: l).dropWhile (· = false) = true :: l := by
  induction m with
  | zero => simp [List.dropWhile]
  | succ m ih => simp [List.replicate_succ]

/-- **For `|C| ≤ n` the key determines `C`.** -/
theorem unpad_padW {n : ℕ} {C : List Bool} (h : C.length ≤ n) : unpad (padW n C) = C := by
  rw [padW, takeD_of_le (n + 1) (C ++ [true]) (by simp; omega), unpad]
  simp only [List.reverse_append, List.reverse_replicate, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append]
  rw [dropWhile_replicate_false]
  simp

theorem padW_inj {n : ℕ} {C C' : List Bool} (h : C.length ≤ n) (h' : C'.length ≤ n)
    (e : padW n C = padW n C') : C = C' := by
  rw [← unpad_padW h, ← unpad_padW h', e]

/-- The template of `n + 1` bits on the tape of index `2`. -/
def emb2 : Fin 1 ↪ Fin 5 := ⟨fun _ => 2, fun a b _ => Subsingleton.elim a b⟩

/-- The sweeps of the cut: tapes `0` the word `C`, `1` scratch, `2` the template, `3` the length
flag, `4` the key. -/
def cutCore : Prog 5 :=
  seq (prim (.copy 1 0)) (seq (prim (.carry allTOp 1 1)) (seq (prim (.copy 3 2))
    (seq (prim (.carry shortOp 3 1)) (seq (prim (.snoc 0 true)) (seq (prim (.copy 4 2))
      (seq (prim (.carry takeOp 4 0)) (seq (prim (.clear 0)) (seq (prim (.clear 1))
        (prim (.clear 2))))))))))

/-- **The cut**: write the template on its own tape, then sweep. -/
def cutX (n : ℕ) : XProg 5 :=
  .seq (.frame emb2 (.prog (putW 0 (List.replicate (n + 1) false)))) (.prog cutCore)

/-- The store after the cut. -/
def cutOut (n : ℕ) (C : List Bool) : Store 5 :=
  ![[], [], [], List.replicate (n + 1) (decide (C.length ≤ n)), padW n C]

theorem run_cutCore {n : ℕ} (s : Store 5) (h2 : s 2 = List.replicate (n + 1) false) :
    run cutCore s = cutOut n (s 0) := by
  have e1 := carryOp_allTOp (s 0) (s 0)
  have e2 := carryOp_shortOp (List.replicate (n + 1) false) (s 0).length
  have e3 := carryOp_takeOp (List.replicate (n + 1) false) (s 0 ++ [true])
  simp only [List.length_replicate] at e2 e3
  funext t
  fin_cases t <;>
    simp [cutCore, run_seq, run_prim, Prim.apply, Function.update_apply, cutOut, h2, e1, e2, e3,
      padW, Nat.lt_succ_iff]

theorem embedF_emb2 {α : Type} (s : Fin 5 → α) (w : α) :
    embedF emb2 s (Function.update (fun j => s (emb2 j)) 0 w) = Function.update s 2 w := by
  funext l
  rcases embedF_cases emb2 s (Function.update (fun j => s (emb2 j)) 0 w) l with ⟨hl, h⟩ | ⟨j, hj, h⟩
  · rw [h]
    have : l ≠ 2 := fun e => by
      subst e
      have := partialInv_self emb2 0
      rw [show emb2 0 = 2 from rfl] at this
      rw [this] at hl; cases hl
    simp [this]
  · rw [h, ← hj, Subsingleton.elim j 0]
    simp [show emb2 0 = 2 from rfl]

theorem coinFree_cutCore : cutCore.CoinFree := rfl

/-- **The law of the cut.** -/
theorem law_cutX (n : ℕ) (s : Store 5) : (cutX n).law s = PMF.pure (cutOut n (s 0)) := by
  rw [cutX, XProg.law_seq, XProg.law_frame, XProg.law_prog,
    law_eq_run_of_coinFree _ (coinFree_putW 0 _), run_putW, PMF.pure_map, PMF.pure_bind,
    embedF_emb2, XProg.law_prog, law_eq_run_of_coinFree _ coinFree_cutCore,
    run_cutCore (n := n) _ (by simp)]
  simp

theorem wf_cutX (n : ℕ) : (cutX n).WF :=
  ⟨wf_putW 0 _, show cutCore.WF by simp [cutCore, Prog.WF]⟩

theorem lenBoundT_cutX (n : ℕ) (ℓ : Fin 5 → ℕ) :
    (cutX n).lenBoundT ℓ = ![0, 0, 0, n + 1, n + 1] := by
  have h : XProg.lenBoundT (.frame emb2 (.prog (putW 0 (List.replicate (n + 1) false)))) ℓ =
      Function.update ℓ 2 (n + 1) := by
    show embedF emb2 ℓ (lenBoundT (putW 0 _) fun j => ℓ (emb2 j)) = _
    rw [lenBoundT_putW, List.length_replicate]
    exact embedF_emb2 ℓ (n + 1)
  show XProg.lenBoundT (.prog cutCore) (XProg.lenBoundT _ ℓ) = _
  rw [h]
  funext t
  fin_cases t <;> simp [XProg.lenBoundT, cutCore, lenBoundT, Prim.lenT, Function.update_apply]

/-- **The time of the cut**: `10` sweeps of words of at most `M` bits (`M` bounds the input and
`n + 1`), plus the template, written on its own tape. -/
theorem timeBoundT_cutX (n : ℕ) (ℓ : Fin 5 → ℕ) {M : ℕ} (hM : ∀ t, ℓ t ≤ M) (hn : n + 1 ≤ M) :
    (cutX n).timeBoundT ℓ ≤ (n + 2) * (2 * (ℓ 2 + (n + 2)) + 5) + 10 * (2 * (M + 10) + 5) := by
  have h1 : timeBoundT (putW (0 : Fin 1) (List.replicate (n + 1) false)) (fun _ => ℓ 2) ≤
      (n + 2) * (2 * (ℓ 2 + (n + 2)) + 5) := by
    have := timeBoundT_le_pcount _ (loopFree_putW (0 : Fin 1) (List.replicate (n + 1) false))
      (fun _ => ℓ 2) (M := ℓ 2) (fun _ => le_rfl)
    simpa using this
  have h2 : timeBoundT cutCore (Function.update ℓ 2 (n + 1)) ≤ 10 * (2 * (M + 10) + 5) := by
    have := timeBoundT_le_pcount cutCore (by simp [cutCore, LoopFree])
      (Function.update ℓ 2 (n + 1)) (M := M) (fun t => by
        by_cases h : t = 2
        · subst h; simpa using hn
        · simpa [h] using hM t)
    simpa [cutCore, pcount] using this
  have h : XProg.lenBoundT (.frame emb2 (.prog (putW 0 (List.replicate (n + 1) false)))) ℓ =
      Function.update ℓ 2 (n + 1) := by
    show embedF emb2 ℓ (lenBoundT (putW 0 _) fun j => ℓ (emb2 j)) = _
    rw [lenBoundT_putW, List.length_replicate]
    exact embedF_emb2 ℓ (n + 1)
  show timeBoundT (putW 0 _) (fun j => ℓ (emb2 j)) +
    XProg.timeBoundT (.prog cutCore) (XProg.lenBoundT _ ℓ) ≤ _
  rw [h]
  exact Nat.add_le_add h1 h2

end Prog

end SigabaNeo.Tape
