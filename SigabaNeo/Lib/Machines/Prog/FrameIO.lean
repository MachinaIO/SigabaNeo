import SigabaNeo.Lib.Machines.Prog.UBP
import SigabaNeo.Lib.Machines.Prog.Pass
import SigabaNeo.Trusted.Primitive

/-!
# Reading and writing framed words on tapes

The inputs and outputs of the algorithms of primitives are tuples of words, `encodeTuple`: the
concatenation of the frames `MultiTapeTM.frame u` (every bit `b` written `[true, b]`, then
`[false]`). Coin-free programs over a few tapes:

* `unfrP : Prog 4` (`0` the source, `1` the destination, `2` counter, `3` flag): consume the first
  frame of the source and append its word to the destination (`run_unfrP`);
* `frP : Prog 3` (`0` the word, `1` counter, `2` scratch): `0 := frame (s 0)` (`run_frP`);
* `leP n : Prog 3` (`0` the word, `1` the flag, `2` scratch): `1 := [true]` if `|s 0| ≤ n`, `[]`
  otherwise (`run_leP`).

Each with closed-form uniform bounds (`ubp_unfrP`, `ubp_frP`, `ubp_leP`).
-/

namespace SigabaNeo.Tape.Prog

open Turing

variable {k : ℕ}

/-! ### Tuples -/

theorem encodeTuple_cons (a : List Bool) (xs : List (List Bool)) :
    SigabaNeo.encodeTuple (a :: xs) = MultiTapeTM.frame a ++ SigabaNeo.encodeTuple xs := rfl

theorem encodeTuple_nil : SigabaNeo.encodeTuple [] = [] := rfl

theorem encodeTuple_single (a : List Bool) :
    SigabaNeo.encodeTuple [a] = MultiTapeTM.frame a := by
  rw [encodeTuple_cons, encodeTuple_nil, List.append_nil]

theorem length_frame (u : List Bool) : (MultiTapeTM.frame u).length = 2 * u.length + 1 := by
  simp only [MultiTapeTM.frame, List.length_append, List.length_flatMap, List.length_cons,
    List.length_nil, List.length_singleton]
  induction u with
  | nil => rfl
  | cons b u ih => simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢; omega

theorem frame_cons (b : Bool) (u : List Bool) :
    MultiTapeTM.frame (b :: u) = true :: b :: MultiTapeTM.frame u := rfl

theorem frame_nil : MultiTapeTM.frame [] = [false] := rfl

/-! ### Unframing -/

/-- The flag word. -/
def flagW (b : Bool) : List Bool := if b then [true] else []

/-- One round: when not done, read a pair `true b` (append `b`) or the terminator. -/
def unfrStep (a : List Bool × List Bool × Bool) : List Bool × List Bool × Bool :=
  if a.2.2 then a else
    match a.1 with
    | true :: r => (r.tail, a.2.1 ++ r.take 1, false)
    | _ => (a.1.tail, a.2.1, true)

theorem unfrStep_done (r d : List Bool) : unfrStep (r, d, true) = (r, d, true) := rfl

theorem iterate_unfrStep_done (r d : List Bool) : ∀ n, unfrStep^[n] (r, d, true) = (r, d, true)
  | 0 => rfl
  | n + 1 => by rw [Function.iterate_succ_apply, unfrStep_done, iterate_unfrStep_done r d n]

theorem iterate_unfrStep (r : List Bool) : ∀ (u d : List Bool) (n : ℕ), u.length + 1 ≤ n →
    unfrStep^[n] (MultiTapeTM.frame u ++ r, d, false) = (r, d ++ u, true)
  | [], d, n + 1, _ => by
    rw [Function.iterate_succ_apply, frame_nil]
    simp only [unfrStep, List.singleton_append, Bool.false_eq_true, ↓reduceIte, List.tail_cons]
    rw [iterate_unfrStep_done, List.append_nil]
  | b :: u, d, n + 1, h => by
    rw [Function.iterate_succ_apply, frame_cons]
    simp only [unfrStep, List.cons_append, Bool.false_eq_true, ↓reduceIte, List.tail_cons,
      List.take_succ_cons, List.take_zero]
    rw [iterate_unfrStep r u (d ++ [b]) n (by simp at h; omega), List.append_assoc]
    rfl

/-- The round on tapes. -/
def unfrBody : Prog 4 :=
  ifBlank 3 (ifBit 0 (prim (.tail 0) ⨾ prim (.snocHead 1 0) ⨾ prim (.tail 0))
    (prim (.tail 0) ⨾ prim (.snoc 3 true))) (prim (.copy 3 3))

/-- **Consume the first frame of tape `0`, append its word to tape `1`.** -/
def unfrP : Prog 4 := prim (.copy 2 0) ⨾ loop 2 unfrBody ⨾ prim (.clear 3)

/-- The store of an abstract state. -/
def unfrG (s : Store 4) (a : List Bool × List Bool × Bool) : Store 4 :=
  Function.update (Function.update (Function.update s 0 a.1) 1 a.2.1) 3 (flagW a.2.2)

theorem run_unfrBody (s : Store 4) (a : List Bool × List Bool × Bool) (w : List Bool) :
    run unfrBody (Function.update (unfrG s a) 2 w) = Function.update (unfrG s (unfrStep a)) 2 w := by
  obtain ⟨r, d, f⟩ := a
  funext t
  cases f
  · rcases r with _ | ⟨b, r⟩
    · simp [unfrBody, unfrG, unfrStep, run_ifBlank, run_ifBit, run_prim, Prim.apply, flagW,
        Function.update_apply]
      fin_cases t <;> simp
    · cases b
      · simp [unfrBody, unfrG, unfrStep, run_ifBlank, run_ifBit, run_prim, Prim.apply, flagW,
          Function.update_apply]
        fin_cases t <;> simp
      · simp [unfrBody, unfrG, unfrStep, run_ifBlank, run_ifBit, run_prim, Prim.apply, flagW,
          Function.update_apply]
        fin_cases t <;> simp
  · simp [unfrBody, unfrG, unfrStep, run_ifBlank, run_prim, Prim.apply, flagW,
      Function.update_apply]
    fin_cases t <;> simp

/-- **The law of `unfrP`.** -/
theorem run_unfrP (s : Store 4) (u r : List Bool) (h0 : s 0 = MultiTapeTM.frame u ++ r)
    (h3 : s 3 = []) :
    run unfrP s = Function.update (Function.update (Function.update s 0 r) 1 (s 1 ++ u)) 2 [] := by
  have hl := run_loop_iter 2 unfrBody (unfrG s) unfrStep (fun _ => True)
    (fun a w _ => run_unfrBody s a w) (fun _ _ => trivial) (s 0) (s 0, s 1, false) trivial
  have hs : Function.update s 2 (s 0) = Function.update (unfrG s (s 0, s 1, false)) 2 (s 0) := by
    funext t
    simp only [unfrG, flagW, Bool.false_eq_true, ↓reduceIte, Function.update_apply]
    fin_cases t <;> simp <;> first | exact h3 | exact h3.symm
  simp only [unfrP, run_seq, run_prim, Prim.apply]
  rw [hs, hl, h0, iterate_unfrStep r u (s 1) _ (by simp only [List.length_append, length_frame]; omega)]
  funext t
  simp only [unfrG, flagW, ↓reduceIte, Function.update_apply]
  fin_cases t <;> simp [h3]

theorem coinFree_unfrP : unfrP.CoinFree := rfl

theorem wf_unfrP : unfrP.WF := by
  simp [unfrP, unfrBody, WF, Preserves, Prim.writes]

/-! ### Bounds -/

theorem ubp_unfrBody (M : ℕ) : UBP unfrBody M (4 * (2 * (M + 2) + 3) + 2) (M + 1) := by
  have h1 := (ubp_prim0 (k := 4) (.tail 0) rfl M).seq ((ubp_prim (.snocHead 1 0) M).seq
    (ubp_prim0 (.tail 0) rfl (M + 1)))
  have h2 := (ubp_prim0 (k := 4) (.tail 0) rfl M).seq (ubp_prim (.snoc 3 true) M)
  have h3 := ubp_prim0 (k := 4) (.copy 3 3) rfl M
  refine (ubp_ifBlank (ubp_ifBit h1 h2) h3).mono ?_ ?_
  · simp only [max_def]; split_ifs <;> omega
  · simp only [max_def]; split_ifs <;> omega

/-- The time of `unfrP` from tapes at most `M`. -/
def unfrT (M : ℕ) : ℕ :=
  (2 * (M + 1) + 3) + (M * (2 * (M + 1 * M) + 3 + (4 * (2 * (M + 1 * M + 2) + 3) + 2) + 1) + 2) +
    (2 * (M + 1 * M + 1) + 3)

theorem ubp_unfrP (M : ℕ) : UBP unfrP M (unfrT M) (2 * M) := by
  have h := (ubp_prim0 (k := 4) (.copy 2 0) rfl M).seq
    ((ubp_loop 2 unfrBody 1 _ ubp_unfrBody M).seq (ubp_prim0 (.clear 3) rfl _))
  refine h.mono (le_of_eq ?_) (by omega)
  simp only [unfrT, Nat.add_assoc]

/-! ### Framing -/

/-- **Frame tape `0`.** -/
def frP : Prog 3 :=
  prim (.copy 1 0) ⨾ loop 1 (prim (.snoc 2 true) ⨾ prim (.snocHead 2 0) ⨾ prim (.tail 0)) ⨾
    prim (.snoc 2 false) ⨾ prim (.copy 0 2) ⨾ prim (.clear 2)

/-- The abstract round. -/
def frStep (a : List Bool × List Bool) : List Bool × List Bool :=
  (a.1.tail, a.2 ++ true :: a.1.take 1)

theorem iterate_frStep : ∀ (u d : List Bool),
    frStep^[u.length] (u, d) = ([], d ++ u.flatMap (fun b => [true, b]))
  | [], d => by simp
  | b :: u, d => by
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [frStep, List.tail_cons, List.take_succ_cons, List.take_zero]
    rw [iterate_frStep u, List.flatMap_cons, List.append_assoc]

/-- **The law of `frP`.** -/
theorem run_frP (s : Store 3) (h2 : s 2 = []) :
    run frP s = Function.update (Function.update s 0 (MultiTapeTM.frame (s 0))) 1 [] := by
  let G : List Bool × List Bool → Store 3 := fun a => Function.update (Function.update s 0 a.1) 2 a.2
  have hl := run_loop_iter 1 (prim (.snoc 2 true) ⨾ prim (.snocHead 2 0) ⨾ prim (.tail 0)) G frStep
    (fun _ => True) (fun a w _ => by
      funext t
      simp only [G, frStep, run_seq, run_prim, Prim.apply, Function.update_apply]
      fin_cases t <;> simp) (fun _ _ => trivial) (s 0) (s 0, []) trivial
  have hs : Function.update s 1 (s 0) = Function.update (G (s 0, [])) 1 (s 0) := by
    funext t
    simp only [G, Function.update_apply]
    fin_cases t <;> simp <;> first | exact h2 | exact h2.symm
  simp only [frP, run_seq, run_prim, Prim.apply]
  rw [hs, hl, iterate_frStep]
  funext t
  simp only [G, Function.update_apply]
  fin_cases t <;> simp [MultiTapeTM.frame, h2]

theorem coinFree_frP : frP.CoinFree := rfl

theorem wf_frP : frP.WF := by
  simp [frP, WF, Preserves, Prim.writes]

/-- The time of `frP` from tapes at most `M`. -/
def frT (M : ℕ) : ℕ :=
  (2 * (M + 1) + 3) + (M * (2 * (M + 2 * M) + 3 + 3 * (2 * (M + 2 * M + 2) + 3) + 1) + 2) +
    3 * (2 * (M + 2 * M + 2) + 3)

theorem ubp_frP (M : ℕ) : UBP frP M (frT M) (3 * M + 1) := by
  have hb : ∀ M', UBP (prim (.snoc (2 : Fin 3) true) ⨾ prim (.snocHead 2 0) ⨾ prim (.tail 0)) M'
      (3 * (2 * (M' + 2) + 3)) (M' + 2) := fun M' =>
    ((ubp_prim (k := 3) (.snoc 2 true) M').seq ((ubp_prim (.snocHead 2 0) (M' + 1)).seq
      (ubp_prim0 (.tail 0) rfl _))).mono (by omega) (by omega)
  have h := (ubp_prim0 (k := 3) (.copy 1 0) rfl M).seq ((ubp_loop 1 _ 2 _ hb M).seq
    ((ubp_prim (.snoc 2 false) _).seq ((ubp_prim0 (.copy 0 2) rfl _).seq
    (ubp_prim0 (.clear 2) rfl _))))
  refine h.mono ?_ (by omega)
  simp only [frT]; omega

/-! ### The length guard -/

/-- Drop `n` bits of tape `i`. -/
def tailsP (i : Fin k) : ℕ → Prog k
  | 0 => prim (.copy i i)
  | n + 1 => prim (.tail i) ⨾ tailsP i n

theorem run_tailsP (i : Fin k) : ∀ (n : ℕ) (s : Store k),
    run (tailsP i n) s = Function.update s i ((s i).drop n)
  | 0, s => by simp [tailsP, run_prim, Prim.apply]
  | n + 1, s => by
    rw [tailsP, run_seq, run_prim, Prim.apply, run_tailsP i n]
    simp [List.drop_tail, Nat.add_comm]

theorem ubp_tailsP (i : Fin k) : ∀ (n M : ℕ), UBP (tailsP i n) M ((n + 1) * (2 * (M + 1) + 3)) M
  | 0, M => (ubp_prim0 (.copy i i) rfl M).mono (by omega) le_rfl
  | n + 1, M => ((ubp_prim0 (.tail i) rfl M).seq (ubp_tailsP i n M)).mono
      (by rw [Nat.add_mul (n + 1) 1]; omega) le_rfl

theorem coinFree_tailsP (i : Fin k) : ∀ n, (tailsP i n).CoinFree
  | 0 => rfl
  | n + 1 => by
    simpa [CoinFree, tailsP, coinFreeB] using coinFree_tailsP i n

theorem wf_tailsP (i : Fin k) : ∀ n, (tailsP i n).WF
  | 0 => trivial
  | n + 1 => ⟨trivial, wf_tailsP i n⟩

/-- **The length guard**: `1 := [true]` if `|s 0| ≤ n`, `[]` otherwise. -/
def leP (n : ℕ) : Prog 3 :=
  prim (.clear 1) ⨾ prim (.copy 2 0) ⨾ tailsP 2 n ⨾
    ifBlank 2 (prim (.snoc 1 true)) (prim (.copy 1 1)) ⨾ prim (.clear 2)

theorem run_leP (n : ℕ) (s : Store 3) :
    run (leP n) s = Function.update (Function.update s 1
      (if (s 0).length ≤ n then [true] else [])) 2 [] := by
  simp only [leP, run_seq, run_prim, Prim.apply, run_tailsP, run_ifBlank]
  funext t
  by_cases h : (s 0).length ≤ n
  · have hd : (s 0).drop n = [] := List.drop_eq_nil_of_le (by omega)
    simp only [Function.update_apply]
    fin_cases t <;> simp [hd, h]
  · have hd : (s 0).drop n ≠ [] := by
      intro e; have := congrArg List.length e; simp at this; omega
    simp only [Function.update_apply]
    fin_cases t <;> simp [hd, h]

theorem coinFree_leP (n : ℕ) : (leP n).CoinFree := by
  have := coinFree_tailsP (2 : Fin 3) n
  simp only [CoinFree] at this
  simp [CoinFree, leP, coinFreeB, this]

theorem wf_leP (n : ℕ) : (leP n).WF :=
  ⟨trivial, trivial, wf_tailsP 2 n, ⟨trivial, trivial⟩, trivial⟩

/-- The time of `leP n` from tapes at most `M`. -/
def leT (n M : ℕ) : ℕ := (n + 5) * (2 * (M + 2) + 3) + 1

theorem ubp_leP (n M : ℕ) : UBP (leP n) M (leT n M) (M + 1) := by
  have h := (ubp_prim0 (k := 3) (.clear 1) rfl M).seq ((ubp_prim0 (.copy 2 0) rfl M).seq
    ((ubp_tailsP 2 n M).seq ((ubp_ifBlank (i := 2) (ubp_prim (.snoc 1 true) M)
      (ubp_prim0 (.copy 1 1) rfl M)).seq (ubp_prim0 (.clear 2) rfl _))))
  refine h.mono ?_ (by simp only [max_def]; split_ifs <;> omega)
  simp only [leT, max_def]
  split_ifs <;> nlinarith

end SigabaNeo.Tape.Prog
