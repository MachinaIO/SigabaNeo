import SigabaNeo.Lib.Machines.Prog.WordBlocks
import SigabaNeo.Lib.Lattices.Homomorphic.SLP

/-!
# Straight-line programs on tapes

A straight-line program `p : SLP ι` runs on tapes with a *gate program* `P` computing the gate's
step `f` on words of `V` bits (`StepSpec`), e.g. the BGG+ NAND of public keys `nandP`.

**Encoding.** A wire is read through its *position* in the list of values
`ins ++ [one] ++ acc` (the `n` input words, the word of `1`, the values of the gates computed so
far): an input `i` at `ix i`, `1` at `n`, the gate `m` at `n + 1 + m` if it is already computed and
at `n` otherwise (the default of `SLP.wireVal`), `wireIx`. A position `j ≤ W` is written in unary on
`W` bits (`unaryW W j`, `j` ones then zeros), and the program as the words of the positions of the
two wires of each gate, in order (`gatesW`, `2W` bits per gate).

**The store.** The values sit on one tape, `V` bits each. Since programs of the fragment `NoGrow` do
not lengthen words, the store starts with `g` padding blocks (any content), `padW ++ ins ++ one`,
and each gate shifts its value in at the end, dropping one padding block. Before gate `t` the store
is `padW.drop (t V) ++ ins ++ one ++ acc` and a pad counter holds `g − t` bits, so the wire at
position `j` is the block `(g − t) + j` (`selP`: skip `g − t` blocks with `skipP`, then one block per
one-bit of the unary position).

`slpEvalP u v P : Prog k` places the gate program by `u` and its own 12 tapes (and `u 0`, `u 1`,
`u 2`) by `v`. **`run_slpEvalP`**: the store becomes `ins ++ [one] ++ SLP.values …` (flattened).
-/

namespace SigabaNeo.Tape

namespace Prog

open scoped Prog
open SigabaNeo.Lattices

variable {k : ℕ}

/-! ### Blocks of a flattened list -/

theorem drop_take_flatten {V : ℕ} :
    ∀ (vs : List (List Bool)), (∀ w ∈ vs, w.length = V) → ∀ (j : ℕ) (hj : j < vs.length),
      ((vs.flatten).drop (j * V)).take V = vs[j]
  | [], _, j, hj => absurd hj (by simp)
  | w :: vs, h, 0, _ => by
    simp only [List.flatten_cons, Nat.zero_mul, List.drop_zero, List.getElem_cons_zero]
    exact List.take_left' (h w (by simp))
  | w :: vs, h, j + 1, hj => by
    have hw : w.length = V := h w (by simp)
    simp only [List.flatten_cons, List.getElem_cons_succ]
    rw [Nat.succ_mul, Nat.add_comm, ← List.drop_drop, List.drop_left' hw]
    exact drop_take_flatten vs (fun x hx => h x (by simp [hx])) j (by simpa using hj)

theorem length_flatten_of {V : ℕ} :
    ∀ (vs : List (List Bool)), (∀ w ∈ vs, w.length = V) → (vs.flatten).length = vs.length * V
  | [], _ => by simp
  | w :: vs, h => by
    rw [List.flatten_cons, List.length_append, h w (by simp),
      length_flatten_of vs (fun x hx => h x (by simp [hx])), List.length_cons, Nat.succ_mul,
      Nat.add_comm]

/-! ### Unary positions -/

/-- The position `j` in unary on `W` bits. -/
def unaryW (W j : ℕ) : List Bool := List.replicate j true ++ List.replicate (W - j) false

theorem length_unaryW {W j : ℕ} (h : j ≤ W) : (unaryW W j).length = W := by
  simp [unaryW]; omega

theorem count_unaryW (W j : ℕ) : (unaryW W j).count true = j := by
  simp [unaryW, List.count_replicate]

/-! ### Store-level pieces (15 tapes)

Tapes: `0` the store, `1` the gate stream, `2` the pad counter, `3` a template of `V` bits, `4` a
template of `W` bits, `5` `6` the unary positions of the two wires, `7` a stream of the store,
`8` the gate counter, `9` `10` counters, `11` a bit, `12` `13` the two values read, `14` the
value of the gate. -/

def ixA : Fin 5 → Fin 15 := ![1, 5, 11, 9, 4]
def ixB : Fin 5 → Fin 15 := ![1, 6, 11, 9, 4]
def dV : Fin 3 → Fin 15 := ![7, 10, 3]
def skP : Fin 5 → Fin 15 := ![7, 9, 10, 2, 3]
def mvA : Fin 5 → Fin 15 := ![7, 12, 11, 9, 3]
def mvB : Fin 5 → Fin 15 := ![7, 13, 11, 9, 3]
def mvC : Fin 5 → Fin 15 := ![14, 0, 11, 9, 3]
theorem ixA_inj : Function.Injective ixA := by decide
theorem ixB_inj : Function.Injective ixB := by decide
theorem dV_inj : Function.Injective dV := by decide
theorem skP_inj : Function.Injective skP := by decide
theorem mvA_inj : Function.Injective mvA := by decide
theorem mvB_inj : Function.Injective mvB := by decide
theorem mvC_inj : Function.Injective mvC := by decide

/-- Read the unary position of the next wire into the register `R` (`5` or `6`). -/
def readIx (R : Fin 15) (e : Fin 5 → Fin 15) : Prog 15 := cp R 4 ⨾ map e mvP

/-- Skip one block of the store stream per one-bit of `R`. -/
def skipT (R : Fin 15) : Prog 15 := forN 9 R (pp R 11 ⨾ ifBit 11 (map dV dropP) (nop 11) ⨾ clr 11)

/-- Read the block of the wire whose unary position is in `R` into `X`. -/
def selP (R : Fin 15) (e : Fin 5 → Fin 15) (X : Fin 15) : Prog 15 :=
  cp 7 0 ⨾ map skP skipP ⨾ skipT R ⨾ cp X 3 ⨾ map e mvP ⨾ clr 7

/-- Before the gate program: read the two positions and the two values. -/
def preG : Prog 15 := readIx 5 ixA ⨾ readIx 6 ixB ⨾ selP 5 mvA 12 ⨾ selP 6 mvB 13

/-- After the gate program: shift its value into the store, count the gate, clear the values. -/
def postG : Prog 15 := map mvC mvP ⨾ tl 2 ⨾ clr 12 ⨾ clr 13

/-- The scratch tapes `5 … 14` are blank. -/
def Clean15 (r : Store 15) : Prop := ∀ i : Fin 15, 5 ≤ i.val → i ≠ 8 → r i = []

set_option linter.unusedSimpArgs false in
theorem run_readIx {W : ℕ} (r : Store 15) (h9 : r 9 = []) (h11 : r 11 = []) (hW : (r 4).length = W) :
    run (readIx 5 ixA) r = Function.update (Function.update r 1 ((r 1).drop W)) 5 (takeD W (r 1)) ∧
    run (readIx 6 ixB) r = Function.update (Function.update r 1 ((r 1).drop W)) 6 (takeD W (r 1)) := by
  constructor
  · simp only [readIx, run_seq, run_copy]
    rw [run_mvP_map ixA_inj _ (by simp [ixA, h11]) (by simp [ixA, h9])]
    funext t; fin_cases t <;> simp [ixA, hW, takeD_of_length' hW, List.drop_left' hW]
  · simp only [readIx, run_seq, run_copy]
    rw [run_mvP_map ixB_inj _ (by simp [ixB, h11]) (by simp [ixB, h9])]
    funext t; fin_cases t <;> simp [ixB, hW, takeD_of_length' hW, List.drop_left' hW]

/-- The abstract round of `skipT`: (positions left, store stream). -/
def skStep (V : ℕ) : List Bool × List Bool → List Bool × List Bool
  | (rw, sw) => (rw.tail, if hd rw = true then sw.drop V else sw)

theorem skStep_iter (V : ℕ) : ∀ (rw sw : List Bool),
    (skStep V)^[rw.length] (rw, sw) = ([], sw.drop (V * rw.count true))
  | [], sw => by simp
  | b :: rw, sw => by
    rw [List.length_cons, Function.iterate_succ_apply]
    cases b
    · simp only [skStep, List.tail_cons, hd, List.headD_cons, Bool.false_eq_true, ite_false]
      rw [skStep_iter V rw sw]; simp
    · simp only [skStep, List.tail_cons, hd, List.headD_cons, ite_true]
      rw [skStep_iter V rw, List.drop_drop, List.count_cons_self, Nat.mul_succ, Nat.add_comm]

theorem hd_take_one (w : List Bool) : hd (w.take 1) = hd w := by cases w <;> rfl

set_option linter.unusedSimpArgs false in
theorem run_skipT {V : ℕ} (R : Fin 15) (hR : R = 5 ∨ R = 6) (r : Store 15)
    (h9 : r 9 = []) (h10 : r 10 = []) (h11 : r 11 = []) (hV : (r 3).length = V) :
    run (skipT R) r = Function.update (Function.update r R []) 7 ((r 7).drop (V * (r R).count true)) := by
  have key := run_forN (k := 15) 9 R (pp R 11 ⨾ ifBit 11 (map dV dropP) (nop 11) ⨾ clr 11)
    (fun a => Function.update (Function.update r R a.1) 7 a.2) (skStep V) (fun a w => by
      obtain ⟨rw, sw⟩ := a
      rcases hR with rfl | rfl
      all_goals
        simp only [run_seq, run_pop, run_ifBit, run_clear, Function.update_self,
          Function.update_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true, hd_take_one]
        cases hb : hd rw
        · simp only [Bool.false_eq_true, ↓reduceIte, run_nop]
          simp only [skStep, hb, Bool.false_eq_true, ite_false]
          funext t; fin_cases t <;> simp [h11]
        · simp only [↓reduceIte]
          simp only [skStep, hb, ite_true]
          rw [run_dropP_map dV_inj _ (by simp [dV, h10])]
          funext t; fin_cases t <;> simp [dV, h11, hV])
    (r R, r 7) r (by simp)
  rw [skipT, key, skStep_iter]
  rcases hR with rfl | rfl <;> (funext t; fin_cases t <;> simp [h9])

set_option linter.unusedSimpArgs false in
theorem run_selP {V : ℕ} (r : Store 15) (h7 : r 7 = []) (h9 : r 9 = []) (h10 : r 10 = [])
    (h11 : r 11 = []) (hV : (r 3).length = V) :
    run (selP 5 mvA 12) r = Function.update (Function.update r 5 []) 12
      (takeD V ((r 0).drop ((r 2).length * V + V * (r 5).count true))) ∧
    run (selP 6 mvB 13) r = Function.update (Function.update r 6 []) 13
      (takeD V ((r 0).drop ((r 2).length * V + V * (r 6).count true))) := by
  constructor
  · simp only [selP, run_seq, run_copy, run_clear]
    rw [run_skipP_map skP_inj _ ?_ ?_, run_skipT (V := V) 5 (Or.inl rfl) _ ?_ ?_ ?_ ?_,
      run_mvP_map mvA_inj _ ?_ ?_]
    · funext t; fin_cases t <;> simp [skP, mvA, hV, h7, List.drop_drop, List.drop_left' hV]
    all_goals simp [skP, mvA, h7, h9, h10, h11, hV]
  · simp only [selP, run_seq, run_copy, run_clear]
    rw [run_skipP_map skP_inj _ ?_ ?_, run_skipT (V := V) 6 (Or.inr rfl) _ ?_ ?_ ?_ ?_,
      run_mvP_map mvB_inj _ ?_ ?_]
    · funext t; fin_cases t <;> simp [skP, mvB, hV, h7, List.drop_drop, List.drop_left' hV]
    all_goals simp [skP, mvB, h7, h9, h10, h11, hV]

/-- The store of a round: the store `st`, the gate stream `gs`, the pad counter `pc`. -/
def mk15 (r : Store 15) (st gs pc : List Bool) : Store 15 :=
  Function.update (Function.update (Function.update r 0 st) 1 gs) 2 pc

set_option linter.unusedSimpArgs false in
/-- **Before the gate program**: the two positions are read from the gate stream, then the two
values from the store. -/
theorem run_preG {V W : ℕ} (r : Store 15) (hr : Clean15 r) (hV : (r 3).length = V)
    (hW : (r 4).length = W) (st ua ub gs pc : List Bool) (ha : ua.length = W)
    (hb : ub.length = W) :
    run preG (mk15 r st (ua ++ ub ++ gs) pc) =
      Function.update (Function.update (mk15 r st gs pc) 12
        (takeD V (st.drop (pc.length * V + V * ua.count true)))) 13
        (takeD V (st.drop (pc.length * V + V * ub.count true))) := by
  have c : ∀ i : Fin 15, 5 ≤ i.val → i ≠ 8 → mk15 r st (ua ++ ub ++ gs) pc i = [] := by
    intro i h1 h2; simp only [mk15]
    rw [Function.update_of_ne (by intro h; subst h; simp at h1),
      Function.update_of_ne (by intro h; subst h; simp at h1),
      Function.update_of_ne (by intro h; subst h; simp at h1)]
    exact hr i h1 h2
  simp only [preG, run_seq]
  rw [(run_readIx (W := W) _ (c 9 (by decide) (by decide)) (c 11 (by decide) (by decide))
    (by simp [mk15, hW])).1]
  rw [(run_readIx (W := W) _ (by simp [mk15, hr 9 (by decide) (by decide)])
    (by simp [mk15, hr 11 (by decide) (by decide)]) (by simp [mk15, hW])).2]
  rw [(run_selP (V := V) _ ?_ ?_ ?_ ?_ ?_).1]
  rotate_left
  all_goals try simp [mk15, hr 7 (by decide) (by decide), hr 9 (by decide) (by decide),
    hr 10 (by decide) (by decide), hr 11 (by decide) (by decide), hV]
  rw [(run_selP (V := V) _ ?_ ?_ ?_ ?_ ?_).2]
  rotate_left
  all_goals try simp [mk15, hr 7 (by decide) (by decide), hr 9 (by decide) (by decide),
    hr 10 (by decide) (by decide), hr 11 (by decide) (by decide), hV]
  have hdrop : (ua ++ (ub ++ gs)).drop W = ub ++ gs := List.drop_left' ha
  have htake : takeD W (ua ++ (ub ++ gs)) = ua := by
    rw [takeD_eq_take (by simp [ha])]; exact List.take_left' ha
  have hdrop2 : (ub ++ gs).drop W = gs := List.drop_left' hb
  have hdropWW : (ua ++ (ub ++ gs)).drop (W + W) = gs := by
    rw [← List.drop_drop, hdrop, hdrop2]
  have htake2 : takeD W (ub ++ gs) = ub := by
    rw [takeD_eq_take (by simp [hb])]; exact List.take_left' hb
  funext t
  fin_cases t <;> simp [mk15, hdrop, htake, hdrop2, htake2, hdropWW, hr 5 (by decide) (by decide),
    hr 6 (by decide) (by decide)]

set_option linter.unusedSimpArgs false in
/-- **After the gate program**: its value is shifted into the store. -/
theorem run_postG {V : ℕ} (r : Store 15) (hr : Clean15 r) (hV : (r 3).length = V)
    (st gs pc a b c : List Bool) (hc : c.length = V) :
    run postG (Function.update (Function.update (Function.update (mk15 r st gs pc) 12 a) 13 b) 14 c) =
      mk15 r ((st ++ c).drop V) gs pc.tail := by
  simp only [postG, run_seq, run_tail, run_clear]
  rw [run_mvP_map mvC_inj _ ?_ ?_]
  · funext t
    fin_cases t <;> simp [mvC, mk15, hV, hc, takeD_of_length' hc, hr 12 (by decide) (by decide),
      hr 13 (by decide) (by decide), hr 14 (by decide) (by decide)]
  all_goals simp [mvC, mk15, hr 11 (by decide) (by decide), hr 9 (by decide) (by decide)]

end Prog

end SigabaNeo.Tape
