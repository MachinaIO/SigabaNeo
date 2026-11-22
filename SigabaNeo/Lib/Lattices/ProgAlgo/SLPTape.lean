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

/-! ### The encoding of a program -/

section Encoding

variable {ι : Type*}

/-- The position of a wire for the gate `t`, in `ins ++ [one] ++ acc`. -/
def wireIx (ix : ι → ℕ) (n t : ℕ) : Wire ι → ℕ
  | .input i => ix i
  | .one => n
  | .gate m => if m < t then n + 1 + m else n

theorem wireIx_le (ix : ι → ℕ) {n : ℕ} (hix : ∀ i, ix i < n) (t : ℕ) (w : Wire ι) :
    wireIx ix n t w ≤ n + t := by
  cases w with
  | input i => have := hix i; simp only [wireIx]; omega
  | one => simp only [wireIx]; omega
  | gate m => simp only [wireIx]; split_ifs <;> omega

/-- **The word of a program**: the unary positions of the two wires of each gate, in order. -/
def gatesW (ix : ι → ℕ) (n W : ℕ) : SLP ι → ℕ → List Bool
  | [], _ => []
  | g :: p, t => unaryW W (wireIx ix n t g.a) ++ unaryW W (wireIx ix n t g.b) ++ gatesW ix n W p (t + 1)

theorem length_gatesW (ix : ι → ℕ) {n W : ℕ} (hix : ∀ i, ix i < n) :
    ∀ (p : SLP ι) (t : ℕ), n + t + p.length ≤ W → (gatesW ix n W p t).length = p.length * (2 * W)
  | [], _, _ => by simp [gatesW]
  | g :: p, t, h => by
    simp only [List.length_cons] at h
    have ha := wireIx_le ix hix t g.a
    have hb := wireIx_le ix hix t g.b
    rw [gatesW, List.length_append, List.length_append, length_unaryW (by omega),
      length_unaryW (by omega), length_gatesW ix hix p (t + 1) (by omega), List.length_cons]
    ring

/-- **Reading a wire**: the entry at its position is its value. -/
theorem getElem_wireIx (ix : ι → ℕ) {n : ℕ} (ins : List (List Bool)) (hn : ins.length = n)
    (hix : ∀ i, ix i < n) (one : List Bool) (acc : List (List Bool)) (w : Wire ι) :
    ∃ h : wireIx ix n acc.length w < (ins ++ [one] ++ acc).length,
      (ins ++ [one] ++ acc)[wireIx ix n acc.length w] =
        SLP.wireVal (fun i => ins.getD (ix i) []) one acc w := by
  have hlen : (ins ++ [one] ++ acc).length = n + 1 + acc.length := by simp [hn]; omega
  cases w with
  | input i =>
    have hi := hix i
    refine ⟨by simp only [wireIx, hlen]; omega, ?_⟩
    simp only [wireIx, SLP.wireVal]
    rw [List.getElem_append_left (by simp [hn]; omega), List.getElem_append_left (by omega),
      List.getD_eq_getElem _ _ (by omega)]
  | one =>
    refine ⟨by simp only [wireIx, hlen]; omega, ?_⟩
    simp only [wireIx, SLP.wireVal]
    rw [List.getElem_append_left (by simp [hn])]
    simp [hn]
  | gate m =>
    by_cases hm : m < acc.length
    · refine ⟨by simp only [wireIx, hm, ite_true, hlen]; omega, ?_⟩
      simp only [wireIx, hm, ite_true, SLP.wireVal]
      rw [List.getElem_append_right (by simp [hn]), List.getD_eq_getElem _ _ hm]
      congr 1; simp [hn]
    · refine ⟨by simp only [wireIx, hm, ite_false, hlen]; omega, ?_⟩
      simp only [wireIx, hm, ite_false, SLP.wireVal]
      rw [List.getElem_append_left (by simp [hn]), List.getD_eq_default _ _ (by omega)]
      simp [hn]

end Encoding

/-! ### Gate programs and the placed evaluator -/

/-- **A gate program** for the step `f` on words of `V` bits: tapes `0` the value, `1` `2` the two
inputs; the precondition `Pre` (templates, blank scratch) does not look at the tapes `0`, `1`, `2`. -/
structure StepSpec {m : ℕ} (P : Prog (m + 3)) (V : ℕ) (f : List Bool → List Bool → List Bool)
    (Pre : Store (m + 3) → Prop) : Prop where
  noGrow : P.NoGrow
  wf : P.WF
  pre_upd : ∀ (s : Store (m + 3)) (i : Fin (m + 3)), i.val < 3 → ∀ w, Pre s →
    Pre (Function.update s i w)
  run_eq : ∀ s, Pre s → (s 1).length = V → (s 2).length = V →
    run P s = Function.update s 0 (f (s 1) (s 2))
  len : ∀ a b, a.length = V → b.length = V → (f a b).length = V

/-- **The placement** of the evaluator's 15 tapes (`v`) and of the gate program's (`u`) on a
machine with `k` tapes: the values read and written are the gate program's tapes `1`, `2`, `0`;
otherwise the two placements are disjoint. -/
structure Placed {m : ℕ} (u : Fin (m + 3) → Fin k) (v : Fin 15 → Fin k) : Prop where
  hu : Function.Injective u
  hv : Function.Injective v
  v12 : v 12 = u 1
  v13 : v 13 = u 2
  v14 : v 14 = u 0
  disj : ∀ (i : Fin 15) (j : Fin (m + 3)), v i = u j → 12 ≤ i.val

/-- One gate: read the two values, run the gate program, shift its value into the store. -/
def slpBody {m : ℕ} (u : Fin (m + 3) → Fin k) (v : Fin 15 → Fin k) (P : Prog (m + 3)) : Prog k :=
  map v preG ⨾ map u P ⨾ map v postG

/-- **The evaluator**: one round per bit of the pad counter `v 2`, i.e. per gate. -/
def slpEvalP {m : ℕ} (u : Fin (m + 3) → Fin k) (v : Fin 15 → Fin k) (P : Prog (m + 3)) : Prog k :=
  forN (v 8) (v 2) (slpBody u v P)

theorem val_one3 (m : ℕ) : ((1 : Fin (m + 3)) : ℕ) = 1 :=
  show 1 % (m + 3) = 1 from Nat.mod_eq_of_lt (show 1 < m + 3 by omega)
theorem val_two3 (m : ℕ) : ((2 : Fin (m + 3)) : ℕ) = 2 :=
  show 2 % (m + 3) = 2 from Nat.mod_eq_of_lt (show 2 < m + 3 by omega)
theorem one_ne_two3 (m : ℕ) : (1 : Fin (m + 3)) ≠ 2 := fun h => by
  have := congrArg Fin.val h; rw [val_one3, val_two3] at this; omega

theorem zero_ne_one3 (m : ℕ) : (0 : Fin (m + 3)) ≠ 1 := fun h => by
  have := congrArg Fin.val h; rw [val_one3] at this; simp at this
theorem zero_ne_two3 (m : ℕ) : (0 : Fin (m + 3)) ≠ 2 := fun h => by
  have := congrArg Fin.val h; rw [val_two3] at this; simp at this

section Placed

variable {m : ℕ} {u : Fin (m + 3) → Fin k} {v : Fin 15 → Fin k} {P : Prog (m + 3)} {V : ℕ}
  {f : List Bool → List Bool → List Bool} {Pre : Store (m + 3) → Prop}

theorem Placed.comp_extend (hpl : Placed u v) (Y : Store 15) (s : Store k) :
    Function.extend v Y s ∘ u =
      Function.update (Function.update (Function.update (s ∘ u) 0 (Y 14)) 1 (Y 12)) 2 (Y 13) := by
  funext ⟨j, hj⟩
  simp only [Function.comp]
  match j, hj with
  | 0, _ =>
    have : (⟨0, by omega⟩ : Fin (m + 3)) = 0 := rfl
    rw [this, ← hpl.v14, hpl.hv.extend_apply, Function.update_of_ne (zero_ne_two3 m),
      Function.update_of_ne (zero_ne_one3 m), Function.update_self]
  | 1, _ =>
    have : (⟨1, by omega⟩ : Fin (m + 3)) = 1 := Fin.ext (by rw [val_one3])
    rw [this, ← hpl.v12, hpl.hv.extend_apply]
    simp [Function.update_of_ne (one_ne_two3 m)]
  | 2, _ =>
    have : (⟨2, by omega⟩ : Fin (m + 3)) = 2 := Fin.ext (by rw [val_two3])
    rw [this, ← hpl.v13, hpl.hv.extend_apply]; simp
  | j + 3, hj =>
    have hne : ∀ i, v i ≠ u ⟨j + 3, hj⟩ := by
      intro i hi
      have h12 := hpl.disj i _ hi
      have : i = 12 ∨ i = 13 ∨ i = 14 := by
        rcases i with ⟨i, hi'⟩; simp only [Fin.ext_iff]; simp at h12 ⊢; omega
      rcases this with rfl | rfl | rfl
      · rw [hpl.v12] at hi; have := congrArg Fin.val (hpl.hu hi); rw [val_one3] at this; simp at this
      · rw [hpl.v13] at hi; have := congrArg Fin.val (hpl.hu hi); rw [val_two3] at this; simp at this
      · rw [hpl.v14] at hi; have := congrArg Fin.val (hpl.hu hi); simp at this
    rw [extend_apply_of_not_mem _ _ hne]
    have h0 : (⟨j + 3, hj⟩ : Fin (m + 3)) ≠ 0 := fun h => by simpa using congrArg Fin.val h
    have h1 : (⟨j + 3, hj⟩ : Fin (m + 3)) ≠ 1 := fun h => by
      have := congrArg Fin.val h; rw [val_one3] at this; simp at this
    have h2 : (⟨j + 3, hj⟩ : Fin (m + 3)) ≠ 2 := fun h => by
      have := congrArg Fin.val h; rw [val_two3] at this; simp at this
    rw [Function.update_of_ne h2, Function.update_of_ne h1, Function.update_of_ne h0]
    rfl

/-- **The gate program inside the evaluator** writes `f` of the two values on the value tape. -/
theorem run_map_step (hpl : Placed u v) (hP : StepSpec P V f Pre) (s : Store k)
    (hPre : Pre (s ∘ u)) (Y : Store 15) (hA : (Y 12).length = V) (hB : (Y 13).length = V) :
    run (map u P) (Function.extend v Y s) =
      Function.extend v (Function.update Y 14 (f (Y 12) (Y 13))) s := by
  have hc := hpl.comp_extend Y s
  have hpre : Pre (Function.extend v Y s ∘ u) := by
    rw [hc]
    exact hP.pre_upd _ 2 (by rw [val_two3]; omega) _ (hP.pre_upd _ 1 (by rw [val_one3]; omega) _
      (hP.pre_upd _ 0 (by simp) _ hPre))
  have h1 : (Function.extend v Y s ∘ u) 1 = Y 12 := by
    rw [hc]; simp [Function.update_of_ne (one_ne_two3 m)]
  have h2 : (Function.extend v Y s ∘ u) 2 = Y 13 := by rw [hc]; simp
  rw [run_map_eq_update hpl.hu P _ 0 _ (hP.run_eq _ hpre (by rw [h1, hA]) (by rw [h2, hB])), h1, h2,
    ← hpl.v14, extend_update hpl.hv]

/-- The block `j` of `L`, after `q` padding blocks. -/
theorem takeD_drop_blocks {V q : ℕ} (pad : List Bool) (hpad : pad.length = q * V)
    (L : List (List Bool)) (hL : ∀ x ∈ L, x.length = V) (j : ℕ) (hj : j < L.length) :
    takeD V ((pad ++ L.flatten).drop (q * V + V * j)) = L[j] := by
  rw [← List.drop_drop, List.drop_left' hpad, Nat.mul_comm V j]
  have hlen := length_flatten_of L hL
  have hle : V ≤ (L.flatten.drop (j * V)).length := by
    rw [List.length_drop, hlen]
    have := Nat.mul_le_mul_right V (show j + 1 ≤ L.length by omega)
    rw [Nat.succ_mul] at this; omega
  rw [takeD_eq_take hle, drop_take_flatten L hL j hj]

/-- The store before a gate: `acc` the values computed, `p'` the gates left, `w` on the counter. -/
noncomputable def slpSt {ι : Type*} (v : Fin 15 → Fin k) (s : Store k) (V : ℕ) (ix : ι → ℕ) (n W : ℕ)
    (padW pcw : List Bool) (base : List (List Bool)) (p' : SLP ι) (acc : List (List Bool))
    (w : List Bool) : Store k :=
  Function.extend v (mk15 (Function.update (s ∘ v) 8 w)
    (padW.drop (acc.length * V) ++ (base ++ acc).flatten) (gatesW ix n W p' acc.length)
    (pcw.drop acc.length)) s

set_option linter.unusedSimpArgs false in
/-- **One gate**: the evaluator's body appends the gate's value. -/
theorem run_slpBody {ι : Type*} (hpl : Placed u v) (hP : StepSpec P V f Pre) (s : Store k)
    (hclean : ∀ i : Fin 15, 5 ≤ i.val → i ≠ 8 → s (v i) = []) (hPre : Pre (s ∘ u)) {W : ℕ}
    (hV : (s (v 3)).length = V) (hW : (s (v 4)).length = W) {ins : List (List Bool)}
    (hins : ∀ x ∈ ins, x.length = V) {one : List Bool} (hone : one.length = V) {n : ℕ}
    (hn : ins.length = n) {ix : ι → ℕ} (hix : ∀ i, ix i < n) (padW pcw : List Bool) (g : Gate ι)
    (p' : SLP ι) (acc : List (List Bool)) (hacc : ∀ x ∈ acc, x.length = V)
    (hpad : padW.length = (acc.length + 1 + p'.length) * V)
    (hpcw : pcw.length = acc.length + 1 + p'.length) (hWg : n + acc.length + 1 + p'.length ≤ W)
    (w : List Bool) :
    run (slpBody u v P) (slpSt v s V ix n W padW pcw (ins ++ [one]) (g :: p') acc w) =
      slpSt v s V ix n W padW pcw (ins ++ [one]) p'
        (acc ++ [f (SLP.wireVal (fun i => ins.getD (ix i) []) one acc g.a)
          (SLP.wireVal (fun i => ins.getD (ix i) []) one acc g.b)]) w := by
  set inp : ι → List Bool := fun i => ins.getD (ix i) []
  set t := acc.length with ht
  set r := Function.update (s ∘ v) 8 w with hrdef
  have hr : Clean15 r := fun i h1 h2 => by
    simp only [r, Function.update_of_ne h2, Function.comp]; exact hclean i h1 h2
  have hr3 : (r 3).length = V := by simp [r, Function.update_of_ne, hV]
  have hr4 : (r 4).length = W := by simp [r, Function.update_of_ne, hW]
  set L := ins ++ [one] ++ acc with hL
  have hLV : ∀ x ∈ L, x.length = V := by
    intro x hx; simp only [L, List.mem_append, List.mem_singleton] at hx
    rcases hx with (hx | rfl) | hx
    · exact hins x hx
    · exact hone
    · exact hacc x hx
  have hLlen : L.length = n + 1 + t := by simp [L, hn, t]; omega
  set pad' := padW.drop (t * V) with hpad'
  have hpadlen : pad'.length = (1 + p'.length) * V := by
    simp only [pad', List.length_drop, hpad]; rw [Nat.add_mul, Nat.add_mul, Nat.add_mul]; omega
  set st := pad' ++ L.flatten with hst
  have hpc : (pcw.drop t).length = 1 + p'.length := by simp [hpcw]; omega
  -- the two reads
  obtain ⟨hja, hva⟩ := getElem_wireIx ix ins hn hix one acc g.a
  obtain ⟨hjb, hvb⟩ := getElem_wireIx ix ins hn hix one acc g.b
  have hA : takeD V (st.drop ((pcw.drop t).length * V + V * (unaryW W (wireIx ix n t g.a)).count true))
      = SLP.wireVal inp one acc g.a := by
    rw [count_unaryW, hpc, takeD_drop_blocks pad' hpadlen L hLV _ hja, hva]
  have hB : takeD V (st.drop ((pcw.drop t).length * V + V * (unaryW W (wireIx ix n t g.b)).count true))
      = SLP.wireVal inp one acc g.b := by
    rw [count_unaryW, hpc, takeD_drop_blocks pad' hpadlen L hLV _ hjb, hvb]
  have hAl : (SLP.wireVal inp one acc g.a).length = V := by rw [← hA, length_takeD]
  have hBl : (SLP.wireVal inp one acc g.b).length = V := by rw [← hB, length_takeD]
  have hla : (unaryW W (wireIx ix n t g.a)).length = W :=
    length_unaryW (by have := wireIx_le ix hix t g.a; omega)
  have hlb : (unaryW W (wireIx ix n t g.b)).length = W :=
    length_unaryW (by have := wireIx_le ix hix t g.b; omega)
  -- run the body
  unfold slpSt slpBody
  simp only [run_seq]
  rw [run_map hpl.hv preG, extend_comp_of_inj hpl.hv, extend_extend hpl.hv]
  have hgs : gatesW ix n W (g :: p') acc.length = unaryW W (wireIx ix n t g.a) ++
      unaryW W (wireIx ix n t g.b) ++ gatesW ix n W p' (t + 1) := rfl
  rw [hgs, run_preG r hr hr3 hr4 _ _ _ _ _ hla hlb, hA, hB]
  rw [run_map_step hpl hP s hPre _ (by simp [hAl]) (by simp [hBl])]
  simp only [Function.update_self, Function.update_of_ne (show (12 : Fin 15) ≠ 13 by decide)]
  rw [run_map hpl.hv postG, extend_comp_of_inj hpl.hv, extend_extend hpl.hv,
    run_postG r hr hr3 _ _ _ _ _ _ (hP.len _ _ hAl hBl)]
  -- the new store
  have hlen' : (acc ++ [f (SLP.wireVal inp one acc g.a) (SLP.wireVal inp one acc g.b)]).length =
      t + 1 := by simp [t]
  rw [hlen']
  congr 2
  · have hle : V ≤ (padW.drop (acc.length * V)).length := by
      rw [← ht, ← hpad', hpadlen]; nlinarith
    rw [List.append_assoc, List.drop_append_of_le_length hle, List.drop_drop]
    congr 1
    · congr 1; rw [← ht]; ring
    · simp
  · rw [List.tail_drop]


theorem slpSt_v8 {ι : Type*} (hpl : Placed u v) (s : Store k) (ix : ι → ℕ) (n W : ℕ)
    (padW pcw : List Bool) (base : List (List Bool)) (p' : SLP ι) (acc : List (List Bool))
    (w : List Bool) : slpSt v s V ix n W padW pcw base p' acc w (v 8) = w := by
  simp [slpSt, hpl.hv.extend_apply, mk15]

theorem tailAt_slpSt {ι : Type*} (hpl : Placed u v) (s : Store k) (ix : ι → ℕ) (n W : ℕ)
    (padW pcw : List Bool) (base : List (List Bool)) (p' : SLP ι) (acc : List (List Bool))
    (x : Bool) (w : List Bool) :
    tailAt (v 8) (slpSt v s V ix n W padW pcw base p' acc (x :: w)) =
      slpSt v s V ix n W padW pcw base p' acc w := by
  rw [tailAt, slpSt_v8 hpl, List.tail_cons]
  unfold slpSt
  rw [← extend_update hpl.hv]
  congr 1
  funext t; fin_cases t <;> simp [mk15]

theorem length_slpRun {ι α : Type*} (inp : ι → α) (one : α) (step : α → α → α) :
    ∀ (p : SLP ι) (acc : List α), (SLP.run inp one step p acc).length = acc.length + p.length
  | [], acc => by simp [SLP.run]
  | g :: p, acc => by
    rw [SLP.run, length_slpRun inp one step p, List.length_append, List.length_cons]
    simp; omega

theorem slpRun_len {ι : Type*} (inp : ι → List Bool) (one : List Bool) {V : ℕ}
    (step : List Bool → List Bool → List Bool) (hinp : ∀ i, (inp i).length = V)
    (hone : one.length = V) (hstep : ∀ a b, a.length = V → b.length = V → (step a b).length = V) :
    ∀ (p : SLP ι) (acc : List (List Bool)), (∀ x ∈ acc, x.length = V) →
      ∀ x ∈ SLP.run inp one step p acc, x.length = V := by
  have hw : ∀ (acc : List (List Bool)), (∀ x ∈ acc, x.length = V) → ∀ w : Wire ι,
      (SLP.wireVal inp one acc w).length = V := by
    intro acc hacc w
    cases w with
    | input i => exact hinp i
    | one => exact hone
    | gate m =>
      simp only [SLP.wireVal]
      by_cases h : m < acc.length
      · rw [List.getD_eq_getElem _ _ h]; exact hacc _ (List.getElem_mem h)
      · rw [List.getD_eq_default _ _ (by omega)]; exact hone
  intro p
  induction p with
  | nil => intro acc h; exact h
  | cons g p ih =>
    intro acc hacc
    apply ih
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hacc x hx
    · rw [List.mem_singleton] at hx; rw [hx]; exact hstep _ _ (hw acc hacc _) (hw acc hacc _)

/-- **The gate loop**: one round per gate left. -/
theorem run_loop_slp {ι : Type*} (hpl : Placed u v) (hP : StepSpec P V f Pre) (s : Store k)
    (hclean : ∀ i : Fin 15, 5 ≤ i.val → i ≠ 8 → s (v i) = []) (hPre : Pre (s ∘ u)) {W : ℕ}
    (hV : (s (v 3)).length = V) (hW : (s (v 4)).length = W) {ins : List (List Bool)}
    (hins : ∀ x ∈ ins, x.length = V) {one : List Bool} (hone : one.length = V) {n : ℕ}
    (hn : ins.length = n) {ix : ι → ℕ} (hix : ∀ i, ix i < n) (padW pcw : List Bool) :
    ∀ (p' : SLP ι) (acc : List (List Bool)) (w : List Bool), (∀ x ∈ acc, x.length = V) →
      padW.length = (acc.length + p'.length) * V → pcw.length = acc.length + p'.length →
      n + acc.length + p'.length ≤ W → w.length = p'.length →
      run (loop (v 8) (slpBody u v P)) (slpSt v s V ix n W padW pcw (ins ++ [one]) p' acc w) =
        slpSt v s V ix n W padW pcw (ins ++ [one]) []
          (SLP.run (fun i => ins.getD (ix i) []) one f p' acc) [] := by
  intro p'
  induction p' with
  | nil =>
    intro acc w _ _ _ _ hw
    have hw0 : w = [] := List.eq_nil_of_length_eq_zero hw
    subst hw0
    rw [run_loop, slpSt_v8 hpl]
    rfl
  | cons g p' ih =>
    intro acc w hacc hpad hpcw hWg hw
    obtain ⟨x, w', rfl⟩ : ∃ x w', w = x :: w' := by
      cases w with
      | nil => simp at hw
      | cons x w' => exact ⟨x, w', rfl⟩
    simp only [List.length_cons] at hw hpad hpcw hWg
    have hstepl : ∀ a b : List Bool, a.length = V → b.length = V → (f a b).length = V := hP.len
    rw [run_loop, slpSt_v8 hpl, List.length_cons, Function.iterate_succ_apply,
      tailAt_slpSt hpl,
      run_slpBody hpl hP s hclean hPre hV hW hins hone hn hix padW pcw g p' acc hacc
        (by rw [hpad]; ring_nf) (by omega) (by omega) w']
    have hacc' : ∀ y ∈ acc ++ [f (SLP.wireVal (fun i => ins.getD (ix i) []) one acc g.a)
        (SLP.wireVal (fun i => ins.getD (ix i) []) one acc g.b)], y.length = V :=
      slpRun_len (fun i => ins.getD (ix i) []) one f (fun i => by
          by_cases h : ix i < ins.length
          · rw [List.getD_eq_getElem _ _ h]; exact hins _ (List.getElem_mem h)
          · exact absurd (hix i) (by omega)) hone hstepl [g] acc hacc
    have := ih _ w' hacc' (by simp only [List.length_append, List.length_singleton, hpad]; ring)
      (by simp [hpcw]; omega) (by simp; omega) (by omega)
    rw [run_loop, slpSt_v8 hpl] at this
    rw [this]
    rfl

/-- **The evaluator on tapes.** From the store `padW ++ ins ++ [one]` (`g` padding blocks), the
word of the program on `v 1` and a pad counter of `g` bits on `v 2`, the store becomes
`ins ++ [one] ++ SLP.values …` (flattened); the gate stream and the pad counter are consumed, every
other tape is restored. -/
theorem run_slpEvalP {ι : Type*} (hpl : Placed u v) (hP : StepSpec P V f Pre) (s : Store k)
    (hclean : ∀ i : Fin 15, 5 ≤ i.val → s (v i) = []) (hPre : Pre (s ∘ u)) {W : ℕ}
    (hV : (s (v 3)).length = V) (hW : (s (v 4)).length = W) {ins : List (List Bool)}
    (hins : ∀ x ∈ ins, x.length = V) {one : List Bool} (hone : one.length = V) {n : ℕ}
    (hn : ins.length = n) {ix : ι → ℕ} (hix : ∀ i, ix i < n) (p : SLP ι) (hWg : n + p.length ≤ W)
    (padW : List Bool) (hpad : padW.length = p.length * V)
    (hst : s (v 0) = padW ++ (ins ++ [one]).flatten) (hgs : s (v 1) = gatesW ix n W p 0)
    (hpc : (s (v 2)).length = p.length) :
    run (slpEvalP u v P) s = Function.update (Function.update (Function.update s (v 0)
      ((ins ++ [one] ++ SLP.values (fun i => ins.getD (ix i) []) one f p).flatten)) (v 1) [])
      (v 2) [] := by
  have hclean' : ∀ i : Fin 15, 5 ≤ i.val → i ≠ 8 → s (v i) = [] := fun i h _ => hclean i h
  have h0 : Function.update s (v 8) (s (v 2)) =
      slpSt v s V ix n W padW (s (v 2)) (ins ++ [one]) p [] (s (v 2)) := by
    unfold slpSt
    have : mk15 (Function.update (s ∘ v) 8 (s (v 2))) (padW.drop (([] : List (List Bool)).length * V)
        ++ (ins ++ [one] ++ []).flatten) (gatesW ix n W p ([] : List (List Bool)).length)
        ((s (v 2)).drop ([] : List (List Bool)).length) = Function.update (s ∘ v) 8 (s (v 2)) := by
      funext t; fin_cases t <;> simp [mk15, hst, hgs]
    rw [this, extend_update hpl.hv, extend_comp_self]
  rw [slpEvalP, forN, run_seq, run_copy, h0,
    run_loop_slp hpl hP s hclean' hPre hV hW hins hone hn hix padW (s (v 2)) p [] (s (v 2))
      (by simp) (by simp [hpad]) (by simp [hpc]) (by simpa using hWg) hpc]
  unfold slpSt
  have hlen : (SLP.run (fun i => ins.getD (ix i) []) one f p []).length = p.length := by
    rw [length_slpRun]; simp
  have e8 : Function.update (s ∘ v) 8 [] = s ∘ v := by
    funext t; by_cases h : t = 8
    · subst h; simp [hclean 8 (by decide)]
    · simp [Function.update_of_ne h]
  rw [hlen, e8, List.drop_of_length_le (by rw [hpad]), List.drop_of_length_le (by rw [hpc]),
    List.nil_append]
  simp only [mk15, extend_update hpl.hv, extend_comp_self]
  rfl



theorem noGrow_preG : preG.NoGrow := rfl
theorem noGrow_postG : postG.NoGrow := rfl
theorem wf_preG : preG.WF := wf_of_wfB (by decide)
theorem wf_postG : postG.WF := wf_of_wfB (by decide)

theorem noGrow_slpEvalP (hP : StepSpec P V f Pre) : (slpEvalP u v P).NoGrow := by
  have h1 := noGrow_preG.map (u := v)
  have h2 := hP.noGrow.map (u := u)
  have h3 := noGrow_postG.map (u := v)
  simp only [NoGrow, slpEvalP, forN, slpBody, noGrowB, Prim.noGrowB, Bool.and_eq_true] at h1 h2 h3 ⊢
  exact ⟨trivial, h1, h2, h3⟩

theorem wf_slpEvalP (hpl : Placed u v) (hP : StepSpec P V f Pre) : (slpEvalP u v P).WF := by
  have hnu : ∀ j, u j ≠ v 8 := fun j h => by have := hpl.disj 8 j h.symm; simp at this
  refine ⟨trivial, ⟨WF.map hpl.hv wf_preG, WF.map hpl.hu hP.wf, WF.map hpl.hv wf_postG⟩,
    (preserves_map hpl.hv 8 _).mpr (preserves_of_preservesB (by decide)),
    preserves_map_of_not_mem hnu _, (preserves_map hpl.hv 8 _).mpr (preserves_of_preservesB (by decide))⟩

/-- **The law of the evaluator** (`run_slpEvalP`). -/
theorem law_slpEvalP {ι : Type*} (hpl : Placed u v) (hP : StepSpec P V f Pre) (s : Store k)
    (hclean : ∀ i : Fin 15, 5 ≤ i.val → s (v i) = []) (hPre : Pre (s ∘ u)) {W : ℕ}
    (hV : (s (v 3)).length = V) (hW : (s (v 4)).length = W) {ins : List (List Bool)}
    (hins : ∀ x ∈ ins, x.length = V) {one : List Bool} (hone : one.length = V) {n : ℕ}
    (hn : ins.length = n) {ix : ι → ℕ} (hix : ∀ i, ix i < n) (p : SLP ι) (hWg : n + p.length ≤ W)
    (padW : List Bool) (hpad : padW.length = p.length * V)
    (hst : s (v 0) = padW ++ (ins ++ [one]).flatten) (hgs : s (v 1) = gatesW ix n W p 0)
    (hpc : (s (v 2)).length = p.length) :
    law (slpEvalP u v P) s = PMF.pure (Function.update (Function.update (Function.update s (v 0)
      ((ins ++ [one] ++ SLP.values (fun i => ins.getD (ix i) []) one f p).flatten)) (v 1) [])
      (v 2) []) := by
  rw [law_eq_run _ (noGrow_slpEvalP hP),
    run_slpEvalP hpl hP s hclean hPre hV hW hins hone hn hix p hWg padW hpad hst hgs hpc]

end Placed

end Prog

end SigabaNeo.Tape
