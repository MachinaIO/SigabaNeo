import PE.Impl.RingBTVW.Prog.WfLib
import SigabaNeo.Lib.Machines.GatesSLP
import SigabaNeo.Lib.Lattices.ProgAlgo.GateListLayout

/-!
# The gate stream of the predicate's own evaluator

The Ring-GSW simulation of the `W_f` block evaluates the predicate's program `predOf 10 gs` with
`slpEvalP` at the input positions `ix = (·.val)` (`n = 10`). Its gate stream is
`gatesW (·.val) 10 W (predOf 10 gs).1 0`; the input of the key component carries the gate list as
`gsW W gs` (the wire indices of `SigabaNeo.parse`: `0` the wire `1`, `1 … 10` the inputs, then the
gates). The two numberings differ: the index `g` of a wire of the gate `t` is, for the evaluator,

* `10` if `g = 0` (the wire `1`);
* `g − 1` if `1 ≤ g ≤ 10` (an input);
* `g` if `g ≥ 11` and the gate `g − 11` is already computed (`g − 11 < t`), `10` otherwise
  (`fpos t g = wireIx (·.val) 10 t (ofIdx 10 g)`, `fpos_*`).

`convP W : Prog 13` (tape `0` the stream `gsW W gs`, consumed) writes on tape `1` the gate stream
`gatesW (·.val) 10 W (predOf 10 gs).1 0`, on tape `2` a counter `replicate |gs| false`, on tape `3`
the unary position `unaryW W (|gs| + 10)` of the predicate's output wire (`run_convP`,
`wireIx_predOf_out`), every other tape blank. Each block of `W` bits is decoded by testing the bits
`0`, `10` and `t + 10` (a counter `replicate (t + 10) true` on tape `4`).
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.Prog SigabaNeo.Lattices
open scoped SigabaNeo.Tape.Prog

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

/-! ### The positions -/

/-- The evaluator's position of the wire of index `g` (gate list numbering) at the gate `t`. -/
def fpos (t g : ℕ) : ℕ := wireIx (fun i : Fin 10 => i.val) 10 t (ofIdx 10 g)

theorem fpos_zero (t : ℕ) : fpos t 0 = 10 := by simp [fpos, ofIdx, wireIx]

theorem fpos_small {t g : ℕ} (h1 : 1 ≤ g) (h2 : g ≤ 10) : fpos t g = g - 1 := by
  simp only [fpos, ofIdx]
  rw [if_neg (by omega), dif_pos (by omega)]
  rfl

theorem fpos_lt {t g : ℕ} (h1 : 11 ≤ g) (h2 : g < t + 11) : fpos t g = g := by
  simp only [fpos, ofIdx]
  rw [if_neg (by omega), dif_neg (by omega)]
  simp only [wireIx]
  rw [if_pos (by omega)]
  omega

theorem fpos_ge {t g : ℕ} (h1 : 11 ≤ g) (h2 : t + 11 ≤ g) : fpos t g = 10 := by
  simp only [fpos, ofIdx]
  rw [if_neg (by omega), dif_neg (by omega)]
  simp only [wireIx]
  rw [if_neg (by omega)]

/-- The gate stream of a gate list, one gate at a time. -/
theorem gatesW_fromGates_cons (W t : ℕ) (g : ℕ × ℕ) (r : GateList) :
    gatesW (fun i : Fin 10 => i.val) 10 W (fromGates 10 (g :: r)) t =
      unaryW W (fpos t g.1) ++ unaryW W (fpos t g.2) ++
        gatesW (fun i : Fin 10 => i.val) 10 W (fromGates 10 r) (t + 1) := rfl

/-- **The position of the predicate's output wire.** -/
theorem wireIx_predOf_out (gs : GateList) :
    wireIx (fun i : Fin 10 => i.val) 10 (predOf 10 gs).1.length (predOf 10 gs).2 = gs.length + 10 := by
  simp only [predOf, fromGates, List.length_map, wireIx]
  split_ifs with h <;> omega

/-! ### Bits of unary words -/

theorem hd_unaryW (W g : ℕ) : hd (unaryW W g) = decide (0 < g) := by
  cases g with
  | zero => cases W <;> simp [unaryW, hd, List.replicate_succ]
  | succ g => simp [unaryW, hd, List.replicate_succ]

theorem hd_drop_unaryW (W g i : ℕ) : hd ((unaryW W g).drop i) = decide (i < g) := by
  rw [unaryW, List.drop_append, List.drop_replicate, List.drop_replicate,
    List.length_replicate]
  by_cases h : i < g
  · obtain ⟨m, hm⟩ : ∃ m, g - i = m + 1 := ⟨g - i - 1, by omega⟩
    simp [hm, List.replicate_succ, hd, h]
  · rw [show g - i = 0 by omega]
    cases hW : W - g - (i - g) <;> simp [List.replicate_succ, hd, h]

theorem unaryW_tail {W g : ℕ} (h1 : 1 ≤ g) (h2 : g ≤ W) :
    (unaryW W g).tail ++ [false] = unaryW W (g - 1) := by
  obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  simp only [unaryW, List.replicate_succ, List.cons_append, List.tail_cons, List.append_assoc,
    Nat.add_sub_cancel]
  congr 1
  rw [← List.replicate_succ', show W - g' = W - (g' + 1) + 1 by omega]

theorem length_unaryW' {W g : ℕ} (h : g ≤ W) : (unaryW W g).length = W := length_unaryW h

/-! ### Small loops -/

theorem run_dropN' (n : ℕ) (i : Fin k) (s : Store k) :
    run (dropN n i) s = Function.update s i ((s i).drop n) := by
  rw [dropN, run_iter, run_tail_iter]

theorem iterate_tail (n : ℕ) (w : List Bool) : (List.tail)^[n] w = w.drop n := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, ih, List.drop_tail, Nat.add_comm]

/-- `y := drop |s z| y` (counter `c`). -/
theorem run_tlLoop {c z y : Fin k} (h1 : c ≠ y) (s : Store k) (hc : s c = []) :
    run (forN c z (tl y)) s = Function.update s y ((s y).drop (s z).length) := by
  have h := run_forN c z (tl y) (fun w => Function.update s y w) List.tail (fun w v => by
      funext j
      simp only [run_tail, Function.update_apply]
      by_cases hj1 : j = y <;> by_cases hj2 : j = c <;> simp_all) (s y) s (by
      funext j
      simp only [Function.update_apply]
      by_cases hj1 : j = y <;> by_cases hj2 : j = c <;> simp_all)
  rw [h, iterate_tail]
  funext j
  simp only [Function.update_apply]
  by_cases hj1 : j = y <;> by_cases hj2 : j = c <;> simp_all

/-! ### The program

Tapes: `0` the stream, `1` the gate stream, `2` the gate counter, `3` the output position, `4`
the counter `replicate (t + 10) true`, `5` the word `unaryW W 10`, `6` the block, `7` a copy,
`8` `9` loop counters, `10` `11` `12` scratch of `appP`. -/

/-- Append tape `j` to the gate stream. -/
abbrev apG (j : Fin 13) : Prog 13 := appP 1 j 10 11 12

/-- **Decode one block** (tape `6`) at the gate `t` (tape `4`). -/
def blkP : Prog 13 :=
  ifBit 6
    (cp 7 6 ⨾ dropN 10 7 ⨾
      ifBit 7 (cp 7 6 ⨾ forN 9 4 (tl 7) ⨾ ifBit 7 (apG 5) (apG 6))
        (cp 7 6 ⨾ tl 7 ⨾ prim (.snoc 7 false) ⨾ apG 7))
    (apG 5) ⨾ clr 7 ⨾ clr 6

/-- Read a block of `W` bits. -/
def readP (W : ℕ) : Prog 13 := appendP 6 0 W

/-- One gate. -/
def gateP (W : ℕ) : Prog 13 :=
  readP W ⨾ blkP ⨾ readP W ⨾ blkP ⨾ prim (.snoc 4 true) ⨾ prim (.snoc 2 false)

/-- **The conversion.** -/
def convP (W : ℕ) : Prog 13 :=
  SigabaNeo.Tape.Prog.putW 4 (List.replicate 10 true) ⨾ SigabaNeo.Tape.Prog.putW 5 (unaryW W 10) ⨾
    forN 8 0 (ifBlank 0 (nop 0) (gateP W)) ⨾ SigabaNeo.Tape.Prog.putW 7 (List.replicate W false) ⨾ forN 9 4 (tl 7) ⨾
    cp 3 4 ⨾ appP 3 7 10 11 12 ⨾ clr 7 ⨾ clr 4 ⨾ clr 5

/-! ### One block -/

theorem run_apG {j : Fin 13} (hj : j ≠ 10 ∧ j ≠ 11 ∧ j ≠ 12 ∧ j ≠ 1) (s : Store 13)
    (h10 : s 10 = []) (h11 : s 11 = []) (h12 : s 12 = []) :
    run (apG j) s = Function.update s 1 (s 1 ++ s j) :=
  run_appP (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hj.1 hj.2.2.2
    s h10 h11 h12

theorem run_blkP {W t g : ℕ} (hg : g ≤ W) (s : Store 13) (h4 : s 4 = List.replicate (t + 10) true)
    (h5 : s 5 = unaryW W 10) (h6 : s 6 = unaryW W g) (h7 : s 7 = []) (h9 : s 9 = [])
    (h10 : s 10 = []) (h11 : s 11 = []) (h12 : s 12 = []) :
    run blkP s = Function.update (Function.update s 1 (s 1 ++ unaryW W (fpos t g))) 6 [] := by
  have hb0 := hd_unaryW W g
  have hb10 := hd_drop_unaryW W g 10
  have hbt := hd_drop_unaryW W g (t + 10)
  simp only [blkP, run_seq, run_ifBit, run_copy, run_dropN', run_clear]
  by_cases g0 : 0 < g
  · rw [if_pos (by simpa [Function.update_apply, g0, h6] using hb0)]
    simp only [Function.update_self]
    by_cases g10 : 10 < g
    · rw [if_pos (by simpa [g10, h6] using hb10)]
      rw [run_tlLoop (by decide) _ (by simp [Function.update_apply, h9])]
      simp only [Function.update_self, Function.update_apply, h6, h4]
      simp only [show ((9 : Fin 13) = 7) = False from by decide, show ((4 : Fin 13) = 7) = False from
        by decide, if_false, h4, List.length_replicate]
      by_cases gt : t + 10 < g
      · rw [if_pos (by simpa [gt, h6] using hbt), run_apG (by decide) _ (by simp [Function.update_apply, h10])
          (by simp [Function.update_apply, h11]) (by simp [Function.update_apply, h12]),
          fpos_ge (by omega) (by omega)]
        funext j
        simp only [Function.update_apply]
        fin_cases j <;> simp [h5, h7]
      · rw [if_neg (by simpa [gt, h6] using hbt), run_apG (by decide) _ (by simp [Function.update_apply, h10])
          (by simp [Function.update_apply, h11]) (by simp [Function.update_apply, h12]),
          fpos_lt (by omega) (by omega)]
        funext j
        simp only [Function.update_apply]
        fin_cases j <;> simp [h6, h7]
    · rw [if_neg (by simpa [g10, h6] using hb10)]
      simp only [run_seq, run_copy, run_tail, run_prim, Prim.apply]
      rw [run_apG (by decide) _ (by simp [Function.update_apply, h10])
          (by simp [Function.update_apply, h11]) (by simp [Function.update_apply, h12]),
          fpos_small (by omega) (by omega)]
      funext j
      simp only [Function.update_apply]
      fin_cases j <;> simp [h7, h6, unaryW_tail (show 1 ≤ g by omega) hg]
  · rw [if_neg (by simpa [Function.update_apply, g0, h6] using hb0),
      run_apG (by decide) _ h10 h11 h12, show g = 0 by omega, fpos_zero]
    funext j
    simp only [Function.update_apply]
    fin_cases j <;> simp [h5, h7]

/-! ### One gate -/

theorem run_readP {W : ℕ} (s : Store 13) (h6 : s 6 = []) :
    run (readP W) s = Function.update (Function.update s 6 ((s 0).take W)) 0 ((s 0).drop W) := by
  rw [readP, run_appendP (by decide), h6, List.nil_append]

/-- The store of the gate loop: the rest of the stream, the gate stream so far, `t`. -/
def gS (W : ℕ) (rem : GateList) (t : ℕ) (acc : List Bool) : Store 13 :=
  ![gsW W rem, acc, List.replicate t false, [], List.replicate (t + 10) true, unaryW W 10, [], [], [],
    [], [], [], []]

/-- The abstract round of the gate loop. -/
def gStep (W : ℕ) : GateList × ℕ × List Bool → GateList × ℕ × List Bool
  | ([], t, acc) => ([], t, acc)
  | (g :: r, t, acc) => (r, t + 1, acc ++ (unaryW W (fpos t g.1) ++ unaryW W (fpos t g.2)))

/-- Every index is at most `W`. -/
def BndG (W : ℕ) (gs : GateList) : Prop := ∀ g ∈ gs, g.1 ≤ W ∧ g.2 ≤ W

theorem run_gateP {W : ℕ} (g : ℕ × ℕ) (r : GateList) (t : ℕ) (acc : List Bool) (hg : g.1 ≤ W ∧ g.2 ≤ W)
    (w : List Bool) :
    run (gateP W) (Function.update (gS W (g :: r) t acc) 8 w) =
      Function.update (gS W r (t + 1) (acc ++ (unaryW W (fpos t g.1) ++ unaryW W (fpos t g.2)))) 8 w := by
  have e0 : gsW W (g :: r) = unaryW W g.1 ++ (unaryW W g.2 ++ gsW W r) := by
    rw [gsW_cons, List.append_assoc]
  have l1 := length_unaryW hg.1
  have l2 := length_unaryW hg.2
  rw [gateP, run_seq, run_readP _ (by simp [gS])]
  rw [run_seq, run_blkP (t := t) hg.1 _ (by simp [gS, Function.update_apply]) (by simp [gS, Function.update_apply])
    (by simp [gS, Function.update_apply, e0, List.take_left' l1]) (by simp [gS, Function.update_apply])
    (by simp [gS, Function.update_apply]) (by simp [gS, Function.update_apply])
    (by simp [gS, Function.update_apply]) (by simp [gS, Function.update_apply])]
  rw [run_seq, run_readP _ (by simp [Function.update_apply])]
  rw [run_seq, run_blkP (t := t) hg.2 _ (by simp [gS, Function.update_apply]) (by simp [gS, Function.update_apply])
    (by simp [gS, Function.update_apply, e0, List.drop_left' l1, List.take_left' l2])
    (by simp [gS, Function.update_apply])
    (by simp [gS, Function.update_apply]) (by simp [gS, Function.update_apply])
    (by simp [gS, Function.update_apply]) (by simp [gS, Function.update_apply])]
  simp only [run_seq, run_prim, Prim.apply]
  funext j
  simp only [Function.update_apply]
  fin_cases j <;> simp [gS, e0, List.drop_left' l1, List.drop_left' l2, List.replicate_succ',
    List.append_assoc]

theorem run_bodyC {W : ℕ} (hW : 0 < W) (a : GateList × ℕ × List Bool) (ha : BndG W a.1)
    (w : List Bool) :
    run (ifBlank 0 (nop 0) (gateP W)) (Function.update (gS W a.1 a.2.1 a.2.2) 8 w) =
      Function.update (gS W (gStep W a).1 (gStep W a).2.1 (gStep W a).2.2) 8 w := by
  obtain ⟨rem, t, acc⟩ := a
  rw [run_ifBlank]
  cases rem with
  | nil => simp [gS, gsW_nil, gStep, Function.update_apply]
  | cons g r =>
    have hg := ha g (by simp)
    have hne : gsW W (g :: r) ≠ [] := by
      intro h
      have := congrArg List.length h
      rw [gsW_cons, List.length_append, List.length_append, length_unaryW hg.1] at this
      simp at this; omega
    rw [if_neg (by simpa [gS, Function.update_apply] using hne)]
    exact run_gateP g r t acc hg w

theorem gStep_iter (W : ℕ) : ∀ (rem : GateList) (n t : ℕ) (acc : List Bool), rem.length ≤ n →
    (gStep W)^[n] (rem, t, acc) =
      ([], t + rem.length, acc ++ gatesW (fun i : Fin 10 => i.val) 10 W (fromGates 10 rem) t)
  | [], n, t, acc, _ => by
    have : ∀ m, (gStep W)^[m] ([], t, acc) = ([], t, acc) := by
      intro m; induction m with
      | zero => rfl
      | succ m ih => rw [Function.iterate_succ_apply]; exact ih
    rw [this]; simp [fromGates, gatesW]
  | g :: r, n + 1, t, acc, h => by
    rw [Function.iterate_succ_apply]
    show (gStep W)^[n] (r, t + 1, acc ++ (unaryW W (fpos t g.1) ++ unaryW W (fpos t g.2))) = _
    rw [gStep_iter W r n (t + 1) _ (by simpa using h), gatesW_fromGates_cons]
    simp only [List.length_cons, List.append_assoc]
    rw [show t + 1 + r.length = t + (r.length + 1) by omega]
  | _ :: _, 0, _, _, h => absurd h (by simp)

theorem bnd_gStep {W : ℕ} (a : GateList × ℕ × List Bool) (ha : BndG W a.1) : BndG W (gStep W a).1 := by
  obtain ⟨rem, t, acc⟩ := a
  cases rem with
  | nil => exact ha
  | cons g r => exact fun x hx => ha x (List.mem_cons_of_mem _ hx)

/-- **The conversion of the gate list.** -/
theorem run_convP {W : ℕ} (hW : 0 < W) (gs : GateList) (hb : BndG W gs) (s : Store 13)
    (hs : s = fun i => if i = 0 then gsW W gs else []) :
    run (convP W) s = ![[], gatesW (fun i : Fin 10 => i.val) 10 W (predOf 10 gs).1 0,
      List.replicate gs.length false, unaryW W (gs.length + 10), [], [], [], [], [], [], [], [], []] := by
  subst hs
  have hloop := run_forN_inv 8 0 (ifBlank 0 (nop 0) (gateP W))
    (fun a => gS W a.1 a.2.1 a.2.2) (gStep W) (fun a => BndG W a.1)
    (fun a w ha => run_bodyC hW a ha w) (fun a ha => bnd_gStep a ha) (gs, 0, []) hb
  simp only [convP, run_seq, run_putW]
  rw [hloop _ (by funext j; simp only [Function.update_apply]; fin_cases j <;> simp [gS])]
  have hlen : gs.length ≤ (Function.update (Function.update (fun i : Fin 13 =>
      if i = 0 then gsW W gs else []) 4 (List.replicate 10 true)) 5 (unaryW W 10) 0).length := by
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), if_pos rfl,
      length_gsW hb]
    nlinarith
  rw [gStep_iter W gs _ 0 [] hlen]
  rw [run_tlLoop (by decide) _ (by simp [Function.update_apply, gS])]
  rw [run_copy, run_appP (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) _ (by simp [Function.update_apply, gS])
    (by simp [Function.update_apply, gS]) (by simp [Function.update_apply, gS])]
  simp only [run_clear]
  funext j
  simp only [Function.update_apply]
  fin_cases j <;> simp [gS, gsW_nil, predOf, unaryW, List.drop_replicate]


theorem coinFree_dropN (n : ℕ) {k : ℕ} (i : Fin k) : (dropN n i).CoinFree :=
  coinFree_iter i (prim (.tail i)) rfl n

theorem wf_dropN (n : ℕ) {k : ℕ} (i : Fin k) : (dropN n i).WF := wf_iter i (prim (.tail i)) trivial n

theorem coinFree_blkP : blkP.CoinFree := rfl
theorem wf_blkP : blkP.WF := wf_of_wfB (by decide)
theorem pres8_blkP : blkP.Preserves 8 := preserves_of_preservesB (by decide)

theorem coinFree_gateP (W : ℕ) : (gateP W).CoinFree := by
  have h1 : (readP W).coinFreeB = true := coinFree_appendP _ _ _
  have h2 : blkP.coinFreeB = true := coinFree_blkP
  simp [CoinFree, gateP, coinFreeB, h1, h2]

theorem wf_gateP (W : ℕ) : (gateP W).WF :=
  ⟨wf_appendP _ _ _, wf_blkP, wf_appendP _ _ _, wf_blkP, trivial, trivial⟩

theorem pres8_gateP (W : ℕ) : (gateP W).Preserves 8 :=
  ⟨preserves_appendP (by decide) (by decide) _, pres8_blkP, preserves_appendP (by decide) (by decide) _,
    pres8_blkP, by simp [Preserves, Prim.writes], by simp [Preserves, Prim.writes]⟩

theorem coinFree_convP (W : ℕ) : (convP W).CoinFree := by
  have h1 := coinFree_gateP W
  have p1 := SigabaNeo.Tape.Prog.coinFree_putW (4 : Fin 13) (List.replicate 10 true)
  have p2 := SigabaNeo.Tape.Prog.coinFree_putW (5 : Fin 13) (unaryW W 10)
  have p3 := SigabaNeo.Tape.Prog.coinFree_putW (7 : Fin 13) (List.replicate W false)
  simp only [CoinFree] at h1 p1 p2 p3
  simp only [CoinFree, convP, forN, coinFreeB, h1, p1, p2, p3, Bool.and_eq_true]
  and_intros
  all_goals trivial

theorem wf_convP (W : ℕ) : (convP W).WF :=
  ⟨SigabaNeo.Tape.Prog.wf_putW _ _, SigabaNeo.Tape.Prog.wf_putW _ _,
    ⟨trivial, ⟨trivial, wf_gateP W⟩, ⟨by simp [nop, Preserves, Prim.writes], pres8_gateP W⟩⟩,
    SigabaNeo.Tape.Prog.wf_putW _ _, ⟨trivial, trivial, by simp [Preserves, Prim.writes]⟩,
    trivial, wf_appP (by decide) (by decide) (by decide), trivial, trivial, trivial⟩

end AdvancedEncryption.RingBTVW.Prog
