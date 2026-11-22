import SigabaNeo.Lib.Machines.Inline.LinDefs

/-!
# Inlining an oracle handler with a short preparation: the preparation

The preparation of `Inline.machineLin` reaches, from the initial configuration, the simulation of
the initial configuration of the oracle machine with `T` steps on the clock and a blank state tape
(`lawLin_prep`), within `4 T + 4 h + 4` steps, `h` the number of digits of `T`.

The counting loop decrements the counter `T` times; a decrement that borrows across `z` digits takes
`2 z + 2` steps. The number of zero digits pays for the borrows (`loop`): the loop takes at most
`4 n + 2 (number of zero digits) + 2` steps from the value `n`.
-/

namespace SigabaNeo.Inline

open Cslib Turing MultiTapeMachine

variable {kA ops m : ℕ} {x : List Bool}

/-! ### One step of a channel-free machine on named configurations -/

theorem lawM_det {S : Type} (Mc : MultiTapePTM (nTapes kA ops m) Bool S (Fin 0)) (N : ℕ) (q : S)
    (ip : Fin (x.length + 2)) (F : Tape kA ops m → ℤ → Option Bool) (P : Tape kA ops m → ℤ)
    (out : List Bool) (d : SignType) (W : Tape kA ops m → Option (Option Bool) × SignType)
    (o : Option Bool) (q' : Option S)
    (htr : ∀ bit, Mc.tr q (mkR (some q) ip F P out).tapes.inputSymbol
      (fun i => F (kind i) (P (kind i))) (fun e => e.elim0) bit = stepR (mkAct d W o q')) :
    lawM Mc (N + 1) (mkR (some q) ip F P out) =
      lawM Mc N (mkR q' (moveInputPos ip d) (fun t => wr (F t) (P t) (W t).1)
        (fun t => P t + (W t).2) (out ++ o.toList)) := by
  unfold lawM
  rw [law_succ_det _ _ N _ () rfl (action := mkAct d W o q') (symbol := fun _ => none)
    (move := fun _ => 0)]
  · rw [step_mkR]
  · intro bit
    have hans : (mkR (some q) ip F P out).answerSymbols = fun e => e.elim0 :=
      funext fun e => e.elim0
    rw [hans]
    exact htr bit

/-! ### The tapes of the preparation -/

/-- The tapes: the tracks hold the digits `l`, the clock `c` cells. -/
def lF (l : List ℕ) (c : ℕ) : Tape kA ops m → ℤ → Option Bool
  | .work i => tapeOfList (l.map fun e => e.testBit i)
  | .st => tapeOfList (l.map fun e => e.testBit kA)
  | .clock => tapeOfList (List.replicate c true)
  | _ => fun _ => none

/-- The heads: the track heads at `p`, the clock head at `pc`. -/
def lP (p pc : ℤ) : Tape kA ops m → ℤ
  | .work _ => p
  | .st => p
  | .clock => pc
  | _ => 0

theorem tW_pos (b : Option (Option ℕ)) (d : SignType) (clk : Option (Option Bool) × SignType)
    (p pc : ℤ) :
    (fun t => lP (kA := kA) (ops := ops) (m := m) p pc t + ((tW b d clk t).2 : ℤ)) =
      lP (p + d) (pc + clk.2) := by
  funext t
  rcases t with i | o | o | _ | _ | j <;> simp [lP, tW]

theorem tW_none (l : List ℕ) (c : ℕ) (p pc : ℤ) (d e : SignType) :
    (fun t => wr (lF (kA := kA) (ops := ops) (m := m) l c t) (lP p pc t)
      (tW none d (none, e) t).1) = lF l c := by
  funext t
  rcases t with i | o | o | _ | _ | j <;> simp [lF, tW]

theorem tapeOfList_set' {α : Type} (w : List α) {i : ℕ} (hi : i < w.length) (a : α) :
    tapeOfList (w.set i a) = Function.update (tapeOfList w) (i : ℤ) (some a) := by
  funext z
  rcases z with z | z
  · by_cases h : z = i
    · subst h; simp [hi]
    · rw [Function.update_of_ne (by simpa using h)]
      simp [Ne.symm h]
  · rfl

theorem replicate_succ_tape (c : ℕ) :
    Function.update (tapeOfList (List.replicate c true)) (c : ℤ) (some true) =
      tapeOfList (List.replicate (c + 1) true) := by
  rw [List.replicate_succ', tapeOfList_append_single, List.length_replicate]

theorem tW_append (l : List ℕ) (c : ℕ) (pc : ℤ) (e : ℕ) (d s : SignType) :
    (fun t => wr (lF (kA := kA) (ops := ops) (m := m) l c t) (lP l.length pc t)
      (tW (some (some e)) d (none, s) t).1) = lF (l ++ [e]) c := by
  funext t
  rcases t with i | o | o | _ | _ | j <;>
    simp [lF, tW, lP, wr, List.map_append, tapeOfList_append_single]

theorem tW_set (l : List ℕ) (c : ℕ) (j : ℕ) (hj : j < l.length) (pc : ℤ) (e : ℕ) (d s : SignType) :
    (fun t => wr (lF (kA := kA) (ops := ops) (m := m) l c t) (lP j pc t)
      (tW (some (some e)) d (none, s) t).1) = lF (l.set j e) c := by
  funext t
  rcases t with i | o | o | _ | _ | j' <;>
    simp [lF, tW, lP, wr, List.map_set, tapeOfList_set' _ (by simpa using hj : j < (l.map _).length)]

theorem tW_set_clock (l : List ℕ) (c : ℕ) (j : ℕ) (hj : j < l.length) (e : ℕ) (d s : SignType) :
    (fun t => wr (lF (kA := kA) (ops := ops) (m := m) l c t) (lP j c t)
      (tW (some (some e)) d (some (some true), s) t).1) = lF (l.set j e) (c + 1) := by
  funext t
  rcases t with i | o | o | _ | _ | j' <;>
    simp [lF, tW, lP, wr, List.map_set, tapeOfList_set' _ (by simpa using hj : j < (l.map _).length),
      replicate_succ_tape]

theorem tapeOfList_erase_last {α : Type} (v : List α) (b : α) :
    Function.update (tapeOfList (v ++ [b])) (v.length : ℤ) none = tapeOfList v := by
  funext z
  by_cases hz : z = (v.length : ℤ)
  · subst hz; simp
  · rw [Function.update_of_ne hz]
    rcases z with z | z
    · have : z ≠ v.length := fun h => hz (by simp [h])
      show (v ++ [b])[z]? = v[z]?
      rw [List.getElem?_append]
      split_ifs with h1
      · rfl
      · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
    · rfl

theorem tW_erase (u : List ℕ) (e c : ℕ) (pc : ℤ) (d s : SignType) :
    (fun t => wr (lF (kA := kA) (ops := ops) (m := m) (u ++ [e]) c t) (lP u.length pc t)
      (tW (some none) d (none, s) t).1) = lF u c := by
  funext t
  rcases t with i | o | o | _ | _ | j <;> simp only [lF, tW, lP, wr, Option.map_some,
    Option.map_none, List.map_append, List.map_cons, List.map_nil] <;>
    first | rfl | (rw [show (u.length : ℤ) = ((u.map _).length : ℤ) by simp]; exact tapeOfList_erase_last _ _)

/-! ### Reading the tracks -/

theorem lF_st_none (l : List ℕ) (c : ℕ) (p : ℤ) :
    lF (kA := kA) (ops := ops) (m := m) l c .st p = none ↔ p < 0 ∨ (l.length : ℤ) ≤ p := by
  simp [lF, tapeOfList_eq_none_iff]

theorem lF_trk (l : List ℕ) (c : ℕ) (j : ℕ) (hj : j < l.length) (pc : ℤ) (i : Fin (kA + 1)) :
    lF (kA := kA) (ops := ops) (m := m) l c (trk i) (lP (kA := kA) (ops := ops) (m := m) j pc (trk i)) = some (l[j].testBit i) := by
  unfold trk
  split_ifs with h
  · simp [lF, lP, hj]
  · have hi : (i : ℕ) = kA := by omega
    simp [lF, lP, hj, hi]

theorem digit_sum (r d : ℕ) (hd : d < 2 ^ r) :
    ∑ i : Fin r, (if d.testBit i then 1 else 0) * 2 ^ (i : ℕ) = d := by
  induction r generalizing d with
  | zero => simp at hd; simp [hd]
  | succ r ih =>
    rw [Fin.sum_univ_succ]
    have h2 : d / 2 < 2 ^ r := by rw [pow_succ] at hd; omega
    have e1 : ∀ i : Fin r, (if d.testBit ((Fin.succ i : Fin (r + 1)) : ℕ) then 1 else 0) *
        2 ^ ((Fin.succ i : Fin (r + 1)) : ℕ) =
        2 * ((if (d / 2).testBit i then 1 else 0) * 2 ^ (i : ℕ)) := by
      intro i
      rw [Fin.val_succ, Nat.testBit_succ, pow_succ]
      ring
    rw [Finset.sum_congr rfl (fun i _ => e1 i), ← Finset.mul_sum, ih (d / 2) h2]
    change (if d.testBit 0 = true then 1 else 0) * 2 ^ 0 + 2 * (d / 2) = d
    rw [Nat.testBit_zero]
    by_cases h : d % 2 = 1
    · simp [h]; omega
    · simp [h]; omega

theorem readDigit_lF (l : List ℕ) (c : ℕ) (j : ℕ) (hj : j < l.length) (pc : ℤ)
    (hB : l[j] < baseB kA) :
    readDigit (fun i => lF (kA := kA) (ops := ops) (m := m) l c (kind i) (lP j pc (kind i))) =
      l[j] := by
  unfold readDigit
  simp only [kind_idx, lF_trk l c j hj pc, Option.some.injEq]
  exact digit_sum (kA + 1) _ hB

/-! ### Steps of the preparation -/

section Steps

variable {SA : Type} (H : Fin ops → Routine (m + 3)) (M : MultiTapePTM kA Bool SA (Fin ops))
  (T : ℕ)

/-- A configuration of the preparation: state `q`, the digits `l` on the tracks with their heads at
`p`, the clock of `c` cells with its head at its end. -/
abbrev lCfg (q : LState SA H (clockDigits kA T).length) (l : List ℕ) (c : ℕ) (p : ℤ) :
    Config (nTapes kA ops m) Bool (LState SA H (clockDigits kA T).length) (Fin 0) x :=
  mkR (some q) 1 (lF l c) (lP p c) []

theorem tr_lSt (ph : LStep) inp work ans bit :
    (machineLin H M T).tr (lSt H (clockDigits kA T) ph) inp work ans bit =
      stepR (lAct H M (clockDigits kA T) ph work) := rfl

theorem tr_wSt (j : Fin ((clockDigits kA T).length + 1)) inp work ans bit :
    (machineLin H M T).tr (wSt H (clockDigits kA T) j) inp work ans bit =
      stepR (wAct H (clockDigits kA T) j) := rfl

/-- One step of the preparation acting on the tracks and the clock. -/
theorem lawM_tW (N : ℕ) (q : LState SA H (clockDigits kA T).length) (l : List ℕ) (c : ℕ) (p : ℤ)
    (b : Option (Option ℕ)) (d : SignType) (clk : Option (Option Bool) × SignType)
    (q' : Option (LState SA H (clockDigits kA T).length))
    (h : ∀ inp ans bit, (machineLin H M T).tr q inp
      (fun i => lF (kA := kA) (ops := ops) (m := m) l c (kind i) (lP p c (kind i))) ans bit =
        stepR (mkAct 0 (tW b d clk) none q')) :
    lawM (machineLin H M T) (N + 1) (lCfg (x := x) H T q l c p) =
      lawM (machineLin H M T) N (mkR q' 1 (fun t => wr (lF l c t) (lP p c t) (tW b d clk t).1)
        (lP (p + d) (c + clk.2)) []) := by
  rw [lawM_det (machineLin H M T) N q 1 _ _ [] 0 (tW b d clk) none q' (fun bit => h _ _ bit)]
  rw [tW_pos]
  simp

theorem work_st (l : List ℕ) (c : ℕ) (p : ℤ) :
    (fun i => lF (kA := kA) (ops := ops) (m := m) l c (kind i) (lP p c (kind i)))
      (Tape.st (kA := kA) (ops := ops) (m := m)).idx = lF (kA := kA) (ops := ops) (m := m) l c .st p := by
  simp [lP]

/-- **Back to the start** of the counter, then onto its digit `0`. -/
theorem lawM_back (l : List ℕ) (c : ℕ) (N : ℕ) :
    ∀ j ≤ l.length, lawM (machineLin H M T) (N + j + 1)
      (lCfg (x := x) H T (lSt H _ .back) l c ((j : ℤ) - 1)) =
      lawM (machineLin H M T) N (lCfg H T (lSt H _ .dec) l c 0) := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [Nat.add_zero, lawM_tW H M T N _ l c _ none 1 (none, 0) (some (lSt H _ .dec)) (by
      intro inp ans bit
      rw [tr_lSt]
      simp only [lAct, kind_idx, lP]
      rw [ite_eq_left (by rw [lF_st_none]; left; simp)]), tW_none]
    simp
  | succ j ih =>
    intro hj
    rw [show N + (j + 1) + 1 = (N + j + 1) + 1 by omega,
      lawM_tW H M T _ _ l c _ none (-1) (none, 0) (some (lSt H _ .back)) (by
      intro inp ans bit
      rw [tr_lSt]
      simp only [lAct, kind_idx, lP]
      rw [ite_eq_right (by rw [lF_st_none]; push_cast; omega)]), tW_none]
    rw [← ih (by omega)]
    congr 2
    simp only [SignType.coe_neg, SignType.coe_one, SignType.coe_zero, add_zero]
    push_cast; ring_nf

theorem set_replicate_append {α : Type} (a b y : α) (r : List α) (pre : ℕ) :
    (List.replicate pre a ++ b :: r).set pre y = List.replicate pre a ++ y :: r := by
  induction pre with
  | zero => simp
  | succ pre ih => simp [List.replicate_succ, ih]

theorem getElem_replicate_append {α : Type} (a b : α) (r : List α) (pre : ℕ) :
    (List.replicate pre a ++ b :: r)[pre]'(by simp) = b := by
  simp [List.getElem_append_right]

/-- **The borrow** across zero digits. -/
theorem lawM_decScan (rest : List ℕ) (c N : ℕ) :
    ∀ z pre, lawM (machineLin H M T) (N + z)
      (lCfg (x := x) H T (lSt H _ .dec) (List.replicate pre (baseB kA - 1) ++
        List.replicate z 0 ++ rest) c pre) =
      lawM (machineLin H M T) N (lCfg H T (lSt H _ .dec)
        (List.replicate (pre + z) (baseB kA - 1) ++ rest) c (pre + z)) := by
  intro z
  induction z with
  | zero => intro pre; simp
  | succ z ih =>
    intro pre
    set l := List.replicate pre (baseB kA - 1) ++ 0 :: (List.replicate z 0 ++ rest) with hl
    have hl' : List.replicate pre (baseB kA - 1) ++ List.replicate (z + 1) 0 ++ rest = l := by
      simp [hl, List.replicate_succ]
    have hlen : pre < l.length := by simp [hl]
    have hget : l[pre] = 0 := getElem_replicate_append _ _ _ _
    rw [hl', show N + (z + 1) = (N + z) + 1 by omega,
      lawM_tW H M T _ _ l c _ (some (some (baseB kA - 1))) 1 (none, 0) (some (lSt H _ .dec)) (by
        intro inp ans bit
        rw [tr_lSt]
        simp only [lAct]
        rw [ite_eq_right (by simp only [kind_idx, lP]; rw [lF_st_none]; push_cast; omega),
          ite_eq_left (by rw [readDigit_lF l c pre hlen _ (by rw [hget]; positivity), hget])]),
      tW_set l c pre hlen]
    have := ih (pre + 1)
    rw [show List.replicate (pre + 1) (baseB kA - 1) ++ List.replicate z 0 ++ rest =
      l.set pre (baseB kA - 1) by
        rw [hl, set_replicate_append, List.replicate_succ']; simp] at this
    rw [show pre + (z + 1) = pre + 1 + z by omega]
    convert this using 3
    · simp only [SignType.coe_one, SignType.coe_zero, add_zero]; push_cast; ring
    · push_cast; ring

/-- **A decrement** on a nonzero digit: the clock grows by one cell, and the heads go back. -/
theorem lawM_decHit (pre d : ℕ) (rest : List ℕ) (hd : d + 1 < baseB kA) (c N : ℕ) :
    lawM (machineLin H M T) (N + 1)
      (lCfg (x := x) H T (lSt H _ .dec) (List.replicate pre (baseB kA - 1) ++ (d + 1) :: rest) c
        pre) =
      lawM (machineLin H M T) N (lCfg H T (lSt H _ .back)
        (List.replicate pre (baseB kA - 1) ++ d :: rest) (c + 1) ((pre : ℤ) - 1)) := by
  set l := List.replicate pre (baseB kA - 1) ++ (d + 1) :: rest with hl
  have hlen : pre < l.length := by simp [hl]
  have hget : l[pre] = d + 1 := getElem_replicate_append _ _ _ _
  rw [lawM_tW H M T _ _ l c _ (some (some d)) (-1) (some (some true), 1)
      (some (lSt H _ .back)) (by
        intro inp ans bit
        rw [tr_lSt]
        simp only [lAct]
        rw [ite_eq_right (by simp only [kind_idx, lP]; rw [lF_st_none]; push_cast; omega),
          ite_eq_right (by rw [readDigit_lF l c pre hlen _ (by rw [hget]; exact hd), hget]; omega),
          readDigit_lF l c pre hlen _ (by rw [hget]; exact hd), hget, Nat.add_sub_cancel]),
    tW_set_clock l c pre hlen, hl, set_replicate_append]
  congr 3 <;> simp only [SignType.coe_neg, SignType.coe_one, SignType.coe_zero, add_zero] <;>
    push_cast <;> ring

/-- The borrow runs past the last digit. -/
theorem lawM_decEnd (l : List ℕ) (c N : ℕ) :
    lawM (machineLin H M T) (N + 1) (lCfg (x := x) H T (lSt H _ .dec) l c l.length) =
      lawM (machineLin H M T) N (lCfg H T (lSt H _ .erase) l c ((l.length : ℤ) - 1)) := by
  rw [lawM_tW H M T _ _ l c _ none (-1) (none, 0) (some (lSt H _ .erase)) (by
        intro inp ans bit
        rw [tr_lSt]
        simp only [lAct]
        rw [ite_eq_left (by simp only [kind_idx, lP]; rw [lF_st_none]; right; rfl)]), tW_none]
  congr 3 <;> simp only [SignType.coe_neg, SignType.coe_one, SignType.coe_zero, add_zero] <;>
    push_cast <;> ring

/-- The configuration after the preparation: the clock of `c` cells with its head on its last cell,
the start of the simulation. -/
abbrev finCfg (c : ℕ) :
    Config (nTapes kA ops m) Bool (LState SA H (clockDigits kA T).length) (Fin 0) x :=
  mkR (some (.inr (ctl0 H M))) 1 (lF [] c) (lP 0 ((c : ℤ) - 1)) []

/-- **Erase the counter** leftwards, then start the simulation. -/
theorem lawM_erase (c N : ℕ) : ∀ n (u : List ℕ), u.length = n →
    lawM (machineLin H M T) (N + n + 1)
      (lCfg (x := x) H T (lSt H _ .erase) u c ((n : ℤ) - 1)) =
      lawM (machineLin H M T) N (finCfg H M T c) := by
  intro n
  induction n with
  | zero =>
    intro u hu
    obtain rfl : u = [] := List.eq_nil_of_length_eq_zero hu
    rw [Nat.add_zero, lawM_tW H M T _ _ [] c _ none 1 (none, -1) (some (.inr (ctl0 H M))) (by
        intro inp ans bit
        rw [tr_lSt]
        simp only [lAct]
        rw [ite_eq_left (by simp only [kind_idx, lP]; rw [lF_st_none]; left; simp)]), tW_none]
    congr 3 <;> simp only [SignType.coe_neg, SignType.coe_one, SignType.coe_zero, add_zero] <;>
      push_cast <;> ring
  | succ n ih =>
    intro u hu
    have hne : u ≠ [] := by rintro rfl; simp at hu
    have hu' : u = u.dropLast ++ [u.getLast hne] := (List.dropLast_append_getLast hne).symm
    have hlen : u.dropLast.length = n := by simp [hu]
    rw [show N + (n + 1) + 1 = (N + n + 1) + 1 by omega, hu',
      lawM_tW H M T _ _ _ c _ (some none) (-1) (none, 0) (some (lSt H _ .erase)) (by
        intro inp ans bit
        rw [tr_lSt]
        simp only [lAct]
        rw [ite_eq_right (by simp only [kind_idx, lP]; rw [lF_st_none]; simp; omega)]),
      show ((n + 1 : ℕ) : ℤ) - 1 = (u.dropLast.length : ℤ) by rw [hlen]; push_cast; ring,
      tW_erase]
    rw [← ih _ hlen]
    congr 3 <;> simp only [SignType.coe_neg, SignType.coe_one, SignType.coe_zero, add_zero, hlen] <;>
      push_cast <;> ring

end Steps

end SigabaNeo.Inline
