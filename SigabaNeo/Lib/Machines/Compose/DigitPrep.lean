import SigabaNeo.Lib.Machines.Compose.Plumbing
import SigabaNeo.Lib.Machines.Inline.LinCost

/-!
# A short preparation writing a unary clock from its digits

`prepTM T` (`Compose.Plumbing`) writes the unary clock of `T + 1` cells with `T + 5` straight-line
states. `DigitPrep.dprepTM k T` writes the same clock, and the same flag, with
`h + 6` states, where `h = (clockDigits k T).length` is the number of digits of `T` in base
`2 ^ (k + 1)` (`Inline.clockDigits`), on `k + 3` tapes:

* tapes `0, …, k` (blank at the start and at the end) are `k + 1` parallel tracks: cell `z` of the
  tracks holds the digit `z` of a counter, its bit `i` on track `i`;
* tape `k + 1` is the clock, tape `k + 2` the flag.

The phases (the counting loop is that of `Inline.machineLin`):

* `F 0`, `F 1`: the flag of a virtual input (a mark at `-1`, the head back at `0`);
* `W j` (`j < h`): write the digit `j` of `T` and move right; `W h`: step back onto the last digit;
* `back`: move left to the start of the counter (the first blank cell of track `k` on the left),
  then step right onto digit `0`;
* `dec`: decrement the counter: a digit `0` becomes `B - 1` (move right, borrow); a digit `d > 0`
  becomes `d - 1`, a cell is added to the clock leftwards, and the head goes back; if the borrow
  runs past the last digit the counter was `0`, and
* `erase`: the counter is erased leftwards; on the blank cell left of it the last cell of the clock
  is written, the clock head steps right, and the machine halts.

It runs exactly `dprepTime k T ≤ 4 T + 4 h + 6` steps from blank tapes, to the configuration
`dFin k T`: blank tracks with their heads at `0`, the clock `clkTape T` with its head at `1 - T`,
and the flag `flagTape` with its head at `0` (`runs_dprep`), the configuration `prepTM T` ends in on
its two tapes.
-/

namespace SigabaNeo.Compose

open Cslib Turing MultiTapeMachine
open Inline (LStep baseB clockDigits)

namespace DigitPrep

variable {k : ℕ} {x : List Bool}

/-! ### Configurations on `k + 3` tapes -/

/-- A configuration on `k + 3` tapes, the input head at `1`, the output empty. -/
def gc {S : Type} (q : Option S) (F : Fin (k + 3) → ℤ → Option Bool) (P : Fin (k + 3) → ℤ) :
    Config (k + 3) Bool S (Fin 0) x :=
  ⟨⟨q, 1, F, P, []⟩, Fin.elim0⟩

/-- An action that keeps the input head and writes no output. -/
def act {S : Type} (W : Fin (k + 3) → Option (Option Bool) × SignType) (q : Option S) :
    Turing.Action (k + 3) Bool S :=
  ⟨0, W, none, q⟩

theorem gc_step {S : Type} (q q' : Option S) (F : Fin (k + 3) → ℤ → Option Bool)
    (P : Fin (k + 3) → ℤ) (W : Fin (k + 3) → Option (Option Bool) × SignType)
    (sym : Fin 0 → Option Bool) (mv : Fin 0 → SignType) :
    (gc (x := x) q F P).step (act W q') sym mv =
      gc q' (fun i => upd (F i) (P i) (W i).1) (fun i => P i + (W i).2) := by
  refine Config.ext ?_ (funext fun o => o.elim0)
  refine Cfg.ext rfl (by simp [gc, act, Config.step, Turing.Action.apply])
    (funext fun i => ?_) (funext fun i => ?_) (by simp [gc, act, Config.step, Turing.Action.apply])
  · rcases h : (W i).1 with _ | s <;> simp [gc, act, Config.step, Turing.Action.apply, upd, h]
  · simp [gc, act, Config.step, Turing.Action.apply]

@[simp] theorem gc_state {S : Type} (q : Option S) (F : Fin (k + 3) → ℤ → Option Bool)
    (P : Fin (k + 3) → ℤ) : (gc (x := x) q F P).tapes.state = q := rfl

/-! ### The layout -/

/-- The tapes: the tracks hold the digits `l`, then the clock `C` and the flag `Fl`. -/
def dF (l : List ℕ) (C Fl : ℤ → Option Bool) (i : Fin (k + 3)) : ℤ → Option Bool :=
  if i.val < k + 1 then tapeOfList (l.map fun e => e.testBit i.val)
  else if i.val = k + 1 then C else Fl

/-- The heads: the track heads at `p`, the clock head at `pc`, the flag head at `pf`. -/
def dP (p pc pf : ℤ) (i : Fin (k + 3)) : ℤ :=
  if i.val < k + 1 then p else if i.val = k + 1 then pc else pf

/-- Act on the tracks (`b`: no write, erase, or write a digit; `d`: the move), the clock and the
flag. -/
def dW (b : Option (Option ℕ)) (d : SignType) (clk fl : Option (Option Bool) × SignType)
    (i : Fin (k + 3)) : Option (Option Bool) × SignType :=
  if i.val < k + 1 then (b.map (Option.map fun e => e.testBit i.val), d)
  else if i.val = k + 1 then clk else fl

theorem dW_pos (p pc pf : ℤ) (b : Option (Option ℕ)) (d : SignType)
    (clk fl : Option (Option Bool) × SignType) :
    (fun i => dP (k := k) p pc pf i + ((dW b d clk fl i).2 : ℤ)) =
      dP (p + d) (pc + clk.2) (pf + fl.2) := by
  funext i; unfold dP dW; split_ifs <;> rfl

theorem dF_upd (l l' : List ℕ) (C Fl : ℤ → Option Bool) (p pc pf : ℤ) (b : Option (Option ℕ))
    (d : SignType) (clk fl : Option (Option Bool) × SignType)
    (htr : ∀ i : ℕ, i < k + 1 → upd (tapeOfList (l.map fun e => e.testBit i)) p
      (b.map (Option.map fun e => e.testBit i)) = tapeOfList (l'.map fun e => e.testBit i)) :
    (fun i => upd (dF (k := k) l C Fl i) (dP p pc pf i) (dW b d clk fl i).1) =
      dF l' (upd C pc clk.1) (upd Fl pf fl.1) := by
  funext i; unfold dF dP dW; split_ifs with h1 h2
  · exact htr i h1
  · rfl
  · rfl

theorem upd_none (t : ℤ → Option Bool) (p : ℤ) : upd t p none = t := rfl

/-- The track write that sets the digit `j`. -/
theorem trk_set (l : List ℕ) (j : ℕ) (hj : j < l.length) (e i : ℕ) :
    upd (tapeOfList (l.map fun e => e.testBit i)) (j : ℤ)
      ((some (some e) : Option (Option ℕ)).map (Option.map fun e => e.testBit i)) =
      tapeOfList ((l.set j e).map fun e => e.testBit i) := by
  simp only [Option.map_some, upd, List.map_set]
  exact (Inline.tapeOfList_set' _ (by simpa using hj) _).symm

/-- The track write that appends a digit. -/
theorem trk_append (l : List ℕ) (e i : ℕ) :
    upd (tapeOfList (l.map fun e => e.testBit i)) (l.length : ℤ)
      ((some (some e) : Option (Option ℕ)).map (Option.map fun e => e.testBit i)) =
      tapeOfList ((l ++ [e]).map fun e => e.testBit i) := by
  simp only [Option.map_some, upd, List.map_append, List.map_cons, List.map_nil]
  rw [tapeOfList_append_single, List.length_map]

/-- The track write that erases the last digit. -/
theorem trk_erase (u : List ℕ) (e i : ℕ) :
    upd (tapeOfList ((u ++ [e]).map fun e => e.testBit i)) (u.length : ℤ)
      ((some none : Option (Option ℕ)).map (Option.map fun e => e.testBit i)) =
      tapeOfList (u.map fun e => e.testBit i) := by
  simp only [Option.map_some, Option.map_none, upd, List.map_append, List.map_cons, List.map_nil]
  rw [show (u.length : ℤ) = ((u.map fun e => e.testBit i).length : ℤ) by simp]
  exact Inline.tapeOfList_erase_last _ _

/-! ### Reading the tracks -/

/-- The digit under the track heads (a blank reads as `0`). -/
def rd (w : Fin (k + 3) → Option Bool) : ℕ :=
  ∑ i : Fin (k + 1), (if w ⟨i, by omega⟩ = some true then 1 else 0) * 2 ^ (i : ℕ)

theorem sym_trk (l : List ℕ) (C Fl : ℤ → Option Bool) (p pc pf : ℤ) (i : ℕ) (hi : i < k + 1) :
    dF (k := k) l C Fl (⟨i, by omega⟩ : Fin (k + 3)) (dP p pc pf (⟨i, by omega⟩ : Fin (k + 3))) =
      tapeOfList (l.map fun e => e.testBit i) p := by
  simp [dF, dP, hi]

theorem last_none_iff (l : List ℕ) (C Fl : ℤ → Option Bool) (p pc pf : ℤ) :
    (fun i => dF (k := k) l C Fl i (dP p pc pf i)) ⟨k, by omega⟩ = none ↔
      p < 0 ∨ (l.length : ℤ) ≤ p := by
  show dF (k := k) l C Fl (⟨k, by omega⟩ : Fin (k + 3)) (dP p pc pf (⟨k, by omega⟩ : Fin (k + 3)))
    = none ↔ _
  rw [sym_trk l C Fl p pc pf k (by omega), tapeOfList_eq_none_iff, List.length_map]

theorem rd_eq (l : List ℕ) (C Fl : ℤ → Option Bool) (j : ℕ) (hj : j < l.length) (pc pf : ℤ)
    (hB : l[j] < baseB k) :
    rd (fun i => dF (k := k) l C Fl i (dP j pc pf i)) = l[j] := by
  unfold rd
  have e : ∀ i : Fin (k + 1),
      (if dF (k := k) l C Fl (⟨i, by omega⟩ : Fin (k + 3)) (dP j pc pf (⟨i, by omega⟩ : Fin (k + 3)))
        = some true then 1 else 0) * 2 ^ (i : ℕ) =
      (if l[j].testBit i then 1 else 0) * 2 ^ (i : ℕ) := by
    intro i
    rw [sym_trk l C Fl j pc pf i i.isLt, tapeOfList_ofNat]
    simp [hj]
  rw [Finset.sum_congr rfl (fun i _ => e i)]
  exact Inline.digit_sum (k + 1) _ hB

/-! ### The machine -/

/-- The control states: the flag, the writing of the digits, the counting loop. -/
abbrev DState (k T : ℕ) : Type := Fin 2 ⊕ (Fin ((clockDigits k T).length + 1) ⊕ LStep)

/-- The action of the preparation in state `q` reading `w`. -/
def dAct (k T : ℕ) (q : DState k T) (w : Fin (k + 3) → Option Bool) :
    Turing.Action (k + 3) Bool (DState k T) :=
  match q with
  | .inl i =>
    if i.val = 0 then act (dW none 0 (none, 0) (none, -1)) (some (.inl 1))
    else act (dW none 0 (none, 0) (some (some true), 1)) (some (.inr (.inl 0)))
  | .inr (.inl j) =>
    if hj : j.val < (clockDigits k T).length then
      act (dW (some (some (clockDigits k T)[j.val])) 1 (none, 0) (none, 0))
        (some (.inr (.inl ⟨j.val + 1, by omega⟩)))
    else act (dW none (-1) (none, 0) (none, 0)) (some (.inr (.inr .back)))
  | .inr (.inr .back) =>
    if w ⟨k, by omega⟩ = none then act (dW none 1 (none, 0) (none, 0)) (some (.inr (.inr .dec)))
    else act (dW none (-1) (none, 0) (none, 0)) (some (.inr (.inr .back)))
  | .inr (.inr .dec) =>
    if w ⟨k, by omega⟩ = none then
      act (dW none (-1) (none, 0) (none, 0)) (some (.inr (.inr .erase)))
    else if rd w = 0 then
      act (dW (some (some (baseB k - 1))) 1 (none, 0) (none, 0)) (some (.inr (.inr .dec)))
    else
      act (dW (some (some (rd w - 1))) (-1) (some (some true), -1) (none, 0))
        (some (.inr (.inr .back)))
  | .inr (.inr .erase) =>
    if w ⟨k, by omega⟩ = none then act (dW none 1 (some (some true), 1) (none, 0)) none
    else act (dW (some none) (-1) (none, 0) (none, 0)) (some (.inr (.inr .erase)))

/-- **The preparation with a digit counter**: tapes `0, …, k` are the tracks, `k + 1` the clock,
`k + 2` the flag. -/
def dprepTM (k T : ℕ) : MultiTapePTM (k + 3) Bool (DState k T) (Fin 0) where
  initial := .inl 0
  tr q _ w _ := fun _ => .step (dAct k T q w) Fin.elim0 Fin.elim0

@[simp] theorem card_DState (k T : ℕ) :
    Fintype.card (DState k T) = (clockDigits k T).length + 6 := by
  simp only [DState, Fintype.card_sum, Fintype.card_fin, Inline.LStep.card]
  ring

section Steps

variable {T : ℕ}

theorem d_one (q : DState k T) (F : Fin (k + 3) → ℤ → Option Bool) (P : Fin (k + 3) → ℤ) :
    law (dprepTM k T) 1 (gc (x := x) (some q) F P) =
      PMF.pure ((gc (some q) F P).step (dAct k T q (fun i => F i (P i))) Fin.elim0 Fin.elim0) :=
  law_one_det _ _ rfl _ _ _ (fun _ => rfl)

/-- One live step, in the layout. -/
theorem runs_stepD {q q' : DState k T} {l l' : List ℕ} {C Fl C' Fl' : ℤ → Option Bool}
    {p pc pf p' pc' pf' : ℤ} {b : Option (Option ℕ)} {d : SignType}
    {clk fl : Option (Option Bool) × SignType} {t : ℕ} {f : Config (k + 3) Bool (DState k T) (Fin 0) x}
    (hact : dAct k T q (fun i => dF l C Fl i (dP p pc pf i)) = act (dW b d clk fl) (some q'))
    (htr : ∀ i : ℕ, i < k + 1 → upd (tapeOfList (l.map fun e => e.testBit i)) p
      (b.map (Option.map fun e => e.testBit i)) = tapeOfList (l'.map fun e => e.testBit i))
    (hC : upd C pc clk.1 = C') (hFl : upd Fl pf fl.1 = Fl') (hp : p + d = p')
    (hpc : pc + clk.2 = pc') (hpf : pf + fl.2 = pf')
    (h : Runs (dprepTM k T) (gc (some q') (dF l' C' Fl') (dP p' pc' pf')) t f) :
    Runs (dprepTM k T) (gc (some q) (dF l C Fl) (dP p pc pf)) (t + 1) f := by
  subst hC hFl hp hpc hpf
  rw [← dF_upd l l' C Fl p pc pf b d clk fl htr, ← dW_pos] at h
  exact runs_cons (by simp) ((d_one _ _ _).trans (by rw [hact, gc_step])) h

/-- The halting step, in the layout. -/
theorem runs_lastD {q : DState k T} {l l' : List ℕ} {C Fl C' Fl' : ℤ → Option Bool}
    {p pc pf p' pc' pf' : ℤ} {b : Option (Option ℕ)} {d : SignType}
    {clk fl : Option (Option Bool) × SignType}
    (hact : dAct k T q (fun i => dF l C Fl i (dP p pc pf i)) = act (dW b d clk fl) none)
    (htr : ∀ i : ℕ, i < k + 1 → upd (tapeOfList (l.map fun e => e.testBit i)) p
      (b.map (Option.map fun e => e.testBit i)) = tapeOfList (l'.map fun e => e.testBit i))
    (hC : upd C pc clk.1 = C') (hFl : upd Fl pf fl.1 = Fl') (hp : p + d = p')
    (hpc : pc + clk.2 = pc') (hpf : pf + fl.2 = pf') :
    Runs (dprepTM k T) (gc (x := x) (some q) (dF l C Fl) (dP p pc pf)) 1
      (gc none (dF l' C' Fl') (dP p' pc' pf')) := by
  subst hC hFl hp hpc hpf
  rw [← dF_upd l l' C Fl p pc pf b d clk fl htr, ← dW_pos]
  exact runs_halt (by simp) ((d_one _ _ _).trans (by rw [hact, gc_step])) rfl

end Steps

/-- Arithmetic side goals of the steps. -/
macro "dprep_solve" : tactic =>
  `(tactic| first
    | rfl
    | (simp only [SignType.coe_neg, SignType.coe_one, SignType.coe_zero]; push_cast; ring)
    | (push_cast; ring)
    | omega)

section Phases

variable {T : ℕ}

/-- A configuration of the main phase: state `q`, the digits `l` on the tracks with their heads at
`p`, the clock of `c` cells (leftwards from `0`) with its head just left of it, the flag. -/
abbrev dc (q : DState k T) (l : List ℕ) (c : ℕ) (p : ℤ) :
    Config (k + 3) Bool (DState k T) (Fin 0) x :=
  gc (some q) (dF l (clkW c) flagTape) (dP p (-(c : ℤ)) 0)

/-- The final configuration, with a clock of `c + 1` cells. -/
def dFin (k T c : ℕ) : Config (k + 3) Bool (DState k T) (Fin 0) x :=
  gc none (dF [] (clkW (c + 1)) flagTape) (dP 0 (1 - (c : ℤ)) 0)

/-- **Back to the start** of the counter, then onto its digit `0`. -/
theorem runs_back (l : List ℕ) (c t : ℕ) (f : Config (k + 3) Bool (DState k T) (Fin 0) x)
    (h : Runs (dprepTM k T) (dc (.inr (.inr .dec)) l c 0) t f) :
    ∀ j ≤ l.length,
      Runs (dprepTM k T) (dc (.inr (.inr .back)) l c ((j : ℤ) - 1)) (t + j + 1) f := by
  intro j
  induction j with
  | zero =>
    intro _
    refine runs_stepD (b := none) (d := 1) (clk := (none, 0)) (fl := (none, 0)) ?_
      (fun _ _ => rfl) rfl rfl (by dprep_solve) (by dprep_solve) (by dprep_solve) h
    simp only [dAct]
    rw [ite_eq_left ((last_none_iff ..).mpr (by left; simp))]
  | succ j ih =>
    intro hj
    refine runs_of_eq (runs_stepD (b := none) (d := -1) (clk := (none, 0)) (fl := (none, 0)) ?_
      (fun _ _ => rfl) rfl rfl (by dprep_solve) (by dprep_solve) (by dprep_solve)
      (ih (by omega))) (by omega)
    simp only [dAct]
    rw [ite_eq_right (by rw [last_none_iff]; push_cast; omega)]

/-- **The borrow** across zero digits. -/
theorem runs_decScan (rest : List ℕ) (c t : ℕ) (f : Config (k + 3) Bool (DState k T) (Fin 0) x) :
    ∀ z pre : ℕ,
      Runs (dprepTM k T) (dc (.inr (.inr .dec))
        (List.replicate (pre + z) (baseB k - 1) ++ rest) c ((pre + z : ℕ) : ℤ)) t f →
      Runs (dprepTM k T) (dc (.inr (.inr .dec))
        (List.replicate pre (baseB k - 1) ++ List.replicate z 0 ++ rest) c pre) (t + z) f := by
  have hB := Inline.baseB_two_le (kA := k)
  intro z
  induction z with
  | zero => intro pre h; simpa using h
  | succ z ih =>
    intro pre h
    set l := List.replicate pre (baseB k - 1) ++ 0 :: (List.replicate z 0 ++ rest) with hl
    have hl' : List.replicate pre (baseB k - 1) ++ List.replicate (z + 1) 0 ++ rest = l := by
      simp [hl, List.replicate_succ]
    have hlen : pre < l.length := by simp [hl]
    have hget : l[pre] = 0 := Inline.getElem_replicate_append _ _ _ _
    have h' := ih (pre + 1) (by rw [show pre + 1 + z = pre + (z + 1) by omega]; exact h)
    rw [show List.replicate (pre + 1) (baseB k - 1) ++ List.replicate z 0 ++ rest =
      l.set pre (baseB k - 1) by
        rw [hl, Inline.set_replicate_append, List.replicate_succ']; simp] at h'
    rw [hl']
    refine runs_of_eq (runs_stepD (b := some (some (baseB k - 1))) (d := 1) (clk := (none, 0))
      (fl := (none, 0)) ?_ (fun i _ => trk_set l pre hlen _ i) rfl rfl (by dprep_solve)
      (by dprep_solve) (by dprep_solve) h') (by omega)
    simp only [dAct]
    rw [ite_eq_right (by rw [last_none_iff]; omega),
      ite_eq_left (by rw [rd_eq l _ _ pre hlen _ _ (by rw [hget]; omega), hget])]

/-- **A decrement** on a nonzero digit: the clock grows by one cell, and the heads go back. -/
theorem runs_decHit (pre d : ℕ) (rest : List ℕ) (hd : d + 1 < baseB k) (c t : ℕ)
    (f : Config (k + 3) Bool (DState k T) (Fin 0) x)
    (h : Runs (dprepTM k T) (dc (.inr (.inr .back))
      (List.replicate pre (baseB k - 1) ++ d :: rest) (c + 1) ((pre : ℤ) - 1)) t f) :
    Runs (dprepTM k T) (dc (.inr (.inr .dec))
      (List.replicate pre (baseB k - 1) ++ (d + 1) :: rest) c pre) (t + 1) f := by
  set l := List.replicate pre (baseB k - 1) ++ (d + 1) :: rest with hl
  have hlen : pre < l.length := by simp [hl]
  have hget : l[pre] = d + 1 := Inline.getElem_replicate_append _ _ _ _
  have hset : l.set pre d = List.replicate pre (baseB k - 1) ++ d :: rest :=
    Inline.set_replicate_append _ _ _ _ _
  refine runs_stepD (b := some (some d)) (d := -1) (clk := (some (some true), -1))
    (fl := (none, 0)) ?_ (fun i _ => by rw [← hset]; exact trk_set l pre hlen d i)
    (clkW_succ c) rfl (by dprep_solve) (by dprep_solve) (by dprep_solve) h
  simp only [dAct]
  rw [ite_eq_right (by rw [last_none_iff]; omega), rd_eq l _ _ pre hlen _ _ (by rw [hget]; exact hd),
    hget, ite_eq_right (by omega), Nat.add_sub_cancel]

/-- The borrow runs past the last digit. -/
theorem runs_decEnd (l : List ℕ) (c t : ℕ) (f : Config (k + 3) Bool (DState k T) (Fin 0) x)
    (h : Runs (dprepTM k T) (dc (.inr (.inr .erase)) l c ((l.length : ℤ) - 1)) t f) :
    Runs (dprepTM k T) (dc (.inr (.inr .dec)) l c l.length) (t + 1) f := by
  refine runs_stepD (b := none) (d := -1) (clk := (none, 0)) (fl := (none, 0)) ?_
    (fun _ _ => rfl) rfl rfl (by dprep_solve) (by dprep_solve) (by dprep_solve) h
  simp only [dAct]
  rw [ite_eq_left ((last_none_iff ..).mpr (by right; exact le_rfl))]

/-- **Erase the counter** leftwards, write the last clock cell, and halt. -/
theorem runs_erase (c : ℕ) : ∀ n (u : List ℕ), u.length = n →
    Runs (dprepTM k T) (dc (x := x) (.inr (.inr .erase)) u c ((n : ℤ) - 1)) (n + 1)
      (dFin k T c) := by
  intro n
  induction n with
  | zero =>
    intro u hu
    obtain rfl : u = [] := List.eq_nil_of_length_eq_zero hu
    refine runs_lastD (b := none) (d := 1) (clk := (some (some true), 1)) (fl := (none, 0)) ?_
      (fun _ _ => rfl) (clkW_succ c) rfl (by dprep_solve) (by dprep_solve) (by dprep_solve)
    simp only [dAct]
    rw [ite_eq_left ((last_none_iff ..).mpr (by left; simp))]
  | succ n ih =>
    intro u hu
    have hne : u ≠ [] := by rintro rfl; simp at hu
    have hu' : u = u.dropLast ++ [u.getLast hne] := (List.dropLast_append_getLast hne).symm
    have hlen : u.dropLast.length = n := by simp [hu]
    rw [hu']
    refine runs_of_eq (runs_stepD (b := some none) (d := -1) (clk := (none, 0)) (fl := (none, 0))
      ?_ ?_ rfl rfl (by dprep_solve) (by dprep_solve) (by dprep_solve) (ih _ hlen)) rfl
    · simp only [dAct]
      rw [ite_eq_right (by
        rw [last_none_iff]; simp only [List.length_append, List.length_singleton, hlen]
        push_cast; omega)]
    · intro i _
      rw [show ((n + 1 : ℕ) : ℤ) - 1 = (u.dropLast.length : ℤ) by rw [hlen]; push_cast; ring]
      exact trk_erase _ _ i

/-- **The counting loop**: from the counter `n` (digits `l`), the clock grows by `n` cells, within
`4 n + 2 (number of zero digits) + 2` steps, and the machine halts. -/
theorem runs_loop : ∀ n (l : List ℕ) (c : ℕ), Nat.ofDigits (baseB k) l = n →
    (∀ d ∈ l, d < baseB k) → ∃ t, t ≤ 4 * n + 2 * l.count 0 + 2 ∧ ∀ x : List Bool,
      Runs (dprepTM k T) (dc (x := x) (.inr (.inr .dec)) l c 0) t (dFin k T (c + n)) := by
  have hB := Inline.baseB_two_le (kA := k)
  intro n
  induction n with
  | zero =>
    intro l c hl _
    have hrep := Inline.eq_replicate_of_ofDigits_eq_zero (by omega) l hl
    refine ⟨2 * l.length + 2, by rw [hrep]; simp, fun x => ?_⟩
    have h3 := runs_erase (k := k) (x := x) (T := T) c l.length
      (List.replicate l.length (baseB k - 1)) (by simp)
    have h2 := runs_decEnd (k := k) (T := T) (List.replicate l.length (baseB k - 1)) c _ _
      (by rw [List.length_replicate]; exact h3)
    rw [List.length_replicate] at h2
    have h1 := runs_decScan (k := k) (T := T) [] c _ _ l.length 0 (by rw [Nat.zero_add, List.append_nil]; exact h2)
    simp only [List.replicate_zero, List.nil_append, List.append_nil, Nat.cast_zero] at h1
    rw [← hrep] at h1
    exact runs_of_eq h1 (by omega)
  | succ n ih =>
    intro l c hl hdig
    obtain ⟨z, d, rest, rfl⟩ := Inline.exists_decomp (b := baseB k) l (by omega)
    have hd : d + 1 < baseB k := hdig _ (by simp)
    set l' := List.replicate z (baseB k - 1) ++ d :: rest with hl'
    have hval : Nat.ofDigits (baseB k) l' = n := by
      rw [Inline.ofDigits_replicate_zero_append, Nat.ofDigits_cons] at hl
      rw [hl', Nat.ofDigits_append, Nat.ofDigits_cons, List.length_replicate]
      have := Inline.ofDigits_replicate_pred (baseB k) z (by omega)
      have e : baseB k ^ z * (d + 1 + baseB k * Nat.ofDigits (baseB k) rest) =
          baseB k ^ z * (d + baseB k * Nat.ofDigits (baseB k) rest) + baseB k ^ z := by ring
      omega
    have hdig' : ∀ e ∈ l', e < baseB k := by
      intro e he
      simp only [hl', List.mem_append, List.mem_replicate, List.mem_cons] at he
      rcases he with ⟨_, rfl⟩ | rfl | he
      · omega
      · omega
      · exact hdig e (by simp [he])
    obtain ⟨t', ht', hlaw⟩ := ih l' (c + 1) hval hdig'
    refine ⟨z + 1 + (z + 1) + t', ?_, fun x => ?_⟩
    · have hc : l'.count 0 ≤ 1 + rest.count 0 := by
        rw [hl', List.count_append, List.count_cons]
        rw [List.count_replicate]
        have : (baseB k - 1 == 0) = false := by simp; omega
        simp only [this, Bool.false_eq_true, ite_false]
        split_ifs <;> simp
      have hc2 : (List.replicate z 0 ++ (d + 1) :: rest).count 0 = z + rest.count 0 := by
        rw [List.count_append, List.count_cons, List.count_replicate]
        simp
      rw [hc2]
      omega
    · have h4 := hlaw x
      have h3 := runs_back (k := k) (T := T) l' (c + 1) t' _ h4 z (by simp [hl'])
      have h2 := runs_decHit (k := k) (T := T) z d rest hd c _ _ h3
      have h1 := runs_decScan (k := k) (T := T) ((d + 1) :: rest) c _ _ z 0 (by rw [Nat.zero_add]; exact h2)
      simp only [List.replicate_zero, List.nil_append, Nat.cast_zero] at h1
      rw [show c + (n + 1) = c + 1 + n by omega]
      exact runs_of_eq h1 (by omega)

/-- **The writing phase**: the digits of the clock on the tracks. -/
theorem runs_write (t : ℕ) (f : Config (k + 3) Bool (DState k T) (Fin 0) x)
    (h : Runs (dprepTM k T) (dc (.inr (.inl ⟨(clockDigits k T).length, by omega⟩))
      (clockDigits k T) 0 (clockDigits k T).length) t f) :
    ∀ m j (hj : j + m = (clockDigits k T).length),
      Runs (dprepTM k T) (dc (.inr (.inl ⟨j, by omega⟩)) ((clockDigits k T).take j) 0 j)
        (t + m) f := by
  intro m
  induction m with
  | zero =>
    intro j hj
    obtain rfl : j = (clockDigits k T).length := by omega
    simpa using h
  | succ m ih =>
    intro j hj
    have hjl : j < (clockDigits k T).length := by omega
    have h' := ih (j + 1) (by omega)
    rw [Inline.take_succ_eq' _ _ hjl] at h'
    have hlen : ((clockDigits k T).take j).length = j := by simp; omega
    refine runs_of_eq (runs_stepD (b := some (some (clockDigits k T)[j])) (d := 1)
      (clk := (none, 0)) (fl := (none, 0)) ?_ ?_ rfl rfl (by dprep_solve) (by dprep_solve)
      (by dprep_solve) h') (by omega)
    · simp only [dAct]; exact dite_eq_left hjl
    · intro i _
      have := trk_append ((clockDigits k T).take j) (clockDigits k T)[j] i
      rwa [hlen] at this

theorem initialConfig_d :
    (dprepTM k T).initialConfig x =
      gc (some (.inl 0)) (dF [] (clkW 0) (fun _ => none)) (dP 0 0 0) := by
  have h1 : dF (k := k) [] (clkW 0) (fun _ => none) = fun _ _ => none := by
    funext i z; unfold dF; split_ifs <;> simp [clkW]
  have h2 : dP (k := k) 0 0 0 = fun _ => 0 := by funext i; unfold dP; split_ifs <;> rfl
  rw [h1, h2]
  exact Config.ext rfl (funext fun o => o.elim0)

end Phases

/-- **The preparation runs** a fixed number of steps, at most `4 T + 4 h + 6`, from blank tapes to
`dFin k T T`. -/
theorem dprep_runs (k T : ℕ) : ∃ t, t ≤ 4 * T + 4 * (clockDigits k T).length + 6 ∧
    ∀ x : List Bool,
      Runs (dprepTM k T) ((dprepTM k T).initialConfig x) t (dFin (x := x) k T T) := by
  have hB := Inline.baseB_two_le (kA := k)
  obtain ⟨t, ht, hlaw⟩ := runs_loop (k := k) (T := T) T (clockDigits k T) 0
    (Nat.ofDigits_digits _ _) (fun d hd => Nat.digits_lt_base (by omega) hd)
  have hcount := List.count_le_length (a := 0) (l := clockDigits k T)
  refine ⟨t + (clockDigits k T).length + 1 + 1 + (clockDigits k T).length + 1 + 1, by omega,
    fun x => ?_⟩
  have hL := hlaw x
  rw [Nat.zero_add] at hL
  have hb := runs_back _ 0 t _ hL (clockDigits k T).length le_rfl
  have hw : Runs (dprepTM k T) (dc (x := x) (.inr (.inl ⟨(clockDigits k T).length, by omega⟩))
      (clockDigits k T) 0 (clockDigits k T).length) (t + (clockDigits k T).length + 1 + 1)
      (dFin k T T) := by
    refine runs_stepD (b := none) (d := -1) (clk := (none, 0)) (fl := (none, 0)) ?_
      (fun _ _ => rfl) rfl rfl (by dprep_solve) (by dprep_solve) (by dprep_solve) hb
    simp only [dAct]; exact dite_eq_right (lt_irrefl _)
  have hw0 := runs_write _ _ hw (clockDigits k T).length 0 (by omega)
  rw [List.take_zero] at hw0
  have hf1 : Runs (dprepTM k T) (gc (x := x) (some (.inl 1)) (dF [] (clkW 0) (fun _ => none))
      (dP 0 0 (-1))) (t + (clockDigits k T).length + 1 + 1 + (clockDigits k T).length + 1)
      (dFin k T T) := by
    refine runs_stepD (b := none) (d := 0) (clk := (none, 0)) (fl := (some (some true), 1)) ?_
      (fun _ _ => rfl) rfl rfl (by dprep_solve) (by dprep_solve) (by dprep_solve) hw0
    simp only [dAct]; rfl
  rw [initialConfig_d]
  refine runs_stepD (b := none) (d := 0) (clk := (none, 0)) (fl := (none, -1)) ?_
    (fun _ _ => rfl) rfl rfl (by dprep_solve) (by dprep_solve) (by dprep_solve) hf1
  simp only [dAct]; rfl

/-- The running time of the preparation. -/
noncomputable def dprepTime (k T : ℕ) : ℕ := Classical.choose (dprep_runs k T)

theorem dprepTime_le (k T : ℕ) : dprepTime k T ≤ 4 * T + 4 * (clockDigits k T).length + 6 :=
  (Classical.choose_spec (dprep_runs k T)).1

/-- **The preparation runs exactly `dprepTime k T` steps.** -/
theorem runs_dprep (k T : ℕ) (x : List Bool) :
    Runs (dprepTM k T) ((dprepTM k T).initialConfig x) (dprepTime k T) (dFin (x := x) k T T) :=
  (Classical.choose_spec (dprep_runs k T)).2 x

end DigitPrep

end SigabaNeo.Compose
