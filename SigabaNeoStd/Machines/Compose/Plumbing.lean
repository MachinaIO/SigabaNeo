import SigabaNeoStd.Machines.Compose.Steps

/-!
# Two small deterministic machines on two tapes

* `prepTM T` (tapes: the clock, the flag): writes the flag of a virtual input (a mark at `-1`, the
  head back at `0`) and a unary clock of `T + 1` cells at `-T, …, 0`, and leaves the clock head at
  `1 - T`. It runs exactly `T + 5` steps (`runs_prep`).
* `rewTM T` (tapes: a buffer, the clock): from a word on the buffer with the head just after it,
  and the clock head at `1`, it rewinds the buffer head to `0` while consuming the clock leftwards.
  For a word of length at most `T` it runs exactly `T + 3` steps (`runs_rew`), so its running time
  does not depend on the word.
-/

namespace SigabaNeo.Compose

open Cslib Turing MultiTapeMachine

variable {x : List Bool}

/-! ### Two-tape configurations -/

/-- A configuration with two work tapes. -/
def pc {n : ℕ} (q : Option (Fin n)) (ip : Fin (x.length + 2)) (out : List Bool)
    (t0 t1 : ℤ → Option Bool) (h0 h1 : ℤ) : Config 2 Bool (Fin n) (Fin 0) x :=
  ⟨⟨q, ip, ![t0, t1], ![h0, h1], out⟩, Fin.elim0⟩

/-- The tape after an optional write. -/
def upd (t : ℤ → Option Bool) (h : ℤ) : Option (Option Bool) → ℤ → Option Bool
  | none => t
  | some s => Function.update t h s

/-- A two-tape action that keeps the input head and writes no output. -/
def act2 {n : ℕ} (a0 a1 : Option (Option Bool) × SignType) (q : Option (Fin n)) :
    Turing.Action 2 Bool (Fin n) :=
  ⟨0, ![a0, a1], none, q⟩

theorem pc_step {n : ℕ} (q q' : Option (Fin n)) (ip : Fin (x.length + 2)) (out : List Bool)
    (t0 t1 : ℤ → Option Bool) (h0 h1 : ℤ) (a0 a1 : Option (Option Bool) × SignType)
    (sym : Fin 0 → Option Bool) (mv : Fin 0 → SignType) :
    (pc q ip out t0 t1 h0 h1).step (act2 a0 a1 q') sym mv =
      pc q' ip out (upd t0 h0 a0.1) (upd t1 h1 a1.1) (h0 + a0.2) (h1 + a1.2) := by
  refine Config.ext ?_ (funext fun o => o.elim0)
  refine Cfg.ext rfl (by simp [pc, act2, Config.step, Turing.Action.apply])
    (funext fun i => ?_) (funext fun i => ?_) (by simp [pc, act2, Config.step, Turing.Action.apply])
  · fin_cases i <;> rcases a0 with ⟨_ | _, _⟩ <;> rcases a1 with ⟨_ | _, _⟩ <;>
      simp [pc, act2, Config.step, Turing.Action.apply, upd]
  · fin_cases i <;> simp [pc, act2, Config.step, Turing.Action.apply]

@[simp] theorem pc_state {n : ℕ} (q : Option (Fin n)) (ip : Fin (x.length + 2)) (out : List Bool)
    (t0 t1 : ℤ → Option Bool) (h0 h1 : ℤ) : (pc q ip out t0 t1 h0 h1).tapes.state = q := rfl

theorem pc_sym0 {n : ℕ} (q : Option (Fin n)) (ip : Fin (x.length + 2)) (out : List Bool)
    (t0 t1 : ℤ → Option Bool) (h0 h1 : ℤ) :
    (pc q ip out t0 t1 h0 h1).tapes.workTapeSymbols 0 = t0 h0 := rfl

theorem pc_sym1 {n : ℕ} (q : Option (Fin n)) (ip : Fin (x.length + 2)) (out : List Bool)
    (t0 t1 : ℤ → Option Bool) (h0 h1 : ℤ) :
    (pc q ip out t0 t1 h0 h1).tapes.workTapeSymbols 1 = t1 h1 := rfl

/-! ### The preparation -/

/-- The clock after writing `j` cells leftwards from `0`. -/
def clkW (j : ℕ) : ℤ → Option Bool := fun p => if -(j : ℤ) < p ∧ p ≤ 0 then some true else none

/-- The prepared clock: `T + 1` cells at `-T, …, 0`. -/
abbrev clkTape (T : ℕ) : ℤ → Option Bool := clkW (T + 1)

/-- The flag of a virtual input: a mark at `-1`. -/
def flagTape : ℤ → Option Bool := Function.update (fun _ => none) (-1) (some true)

theorem clkW_succ (j : ℕ) : Function.update (clkW j) (-(j : ℤ)) (some true) = clkW (j + 1) := by
  funext p
  by_cases hp : p = -(j : ℤ)
  · subst hp; simp [clkW]
  · rw [Function.update_of_ne hp]; simp only [clkW]; push_cast
    congr 1; apply propext; omega

theorem clkTape_true (T j : ℕ) (hj : j ≤ T) : clkTape T (-(j : ℤ)) = some true := by
  simp only [clkW, if_pos (show -((T + 1 : ℕ) : ℤ) < -(j : ℤ) ∧ -(j : ℤ) ≤ 0 by omega)]

theorem clkTape_end (T : ℕ) : clkTape T (-((T + 1 : ℕ) : ℤ)) = none := by
  simp only [clkW]; rw [if_neg (by omega)]

/-- The successor state of the preparation. -/
def prepNext (T : ℕ) (i : Fin (T + 5)) : Option (Fin (T + 5)) :=
  if h : i.val + 1 < T + 5 then some ⟨i.val + 1, h⟩ else none

/-- The action of the preparation in state `i`. -/
def prepAct (T : ℕ) (i : Fin (T + 5)) : Turing.Action 2 Bool (Fin (T + 5)) :=
  if i.val = 0 then act2 (none, 0) (none, -1) (prepNext T i)
  else if i.val = 1 then act2 (none, 0) (some (some true), 1) (prepNext T i)
  else if i.val < T + 3 then act2 (some (some true), -1) (none, 0) (prepNext T i)
  else act2 (none, 1) (none, 0) (prepNext T i)

/-- **The preparation**: tape `0` is the clock, tape `1` the flag. -/
def prepTM (T : ℕ) : MultiTapePTM 2 Bool (Fin (T + 5)) (Fin 0) where
  initial := 0
  tr q _ _ _ := fun _ => .step (prepAct T q) Fin.elim0 Fin.elim0

/-- The final configuration of the preparation. -/
def prepFin (T : ℕ) : Config 2 Bool (Fin (T + 5)) (Fin 0) x :=
  pc none 1 [] (clkTape T) flagTape (1 - T) 0

theorem runs_of_eq {k : ℕ} {S : Type} {M : MultiTapePTM k Bool S (Fin 0)}
    {c c' : Config k Bool S (Fin 0) x} {t t' : ℕ} (h : Runs M c t c') (ht : t = t') :
    Runs M c t' c' := ht ▸ h

theorem prep_one (T : ℕ) (i : Fin (T + 5)) (ip : Fin (x.length + 2)) (out : List Bool)
    (t0 t1 : ℤ → Option Bool) (h0 h1 : ℤ) :
    law (prepTM T) 1 (pc (some i) ip out t0 t1 h0 h1) =
      PMF.pure ((pc (some i) ip out t0 t1 h0 h1).step (prepAct T i) Fin.elim0 Fin.elim0) :=
  law_one_det _ _ rfl _ _ _ (fun _ => rfl)

theorem prep_loop (T : ℕ) : ∀ m j, (h : j + m = T + 1) →
    Runs (prepTM T) (pc (some ⟨2 + j, by omega⟩) 1 [] (clkW j) flagTape (-(j : ℤ)) 0) (m + 2)
      (prepFin (x := x) T) := by
  intro m
  induction m with
  | zero =>
    intro j hj
    obtain rfl : j = T + 1 := by omega
    have ha : prepAct T ⟨2 + (T + 1), by omega⟩ =
        act2 (none, 1) (none, 0) (some ⟨T + 4, by omega⟩) := by
      unfold prepAct prepNext
      rw [if_neg (show ¬ 2 + (T + 1) = 0 by omega), if_neg (show ¬ 2 + (T + 1) = 1 by omega),
        if_neg (show ¬ 2 + (T + 1) < T + 3 by omega), dif_pos (show 2 + (T + 1) + 1 < T + 5 by omega)]
      exact congrArg (act2 _ _) (congrArg some (Fin.ext (by simp; omega)))
    have hb : prepAct T ⟨T + 4, by omega⟩ = act2 (none, 1) (none, 0) none := by
      unfold prepAct prepNext
      rw [if_neg (show ¬ T + 4 = 0 by omega), if_neg (show ¬ T + 4 = 1 by omega),
        if_neg (show ¬ T + 4 < T + 3 by omega), dif_neg (show ¬ T + 4 + 1 < T + 5 by omega)]
    refine runs_cons (by simp) (prep_one ..) ?_
    rw [ha, pc_step]
    refine runs_halt (c' := prepFin T) (by simp) ?_ rfl
    rw [prep_one, hb, pc_step]
    simp only [prepFin, upd, SignType.coe_one, SignType.coe_zero, add_zero]
    congr 2; push_cast; ring
  | succ m ih =>
    intro j hj
    have ha : prepAct T ⟨2 + j, by omega⟩ =
        act2 (some (some true), -1) (none, 0) (some ⟨2 + (j + 1), by omega⟩) := by
      unfold prepAct prepNext
      rw [if_neg (show ¬ 2 + j = 0 by omega), if_neg (show ¬ 2 + j = 1 by omega),
        if_pos (show 2 + j < T + 3 by omega), dif_pos (show 2 + j + 1 < T + 5 by omega)]
      exact congrArg (act2 _ _) (congrArg some (Fin.ext (by simp; omega)))
    refine runs_of_eq (runs_cons (by simp) (prep_one ..) ?_) (by omega : m + 2 + 1 = m + 1 + 2)
    rw [ha, pc_step]
    simp only [upd, clkW_succ, SignType.coe_neg, SignType.coe_one, SignType.coe_zero, add_zero]
    convert ih (j + 1) (by omega) using 3
    push_cast; ring

/-- The preparation from blank tapes. -/
def prepInit (T : ℕ) : Config 2 Bool (Fin (T + 5)) (Fin 0) x :=
  pc (some 0) 1 [] (fun _ => none) (fun _ => none) 0 0

theorem prepTM_initialConfig (T : ℕ) : (prepTM T).initialConfig x = prepInit T := by
  refine Config.ext ?_ (funext fun o => o.elim0)
  refine Cfg.ext rfl rfl (funext fun i => ?_) (funext fun i => ?_) rfl <;> fin_cases i <;> rfl

/-- **The preparation runs exactly `T + 5` steps.** -/
theorem runs_prep (T : ℕ) : Runs (prepTM T) (prepInit (x := x) T) (T + 5) (prepFin T) := by
  have h0 : prepAct T 0 = act2 (none, 0) (none, -1) (some 1) := by
    simp only [prepAct, prepNext]; simp
  have h1 : prepAct T 1 = act2 (none, 0) (some (some true), 1) (some ⟨2, by omega⟩) := by
    simp only [prepAct, prepNext]; simp
  refine runs_of_eq (runs_cons (by simp [prepInit]) (prep_one ..) ?_) (by omega : T + 3 + 1 + 1 = T + 5)
  rw [h0, pc_step]
  refine runs_cons (by simp) (prep_one ..) ?_
  rw [h1, pc_step]
  simp only [upd, SignType.coe_neg, SignType.coe_one, SignType.coe_zero, add_zero]
  have := prep_loop (x := x) T (T + 1) 0 (by omega)
  convert this using 3
  all_goals first | rfl | (simp [clkW]; done) | (simp [clkW]; omega) | omega | simp

/-! ### The rewinding -/

/-- The action of the rewinding in state `q` reading `w`: tape `0` is the buffer, tape `1` the
clock. -/
def rewAct (q : Fin 3) (w : Fin 2 → Option Bool) : Turing.Action 2 Bool (Fin 3) :=
  if q.val = 0 then act2 (none, -1) (none, -1) (some 1)
  else if w 1 = some true then
    if q.val = 1 then
      if w 0 = none then act2 (none, 1) (none, -1) (some 2)
      else act2 (none, -1) (none, -1) (some 1)
    else act2 (none, 0) (none, -1) (some 2)
  else act2 (none, 0) (none, 0) none

/-- **The rewinding.** -/
def rewTM : MultiTapePTM 2 Bool (Fin 3) (Fin 0) where
  initial := 0
  tr q _ w _ := fun _ => .step (rewAct q w) Fin.elim0 Fin.elim0

theorem rew_one (i : Fin 3) (ip : Fin (x.length + 2)) (out : List Bool)
    (t0 t1 : ℤ → Option Bool) (h0 h1 : ℤ) :
    law rewTM 1 (pc (some i) ip out t0 t1 h0 h1) =
      PMF.pure ((pc (some i) ip out t0 t1 h0 h1).step (rewAct i ![t0 h0, t1 h1])
        Fin.elim0 Fin.elim0) := by
  refine law_one_det _ _ rfl _ _ _ (fun _ => ?_)
  have : (pc (some i) ip out t0 t1 h0 h1).tapes.workTapeSymbols = ![t0 h0, t1 h1] := by
    funext j; fin_cases j <;> rfl
  rw [this]; rfl

variable (T : ℕ) (y : List Bool) (ip : Fin (x.length + 2)) (out : List Bool)

/-- The final configuration of the rewinding. -/
def rewFin : Config 2 Bool (Fin 3) (Fin 0) x :=
  pc none ip out (tapeOfList y) (clkTape T) 0 (-((T + 1 : ℕ) : ℤ))

theorem rew_done : ∀ m c, (h : c + m = T + 1) →
    Runs rewTM (pc (some 2) ip out (tapeOfList y) (clkTape T) 0 (-(c : ℤ))) (m + 1)
      (rewFin T y ip out) := by
  intro m
  induction m with
  | zero =>
    intro c hc
    obtain rfl : c = T + 1 := by omega
    refine runs_halt (c' := rewFin T y ip out) (by simp) ?_ rfl
    rw [rew_one]
    simp only [rewAct, Matrix.cons_val_one, Matrix.cons_val_zero, clkTape_end]
    rw [if_neg (by decide), if_neg (by simp), pc_step]
    rfl
  | succ m ih =>
    intro c hc
    refine runs_of_eq (runs_cons (by simp) (rew_one ..) ?_) rfl
    simp only [rewAct, Matrix.cons_val_one, Matrix.cons_val_zero, clkTape_true T c (by omega)]
    simp only [Fin.isValue, Fin.val_two, OfNat.ofNat_ne_zero, ↓reduceIte]
    rw [if_neg (by decide), pc_step]
    simp only [upd, SignType.coe_neg, SignType.coe_one, SignType.coe_zero, add_zero]
    convert ih (c + 1) (by omega) using 3
    push_cast; ring

theorem rew_scan (hy : y.length ≤ T) : ∀ m j, (h : j + m = y.length) →
    Runs rewTM (pc (some 1) ip out (tapeOfList y) (clkTape T) ((y.length : ℤ) - 1 - j) (-(j : ℤ)))
      (m + (T - y.length) + 2) (rewFin T y ip out) := by
  intro m
  induction m with
  | zero =>
    intro j hj
    obtain rfl : j = y.length := by omega
    refine runs_of_eq (runs_cons (by simp) (rew_one ..) ?_) (by omega : T - y.length + 1 + 1 = 0 + (T - y.length) + 2)
    have hb : tapeOfList y ((y.length : ℤ) - 1 - y.length) = none := by
      rw [show (y.length : ℤ) - 1 - y.length = Int.negSucc 0 by omega]; rfl
    simp only [rewAct, Matrix.cons_val_one, Matrix.cons_val_zero, clkTape_true T y.length hy, hb]
    simp only [Fin.isValue, Fin.val_one, one_ne_zero, ↓reduceIte]
    rw [pc_step]
    simp only [upd, SignType.coe_neg, SignType.coe_one, SignType.coe_zero, add_zero]
    convert rew_done T y ip out (T - y.length) (y.length + 1) (by omega) using 3
    · omega
    · push_cast; ring
  | succ m ih =>
    intro j hj
    have hb : tapeOfList y ((y.length : ℤ) - 1 - j) ≠ none := by
      rw [show (y.length : ℤ) - 1 - j = ((y.length - 1 - j : ℕ) : ℤ) by omega, tapeOfList_ofNat]
      simp; omega
    refine runs_of_eq (runs_cons (by simp) (rew_one ..) ?_)
      (by omega : m + (T - y.length) + 2 + 1 = m + 1 + (T - y.length) + 2)
    simp only [rewAct, Matrix.cons_val_one, Matrix.cons_val_zero, clkTape_true T j (by omega)]
    simp only [Fin.isValue, Fin.val_one, one_ne_zero, ↓reduceIte, if_neg hb]
    rw [pc_step]
    simp only [upd, SignType.coe_neg, SignType.coe_one, SignType.coe_zero, add_zero]
    convert ih (j + 1) (by omega) using 3 <;> push_cast <;> ring

/-- The rewinding from the end of the word, the clock head at `1`. -/
def rewInit : Config 2 Bool (Fin 3) (Fin 0) x :=
  pc (some 0) ip out (tapeOfList y) (clkTape T) y.length 1

/-- **The rewinding runs exactly `T + 3` steps** on a word of length at most `T`. -/
theorem runs_rew (hy : y.length ≤ T) :
    Runs rewTM (rewInit T y ip out) (T + 3) (rewFin T y ip out) := by
  refine runs_of_eq (runs_cons (by simp [rewInit]) (rew_one ..) ?_) (by omega : y.length + (T - y.length) + 2 + 1 = T + 3)
  simp only [rewAct, Fin.isValue, Fin.val_zero, ↓reduceIte]
  rw [pc_step]
  simp only [upd, SignType.coe_neg, SignType.coe_one, add_zero]
  convert rew_scan T y ip out hy y.length 0 (by omega) using 3 <;> push_cast <;> ring

end SigabaNeo.Compose
