import SigabaNeo.Lib.Machines.Inline.Routine

/-!
# Inlining an oracle handler: the machine

Given an oracle machine `M` with `kA` work tapes and `ops` channels, a handler routine `H o` with
`m + 3` tapes for each channel `o`, a clock `T` and the encoding `w` of the initial handler state,
`Inline.machine` is one closed fair-coin machine that runs `M` for at most `T` of its own steps,
answering each query on channel `o` by running `H o`.

## Tapes

`Tape kA ops m` names the `nTapes kA ops m = kA + 2 * ops + 2 + m` tapes:

* `work i`: the work tapes of `M`;
* `qry o`: the query buffer of channel `o` (the buffer lies at `0, …, len - 1`, the head at `len`);
* `ans o`: the answer tape of channel `o`;
* `clock`: a unary clock of `T` cells, consumed leftwards, one cell per step of `M`;
* `st`: the encoded handler state;
* `scr j`: scratch tapes of the handler.

`H o` runs on `qry o` (its tape `0`, the query), `ans o` (its tape `1`, the answer), `st` (its tape
`2`, the state) and the scratch tapes.

## Control

* a straight-line preparation writes `w` on `st` and the clock;
* simulation states `(q, fl)`: `q` the state of `M`, `fl o` a flag per channel: `empty` when the
  answer of `o` is empty (its head then stays at `0`), otherwise `left`/`right`, telling on which
  side of the answer the head is whenever it reads a blank;
* query states `(q, fl, o, ·)`: the next state of `M` after a query on `o`, then the phases
  `cleanStart, seekR, seekL, toEnd, eraseL` (erase the old answer and return to `0`),
  `rewQ0, rewQ` (rewind the query), the states of `H o`, then `qToEnd, qErase` (erase the query).
-/

namespace SigabaNeo.Inline

open Cslib Turing MultiTapeMachine

/-- The tapes of the inlined machine. -/
inductive Tape (kA ops m : ℕ) where
  | work (i : Fin kA)
  | qry (o : Fin ops)
  | ans (o : Fin ops)
  | clock
  | st
  | scr (j : Fin m)
  deriving DecidableEq

/-- Number of tapes of the inlined machine. -/
abbrev nTapes (kA ops m : ℕ) : ℕ := kA + 2 * ops + 2 + m

variable {kA ops m : ℕ}

/-- The position of a tape. -/
def Tape.idx : Tape kA ops m → Fin (nTapes kA ops m)
  | .work i => ⟨i, by simp only [nTapes]; omega⟩
  | .qry o => ⟨kA + o, by simp only [nTapes]; omega⟩
  | .ans o => ⟨kA + ops + o, by simp only [nTapes]; omega⟩
  | .clock => ⟨kA + 2 * ops, by simp only [nTapes]; omega⟩
  | .st => ⟨kA + 2 * ops + 1, by simp only [nTapes]; omega⟩
  | .scr j => ⟨kA + 2 * ops + 2 + j, by simp only [nTapes]; omega⟩

/-- The tape at a position. -/
def kind (i : Fin (nTapes kA ops m)) : Tape kA ops m :=
  if h : i.val < kA then .work ⟨i, h⟩
  else if h : i.val < kA + ops then .qry ⟨i - kA, by have := i.isLt; simp only [nTapes] at this; omega⟩
  else if h : i.val < kA + 2 * ops then .ans ⟨i - kA - ops, by have := i.isLt; simp only [nTapes] at this; omega⟩
  else if h : i.val = kA + 2 * ops then .clock
  else if h : i.val = kA + 2 * ops + 1 then .st
  else .scr ⟨i - (kA + 2 * ops + 2), by have := i.isLt; simp only [nTapes] at this; omega⟩

@[simp] theorem kind_idx (t : Tape kA ops m) : kind t.idx = t := by
  rcases t with i | o | o | _ | _ | j <;> unfold kind Tape.idx <;> dsimp only <;> split_ifs <;>
    first | omega | rfl | (congr 1; ext; simp; try omega)

/-! ### Configurations and actions through tape names -/

/-- A configuration of the inlined machine, its tapes given by name. -/
def mkR {S : Type} {x : List Bool} (q : Option S) (ip : Fin (x.length + 2))
    (F : Tape kA ops m → ℤ → Option Bool) (P : Tape kA ops m → ℤ) (out : List Bool) :
    Config (nTapes kA ops m) Bool S (Fin 0) x where
  tapes := ⟨q, ip, fun i => F (kind i), fun i => P (kind i), out⟩

/-- An action of the inlined machine, its tape actions given by name. -/
def mkAct {S : Type} (d : SignType) (W : Tape kA ops m → Option (Option Bool) × SignType)
    (out : Option Bool) (q : Option S) : Turing.Action (nTapes kA ops m) Bool S :=
  ⟨d, fun i => W (kind i), out, q⟩

/-- An ordinary instruction of a machine without channels. -/
def stepR {n : ℕ} {S : Type} (a : Turing.Action n Bool S) : MultiTapeMachine.Action n Bool S (Fin 0) :=
  .step a (fun _ => none) (fun _ => 0)

/-- The effect of an optional write on a tape. -/
def wr (f : ℤ → Option Bool) (p : ℤ) : Option (Option Bool) → ℤ → Option Bool
  | none => f
  | some b => Function.update f p b

@[simp] theorem wr_none (f : ℤ → Option Bool) (p : ℤ) : wr f p none = f := rfl

/-- No tape action. -/
def noop : Tape kA ops m → Option (Option Bool) × SignType := fun _ => (none, 0)

/-- Act on one tape only. -/
def mv1 (t : Tape kA ops m) (b : Option (Option Bool)) (d : SignType) :
    Tape kA ops m → Option (Option Bool) × SignType :=
  fun t' => if t' = t then (b, d) else (none, 0)

theorem step_mkR {S : Type} {x : List Bool} (q : Option S) (ip : Fin (x.length + 2))
    (F : Tape kA ops m → ℤ → Option Bool) (P : Tape kA ops m → ℤ) (out : List Bool)
    (d : SignType) (W : Tape kA ops m → Option (Option Bool) × SignType) (o : Option Bool)
    (q' : Option S) :
    (mkR q ip F P out).step (mkAct d W o q') (fun _ => none) (fun _ => 0) =
      mkR q' (moveInputPos ip d) (fun t => wr (F t) (P t) (W t).1) (fun t => P t + (W t).2)
        (out ++ o.toList) := by
  refine Config.ext ?_ (funext fun o => o.elim0)
  refine Cfg.ext rfl rfl ?_ rfl rfl
  funext i
  simp only [Config.step, Turing.Action.apply, mkR, mkAct]
  cases (W (kind i)).1 <;> rfl

@[simp] theorem mkR_symbol {S : Type} {x : List Bool} (q : Option S) (ip : Fin (x.length + 2))
    (F : Tape kA ops m → ℤ → Option Bool) (P : Tape kA ops m → ℤ) (out : List Bool)
    (t : Tape kA ops m) :
    (mkR q ip F P out).tapes.workTapeSymbols t.idx = F t (P t) := by
  simp [Cfg.workTapeSymbols, mkR]

@[simp] theorem mkR_state {S : Type} {x : List Bool} (q : Option S) (ip : Fin (x.length + 2))
    (F : Tape kA ops m → ℤ → Option Bool) (P : Tape kA ops m → ℤ) (out : List Bool) :
    (mkR q ip F P out).tapes.state = q := rfl

@[simp] theorem mkR_output {S : Type} {x : List Bool} (q : Option S) (ip : Fin (x.length + 2))
    (F : Tape kA ops m → ℤ → Option Bool) (P : Tape kA ops m → ℤ) (out : List Bool) :
    (mkR q ip F P out).tapes.output = out := rfl

theorem mkR_workTapes {S : Type} {x : List Bool} (q : Option S) (ip : Fin (x.length + 2))
    (F : Tape kA ops m → ℤ → Option Bool) (P : Tape kA ops m → ℤ) (out : List Bool)
    (t : Tape kA ops m) :
    (mkR q ip F P out).tapes.workTapes t.idx = F t := by
  simp [mkR]

/-- The input symbol depends only on the input head. -/
theorem inputSymbol_congr {k k' : ℕ} {S S' : Type} {x : List Bool} {c : Cfg k Bool S x}
    {c' : Cfg k' Bool S' x} (h : c.inputPos = c'.inputPos) : c.inputSymbol = c'.inputSymbol := by
  unfold Cfg.inputSymbol
  simp only [h]

/-- On the empty input every symbol read is blank. -/
theorem inputSymbol_nil {k : ℕ} {S : Type} (c : Cfg k Bool S []) : c.inputSymbol = none := by
  unfold Cfg.inputSymbol
  have := c.inputPos.isLt
  simp only [List.length_nil] at this ⊢
  split_ifs with h1 h2
  · rfl
  · rfl
  · exfalso; apply h2; have : c.inputPos.val ≠ 0 := fun h => h1 (Fin.ext h); omega

/-! ### Flags and control states -/

/-- The control phases of a query. -/
inductive QStep where
  | cleanStart | seekR | seekL | toEnd | eraseL | rewQ0 | rewQ | qToEnd | qErase
  deriving DecidableEq

instance : Fintype QStep :=
  ⟨⟨(([.cleanStart, .seekR, .seekL, .toEnd, .eraseL, .rewQ0, .rewQ, .qToEnd, .qErase] :
      List QStep) : Multiset QStep), by decide⟩, fun x => by cases x <;> decide⟩

/-- The flag of a channel: its answer is empty, or (when the head reads a blank) the head is left
or right of the answer. -/
inductive AFlag where
  | empty | left | right
  deriving DecidableEq

instance : Fintype AFlag :=
  ⟨⟨(([.empty, .left, .right] : List AFlag) : Multiset AFlag), by decide⟩,
    fun x => by cases x <;> decide⟩

@[simp] theorem QStep.card : Fintype.card QStep = 9 := rfl
@[simp] theorem AFlag.card : Fintype.card AFlag = 3 := rfl

variable {SA : Type} (H : Fin ops → Routine (m + 3))

/-- The control of the simulation: the state of the simulated machine, the channel flags, and the
phase of the query in progress, if any. -/
abbrev Ctl (SA : Type) (H : Fin ops → Routine (m + 3)) : Type :=
  (SA × (Fin ops → AFlag)) × Option (Σ o : Fin ops, QStep ⊕ (H o).State)

/-- The control states: the preparation, then the simulation. -/
abbrev RState (SA : Type) (H : Fin ops → Routine (m + 3)) (T : ℕ) (w : List Bool) : Type :=
  Fin (2 * w.length + T + 1) ⊕ Ctl SA H

/-! ### The tapes of the handler -/

/-- The tape of the inlined machine on which tape `j` of the handler of `o` runs. -/
def hTape (o : Fin ops) (j : Fin (m + 3)) : Tape kA ops m :=
  if h0 : j.val = 0 then .qry o
  else if h1 : j.val = 1 then .ans o
  else if h2 : j.val = 2 then .st
  else .scr ⟨j.val - 3, by omega⟩

/-- The handler tape that runs on a tape of the inlined machine, if any. -/
def hPre (o : Fin ops) : Tape kA ops m → Option (Fin (m + 3))
  | .qry o' => if o' = o then some 0 else none
  | .ans o' => if o' = o then some 1 else none
  | .st => some 2
  | .scr j => some ⟨j.val + 3, by omega⟩
  | _ => none

@[simp] theorem hPre_hTape (o : Fin ops) (j : Fin (m + 3)) :
    hPre o (hTape (kA := kA) o j) = some j := by
  unfold hTape
  split_ifs with h0 h1 h2
  · simp [hPre]; ext; simp [h0]
  · simp [hPre]; ext; simp [h1]
  · simp [hPre]; ext; simp [h2]
  · simp only [hPre, Option.some.injEq]; ext; simp; omega

theorem hTape_of_hPre {o : Fin ops} {t : Tape kA ops m} {j : Fin (m + 3)}
    (h : hPre o t = some j) : hTape o j = t := by
  rcases t with i | o' | o' | _ | _ | j' <;> simp only [hPre, reduceCtorEq] at h
  · split_ifs at h with h'; simp only [Option.some.injEq] at h
    subst h h'; simp [hTape]
  · split_ifs at h with h'; simp only [Option.some.injEq] at h
    subst h h'; simp [hTape]
  · simp only [Option.some.injEq] at h; subst h; simp [hTape, Nat.mod_eq_of_lt (show 2 < m + 3 by omega)]
  · simp only [Option.some.injEq] at h; subst h; simp [hTape]

/-! ### The transitions -/

section Machine

variable (M : MultiTapePTM kA Bool SA (Fin ops)) (T : ℕ) (w : List Bool)

/-- The simulation state `(q, fl)`. -/
def simS (q : SA) (fl : Fin ops → AFlag) : RState SA H T w := .inr ((q, fl), none)

/-- A query state. -/
def qS (q : SA) (fl : Fin ops → AFlag) (o : Fin ops) (ph : QStep) : RState SA H T w :=
  .inr ((q, fl), some ⟨o, .inl ph⟩)

/-- A handler state. -/
def hS (q : SA) (fl : Fin ops → AFlag) (o : Fin ops) (h : (H o).State) : RState SA H T w :=
  .inr ((q, fl), some ⟨o, .inr h⟩)

/-- Instruction `i` of the preparation: write `w` on `st` and rewind it, then write the clock and
step back onto its last cell. -/
def prepAct (i : Fin (2 * w.length + T + 1)) :
    Turing.Action (nTapes kA ops m) Bool (RState SA H T w) :=
  let next : Option (RState SA H T w) :=
    if h : i.val + 1 < 2 * w.length + T + 1 then some (.inl ⟨i.val + 1, h⟩)
    else some (simS H T w M.initial (fun _ => .empty))
  if h : i.val < w.length then mkAct 0 (mv1 .st (some (some w[i.val])) 1) none next
  else if i.val < 2 * w.length then mkAct 0 (mv1 .st none (-1)) none next
  else if i.val < 2 * w.length + T then mkAct 0 (mv1 .clock (some (some true)) 1) none next
  else mkAct 0 (mv1 .clock none (-1)) none next

/-- The tape actions of a simulated ordinary step. -/
def simW (fl : Fin ops → AFlag) (act : Turing.Action kA Bool SA) (sy : Fin ops → Option Bool)
    (mv : Fin ops → SignType) : Tape kA ops m → Option (Option Bool) × SignType
  | .work i => act.workTapes i
  | .qry o => match sy o with
    | some b => (some (some b), 1)
    | none => (none, 0)
  | .ans o => (none, if fl o = .empty then 0 else mv o)
  | .clock => (none, -1)
  | .st => (none, 0)
  | .scr _ => (none, 0)

/-- The flags after a simulated ordinary step, from the symbols read on the answer tapes. -/
def newFl (fl : Fin ops → AFlag) (rd : Fin ops → Option Bool) (mv : Fin ops → SignType)
    (o : Fin ops) : AFlag :=
  match fl o with
  | .empty => .empty
  | f => if rd o = none then f else if mv o = -1 then .left else .right

/-- A simulation step: halt if the clock is exhausted, otherwise run one instruction of `M`. -/
def simAct (q : SA) (fl : Fin ops → AFlag) (inp : Option Bool)
    (work : Fin (nTapes kA ops m) → Option Bool) (bit : Bool) :
    Turing.Action (nTapes kA ops m) Bool (RState SA H T w) :=
  if work (Tape.clock (kA := kA) (ops := ops) (m := m)).idx ≠ some true then
    mkAct 0 noop none none
  else
    match M.tr q inp (fun i => work (Tape.work i).idx) (fun o => work (Tape.ans o).idx) bit with
    | .step act sy mv => mkAct act.inputTape (simW fl act sy mv) act.output
        (act.state.map fun q' => simS H T w q'
          (newFl fl (fun o => work (Tape.ans (kA := kA) (m := m) o).idx) mv))
    | .query o nx => mkAct 0 (mv1 .clock none (-1)) none (some (qS H T w nx fl o .cleanStart))

/-- A step of a query phase. -/
def qAct (q : SA) (fl : Fin ops → AFlag) (o : Fin ops) (ph : QStep)
    (work : Fin (nTapes kA ops m) → Option Bool) :
    Turing.Action (nTapes kA ops m) Bool (RState SA H T w) :=
  let a := work (Tape.ans o).idx
  let qs := work (Tape.qry o).idx
  let go (ph' : QStep) : Option (RState SA H T w) := some (qS H T w q fl o ph')
  match ph with
  | .cleanStart =>
    if fl o = .empty then mkAct 0 noop none (go .rewQ0)
    else if a ≠ none then mkAct 0 (mv1 (.ans o) none 1) none (go .toEnd)
    else if fl o = .left then mkAct 0 (mv1 (.ans o) none 1) none (go .seekR)
    else mkAct 0 (mv1 (.ans o) none (-1)) none (go .seekL)
  | .seekR =>
    if a = none then mkAct 0 (mv1 (.ans o) none 1) none (go .seekR)
    else mkAct 0 (mv1 (.ans o) none 1) none (go .toEnd)
  | .seekL =>
    if a = none then mkAct 0 (mv1 (.ans o) none (-1)) none (go .seekL)
    else mkAct 0 (mv1 (.ans o) (some none) (-1)) none (go .eraseL)
  | .toEnd =>
    if a ≠ none then mkAct 0 (mv1 (.ans o) none 1) none (go .toEnd)
    else mkAct 0 (mv1 (.ans o) none (-1)) none (go .eraseL)
  | .eraseL =>
    if a ≠ none then mkAct 0 (mv1 (.ans o) (some none) (-1)) none (go .eraseL)
    else mkAct 0 (mv1 (.ans o) none 1) none (go .rewQ0)
  | .rewQ0 => mkAct 0 (mv1 (.qry o) none (-1)) none (go .rewQ)
  | .rewQ =>
    if qs ≠ none then mkAct 0 (mv1 (.qry o) none (-1)) none (go .rewQ)
    else mkAct 0 (mv1 (.qry o) none 1) none (some (hS H T w q fl o (H o).machine.initial))
  | .qToEnd =>
    if qs ≠ none then mkAct 0 (mv1 (.qry o) none 1) none (go .qToEnd)
    else mkAct 0 (mv1 (.qry o) none (-1)) none (go .qErase)
  | .qErase =>
    if qs ≠ none then mkAct 0 (mv1 (.qry o) (some none) (-1)) none (go .qErase)
    else mkAct 0 (mv1 (.qry o) none 1) none
      (some (simS H T w q (Function.update fl o (if a = none then .empty else .right))))

/-- The tape actions of a handler instruction. -/
def hW (o : Fin ops) (a : Turing.Action (m + 3) Bool (H o).State) :
    Tape kA ops m → Option (Option Bool) × SignType :=
  fun t => match hPre o t with
    | some j => a.workTapes j
    | none => (none, 0)

/-- A step of the handler of `o`; when it halts, erase the query. -/
def hAct (q : SA) (fl : Fin ops → AFlag) (o : Fin ops) (h : (H o).State)
    (work : Fin (nTapes kA ops m) → Option Bool) (bit : Bool) :
    MultiTapeMachine.Action (nTapes kA ops m) Bool (RState SA H T w) (Fin 0) :=
  match (H o).machine.tr h none (fun j => work (hTape o j).idx) (fun e => e.elim) bit with
  | .step a _ _ => stepR (mkAct 0 (hW H o a) none
      (match a.state with
        | none => some (qS H T w q fl o .qToEnd)
        | some h' => some (hS H T w q fl o h')))
  | .query e _ => e.elim

/-- **The inlined machine.** -/
def machine : MultiTapePTM (nTapes kA ops m) Bool (RState SA H T w) (Fin 0) where
  initial := .inl ⟨0, by omega⟩
  tr q inp work _ := fun bit => match q with
    | .inl i => stepR (prepAct H M T w i)
    | .inr ((q, fl), none) => stepR (simAct H M T w q fl inp work bit)
    | .inr ((q, fl), some ⟨o, .inl ph⟩) => stepR (qAct H T w q fl o ph work)
    | .inr ((q, fl), some ⟨o, .inr h⟩) => hAct H T w q fl o h work bit

end Machine

end SigabaNeo.Inline
