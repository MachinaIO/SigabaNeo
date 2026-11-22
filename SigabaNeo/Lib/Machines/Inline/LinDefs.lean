import SigabaNeo.Lib.Machines.Inline.LinSim

/-!
# Inlining an oracle handler with a short preparation: the machine

`Inline.machine` writes the unary clock of `T` cells with `T` straight-line states, so its number of
states, and with it its description length, grows with `T`. `Inline.machineLin` writes the clock
with `h + 4` states, where `h` is the number of digits of `T` in base `B = 2 ^ (kA + 1)`, `kA` the
number of work tapes of the simulated machine (`clockDigits`), and starts the handler state blank.

## The preparation

The `kA` work tapes of the simulated machine and the `st` tape (all blank at the start, and again at
the end of the preparation) serve as `kA + 1` parallel tracks: cell `z` of the tracks holds the
digit `z` of a counter, its bit `i` on track `i` (`trk i`). The tracks are read as one digit
(`readDigit`) and written as one digit (`tW`) in one step.

* `W j` (`j < h`): write the digit `j` of `T` and move right; `W h`: step back onto the last digit;
* `back`: move left to the start of the counter (the first blank cell of `st` on the left), then
  step right onto digit `0`, and decrement;
* `dec`: decrement the counter: a digit `0` becomes `B - 1` (move right, borrow); a digit `d > 0`
  becomes `d - 1`, a `1` is appended to the clock, and the head goes back; if the borrow runs past
  the last digit the counter was `0`: the clock holds `T` cells, and
* `erase`: the counter is erased leftwards, then the heads go back to the start, the clock head
  steps back onto the last cell of the clock, and the simulation starts (`ctl0`).

The simulation, query and handler phases are those of `Inline.machine` (through `Inline.simM`).
-/

namespace SigabaNeo.Inline

open Cslib Turing MultiTapeMachine

/-- The phases of the counting loop. -/
inductive LStep where
  | back | dec | erase
  deriving DecidableEq

instance : Fintype LStep :=
  ⟨⟨(([.back, .dec, .erase] : List LStep) : Multiset LStep), by decide⟩,
    fun x => by cases x <;> decide⟩

@[simp] theorem LStep.card : Fintype.card LStep = 3 := rfl

/-- The base of the counter: a digit is a column of `kA + 1` bits. -/
abbrev baseB (kA : ℕ) : ℕ := 2 ^ (kA + 1)

/-- The digits of the clock `T` in base `baseB kA`, least significant first. -/
def clockDigits (kA T : ℕ) : List ℕ := Nat.digits (baseB kA) T

/-- The control states: the writing of the digits, the counting loop, the simulation. -/
abbrev LState (SA : Type) {ops m : ℕ} (H : Fin ops → Routine (m + 3)) (h : ℕ) : Type :=
  (Fin (h + 1) ⊕ LStep) ⊕ Ctl SA H

variable {kA ops m : ℕ}

/-- The track of bit `i`: the work tapes of the simulated machine, then `st`. -/
def trk (i : Fin (kA + 1)) : Tape kA ops m :=
  if h : i.val < kA then .work ⟨i, h⟩ else .st

/-- The digit under the track heads (a blank reads as `0`). -/
def readDigit (work : Fin (nTapes kA ops m) → Option Bool) : ℕ :=
  ∑ i : Fin (kA + 1), (if work (trk (ops := ops) (m := m) i).idx = some true then 1 else 0) * 2 ^ (i : ℕ)

/-- Act on the tracks (`b`: no write, erase, or write a digit; `d`: the move) and on the clock. -/
def tW (b : Option (Option ℕ)) (d : SignType) (clk : Option (Option Bool) × SignType) :
    Tape kA ops m → Option (Option Bool) × SignType
  | .work i => (b.map (Option.map fun e => e.testBit i), d)
  | .st => (b.map (Option.map fun e => e.testBit kA), d)
  | .clock => clk
  | _ => (none, 0)

section Machine

variable {SA : Type} (H : Fin ops → Routine (m + 3)) (M : MultiTapePTM kA Bool SA (Fin ops))

/-- A state of the writing phase. -/
def wSt (l : List ℕ) (j : Fin (l.length + 1)) : LState SA H l.length := .inl (.inl j)

/-- A state of the counting loop. -/
def lSt (l : List ℕ) (ph : LStep) : LState SA H l.length := .inl (.inr ph)

/-- Instruction `j` of the writing phase. -/
def wAct (l : List ℕ) (j : Fin (l.length + 1)) :
    Turing.Action (nTapes kA ops m) Bool (LState SA H l.length) :=
  if hj : j.val < l.length then
    mkAct 0 (tW (some (some l[j.val])) 1 (none, 0)) none (some (wSt H l ⟨j.val + 1, by omega⟩))
  else mkAct 0 (tW none (-1) (none, 0)) none (some (lSt H l .back))

/-- A step of the counting loop. -/
def lAct (l : List ℕ) (ph : LStep) (work : Fin (nTapes kA ops m) → Option Bool) :
    Turing.Action (nTapes kA ops m) Bool (LState SA H l.length) :=
  match ph with
  | .back =>
    if work (Tape.st (kA := kA) (ops := ops) (m := m)).idx = none then
      mkAct 0 (tW none 1 (none, 0)) none (some (lSt H l .dec))
    else mkAct 0 (tW none (-1) (none, 0)) none (some (lSt H l .back))
  | .dec =>
    if work (Tape.st (kA := kA) (ops := ops) (m := m)).idx = none then
      mkAct 0 (tW none (-1) (none, 0)) none (some (lSt H l .erase))
    else if readDigit work = 0 then
      mkAct 0 (tW (some (some (baseB kA - 1))) 1 (none, 0)) none (some (lSt H l .dec))
    else
      mkAct 0 (tW (some (some (readDigit work - 1))) (-1) (some (some true), 1)) none
        (some (lSt H l .back))
  | .erase =>
    if work (Tape.st (kA := kA) (ops := ops) (m := m)).idx = none then
      mkAct 0 (tW none 1 (none, -1)) none (some (.inr (ctl0 H M)))
    else mkAct 0 (tW (some none) (-1) (none, 0)) none (some (lSt H l .erase))

/-- **The inlined machine with a short preparation**, for the clock `T`. -/
def machineLin (T : ℕ) :
    MultiTapePTM (nTapes kA ops m) Bool (LState SA H (clockDigits kA T).length) (Fin 0) where
  initial := wSt H (clockDigits kA T) ⟨0, by omega⟩
  tr q inp work ans := fun bit => match q with
    | .inl (.inl j) => stepR (wAct H (clockDigits kA T) j)
    | .inl (.inr ph) => stepR (lAct H M (clockDigits kA T) ph work)
    | .inr c => ((simM H M T []).tr c inp work ans bit).mapState Sum.inr

end Machine

end SigabaNeo.Inline
