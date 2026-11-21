import PE

/-!
# Predicate encryption for a date window on a 10-bit attribute

The measured case "Ours: range and regex checks (10-bit attribute)" of Suegami, *Implementing
Predicate Encryption for Branching Programs* (ePrint 2026/2539, Section 7.1, Table 1), as a
concrete predicate encryption primitive (`AdvancedEncryption.PE`). This file is the problem
author's: it fixes the universe and the parameters, and so what a submission must achieve and at
which cost it is measured.

**Attribute.** A calendar date given as two 5-bit symbols, its month and then its day (`Date`);
the attribute has 10 bits, each symbol most significant bit first (`encDate`).

**Required predicates.** For every date window `[a, b]`, where `a ≤ b` are valid dates of the same
year (`Window`), the predicate `accepts w` that is authorized for a date `x` iff both hold:

* Format (the regular-expression check): `x` is a valid date: its month is in `1…12` and its day in
  `1…` the number of days of that month, with 29 days for February (`valid`);
* Range: `a ≤ x ≤ b`, months first and then days (`dateLe`).

For instance, February 30 lies in the window from January 15 to March 15 but is not a valid date
(`feb30_not_accepted`).

**How predicates are represented is not fixed.** The algorithms take predicates in the
implementation's own representation (a circuit, a branching program, …), with the meaning its
`Eval` gives them, as for every `PE`. What this file requires is the proposition `Expressive` of
`PE`: for every window `w`, the implementation has a predicate `C` authorized for exactly the dates
`x` with `accepts w x`. Its correctness and attribute hiding then hold for these predicates, and the
cost is measured for the implementation that supports them.

**Message.** One bit, encoded as itself.

**Parameters.** `λ = 128` and `κ = 128` (the paper targets 128-bit security and proves decryption
fails with probability below `2^{-128}`), and the cost of one run of each algorithm (`q = q_k = 1`),
as Table 1 reports one run of `KeyGen`, `Enc` and `Dec`.
-/

namespace AdvancedEncryption.PE.DateWindow

open SigabaNeo

/-! ### The attribute -/

/-- A 5-bit symbol. -/
abbrev Sym := Fin 32

/-- The 5 bits of a symbol, most significant first. -/
def symBits (s : Sym) : List Bool := List.ofFn fun i : Fin 5 => s.val.testBit (4 - i.val)

/-- Bits read as a number, most significant first. -/
def ofBits (l : List Bool) : ℕ := l.foldl (fun acc b => 2 * acc + b.toNat) 0

theorem ofBits_symBits : ∀ s : Sym, ofBits (symBits s) = s.val := by decide

theorem length_symBits (s : Sym) : (symBits s).length = 5 := by simp [symBits]

theorem symBits_injective : Function.Injective symBits := fun s t h =>
  Fin.ext (by rw [← ofBits_symBits s, ← ofBits_symBits t, h])

/-- A date: its month and its day, as two 5-bit symbols. -/
abbrev Date := Sym × Sym

/-- The 10 bits of a date: the month, then the day. -/
def encDate : Date ↪ List Bool where
  toFun x := symBits x.1 ++ symBits x.2
  inj' x y h := by
    obtain ⟨h1, h2⟩ := List.append_inj h (by rw [length_symBits, length_symBits])
    exact Prod.ext (symBits_injective h1) (symBits_injective h2)

/-- The number of days of a month, with 29 days for February. -/
def daysIn : ℕ → ℕ
  | 2 => 29
  | 4 | 6 | 9 | 11 => 30
  | _ => 31

/-- The format check: the month is in `1…12` and the day in `1…daysIn month`. -/
def valid (x : Date) : Bool :=
  1 ≤ x.1.val && x.1.val ≤ 12 && 1 ≤ x.2.val && x.2.val ≤ daysIn x.1.val

/-- The order of dates: months first, then days. -/
def dateLe (x y : Date) : Bool := x.1 < y.1 || (x.1 = y.1 && x.2 ≤ y.2)

/-! ### The predicate -/

/-- A date window `[a, b]`: valid dates `a ≤ b`. -/
def Window : Type := {w : Date × Date // valid w.1 ∧ valid w.2 ∧ dateLe w.1 w.2}

/-- The key for `w = [a, b]` is authorized for `x` iff `x` is a valid date and `a ≤ x ≤ b`. -/
def accepts (w : Window) (x : Date) : Bool := valid x && dateLe w.1.1 x && dateLe x w.1.2

/-! ### The message -/

/-- A message, one bit, encoded as itself. -/
def encMsg : Bool ↪ List Bool := ⟨fun b => [b], fun _ _ h => List.singleton_inj.mp h⟩

/-! ### The primitive -/

/-- The universe: dates, one-bit messages, and the date-window predicates. The universe is
fixed, so the algorithms are given no description of it. -/
def dateUniverse : Universe where
  Attr := Date
  Msg := Bool
  encAttr := encDate
  encMsg := encMsg
  Req := Window
  req w x := accepts w x = true
  desc := []

/-- `λ = 128`, `κ = 128`, and one run of each algorithm. -/
def params : Params where
  secBits := 128
  corrBits := 128
  runs := 1
  keyRuns := 1

/-- Predicate encryption for a date window on a 10-bit attribute. -/
def primitive : Primitive := AdvancedEncryption.PE dateUniverse params

/-! ### Checks of the definition -/

/-- The window from January 15 to March 15. -/
def jan15mar15 : Window := ⟨((1, 15), (3, 15)), by decide⟩

/-- February 30 lies in the window but is not a valid date. -/
theorem feb30_not_accepted : accepts jan15mar15 (2, 30) = false := by decide

theorem feb29_accepted : accepts jan15mar15 (2, 29) = true := by decide

theorem jan14_not_accepted : accepts jan15mar15 (1, 14) = false := by decide

theorem mar15_accepted : accepts jan15mar15 (3, 15) = true := by decide

theorem month13_not_valid : valid (13, 1) = false := by decide

end AdvancedEncryption.PE.DateWindow
