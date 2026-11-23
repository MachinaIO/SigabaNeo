import PE

/-!
# Predicate encryption for branching programs on a 128-bit attribute

Predicate encryption (`AdvancedEncryption.PE`) for the class of branching programs of Definition 2
of Suegami, *Implementing Predicate Encryption for Branching Programs* (ePrint 2026/2539), at
`T = 16` steps, width `w = 2^32`, alphabet `|Σ| = 256` and `ℓ = 16` input symbols, step `i` reading
symbol `i` (`ι(i) = i`). This file is the problem author's: it fixes the universe and the
parameters, and so what a submission must achieve and at which cost it is measured.

**Attribute.** 16 symbols of 8 bits (`Attr`); the attribute has 128 bits, symbol 0 first, each
symbol most significant bit first (`encAttr`).

**Required predicates.** Every branching program `F` (`BP`): 15 transition tables
`State → Sym → State` on 32-bit states and an output table `State → Sym → Bool`. From `z₀ = 0`,
step `i < 15` moves to `z_{i+1} = step i z_i x_i` (`run`); the output bit is the last table at
`(z₁₅, x₁₅)` (`output`). A key for `F` is authorized for `x` iff `F(x) = 0` (as `C(x) = 0` in
BTVW17). The class is closed under complementing `out`, so this choice loses nothing.

**How predicates are represented is not fixed.** As for every `PE`, the algorithms take predicates
in the implementation's own representation with the meaning its `Eval` gives them; this file
requires `Expressive`: for every program `F`, the implementation has a predicate authorized for
exactly the attributes `x` with `F(x) = 0`.

**Message.** One bit, encoded as itself.

**Parameters.** `λ = 128`, `κ = 128`, and the cost of one run of each algorithm.
-/

namespace AdvancedEncryption.PE.BranchingProgram

open SigabaNeo

/-! ### The attribute -/

/-- An 8-bit symbol. -/
abbrev Sym := Fin 256

/-- A 32-bit state. -/
abbrev State := Fin (2 ^ 32)

/-- An attribute: 16 symbols. -/
abbrev Attr := Fin 16 → Sym

/-- The 8 bits of a symbol, most significant first. -/
def symBits (s : Sym) : List Bool := List.ofFn fun i : Fin 8 => s.val.testBit (7 - i.val)

/-- Bits read as a number, most significant first. -/
def ofBits (l : List Bool) : ℕ := l.foldl (fun acc b => 2 * acc + b.toNat) 0

theorem ofBits_symBits : ∀ s : Sym, ofBits (symBits s) = s.val := by decide +kernel

theorem length_symBits (s : Sym) : (symBits s).length = 8 := by simp [symBits]

theorem symBits_injective : Function.Injective symBits := fun s t h =>
  Fin.ext (by rw [← ofBits_symBits s, ← ofBits_symBits t, h])

theorem flatMap_symBits_injective :
    ∀ {l l' : List Sym}, l.flatMap symBits = l'.flatMap symBits → l = l'
  | [], [], _ => rfl
  | [], s :: l', h => by
    have := congrArg List.length h
    simp [length_symBits] at this; omega
  | s :: l, [], h => by
    have := congrArg List.length h
    simp [length_symBits] at this
  | s :: l, s' :: l', h => by
    simp only [List.flatMap_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by rw [length_symBits, length_symBits])
    rw [symBits_injective h1, flatMap_symBits_injective h2]

/-- The 128 bits of an attribute: symbol 0 first. -/
def encAttr : Attr ↪ List Bool where
  toFun x := (List.ofFn x).flatMap symBits
  inj' _ _ h := List.ofFn_injective (flatMap_symBits_injective h)

/-! ### Branching programs -/

/-- A branching program: 15 transition tables and an output table. -/
structure BP where
  /-- The transition table of step `i`. -/
  step : Fin 15 → State → Sym → State
  /-- The output table. -/
  out : State → Sym → Bool

/-- The state before the last step: `z₀ = 0`, `z_{i+1} = step i z_i x_i`. -/
def run (F : BP) (x : Attr) : State :=
  Fin.foldl 15 (fun z i => F.step i z (x i.castSucc)) 0

/-- The output bit `F(x)`: the last table at `(z₁₅, x₁₅)`. -/
def output (F : BP) (x : Attr) : Bool := F.out (run F x) (x (Fin.last 15))

/-! ### The message -/

/-- A message, one bit, encoded as itself. -/
def encMsg : Bool ↪ List Bool := ⟨fun b => [b], fun _ _ h => List.singleton_inj.mp h⟩

/-! ### The primitive -/

/-- The universe: 128-bit attributes, one-bit messages, and the branching programs, a key for `F`
being authorized for `x` iff `F(x) = 0`. The universe is fixed, so the algorithms are given no
description of it. -/
def bpUniverse : Universe where
  Attr := Attr
  Msg := Bool
  encAttr := encAttr
  encMsg := encMsg
  Req := BP
  req F x := output F x = false
  desc := []

/-- `λ = 128`, `κ = 128`, and one run of each algorithm. -/
def params : Params where
  secBits := 128
  corrBits := 128
  runs := 1
  keyRuns := 1

/-- Predicate encryption for branching programs on a 128-bit attribute. -/
def primitive : Primitive := AdvancedEncryption.PE bpUniverse params

/-! ### Checks of the definition -/

theorem length_encAttr (x : Attr) : (encAttr x).length = 128 := by
  show ((List.ofFn x).flatMap symBits).length = 128
  rw [List.length_flatMap]
  simp [length_symBits]

/-- Equality with a fixed string `t`, as an automaton with a dead state: state `0` while the
prefix read so far is that of `t`, state `1` after a mismatch. -/
def eqProg (t : Attr) : BP where
  step i z a := if z = 0 ∧ a = t i.castSucc then 0 else 1
  out z a := !(decide (z = 0) && decide (a = t (Fin.last 15)))

/-- The string `0, 1, …, 15`. -/
def iota16 : Attr := fun i => ⟨i.val, by omega⟩

theorem eqProg_accepts : output (eqProg iota16) iota16 = false := by decide

theorem eqProg_rejects : output (eqProg iota16) (fun _ => 0) = true := by decide

theorem eqProg_rejects_last :
    output (eqProg iota16) (Function.update iota16 (Fin.last 15) 0) = true := by decide

/-- The program that authorizes nothing. -/
def rejectAll : BP where
  step _ _ _ := 0
  out _ _ := true

theorem rejectAll_output (x : Attr) : output rejectAll x = true := rfl

end AdvancedEncryption.PE.BranchingProgram
