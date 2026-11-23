import PE

/-!
# Predicate encryption for branching programs on a 128-bit attribute

Predicate encryption (`AdvancedEncryption.PE`) for the class of branching programs of Definition 2
of Suegami, *Implementing Predicate Encryption for Branching Programs* (ePrint 2026/2539), on a
128-bit attribute, with **14-bit states**, the symbol width chosen by the implementation. This file
is the problem author's: it fixes the universes and the parameters, and so what a submission must
achieve and at which cost it is measured.

**Symbol width.** A width `w : Width` is a number of bits `s` dividing `128`; the attribute is then
`L = 128 / s` symbols of `s` bits (`Attribute w`), symbol `0` first, each symbol most significant
bit first (`encAttribute w`). Whatever the width, the attribute is the same 128-bit string
(`length_encAttribute`). A submission chooses its width `w` and is a submission for
`primitive w`; submissions for different widths are compared by their costs.

**Required predicates.** For the width `w`, every branching program `F : Program w` that reads
symbol `i` at step `i`: `L − 1` transition tables `ProgState → Symbol w → ProgState` on 14-bit
states and an output table `ProgState → Symbol w → Bool`. From `z₀ = 0`, step `i < L − 1` moves to
`z_{i+1} = step i z_i x_i` (`Program.run`); the output bit is the last table at `(z_{L−1}, x_{L−1})`
(`Program.output`). A key for `F` is authorized for `x` iff `F(x) = 0`. The class is closed under
complementing `out`, so this choice loses nothing.

**How predicates are represented is not fixed.** As for every `PE`, the algorithms take predicates
in the implementation's own representation with the meaning its `Eval` gives them; this file
requires `Expressive`: for every program `F`, the implementation has a predicate authorized for
exactly the attributes `x` with `F(x) = 0`.

**Message.** One bit, encoded as itself.

**Parameters.** `λ = 128`, `κ = 128`, and the cost of one run of each algorithm.
-/

namespace AdvancedEncryption.PE.BranchingProgram

open SigabaNeo

/-! ### The symbol width -/

/-- A symbol width: `bits` bits per symbol, dividing `128`. -/
structure Width where
  /-- The bits of a symbol. -/
  bits : ℕ
  dvd : bits ∣ 128
  pos : 0 < bits

namespace Width

/-- The number of symbols: `128 / bits`. -/
def len (w : Width) : ℕ := 128 / w.bits

theorem len_pos (w : Width) : 0 < w.len :=
  Nat.div_pos (Nat.le_of_dvd (by norm_num) w.dvd) w.pos

theorem bits_mul_len (w : Width) : w.bits * w.len = 128 := Nat.mul_div_cancel' w.dvd

end Width

/-- The width of 8 bits: 16 symbols of 8 bits. -/
def w8 : Width := ⟨8, by norm_num, by norm_num⟩

/-! ### The attribute -/

/-- The bits of a state. -/
abbrev stateBits : ℕ := 14

/-- A 14-bit state. -/
abbrev ProgState := Fin (2 ^ stateBits)

/-- A symbol of width `w`. -/
abbrev Symbol (w : Width) := Fin (2 ^ w.bits)

/-- An attribute: `128 / bits` symbols. -/
abbrev Attribute (w : Width) := Fin w.len → Symbol w

/-- The bits of a symbol, most significant first. -/
def symbolBits (w : Width) (a : Symbol w) : List Bool :=
  List.ofFn fun i : Fin w.bits => a.val.testBit (w.bits - 1 - i.val)

theorem length_symbolBits (w : Width) (a : Symbol w) : (symbolBits w a).length = w.bits := by
  simp [symbolBits]

theorem symbolBits_injective (w : Width) : Function.Injective (symbolBits w) := by
  intro a b h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < w.bits
  · have hf := congrFun (List.ofFn_injective h) ⟨w.bits - 1 - j, by omega⟩
    have e : w.bits - 1 - (w.bits - 1 - j) = j := by omega
    simpa only [e] using hf
  · have hK : w.bits ≤ j := Nat.le_of_not_lt hj
    rw [Nat.testBit_lt_two_pow (a.isLt.trans_le (Nat.pow_le_pow_right (by norm_num) hK)),
      Nat.testBit_lt_two_pow (b.isLt.trans_le (Nat.pow_le_pow_right (by norm_num) hK))]

theorem flatMap_symbolBits_injective (w : Width) :
    ∀ {l l' : List (Symbol w)}, l.flatMap (symbolBits w) = l'.flatMap (symbolBits w) → l = l'
  | [], [], _ => rfl
  | [], s :: l', h => by
    have := congrArg List.length h
    simp [length_symbolBits] at this
    have := w.pos; omega
  | s :: l, [], h => by
    have := congrArg List.length h
    simp [length_symbolBits] at this
    have := w.pos; omega
  | s :: l, s' :: l', h => by
    simp only [List.flatMap_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by rw [length_symbolBits, length_symbolBits])
    rw [symbolBits_injective w h1, flatMap_symbolBits_injective w h2]

/-- The 128 bits of an attribute: symbol 0 first. -/
def encAttribute (w : Width) : Attribute w ↪ List Bool where
  toFun x := (List.ofFn x).flatMap (symbolBits w)
  inj' _ _ h := List.ofFn_injective (flatMap_symbolBits_injective w h)

/-! ### Branching programs -/

/-- A branching program for the width `w`: `L − 1` transition tables and an output table. -/
structure Program (w : Width) where
  /-- The transition table of step `i`. -/
  step : Fin (w.len - 1) → ProgState → Symbol w → ProgState
  /-- The output table. -/
  out : ProgState → Symbol w → Bool

namespace Program

variable {w : Width}

/-- The state before the last step: `z₀ = 0`, `z_{i+1} = step i z_i x_i`. -/
def run (F : Program w) (x : Attribute w) : ProgState :=
  Fin.foldl (w.len - 1) (fun z i => F.step i z (x ⟨i.val, by omega⟩)) 0

/-- The output bit `F(x)`: the last table at `(z_{L−1}, x_{L−1})`. -/
def output (F : Program w) (x : Attribute w) : Bool :=
  F.out (F.run x) (x ⟨w.len - 1, by have := w.len_pos; omega⟩)

end Program

/-! ### The message -/

/-- A message, one bit, encoded as itself. -/
def encMsg : Bool ↪ List Bool := ⟨fun b => [b], fun _ _ h => List.singleton_inj.mp h⟩

/-! ### The primitive -/

/-- The universe for the width `w`: 128-bit attributes as `128 / bits` symbols, one-bit messages,
and the branching programs on 14-bit states, a key for `F` being authorized for `x` iff `F(x) = 0`.
The universe is fixed, so the algorithms are given no description of it. -/
def univ (w : Width) : Universe where
  Attr := Attribute w
  Msg := Bool
  encAttr := encAttribute w
  encMsg := encMsg
  Req := Program w
  req F x := F.output x = false
  desc := []

/-- `λ = 128`, `κ = 128`, and one run of each algorithm. -/
def params : Params where
  secBits := 128
  corrBits := 128
  runs := 1
  keyRuns := 1

/-- Predicate encryption for branching programs on a 128-bit attribute with 14-bit states, for
the symbol width `w` chosen by the submission. -/
def primitive (w : Width) : Primitive := AdvancedEncryption.PE (univ w) params

/-! ### Checks of the definition -/

theorem length_encAttribute (w : Width) (x : Attribute w) : (encAttribute w x).length = 128 := by
  show ((List.ofFn x).flatMap (symbolBits w)).length = 128
  rw [List.length_flatMap]
  simp only [length_symbolBits, List.map_ofFn, Function.comp_def, List.sum_ofFn,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [mul_comm]; exact w.bits_mul_len

/-- Equality with a fixed string `t`, as an automaton with a dead state. -/
def eqProg (w : Width) (t : Attribute w) : Program w where
  step i z a := if z = 0 ∧ a = t ⟨i.val, by omega⟩ then 0 else 1
  out z a := !(decide (z = 0) && decide (a = t ⟨w.len - 1, by have := w.len_pos; omega⟩))

/-- The string `0, 1, …, 15` of 8-bit symbols. -/
def iota16 : Attribute w8 := fun i => ⟨i.val, by have := i.isLt; simp [w8, Width.len] at *; omega⟩

theorem eqProg_accepts : (eqProg w8 iota16).output iota16 = false := by decide

theorem eqProg_rejects : (eqProg w8 iota16).output (fun _ => 0) = true := by decide

/-- The program that authorizes nothing. -/
def rejectAll (w : Width) : Program w where
  step _ _ _ := 0
  out _ _ := true

theorem rejectAll_output {w : Width} (x : Attribute w) : (rejectAll w).output x = true := rfl

end AdvancedEncryption.PE.BranchingProgram
