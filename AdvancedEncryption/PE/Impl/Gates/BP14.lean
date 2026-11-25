import PE.BranchingProgram

/-!
# Branching programs with 14-bit states and 8-bit symbols

The predicate class of the dual-use implementation (`PE/Impl/RingBTVW`), in the concrete form its
proofs use: branching programs of 16 steps on 14-bit states (`State`, the problem's `ProgState`)
over 8-bit symbols (`BP`, `run`, `output`), the 128-bit attribute as 16 symbols (`Attr`,
`encAttr`), and the universe `bpUniverse` whose required predicates are these programs. This is
`PE.BranchingProgram.univ w8` field by field (the width chosen by the implementation is `w8`):
the attributes, messages, encodings and description are definitionally those of `univ w8`, and a
`Program w8` is a `BP` with the same tables (`PE/Impl/RingBTVW/Relaxed.lean`).
-/

namespace AdvancedEncryption.PE.BranchingProgram

open SigabaNeo

/-! ### The attribute -/

/-- An 8-bit symbol. -/
abbrev Sym := Fin 256

/-- A 14-bit state. -/
abbrev State := Fin (2 ^ 14)

theorem state_eq : State = ProgState := rfl

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

/-! ### The universe -/

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

/-! ### Checks of the definition -/

theorem length_encAttr (x : Attr) : (encAttr x).length = 128 := by
  show ((List.ofFn x).flatMap symBits).length = 128
  rw [List.length_flatMap]
  simp [length_symBits]

end AdvancedEncryption.PE.BranchingProgram
