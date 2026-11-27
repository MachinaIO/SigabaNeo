import SigabaNeo.Trusted.Benchmark
import SigabaNeoStd.Machines.FromPolyTime
import SigabaNeoStd.Machines.AlmostConst
import Mathlib.Data.Set.Finite.Basic

/-!
# Bootstrap fixtures: shared pieces

BOOTSTRAP FIXTURES, not research benchmarks. They exercise the certified-generator gate
(`SigabaNeo.Trusted.Benchmark`, `SigabaNeo.Trusted.GeneratorCheck`) on tiny families whose tasks
are trivially solved.

* `Fixture.Word`: a bit word of at most `Word.maxLen` bits, serialized as itself.
* `Fixture.haltMachine`: the explicit machine that halts at once: a 0-tape, 1-state cslib
  machine with the clock `0`. Its output is the empty word (`haltMachine_run`) and its cost is
  `30` (`haltMachine_cost`: no steps, and a table of `6 · 1 · 3^0 · 3^0` entries of
  `entryBits 0 1 0 = 5` bits).
* `Fixture.exists_const_machine`: a deterministic machine that outputs a fixed word on every input
  (a probe for diversity proofs).
-/

namespace SigabaNeo.Benchmark.Fixture

open Cslib Turing

/-- The longest word of a task. -/
def Word.maxLen : ℕ := 128

/-- A bit word of at most `Word.maxLen` bits. -/
structure Word where
  /-- The bits. -/
  bits : List Bool
  /-- They are bounded. -/
  bounded : bits.length ≤ Word.maxLen

namespace Word

theorem ext' {x y : Word} (h : x.bits = y.bits) : x = y := by
  cases x; cases y; cases h; rfl

/-- The serialization: the bits themselves. -/
def encode (x : Word) : List Bool := x.bits

/-- Words of at most `maxLen` bits are tasks. -/
def decode (w : List Bool) : Option Word :=
  if h : w.length ≤ maxLen then some ⟨w, h⟩ else none

theorem decode_encode (x : Word) : decode (encode x) = some x := by
  simp [decode, encode, x.bounded]

end Word

/-- The 0-tape, 1-state machine that halts at once. -/
def haltTM : MultiTapeTM 0 Bool Unit :=
  MultiTapeTM.ofTr () fun _ _ _ => ⟨0, Fin.elim0, none, none⟩

/-- `haltTM` with the clock `0`. -/
noncomputable def haltMachine : Machine := Machine.ofTM haltTM 0

/-- It outputs the empty word. -/
theorem haltMachine_run (x : List Bool) : haltMachine.run x = PMF.pure [] := by
  rw [haltMachine, Machine.run_ofTM]
  rfl

theorem haltMachine_deterministic : haltMachine.Deterministic :=
  Machine.deterministic_ofTM _ _

/-- Its cost: `0` steps and a description of `6 · 1 · 1 · 1 · 5 = 30` bits. -/
theorem haltMachine_cost : haltMachine.cost = 30 := by
  simp [haltMachine, Machine.ofTM, Machine.cost, Machine.descLen, Machine.entryBits]

/-- A deterministic machine that outputs `w` on every input. -/
theorem exists_const_machine (w : List Bool) :
    ∃ M : Machine, M.Deterministic ∧ ∀ x, M.run x = PMF.pure w :=
  Machine.exists_of_almostConst (f := fun _ : List Bool => w)
    (encIn := Function.Embedding.refl _) (encOut := Function.Embedding.refl _)
    ⟨w, by simp⟩

/-- No tuple of one variable is encoded by the empty word. -/
theorem decodeTuple_one_nil : decodeTuple 1 [] = [[]] := by
  have hn : ¬ ∃ xs : List (List Bool), xs.length = 1 ∧ encodeTuple xs = [] := by
    rintro ⟨xs, hl, he⟩
    match xs, hl with
    | [x], _ =>
      have := congrArg List.length he
      simp [encodeTuple, MultiTapeTM.length_frame] at this
  simp only [decodeTuple, hn, dite_false]
  rfl

/-- The output law of a one-output algorithm whose machine has the point output law `pure w`. -/
theorem Impl.run_of_pure {Alg : Type} {sig : Alg → AlgSig} (I : Impl sig) (a : Alg)
    (hout : (sig a).outputs.length = 1) (pw : List Bool) (xs : List (List Bool)) (w : List Bool)
    (hw : (I.machine a).run (encodeTuple (pw :: xs)) = PMF.pure w) :
    I.run a pw xs = PMF.pure (decodeTuple 1 w) := by
  rw [Impl.run, hw, PMF.pure_map, hout]

/-- The solver's target is the solvability of the decoded task. -/
theorem target_iff {F : Family} {bits : List Bool} {x : F.Task} (h : F.decode bits = some x) :
    Target F bits ↔ F.Solvable x := by
  unfold Target
  rw [h]

end SigabaNeo.Benchmark.Fixture
