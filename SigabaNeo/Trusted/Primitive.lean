import SigabaNeo.Trusted.Machine
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List

/-!
# Cryptographic primitives

The form of primitives of the Sigaba Neo concept (Section 3.1), described in `docs/PRIMITIVES.md`.
Submissions and the final statement `Spec` are in `SigabaNeo.Trusted.Submission`.

**Vocabulary.** Algorithms and attackers are explicit machines (`Machine ops`,
`SigabaNeo.Trusted.Machine`); an algorithm's worst-case number of steps is at most its clock
`time`. `encodeTuple`, `decodeTuple`: the fixed encoding of the tuple of variables on the input
and output tapes, cslib-frontier's `encList encBits` (each variable framed, then concatenated).

**Primitives (Section 3.1).**

* `AlgSig`: the signature of one algorithm: its name, the names of its input and output variables
  and whether it takes randomness. The types of the variables are not fixed: every variable is a
  bit string, and a primitive fixes an encoding only for the variables its propositions read.
* `Impl sig`: a `Machine` for each algorithm, deterministic where the signature says so.
  `Impl.run impl a pw xs` runs algorithm `a` on the parameters' encoding `pw` followed by the input
  variables `xs`, and decodes its output word into `(sig a).outputs.length` variables (a malformed
  output word decodes to empty variables).
* `Primitive`: a parameter set with its concrete values and their encoding (given to every
  algorithm), a set of algorithms, a set of propositions and a cost function.
-/

namespace SigabaNeo

open Cslib Turing

/-! ### Encoding of tuples of variables -/

/-- The input or output tape of an algorithm holds its variables framed one after another. -/
def encodeTuple (xs : List (List Bool)) : List Bool := MultiTapeTM.encList MultiTapeTM.encBits xs

theorem encodeTuple_injective : Function.Injective encodeTuple :=
  (MultiTapeTM.encList MultiTapeTM.encBits).injective

open Classical in
/-- The `n` variables encoded by a word, or `n` empty variables if the word encodes no tuple of
length `n`. -/
noncomputable def decodeTuple (n : ℕ) (w : List Bool) : List (List Bool) :=
  if h : ∃ xs : List (List Bool), xs.length = n ∧ encodeTuple xs = w then Classical.choose h
  else List.replicate n []

theorem decodeTuple_encodeTuple (xs : List (List Bool)) :
    decodeTuple xs.length (encodeTuple xs) = xs := by
  have h : ∃ ys : List (List Bool), ys.length = xs.length ∧ encodeTuple ys = encodeTuple xs :=
    ⟨xs, rfl, rfl⟩
  unfold decodeTuple
  rw [dite_eq_left h]
  exact encodeTuple_injective (Classical.choose_spec h).2


/-! ### Primitives (Section 3.1) -/

/-- The signature of an algorithm: its name, the names of its input and output variables, and
whether it takes randomness. The types of the variables are not fixed. -/
structure AlgSig where
  /-- Name of the algorithm. -/
  name : String
  /-- Names of the input variables (the parameters come first, and are not listed). -/
  inputs : List String
  /-- Names of the output variables. -/
  outputs : List String
  /-- Whether the algorithm takes a random tape. -/
  randomized : Bool

/-- An implementation: a machine for each algorithm, deterministic unless its signature takes
randomness. Internal parameters chosen by the implementation live in these machines. -/
structure Impl {Alg : Type} (sig : Alg → AlgSig) where
  /-- The machine of each algorithm. -/
  machine : Alg → Machine
  /-- Algorithms that take no randomness are implemented deterministically. -/
  deterministic : ∀ a, (sig a).randomized = false → (machine a).Deterministic

namespace Impl

variable {Alg : Type} {sig : Alg → AlgSig}

/-- Run algorithm `a` on the encoded parameters `pw` and the input variables `xs`; the law of its
output variables. -/
noncomputable def run (impl : Impl sig) (a : Alg) (pw : List Bool) (xs : List (List Bool)) :
    PMF (List (List Bool)) :=
  ((impl.machine a).run (encodeTuple (pw :: xs))).map (decodeTuple (sig a).outputs.length)

end Impl

/-- A cryptographic primitive (Section 3.1): a parameter set with its concrete values, a set of
algorithms, a set of propositions and a cost function. -/
structure Primitive where
  /-- The parameter set. -/
  Params : Type
  /-- The concrete values of the parameters. -/
  params : Params
  /-- The encoding of the parameters, given as input to every algorithm by default. -/
  encodeParams : Params → List Bool
  /-- The algorithms. -/
  Alg : Type
  /-- The signature of each algorithm. -/
  sig : Alg → AlgSig
  /-- The propositions. -/
  PropIndex : Type
  /-- The content of each proposition, about an implementation at the given parameters. -/
  prop : PropIndex → Params → Impl sig → Prop
  /-- How the cost of an implementation is measured. -/
  cost : Params → Impl sig → ℕ

end SigabaNeo
