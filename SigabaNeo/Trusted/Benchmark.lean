import SigabaNeo.Trusted.Submission

/-!
# Certified task generators (benchmark families)

TRUSTED. The vocabulary of certified curricula: task families, the certificate a task generator
must prove, and the statement a solver proves for a sampled task. It adds definitions only, and
changes none of the existing ones (`Machine`, `Primitive`, `Assumption`, `Submission`, `Spec`).

* `Seed k`: `k` seed bits.
* `Family`: a reviewed task family: a type of task descriptors with an executable canonical
  serialization (`encode`, `decode`, `decode_encode`), the exact statement that a task is solved
  (`Solvable`) and the exact relation saying that two tasks are the same problem (`SameProblem`, an
  equivalence).
* `Certified F L k h gen`: the generator `gen` has `L > 0` levels, `h ≤ k`, every task it generates
  at every level and seed is solvable, and at every level and seed the seeds that give the same
  problem are at most a `2^-h` fraction of all seeds (`2^h · |fiber| ≤ 2^k`). The uniform seed then
  has at least `h` bits of min-entropy modulo `SameProblem` (`SigabaNeoStd.Benchmarks.Entropy`).
  `L`, `k` and `h` are fixed by the trusted policy, not by the generator.
* `Target F bits`: what a solver proves for the sampled descriptor `bits`: it decodes to a task,
  and that task is solvable.

Two kinds of reviewed adapters give families:

* `DesignAdapter`: a task is a concrete primitive (a common carrier of algorithms and
  propositions, with parameters that depend on the task), a registry with pinned strengths and a
  cost cap. It is solved by a submission with `Spec`, valid premises and claimed cost at most the
  cap (`AcceptDesign`). Two tasks are the same problem when the same implementations satisfy all
  their propositions (`SameDesign`).
* `AttackAdapter`: a task is a `Problem` with a bound `c` (and, possibly, the strength `k > c` it
  claims to refute). It is solved by an explicit machine with a positive gain and
  `cost ≤ 2^c · gain` (`AcceptAttack`, which is `Assumption.Attack` on an assumption's problem,
  `exists_acceptAttack_iff`). Two tasks are the same problem when every machine has the same gain
  on both (`SameAttack`).
-/

namespace SigabaNeo.Benchmark

/-- `k` seed bits. -/
abbrev Seed (k : ℕ) := Fin k → Bool

/-- A reviewed task family: descriptors with an executable canonical serialization, the statement
that a task is solved, and the equivalence "same problem". -/
structure Family where
  /-- The task descriptors. -/
  Task : Type
  /-- The canonical serialization of a descriptor. -/
  encode : Task → List Bool
  /-- Its inverse on canonical words. -/
  decode : List Bool → Option Task
  /-- Decoding inverts encoding. -/
  decode_encode : ∀ x, decode (encode x) = some x
  /-- The statement that the task is solved. -/
  Solvable : Task → Prop
  /-- Two descriptors are the same problem. -/
  SameProblem : Task → Task → Prop
  /-- `SameProblem` is an equivalence. -/
  sameProblem_equiv : Equivalence SameProblem

/-- The certificate of a generator with `L` levels and `k` seed bits, at diversity `h`: at least
one level, `h ≤ k`, every generated task is solvable, and at every level and seed at most
`2^(k-h)` seeds give the same problem. -/
def Certified (F : Family) (L k h : ℕ) (gen : Fin L → Seed k → F.Task) : Prop :=
  0 < L ∧ h ≤ k ∧ (∀ d r, F.Solvable (gen d r)) ∧
    ∀ d r, 2 ^ h * Nat.card {s : Seed k // F.SameProblem (gen d r) (gen d s)} ≤ 2 ^ k

/-- What a solver proves for the sampled descriptor `bits`: it is a task, and the task is
solvable. -/
def Target (F : Family) (bits : List Bool) : Prop :=
  match F.decode bits with
  | some x => F.Solvable x
  | none => False

/-! ### Design tasks -/

/-- A reviewed family of design tasks: a common carrier of algorithms, parameters and
propositions; each task fixes the parameters, and the family pins the registry, the strengths and
the cost cap of each task. -/
structure DesignAdapter where
  /-- The task descriptors. -/
  Task : Type
  /-- The canonical serialization of a descriptor. -/
  encode : Task → List Bool
  /-- Its inverse on canonical words. -/
  decode : List Bool → Option Task
  /-- Decoding inverts encoding. -/
  decode_encode : ∀ x, decode (encode x) = some x
  /-- The algorithms (common to all tasks). -/
  Alg : Type
  /-- Their signatures. -/
  sig : Alg → AlgSig
  /-- The parameter set. -/
  Params : Type
  /-- The parameters of a task. -/
  params : Task → Params
  /-- The encoding of the parameters given to every algorithm. -/
  encodeParams : Params → List Bool
  /-- The propositions. -/
  PropIndex : Type
  /-- Their content. -/
  prop : PropIndex → Params → Impl sig → Prop
  /-- The cost function. -/
  cost : Params → Impl sig → ℕ
  /-- The admitted assumptions. -/
  registry : Registry
  /-- Their pinned strengths. -/
  strength : registry.Strength
  /-- The cost cap of each task. -/
  cap : Task → ℕ

namespace DesignAdapter

variable (A : DesignAdapter)

/-- The primitive of a task. -/
def primitive (x : A.Task) : Primitive where
  Params := A.Params
  params := A.params x
  encodeParams := A.encodeParams
  Alg := A.Alg
  sig := A.sig
  PropIndex := A.PropIndex
  prop := A.prop
  cost := A.cost

/-- A submission solves a task: `Spec`, valid premises at the pinned strengths, and claimed cost
at most the cap. -/
def AcceptDesign (x : A.Task) (u : Submission (A.primitive x) A.registry) : Prop :=
  Spec (A.primitive x) A.registry u ∧ u.Valid A.strength ∧ u.N ≤ A.cap x

/-- A task is solvable: some submission solves it. -/
def SolvableDesign (x : A.Task) : Prop := ∃ u, A.AcceptDesign x u

/-- An implementation satisfies every proposition of the task (the semantic content, without
premises, cost or cap). -/
def SemanticAccept (x : A.Task) (I : Impl A.sig) : Prop := ∀ i, A.prop i (A.params x) I

/-- Two design tasks are the same problem when the same implementations satisfy them. -/
def SameDesign (x y : A.Task) : Prop := ∀ I, A.SemanticAccept x I ↔ A.SemanticAccept y I

theorem sameDesign_equiv : Equivalence A.SameDesign where
  refl _ _ := Iff.rfl
  symm h I := (h I).symm
  trans h h' I := (h I).trans (h' I)

/-- The family of the design tasks. -/
def family : Family where
  Task := A.Task
  encode := A.encode
  decode := A.decode
  decode_encode := A.decode_encode
  Solvable := A.SolvableDesign
  SameProblem := A.SameDesign
  sameProblem_equiv := A.sameDesign_equiv

end DesignAdapter

/-! ### Cryptanalysis tasks -/

/-- A reviewed family of attack tasks: each task is a problem with the bound `c` an attack must
meet, and possibly the strength `k` it claims to refute. -/
structure AttackAdapter where
  /-- The task descriptors. -/
  Task : Type
  /-- The canonical serialization of a descriptor. -/
  encode : Task → List Bool
  /-- Its inverse on canonical words. -/
  decode : List Bool → Option Task
  /-- Decoding inverts encoding. -/
  decode_encode : ∀ x, decode (encode x) = some x
  /-- The problem given to the attacker. -/
  problem : Task → Problem
  /-- The bound `c`: an attack has `cost ≤ 2^c · gain`. -/
  bound : Task → ℕ
  /-- The strength `k` the task claims to refute, if any. -/
  refutes : Task → Option ℕ

namespace AttackAdapter

variable (A : AttackAdapter)

/-- A machine solves a task: positive gain and `cost ≤ 2^c · gain`. -/
def AcceptAttack (x : A.Task) (M : Machine) : Prop :=
  0 < (A.problem x).gain M ∧ (M.cost : ℝ) ≤ 2 ^ A.bound x * (A.problem x).gain M

/-- A task is solvable: its refutation claim, if any, is strict (`c < k`), and some machine
solves it. -/
def SolvableAttack (x : A.Task) : Prop :=
  (∀ k, A.refutes x = some k → A.bound x < k) ∧ ∃ M, A.AcceptAttack x M

/-- Two attack tasks are the same problem when every machine has the same gain on both. -/
def SameAttack (x y : A.Task) : Prop := ∀ M, (A.problem x).gain M = (A.problem y).gain M

theorem sameAttack_equiv : Equivalence A.SameAttack where
  refl _ _ := rfl
  symm h M := (h M).symm
  trans h h' M := (h M).trans (h' M)

/-- The family of the attack tasks. -/
def family : Family where
  Task := A.Task
  encode := A.encode
  decode := A.decode
  decode_encode := A.decode_encode
  Solvable := A.SolvableAttack
  SameProblem := A.SameAttack
  sameProblem_equiv := A.sameAttack_equiv

variable {A}

/-- On an assumption's problem, solving the task is exactly `Assumption.Attack` at the bound. -/
theorem exists_acceptAttack_iff {x : A.Task} {a : Assumption} {p : a.Params}
    (h : A.problem x = a.problem p) : (∃ M, A.AcceptAttack x M) ↔ a.Attack p (A.bound x) := by
  unfold AcceptAttack Assumption.Attack
  rw [h]

/-- A solved task that claims to refute `HardAt k` refutes it. -/
theorem SolvableAttack.not_hardAt {x : A.Task} {a : Assumption} {p : a.Params} {k : ℕ}
    (h : A.problem x = a.problem p) (hs : A.SolvableAttack x) (hk : A.refutes x = some k) :
    ¬ a.HardAt p k :=
  ((exists_acceptAttack_iff h).mp hs.2).not_hardAt (hs.1 k hk)

end AttackAdapter

end SigabaNeo.Benchmark
