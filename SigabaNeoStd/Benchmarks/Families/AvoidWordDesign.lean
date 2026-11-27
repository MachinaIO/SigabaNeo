import SigabaNeoStd.Benchmarks.Families.Common

/-!
# Bootstrap fixture: the "avoid a word" design family

BOOTSTRAP FIXTURE, not a research benchmark: every task is solved by the machine that halts at
once. It exercises the design side of the certified-generator gate.

A task is a word `w` (`Fixture.Word`). The primitive has one deterministic algorithm `Out` with no
input variables and one output variable; it receives `w` as its parameters. Its one proposition:
the algorithm never outputs `w` (the probability of the output tuple `[w]` is `0`). The cost is
the cost of the machine (steps plus description); the cap is `avoidDesignCap = 64`. The registry is
empty: no premises.

* `avoidDesign_solvable`: a task with a nonempty word is solved by `haltMachine` (output: the
  empty variable; cost `30`).
* `avoidDesign_sameProblem`: two tasks are the same problem only if their words are equal (probe:
  the machine that always outputs the word of the first task violates it and satisfies every other
  task).
-/

namespace SigabaNeo.Benchmark.Fixture

/-- The one algorithm: deterministic, no input variables, one output variable. -/
def avoidSig (_ : Unit) : AlgSig := ⟨"Out", [], ["out"], false⟩

/-- The proposition at the word `w`: the algorithm, given `w`, never outputs `w`. -/
def avoidProp (_ : Unit) (w : List Bool) (I : Impl avoidSig) : Prop := I.run () w [] [w] = 0

/-- The empty registry. -/
def emptyRegistry : Registry := Registry.of (Empty.elim : Empty → Assumption)

/-- Its (empty) strengths. -/
def emptyStrength : emptyRegistry.Strength := fun n => n.elim

/-- The cost cap of every task. -/
def avoidDesignCap : ℕ := 64

/-- The adapter of the family. -/
def avoidDesign : DesignAdapter where
  Task := Word
  encode := Word.encode
  decode := Word.decode
  decode_encode := Word.decode_encode
  Alg := Unit
  sig := avoidSig
  Params := List Bool
  params x := x.bits
  encodeParams := id
  PropIndex := Unit
  prop := avoidProp
  cost _ I := (I.machine ()).cost
  registry := emptyRegistry
  strength := emptyStrength
  cap _ := avoidDesignCap

/-- The family "avoid a word" (design). -/
def avoidDesignFamily : Family := avoidDesign.family

/-- The implementation by the machine that halts at once. -/
noncomputable def haltImpl : Impl avoidSig :=
  ⟨fun _ => haltMachine, fun _ _ => haltMachine_deterministic⟩

theorem haltImpl_run (pw : List Bool) : haltImpl.run () pw [] = PMF.pure [[]] := by
  rw [Impl.run_of_pure haltImpl () rfl pw [] [] (haltMachine_run _), decodeTuple_one_nil]

/-- Every task with a nonempty word is solved by `haltMachine`, at the claimed cost `30`. -/
theorem avoidDesign_solvable {x : Word} (hx : x.bits ≠ []) : avoidDesignFamily.Solvable x := by
  refine ⟨⟨haltImpl, fun _ => [], 30⟩, ⟨fun i _ => ?_, ?_⟩, fun _ d hd => by simp at hd, ?_⟩
  · show haltImpl.run () x.bits [] [x.bits] = 0
    rw [haltImpl_run, PMF.pure_apply_of_ne]
    intro h
    exact hx (List.cons.inj h).1
  · show haltMachine.cost ≤ 30
    rw [haltMachine_cost]
  · show 30 ≤ 64
    norm_num

/-- Two tasks are the same problem only if their words are equal. -/
theorem avoidDesign_sameProblem {x y : Word} (h : avoidDesignFamily.SameProblem x y) : x = y := by
  obtain ⟨M, hdet, hM⟩ := exists_const_machine (encodeTuple [x.bits])
  let I : Impl avoidSig := ⟨fun _ => M, fun _ _ => hdet⟩
  have hrun (pw : List Bool) : I.run () pw [] = PMF.pure [x.bits] := by
    rw [Impl.run_of_pure I () rfl pw [] _ (hM _)]
    exact congrArg PMF.pure (decodeTuple_encodeTuple [x.bits])
  have hx : ¬ avoidDesign.SemanticAccept x I := fun hs => by
    have := hs ()
    change I.run () x.bits [] [x.bits] = 0 at this
    rw [hrun, PMF.pure_apply_self] at this
    exact one_ne_zero this
  have hy : ¬ avoidDesign.SemanticAccept y I := fun hs => hx ((h I).mpr hs)
  apply Word.ext'
  by_contra hne
  apply hy
  intro i
  change I.run () y.bits [] [y.bits] = 0
  rw [hrun, PMF.pure_apply_of_ne]
  intro he
  exact hne (List.cons.inj he).1.symm

/-- The solver's target for a nonempty word of at most `Word.maxLen` bits. -/
theorem avoidDesign_target {bits : List Bool} (hlen : bits.length ≤ Word.maxLen)
    (hne : bits ≠ []) : Target avoidDesignFamily bits :=
  (target_iff (F := avoidDesignFamily) (x := ⟨bits, hlen⟩) (by simp [avoidDesignFamily,
    DesignAdapter.family, avoidDesign, Word.decode, hlen])).mpr (avoidDesign_solvable hne)

end SigabaNeo.Benchmark.Fixture
