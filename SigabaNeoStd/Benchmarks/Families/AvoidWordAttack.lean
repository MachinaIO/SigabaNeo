import SigabaNeoStd.Benchmarks.Families.Common

/-!
# Bootstrap fixture: the "avoid a word" attack family

BOOTSTRAP FIXTURE, not a research benchmark: every task is solved by the machine that halts at
once. It exercises the cryptanalysis side of the certified-generator gate. It is a synthetic
search problem, not a registered assumption, and changes no strength.

A task is a word `w` (`Fixture.Word`). Its problem is the search problem with the single instance
`[]` whose solutions are the words other than `w` (`avoidProblem w`). An attack must have
`cost ≤ 2^5 · gain` (`avoidAttackBound = 5`), and the task claims to refute strength
`avoidAttackRefutes = 6`, which is strict (`5 < 6`).

* `avoidAttack_gain_halt`: `haltMachine` (cost `30 ≤ 2^5`) has gain `1` on a nonempty word.
* `avoidAttack_solvable`: every task with a nonempty word is solvable.
* `avoidAttack_sameProblem`: two tasks are the same problem only if their words are equal (probe:
  the machine that always outputs the first word has gain `0` on its task, `1` on every other).
-/

namespace SigabaNeo.Benchmark.Fixture

/-- Output a word other than `w` (on the empty instance). -/
noncomputable def avoidProblem (w : List Bool) : Problem := .search (PMF.pure ([], {u | u ≠ w}))

/-- The bound `c` of every task. -/
def avoidAttackBound : ℕ := 5

/-- The strength every task claims to refute. -/
def avoidAttackRefutes : ℕ := 6

/-- The adapter of the family. -/
noncomputable def avoidAttack : AttackAdapter where
  Task := Word
  encode := Word.encode
  decode := Word.decode
  decode_encode := Word.decode_encode
  problem x := avoidProblem x.bits
  bound _ := avoidAttackBound
  refutes _ := some avoidAttackRefutes

/-- The family "avoid a word" (attack). -/
noncomputable def avoidAttackFamily : Family := avoidAttack.family

/-- The gain on `avoidProblem w`: the probability of an output other than `w` on `[]`. -/
theorem avoidProblem_gain (w : List Bool) (M : Machine) :
    (avoidProblem w).gain M = ((M.run []).toOuterMeasure {u | u ≠ w}).toReal := by
  simp only [avoidProblem, Problem.gain, Machine.solveProb]
  rw [tsum_eq_single ([], {u | u ≠ w})]
  · rw [PMF.pure_apply_self, one_mul]
  · intro z hz
    rw [PMF.pure_apply_of_ne _ _ hz, zero_mul]

/-- The gain of a machine with the point output `v`: `1` if `v ≠ w`, else `0`. -/
theorem avoidProblem_gain_of_pure {w v : List Bool} {M : Machine} (hM : M.run [] = PMF.pure v) :
    (avoidProblem w).gain M = if v ≠ w then 1 else 0 := by
  rw [avoidProblem_gain, hM, PMF.toOuterMeasure_pure_apply]
  split_ifs <;> simp_all

/-- `haltMachine` has gain `1` on a nonempty word. -/
theorem avoidAttack_gain_halt {w : List Bool} (hw : w ≠ []) :
    (avoidProblem w).gain haltMachine = 1 := by
  rw [avoidProblem_gain_of_pure (haltMachine_run [])]
  simp [Ne.symm hw]

/-- Every task with a nonempty word is solved by `haltMachine`: gain `1`, cost `30 ≤ 2^5`, and the
refutation claim is strict. -/
theorem avoidAttack_solvable {x : Word} (hx : x.bits ≠ []) : avoidAttackFamily.Solvable x := by
  refine ⟨fun k hk => ?_, haltMachine, ?_, ?_⟩
  · cases hk
    show avoidAttackBound < avoidAttackRefutes
    decide
  · show 0 < (avoidProblem x.bits).gain haltMachine
    rw [avoidAttack_gain_halt hx]
    exact one_pos
  · show (haltMachine.cost : ℝ) ≤ 2 ^ avoidAttackBound * (avoidProblem x.bits).gain haltMachine
    rw [avoidAttack_gain_halt hx, haltMachine_cost, avoidAttackBound]
    norm_num

/-- Two tasks are the same problem only if their words are equal. -/
theorem avoidAttack_sameProblem {x y : Word} (h : avoidAttackFamily.SameProblem x y) : x = y := by
  obtain ⟨M, -, hM⟩ := exists_const_machine x.bits
  have he : (avoidProblem x.bits).gain M = (avoidProblem y.bits).gain M := h M
  rw [avoidProblem_gain_of_pure (hM []), avoidProblem_gain_of_pure (hM [])] at he
  apply Word.ext'
  by_contra hne
  simp [hne] at he

/-- The solver's target for a nonempty word of at most `Word.maxLen` bits. -/
theorem avoidAttack_target {bits : List Bool} (hlen : bits.length ≤ Word.maxLen)
    (hne : bits ≠ []) : Target avoidAttackFamily bits :=
  (target_iff (F := avoidAttackFamily) (x := ⟨bits, hlen⟩) (by simp [avoidAttackFamily,
    AttackAdapter.family, avoidAttack, Word.decode, hlen])).mpr (avoidAttack_solvable hne)

end SigabaNeo.Benchmark.Fixture
