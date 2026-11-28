import SigabaNeoStd.Benchmarks.Entropy
import SigabaNeoStd.Benchmarks.Families.AvoidWordAttack

/-!
# Bootstrap fixture generator: "avoid a word" (attack), one level

BOOTSTRAP FIXTURE for the tests of the certified-generator gate, not a research benchmark.
At seed `r` the task is the word `1 r`. Every task is solved by `haltMachine` (gain `1`,
cost `30 ≤ 2^5`, strict against the claimed `6` bits); equal gains force equal seeds, so the
diversity is `h = k = 8`.
-/

namespace Generators.AvoidAttack

open SigabaNeo.Benchmark SigabaNeo.Benchmark.Fixture

/-- The generator. -/
def generate (_ : Fin 1) (r : Seed 8) : Word :=
  ⟨true :: List.ofFn r, by simp [Word.maxLen]⟩

/-- The certificate: one level, 8 seed bits, 8 bits of diversity. -/
theorem certified : Certified avoidAttackFamily 1 8 8 generate :=
  certified_of_injective (by norm_num)
    (fun _ _ => avoidAttack_solvable (by simp [generate]))
    (fun _ _ _ h => List.ofFn_injective
      (List.cons.inj (congrArg Word.bits (avoidAttack_sameProblem h))).2)

end Generators.AvoidAttack
