import Generators.AvoidDesign
import SigabaNeoStd.Benchmarks.Families.AvoidWordAttack

/-!
Negative fixture: a true certificate for another family (the attack family) than the policy's
(the design family).
-/

namespace Generators.WrongFamily

open SigabaNeo.Benchmark SigabaNeo.Benchmark.Fixture

theorem certified : Certified avoidAttackFamily 2 8 8 Generators.AvoidDesign.generate :=
  certified_of_injective (by norm_num)
    (fun _ _ => avoidAttack_solvable (by simp [AvoidDesign.generate, AvoidDesign.word]))
    (fun _ _ _ h => AvoidDesign.word_injective (congrArg Word.bits (avoidAttack_sameProblem h)))

end Generators.WrongFamily
