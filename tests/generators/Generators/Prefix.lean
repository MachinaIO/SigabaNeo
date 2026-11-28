import SigabaNeoStd.Benchmarks.Entropy
import SigabaNeoStd.Benchmarks.Families.AvoidWordDesign

/-!
# Bootstrap fixture generator: a bounded fiber (design)

BOOTSTRAP FIXTURE for the tests of the certified-generator gate, not a research benchmark.
The task reads only the first 4 of the 8 seed bits: each fiber has `2^4` seeds, so the generator
is certified at `h = 4` (partial seed recovery), not more.
-/

namespace Generators.Prefix

open SigabaNeo.Benchmark SigabaNeo.Benchmark.Fixture

/-- The generator: the word `1 r₀ r₁ r₂ r₃`. -/
def generate (_ : Fin 1) (r : Seed 8) : Word :=
  ⟨true :: List.ofFn (seedPrefix (by norm_num : 4 ≤ 8) r), by simp [Word.maxLen]⟩

/-- The certificate at `h = 4`. -/
theorem certified : Certified avoidDesignFamily 1 8 4 generate :=
  certified_of_prefix (by norm_num) (by norm_num)
    (fun _ _ => avoidDesign_solvable (by simp [generate]))
    (fun _ _ _ h => List.ofFn_injective
      (List.cons.inj (congrArg Word.bits (avoidDesign_sameProblem h))).2)

end Generators.Prefix
