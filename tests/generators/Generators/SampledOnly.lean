import Generators.AvoidDesign

/-! Negative fixture: solvability of one sampled seed at one level, not the certificate. -/

namespace Generators.SampledOnly

open SigabaNeo.Benchmark SigabaNeo.Benchmark.Fixture

theorem certified : avoidDesignFamily.Solvable (Generators.AvoidDesign.generate 0 fun _ => false) :=
  avoidDesign_solvable (by simp [AvoidDesign.generate, AvoidDesign.word])

end Generators.SampledOnly
