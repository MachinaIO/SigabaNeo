import Generators.AvoidDesign

/-! Negative fixture: the certificate is `sorry`. -/

namespace Generators.Sorry

open SigabaNeo.Benchmark SigabaNeo.Benchmark.Fixture

theorem certified : Certified avoidDesignFamily 2 8 8 Generators.AvoidDesign.generate := by
  sorry

end Generators.Sorry
