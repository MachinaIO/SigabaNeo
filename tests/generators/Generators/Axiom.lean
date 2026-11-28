import Generators.AvoidDesign

/-! Negative fixture: the certificate rests on an extra axiom. -/

namespace Generators.Axiom

open SigabaNeo.Benchmark SigabaNeo.Benchmark.Fixture

axiom cheat : Certified avoidDesignFamily 2 8 8 Generators.AvoidDesign.generate

theorem certified : Certified avoidDesignFamily 2 8 8 Generators.AvoidDesign.generate := cheat

end Generators.Axiom
