import SigabaNeoStd.Benchmarks.Families.AvoidWordDesign

/-!
Negative fixture for the runtime bridge: the descriptor is quick to evaluate but its kernel check
exceeds the heartbeat budget.
-/

namespace Generators.Slow

open SigabaNeo.Benchmark SigabaNeo.Benchmark.Fixture

/-- `n` steps of counting. -/
def count : ℕ → ℕ → ℕ
  | 0, a => a
  | n + 1, a => count n (a + 1)

def generate (_ : Fin 1) (r : Seed 8) : Word :=
  if count 100000 0 = 0 then ⟨[false], by decide⟩ else ⟨true :: List.ofFn r, by simp [Word.maxLen]⟩

end Generators.Slow
