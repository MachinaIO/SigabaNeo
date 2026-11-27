import SigabaNeoStd.Benchmarks.Families.AvoidWordDesign

/-!
Negative fixture for the runtime bridge: the compiled code of the generator (`implemented_by`)
differs from its definition, so the evaluated descriptor is not the kernel's.
-/

namespace Generators.Mismatch

open SigabaNeo.Benchmark SigabaNeo.Benchmark.Fixture

def generateImpl (_ : Fin 1) (r : Seed 8) : Word := ⟨false :: List.ofFn r, by simp [Word.maxLen]⟩

@[implemented_by generateImpl]
def generate (_ : Fin 1) (r : Seed 8) : Word := ⟨true :: List.ofFn r, by simp [Word.maxLen]⟩

end Generators.Mismatch
