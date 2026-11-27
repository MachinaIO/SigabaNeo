import SigabaNeoStd.Benchmarks.Entropy
import SigabaNeoStd.Benchmarks.Families.AvoidWordDesign

/-!
# Negative fixture: a constant generator

Every seed gives the word `1`. It is certified at `h = 0` only (`certified0`), and provably not at
`h = 8` (`not_certified`).
-/

namespace Generators.Constant

open SigabaNeo.Benchmark SigabaNeo.Benchmark.Fixture

def generate (_ : Fin 1) (_ : Seed 8) : Word := ⟨[true], by decide⟩

theorem certified0 : Certified avoidDesignFamily 1 8 0 generate := by
  refine ⟨by norm_num, by norm_num, fun _ _ => avoidDesign_solvable (by simp [generate]),
    fun d r => ?_⟩
  have := Nat.card_le_card_of_injective _ (Subtype.val_injective (p := fun s : Seed 8 =>
    avoidDesignFamily.SameProblem (generate d r) (generate d s)))
  rw [Nat.card_eq_fintype_card (α := Seed 8), card_seed] at this
  simpa using this

theorem not_certified : ¬ Certified avoidDesignFamily 1 8 8 generate :=
  not_certified_const (by norm_num) (by norm_num) _

end Generators.Constant
