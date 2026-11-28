import SigabaNeoStd.Benchmarks.Entropy
import SigabaNeoStd.Benchmarks.Families.AvoidWordDesign

/-!
# Bootstrap fixture generator: "avoid a word" (design), two levels

BOOTSTRAP FIXTURE for the tests of the certified-generator gate, not a research benchmark.
At level `d` and seed `r` the task is the word `0^d 1 r` (`d` zeros, a one, the 8 seed bits).
Every task is solved by `haltMachine`; the same problem forces the same seed, so the diversity is
the full `h = k = 8` bits at both levels.
-/

namespace Generators.AvoidDesign

open SigabaNeo.Benchmark SigabaNeo.Benchmark.Fixture

/-- The word of level `d` and seed `r`. -/
def word (d : ℕ) (r : Seed 8) : List Bool := List.replicate d false ++ true :: List.ofFn r

theorem word_length (d : ℕ) (r : Seed 8) : (word d r).length = d + 9 := by
  simp [word]

/-- The generator. -/
def generate (d : Fin 2) (r : Seed 8) : Word :=
  ⟨word d r, by rw [word_length]; unfold Word.maxLen; omega⟩

theorem word_injective {d : ℕ} {r s : Seed 8} (h : word d r = word d s) : r = s :=
  List.ofFn_injective (List.cons.inj (List.append_cancel_left h)).2

/-- The certificate: two levels, 8 seed bits, 8 bits of diversity. -/
theorem certified : Certified avoidDesignFamily 2 8 8 generate :=
  certified_of_injective (by norm_num)
    (fun d r => avoidDesign_solvable (by simp [generate, word]))
    (fun _ _ _ h => word_injective (congrArg Word.bits (avoidDesign_sameProblem h)))

end Generators.AvoidDesign
