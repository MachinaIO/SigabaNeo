import Definitions.Def_Vacuous
/-!
# A refutation of `TestCase.Vacuous.strong` under two hypotheses

`strong` (`True`) cannot be refuted outright. The first hypothesis, `Vacuous.target`, is `False`,
so the implication holds anyway: this is the vacuity of docs/DESIGN.md ("Vacuity"), as a test
case. The proof uses `h₀` and not `h₁`, so `referencedHypotheses` is `[h₀]`.
-/

namespace TestCase.Vacuous

open TestCase

theorem refutation (h₀ : Vacuous.target) (h₁ : Echo.target) : ¬ Vacuous.strong :=
  fun _ => h₀.elim

end TestCase.Vacuous
