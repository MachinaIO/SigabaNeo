import Definitions.Def_Vacuous
/-! Positive fixture: a refutation of the vacuous test target. -/

namespace TestCase.Vacuous

theorem refutation : ¬ TestCase.Vacuous.target := fun h => h

end TestCase.Vacuous
