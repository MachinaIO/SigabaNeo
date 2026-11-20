/-
TEST ONLY. Deliberately vacuous targets, used by `tests/` to exercise the check end to end
without a cryptographic proof. They must never be mistaken for real
assumptions.

* `target` is `False`, so `¬ target` holds trivially.
* `strong` is `True`, which cannot be refuted. A refutation of `strong` under the hypothesis
  `target` exists only because that hypothesis is false (docs/DESIGN.md, "Vacuity").
-/
import Definitions.Def_Echo
namespace TestCase.Vacuous

def target : Prop := False

def strong : Prop := True

end TestCase.Vacuous
