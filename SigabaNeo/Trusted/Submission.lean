import SigabaNeo.Trusted.Assumption
import SigabaNeo.Trusted.Primitive

/-!
# Submissions and the final statement

Submissions and their final statement `Spec` of the Sigaba Neo concept (Section 3.2), described in
`docs/PRIMITIVES.md`.

* `Submission P R`: an implementation of the primitive `P`, the premises of each proposition, which
  name assumptions of the registry `R` (`Premise R`), and a claimed cost `N`.
* `Spec P R u`: each proposition holds when every premise `(n, p₀, k)` has `HardAt n p₀ k`, and the
  cost is at most `N`. It does not mention strengths, so lowering them never changes it.
* `Submission.Valid u H`: every premise is `Valid` at the harness's current strengths `H`
  (`k ≤ H n p₀`). The strengths come from the harness, not from the submission. With `Spec` and the
  claims of the assumptions at `H` it gives every proposition (`Spec.prop_of_valid`).
-/

namespace SigabaNeo

/-- What Design AI hands over: an implementation, the premises of each proposition, and the
claimed cost. -/
structure Submission (P : Primitive) (R : Registry) where
  /-- A machine for each algorithm. -/
  impl : Impl P.sig
  /-- The premises of each proposition. -/
  deps : P.PropIndex → List (Premise R)
  /-- The claimed cost. -/
  N : ℕ

variable {P : Primitive} {R : Registry}

/-- The final statement: each proposition holds when its premises do, and the cost of the
implementation is at most `N`. -/
def Spec (P : Primitive) (R : Registry) (u : Submission P R) : Prop :=
  (∀ i, (∀ d ∈ u.deps i, d.Holds) → P.prop i P.params u.impl) ∧ P.cost P.params u.impl ≤ u.N

/-- Every premise asks for at most the current strength of its assumption. -/
def Submission.Valid (u : Submission P R) (H : R.Strength) : Prop :=
  ∀ i, ∀ d ∈ u.deps i, d.Valid H

/-- A proven `Spec` of a submission valid at the current strengths `H` gives each proposition from
the claims, at `H`, of the assumptions its premises name. -/
theorem Spec.prop_of_valid {u : Submission P R} {H : R.Strength} (h : Spec P R u)
    (hv : u.Valid H) (i : P.PropIndex) (ha : ∀ d ∈ u.deps i, R.Holds H d.n) :
    P.prop i P.params u.impl :=
  h.1 i fun d hd => Premise.hardAt (hv i d hd) (ha d hd)

end SigabaNeo
