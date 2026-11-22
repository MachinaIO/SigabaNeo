import SigabaNeo.Lib.Lattices.Estimator.Bound.Loops
import SigabaNeo.Lib.Lattices.Estimator.Bound.Search
import SigabaNeo.Lib.Lattices.Estimator.Bound.Scan
import SigabaNeo.Lib.Lattices.Estimator.Bound.RedLB
import SigabaNeo.Lib.Lattices.Estimator.Bound.Guess
import SigabaNeo.Lib.Lattices.Estimator.Bound.DualHybrid
import SigabaNeo.Lib.Lattices.Estimator.Bound.Bkw
import SigabaNeo.Lib.Lattices.Estimator.Bound.Profile
import SigabaNeo.Lib.Lattices.Estimator.Bound.Binom
import SigabaNeo.Lib.Lattices.Estimator.Bound.Primal
import SigabaNeo.Lib.Lattices.Estimator.Bound.PrimalEval
import SigabaNeo.Lib.Lattices.Estimator.Bound.Arora
import SigabaNeo.Lib.Lattices.RingLWE

/-!
# Certified lower bounds on `estimatorBits`

`estimatorBits p ≥ kb` follows from a lower bound `kb` bits on each of the ten attacks
(`estimatorBits_ge_of`). Each attack has a lower-bound theorem that does not evaluate it (the
evaluation is infeasible at large parameters, and the kernel cannot hold a modulus like `2^(2^25)`):

| Attack | Theorem | Argument |
| --- | --- | --- |
| `usvp` | `Usvp.costQ_ge`, `Usvp.check_spec` | scan of `β < maxBeta`, evaluated by kernel (`redLB` above `β₀`) |
| `dual` | `Dual.costQ_ge`, `Dual.check_spec` | same |
| `dual_hybrid` | `DualHybrid.cost_ge` | guessing cost `≥ k + t`, reduction cost, or `v > 10` (monotone in `d`) |
| `bdd`, `bdd_hybrid`, `bdd_mitm_hybrid` | `PrimalHybrid.estimate_ge` | reduction cost, guessing cost and miss probability (binomial tail), or Babai's failure on the GSA profile (AM–GM) |
| `bkw` | `Bkw.cost_eq_none` | the `q^b` table exceeds the `2^1024` cap |
| `arora-gb` | `AroraGB.cost_ge` | the first Hilbert series coefficients grow, so the degree of regularity is large |
| `exhaustive_search` | `Guess.exhaustiveCost_eq_none` | the search space exceeds the `2^10000` cap |
| `mitm` | `Guess.mitmCost_eq` | evaluated by kernel |

They rest only on the definitions of the attack models: they are lower bounds on the models'
values, not on the cost of actual attacks.
-/

namespace SigabaNeo.Lattices.Estimator

open Fx

/-- `kb ≤ estimatorBits p` from a lower bound on each attack. -/
theorem estimatorBits_ge_of {p : LWEParams} {kb : ℕ} (hfb : kb ≤ 4673)
    (h1 : CostGe ((kb : ℤ) * ONE) (AroraGB.cost p)) (h2 : CostGe ((kb : ℤ) * ONE) (Bkw.cost p))
    (h3 : CostGe ((kb : ℤ) * ONE) (Usvp.cost p)) (h4 : CostGe ((kb : ℤ) * ONE) (PrimalBdd.cost p))
    (h5 : CostGe ((kb : ℤ) * ONE) (PrimalHybrid.costBdd p))
    (h6 : CostGe ((kb : ℤ) * ONE) (PrimalHybrid.costMitm p))
    (h7 : CostGe ((kb : ℤ) * ONE) (Dual.cost p)) (h8 : CostGe ((kb : ℤ) * ONE) (DualHybrid.cost p))
    (h9 : CostGe ((kb : ℤ) * ONE) (Guess.exhaustiveCost p))
    (h10 : CostGe ((kb : ℤ) * ONE) (Guess.mitmCost p)) :
    kb ≤ estimatorBits p := by
  apply floorBits_ge _ (kb_le_fallbackBits hfb)
  intro a ha
  simp only [attacks, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10

end SigabaNeo.Lattices.Estimator

namespace SigabaNeo.Lattices

/-- `kb ≤ ModuleLWE.H p` from a lower bound on the estimator at the LWE view, on the domain. -/
theorem ModuleLWE.H_ge_of {p : ModuleLWE.Params} {kb : ℕ} (hdom : p.inDomain = true)
    (h : kb ≤ Estimator.estimatorBits (ModuleLWE.toEstimator p)) : kb ≤ ModuleLWE.H p := by
  unfold ModuleLWE.H; rw [if_pos hdom]; exact h

/-- `kb ≤ RingLWE.H p` from a lower bound on the estimator at the LWE view, on the domain. -/
theorem RingLWE.H_ge_of {p : RingLWE.Params} {kb : ℕ} (hdom : p.toModule.inDomain = true)
    (h : kb ≤ Estimator.estimatorBits (ModuleLWE.toEstimator p.toModule)) : kb ≤ RingLWE.H p :=
  ModuleLWE.H_ge_of hdom h

end SigabaNeo.Lattices
