module

public import SigabaNeo.Lib.Lattices.Research.Wall1.FixedBlockScore
public import SigabaNeo.Lib.Lattices.Research.Wall1.FixedBlockCap506
import Mathlib.Tactic

public section
namespace SigabaNeo.Wall1.FinalBlock

/-- Part 181's strict terminal failure budget on a score-accepted rank-505 block. -/
theorem failure_lt_score506 {N : ℕ} (B : FinalBlock N 505)
    (hs : B.score (1919/2) ≤ 0.00012938) : 1 - B.success < 0.000607731 := by
  linarith [B.failure_le_capTail_add_score (1919/2), B.capTail_505_lt]

end SigabaNeo.Wall1.FinalBlock

#print axioms SigabaNeo.Wall1.FinalBlock.failure_lt_score506
