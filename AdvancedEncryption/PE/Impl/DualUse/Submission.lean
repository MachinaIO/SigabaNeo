import PE.Impl.DualUse.AHFinal
import PE.Impl.DualUse.ImplP
import PE.Impl.DualUse.Prog.CfX
import PE.Impl.DualUse.Prog.WfB2CoinFree
import PE.Impl.DualUse.Prog.CompCost
import SigabaNeo.Trusted.Submission

/-!
# The submission for the date-window predicate encryption
-/

namespace AdvancedEncryption.DualUse.Sub

open SigabaNeo SigabaNeo.Lattices SigabaNeo.Tape AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow
open AdvancedEncryption.DualUse.Prog AdvancedEncryption.DualUse.Params

theorem confP_d3 : 3 ≤ confP.d := by show 3 ≤ dp; rw [dp_def]; norm_num

theorem hS_conf : lenKA hkp confP + Np * Kp ≤ lenZ confP := by
  simp only [lenKA, lenZ, DualUse.rowL, lPsi, fixLen]
  comp_unfold
  norm_num

end AdvancedEncryption.DualUse.Sub
