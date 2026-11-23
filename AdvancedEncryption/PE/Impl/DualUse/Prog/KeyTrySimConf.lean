import PE.Impl.DualUse.Prog.KeyPTimeV
import PE.Impl.DualUse.Prog.KeyTightConf

/-!
# The sweeps of the simulated key try at `confP`

`pEval_wKS_conf`: at the variables of `confP` with the top `2^250 + 1 + lenPK` (the bound of the
tapes before the simulated key try of the reductions' key component), the sweeps `wKS` of the
simulated key try are at most `2^240` (checked by evaluation, `decide +kernel`).
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg AdvancedEncryption.DualUse.Params
open AdvancedEncryption.DualUse.Algo AdvancedEncryption.DualUse.Algo.Params
open SigabaNeo.Lattices.Algo
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow

/-! ### The simulated key try at `confP` -/

theorem ρS_conf : ρS hkp confP (2 ^ 250) cfP =
    [2 ^ 250 + 1 + 29931556208626396671394777597180314650064272740057088,
    2 ^ 34, 2 ^ 25, 2 ^ 25 + 1, 2 ^ 61, 1 + (2 * (2 ^ 25 + 1) + 2 * (2 ^ 25 + 1)),
    29931556208626396671394777597180314650064272740057088, 16041444,
    (2 ^ 61 + (1 + (2 * (2 ^ 25 + 1) + 2 * (2 ^ 25 + 1)))) * 2 ^ 34 * 16041444] := by
  simp only [ρS, simTop, AdvancedEncryption.DualUse.Algo.nT]
  rw [lenPK_eq, confP_d, cfP_B, cfP_m, Np_def, Kp_def, kp_eq]

set_option maxRecDepth 100000 in
/-- **The sweeps of the simulated key try at `confP`**, checked by evaluation. -/
theorem pEval_wKS_conf : Sym.pEval (ρS hkp confP (2 ^ 250) cfP) KeySV.wKS ≤ 2 ^ 240 := by
  rw [ρS_conf]; decide +kernel

end AdvancedEncryption.DualUse.Prog
