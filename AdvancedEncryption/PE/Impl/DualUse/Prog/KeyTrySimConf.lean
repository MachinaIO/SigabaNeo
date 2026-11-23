import PE.Impl.DualUse.Prog.KeyPTimeV
import PE.Impl.DualUse.Prog.KeyTightConf

/-!
# The sweeps of the simulated key try at `confA`

`pEval_wKS_conf`: at the variables of `confA` with the top `2^262 + 1 + lenPK` (the bound of the
tapes before the simulated key try of the reductions' key component: the stream block leaves at
most `2^262` bits), the sweeps `wKS` of the simulated key try are at most `2^224` (checked by
evaluation, `decide +kernel`).
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg AdvancedEncryption.DualUse.Params
open AdvancedEncryption.DualUse.Algo AdvancedEncryption.DualUse.Algo.Params
open SigabaNeo.Lattices.Algo
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPWord

set_option exponentiation.threshold 3000

theorem ρS_conf : ρS hkp confP (2 ^ 262) cfP =
    [2 ^ 262 + 1 + 1569275468922709748577758203934090069617389767520910573568,
    2 ^ 36, 2 ^ 27, 2 ^ 27 + 1, 2 ^ 65, 1 + (2 * (2 ^ 27 + 1) + 2 * (2 ^ 27 + 1)),
    1569275468922709748577758203934090069617389767520910573568, 51056224,
    (2 ^ 65 + (1 + (2 * (2 ^ 27 + 1) + 2 * (2 ^ 27 + 1)))) * 2 ^ 36 * 51056224] := by
  simp only [ρS, simTop, AdvancedEncryption.DualUse.Algo.nT]
  rw [lenPK_eq, confP_d, cfP_B, cfP_m, Np_def, Kp_def, kp_eq]

set_option maxRecDepth 100000 in
/-- **The sweeps of the simulated key try at `confA`**, checked by evaluation. -/
theorem pEval_wKS_conf : Sym.pEval (ρS hkp confP (2 ^ 262) cfP) KeySV.wKS ≤ 2 ^ 224 := by
  rw [ρS_conf]; decide +kernel

end AdvancedEncryption.DualUse.Prog
