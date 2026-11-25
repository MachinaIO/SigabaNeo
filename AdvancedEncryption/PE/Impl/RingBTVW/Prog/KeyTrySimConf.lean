import PE.Impl.RingBTVW.Prog.KeyPTimeV
import PE.Impl.RingBTVW.Prog.KeyTightConf

/-!
# The sweeps of the simulated key try at `confA`

`pEval_wKS_conf`: at the variables of `confA` with the top `2^262 + 1 + lenPK` (the bound of the
tapes before the simulated key try of the reductions' key component: the stream block leaves at
most `2^262` bits), the sweeps `wKS` of the simulated key try are at most `2^224` (checked by
evaluation, `decide +kernel`).
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg AdvancedEncryption.RingBTVW.Params
open AdvancedEncryption.RingBTVW.Algo AdvancedEncryption.RingBTVW.Algo.Params
open SigabaNeo.Lattices.Algo
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPWord

set_option exponentiation.threshold 3000

theorem ρS_conf : ρS hkp confP (2 ^ 262) cfP =
    [2 ^ 262 + 1 + 6129982437495116521683020588912456589297838140178825216,
    2 ^ 34, 2 ^ 26, 2 ^ 26 + 1, 2 ^ 62, 1 + (2 * (2 ^ 26 + 1) + 2 * (2 ^ 26 + 1)),
    6129982437495116521683020588912456589297838140178825216, 21139048,
    (2 ^ 62 + (1 + (2 * (2 ^ 26 + 1) + 2 * (2 ^ 26 + 1)))) * 2 ^ 34 * 21139048] := by
  simp only [ρS, simTop, AdvancedEncryption.RingBTVW.Algo.nT]
  rw [lenPK_eq, confP_d, cfP_B, cfP_m, Np_def, Kp_def, kp_eq]

set_option maxRecDepth 100000 in
/-- **The sweeps of the simulated key try at `confA`**, checked by evaluation. -/
theorem pEval_wKS_conf : Sym.pEval (ρS hkp confP (2 ^ 262) cfP) KeySV.wKS ≤ 2 ^ 224 := by
  rw [ρS_conf]; decide +kernel

end AdvancedEncryption.RingBTVW.Prog
