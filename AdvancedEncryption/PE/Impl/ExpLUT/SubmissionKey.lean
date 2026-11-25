import PE.Impl.ExpLUT.SubmissionAssembly
import PE.Impl.ExpLUT.Prog.RedKeyTTop
import PE.Impl.ExpLUT.Prog.RedKeyTIn
import PE.Impl.ExpLUT.Prog.RedKeyPktOk

/-!
# The final statement, up to the two cost certificates of the key component

`midK := mid (pkOf pkt)` is the middle phase of the reduction's key component (law: `rkMidOk_pkt`).
**`spec_of_costs`**: the final `Spec` of the submission from the cost certificate of `midK`
(`RkMidBound midK a`, `midK.size ≤ 2^190`) and that of the back end (`RkTailCert a Lt Tt`).
-/

namespace AdvancedEncryption.ExpLUT.Sub

open SigabaNeo SigabaNeo.Tape AdvancedEncryption.PE AdvancedEncryption.ExpLUT AdvancedEncryption.ExpLUT.Prog
open AdvancedEncryption.ExpLUT.Params

/-- The middle phase of the key component. -/
noncomputable abbrev midK : XProg 247 := RedKeyMid.mid (RedKeyMid.pkOf RedKeyPkt.pkt)

/-- **The final statement from the two cost certificates of the key component.** -/
theorem spec_of_costs (a : Fin 105 → ℕ) (hb : RedKeyT.RkMidBound midK a) (Lt Tt : ℕ)
    (ht : RedKeyT.RkTailCert a Lt Tt) (hLt : Lt ≤ 2 ^ 125) (hTt : Tt ≤ 2 ^ 449)
    (hsm : midK.size ≤ 2 ^ 190) (hst : (rkTailP Dc Bk rSmall).size ≤ 2 ^ 195) :
    Spec (BranchingProgram.primitive BranchingProgram.w8) registry
      (submissionOf DecConf.decMachine decMachine_det Ncost) :=
  spec_of_keyComp (RedKeyT.keyCompOfT midK (RedKeyMid.wf_mid RedKeyPkt.wf_pkOf_pkt) RedKeyPkt.rkMidOk_pkt a hb Lt Tt
    ht hLt hTt hsm hst)

end AdvancedEncryption.ExpLUT.Sub
