import PE.Impl.ExpLUT.Prog.RedKeyTMain
import PE.Impl.ExpLUT.Prog.RedKeyTSpecG
import PE.Impl.ExpLUT.Prog.RedKeyTSize

/-!
# Module 9: the key component and the final statement from the middle phases

* **`rkTailPkg`**: the back-end package (`rkTailCert_of`, `rkLt = 2^102 + 2^120 ≤ 2^125`,
  `rkTt = 2^436 ≤ 2^449`, `size_rkTailP_Dc : size ≤ 2^195`);
* **`keyCompOfMid`**: `Sub.KeyComp` from `mid`, `mid.WF`, `RkMidOk mid`, `mid.size ≤ 2^190` and
  `∃ a, RkTailIn a ∧ RkMidBound mid a`;
* **`spec_of_mid`**: the final `Spec`.
-/

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyT

open SigabaNeo SigabaNeo.Tape
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Generic
open AdvancedEncryption.ExpLUT.Prog.RedKeyM

/-- **The back-end package.** -/
theorem rkTailPkg : RkTailPkg rkLt rkTt :=
  ⟨fun _ ha => rkTailCert_of ha, rkLt_le, rkTt_le, size_rkTailP_Dc⟩

/-- **The key component** from the middle phases. -/
noncomputable def keyCompOfMid (mid : XProg 247) (hwf : mid.WF) (hm : RkMidOk mid)
    (hsm : mid.size ≤ 2 ^ 190) (hb : ∃ a, RkTailIn a ∧ RkMidBound mid a) : Sub.KeyComp :=
  keyCompOfIn rkTailPkg mid hwf hm hsm hb

/-- **The final statement** from the middle phases. -/
theorem spec_of_mid (mid : XProg 247) (hwf : mid.WF) (hm : RkMidOk mid)
    (hsm : mid.size ≤ 2 ^ 190) (hb : ∃ a, RkTailIn a ∧ RkMidBound mid a) :
    Spec (BranchingProgram.primitive BranchingProgram.w8) Sub.registry
      (Sub.submissionOf DecConf.decMachine Sub.decMachine_det Sub.Ncost) :=
  spec_of_mid_pkg rkTailPkg mid hwf hm hsm hb

end AdvancedEncryption.ExpLUT.Prog.RedKeyT
