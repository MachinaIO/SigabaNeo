import PE.Impl.ExpLUT.Prog.RedPubPDc
import PE.Impl.ExpLUT.AH.RedChain

/-!
# The `pub` fields of `Generic.Comps` (package G2, P7)

**`law_pub_spS`**: the law of `pubP Dc` in the form of the field `law_pub` of `Generic.Comps`
for the challenger `spS Dc kb L (rawF Dc) setupS impl χfl i₀` (secrets `RawSec Dc`, encoded by
`rawEnc Dc`; any `Ok`), for every setup `setupS`; with `wf_pubP_Dc` (`wf_pub`), `len_pubP_Dc`
(`len_pub`: output within `2^102 ≤ 2^125`), `time_pubP_Dc` (`≤ 2^450`), `size_pubP_Dc`
(`≤ 2^200`).
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog.RedPubP

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape AdvancedEncryption.PE
  AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Generic

/-- **`law_pub` of `Generic.Comps`.** -/
theorem law_pub_spS (kb : KeyBoxes Dc) (L : ℕ)
    (setupS : CInst Dc → Attribute w8 → PMF (RawSec Dc)) (impl : Impl sig) (χfl : PMF (Rg Dc))
    (i₀ : CInst Dc) (σ : RawSec Dc) {Ok : Prop} (_ : Ok) :
    XProg.law (pubP Dc) (io2 (R := 245) ((w8Codes (rawEnc Dc)).sig.enc σ) [] []) =
      PMF.pure (io2 (R := 245) ((spS Dc kb L (rawF Dc) setupS impl χfl i₀).pub σ) [] []) :=
  law_pubP_Dc σ

end AdvancedEncryption.ExpLUT.Prog.RedPubP
