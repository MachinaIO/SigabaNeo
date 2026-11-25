import PE.Impl.ExpLUT.Prog.RedKeyTIn

/-!
# Module 9: `KeyComp` and the final statement from a back-end package (generic form)

`RkTailPkg Lt Tt`: the back end's obligations, stated against the interface `RkTailIn`:
a certificate `RkTailCert a Lt Tt` for **every** `a` with `RkTailIn a`, `Lt ≤ 2^125`,
`Tt ≤ 2^449` and `(rkTailP Dc Bk rSmall).size ≤ 2^195`.

* **`keyCompOfIn`**: `Sub.KeyComp` from `mid`, `RkMidOk mid`, `mid.WF`, `mid.size ≤ 2^190`,
  `∃ a, RkTailIn a ∧ RkMidBound mid a` and a package;
* **`spec_of_mid_pkg`**: the final `Spec`.

`RedKeyTSpec` instantiates the package (`rkTailPkg`).
-/

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyT

open SigabaNeo SigabaNeo.Tape
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Generic
open AdvancedEncryption.ExpLUT.Prog.RedKeyM
open AdvancedEncryption.ExpLUT.Params

/-- **The obligations of the back end**, against the interface `RkTailIn`. -/
structure RkTailPkg (Lt Tt : ℕ) : Prop where
  cert : ∀ a, RkTailIn a → RkTailCert a Lt Tt
  hLt : Lt ≤ 2 ^ 125
  hTt : Tt ≤ 2 ^ 449
  size : (rkTailP Dc Bk rSmall).size ≤ 2 ^ 195

/-- **The key component** from the middle phases and a back-end package. -/
noncomputable def keyCompOfIn {Lt Tt : ℕ} (pk : RkTailPkg Lt Tt) (mid : XProg 247)
    (hwf : mid.WF) (hm : RkMidOk mid) (hsm : mid.size ≤ 2 ^ 190)
    (hb : ∃ a, RkTailIn a ∧ RkMidBound mid a) : Sub.KeyComp :=
  keyCompOfT mid hwf hm (Classical.choose hb) (Classical.choose_spec hb).2 Lt Tt
    (pk.cert _ (Classical.choose_spec hb).1) pk.hLt pk.hTt hsm pk.size

/-- **The final statement** from the middle phases and a back-end package. -/
theorem spec_of_mid_pkg {Lt Tt : ℕ} (pk : RkTailPkg Lt Tt) (mid : XProg 247)
    (hwf : mid.WF) (hm : RkMidOk mid) (hsm : mid.size ≤ 2 ^ 190)
    (hb : ∃ a, RkTailIn a ∧ RkMidBound mid a) :
    Spec (BranchingProgram.primitive BranchingProgram.w8) Sub.registry
      (Sub.submissionOf DecConf.decMachine Sub.decMachine_det Sub.Ncost) :=
  Sub.spec_of_keyComp (keyCompOfIn pk mid hwf hm hsm hb)

end AdvancedEncryption.ExpLUT.Prog.RedKeyT
