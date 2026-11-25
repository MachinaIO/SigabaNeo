import PE.Impl.ExpLUT.Prog.RedKeyMFront
import PE.Impl.ExpLUT.SubmissionAssembly

/-!
# `KGsim` on the VM (module 8): the `KeyComp` record from the middle phases

**`keyCompOf`**: a `Sub.KeyComp` from a middle phase `mid : XProg 247` with `mid.WF`,
`RkMidOk mid` (`RedKeyMFront`) and the three certificates of module 9 for `rkKeyP mid`.
**`law_rkKeyP_spR`**: the `law` field itself (from `RkMidOk` alone).
-/

namespace AdvancedEncryption.ExpLUT.Sub

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Generic
open AdvancedEncryption.ExpLUT AdvancedEncryption.ExpLUT.Prog AdvancedEncryption.ExpLUT.Params
open AdvancedEncryption.ExpLUT.Prog.RedKeyM

/-- **The `law` field of `KeyComp`** for `rkKeyP mid`. -/
theorem law_rkKeyP_spR {mid : XProg 247} (hm : RkMidOk mid) (σ : RawSec Dc) (C : List Bool) :
    XProg.law (rkKeyP mid) (io2 (R := 245) (cdR.sig.enc σ) C []) =
      (spR.key σ C).map fun sk => io2 (R := 245) sk [] [] :=
  law_rkKeyP hm σ C

/-- **The key component** from the middle phases and the certificates of module 9. -/
noncomputable def keyCompOf (mid : XProg 247) (hwf : mid.WF) (hm : RkMidOk mid) (Lk : ℕ)
    (hLk : Lk ≤ 2 ^ 125)
    (hlen : XProg.lenBoundT (rkKeyP mid) (io2 (R := 245) (sigBound cdR (WR Dc)) predLen 0) ≤
      io2 (R := 245) Lk 0 0)
    (htime : XProg.timeBoundT (rkKeyP mid) (io2 (R := 245) (sigBound cdR (WR Dc)) predLen 0) ≤
      2 ^ 450)
    (hsize : (rkKeyP mid).size ≤ 2 ^ 200) : KeyComp where
  keyP := rkKeyP mid
  wf := wf_rkKeyP hwf
  law := law_rkKeyP_spR hm
  Lk := Lk
  hLk := hLk
  len := hlen
  time := htime
  size := hsize

end AdvancedEncryption.ExpLUT.Sub
