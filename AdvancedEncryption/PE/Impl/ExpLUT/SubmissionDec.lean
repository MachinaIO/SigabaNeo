import PE.Impl.ExpLUT.SubmissionCore
import PE.Impl.ExpLUT.Prog.DecDescConf
import PE.Impl.ExpLUT.Prog.DescTightDec
import PE.Impl.ExpLUT.Prog.DecTight
import PE.Impl.ExpLUT.Prog.DecTimeConf
import PE.Impl.ExpLUT.AH.RedConstDc

/-!
# The ExpLUT submission with the concrete `Dec` machine

`implX := implE decMachine _`; **`spec_of_comps`**: the final statement from the reduction's
components (with the coarse bounds of `const_le_Dc`) and the clock of `Dec` (`≤ 2^727`), with
claimed cost `2^745` (the description of `Enc`, `≤ 2^744`, dominates).
-/

namespace AdvancedEncryption.ExpLUT.Sub

open SigabaNeo SigabaNeo.Lattices AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open AdvancedEncryption.ExpLUT AdvancedEncryption.ExpLUT.Prog AdvancedEncryption.ExpLUT.Params
open AdvancedEncryption.PE.Generic

theorem decMachine_det : DecConf.decMachine.Deterministic := DecConf.decSpec_decMachine.1

/-- The implementation with the concrete `Dec` machine. -/
noncomputable abbrev implX : Impl PE.sig := implE DecConf.decMachine decMachine_det

/-- The claimed cost. -/
def Ncost : ℕ := 2 ^ 636

set_option exponentiation.threshold 2000 in
theorem cost_implX_le (hT : DecConf.decMachine.time ≤ 2 ^ 225) :
    PE.cost params implX ≤ Ncost := by
  refine (cost_implE_le DecConf.decMachine decMachine_det hT DecConf.descLen_decMachine_tight).trans ?_
  unfold Ncost
  norm_num

/-- **The final statement** from the components of the reduction (with coarse bounds) and the
clock of `Dec`. -/
theorem spec_of_comps (hT : DecConf.decMachine.time ≤ 2 ^ 225)
    (rc : RawComps Dc kbDc predLen implX χfl) (hR : rc.R ≤ 300)
    (hSz : 2 * (rc.cs.setupP.size + rc.cs.pubP.size) + rc.cs.keyP.size + rc.cs.authP.size +
      rc.cs.chalP.size ≤ 2 ^ 240)
    (hTc : compTimeP rc.cb ≤ 2 ^ 500)
    (hSsig : rc.cb.Ssig ≤ 2 ^ 125) (hLp : rc.cb.Lp ≤ 2 ^ 125) (hLk : rc.cb.Lk ≤ 2 ^ 125)
    (hLa : rc.cb.La ≤ 2 ^ 125) (hLc : rc.cb.Lc ≤ 2 ^ 125) :
    Spec (BranchingProgram.primitive BranchingProgram.w8) registry
      (submissionOf DecConf.decMachine decMachine_det Ncost) :=
  spec_of_parts DecConf.decMachine decMachine_det Ncost DecConf.decSpec_decMachine rc
    (hC_of_bounds rc (const_le_Dc rc hR hSz hTc hSsig hLp hLk hLa hLc)) (cost_implX_le hT)

theorem time_decMachine_816 : DecConf.decMachine.time ≤ 2 ^ 816 :=
  DecConf.time_decMachine.trans (Nat.pow_le_pow_right (by norm_num) (by norm_num))

/-- **The final statement** from the components of the reduction (with coarse bounds) alone. -/
theorem spec_of_rawComps (rc : RawComps Dc kbDc predLen implX χfl) (hR : rc.R ≤ 300)
    (hSz : 2 * (rc.cs.setupP.size + rc.cs.pubP.size) + rc.cs.keyP.size + rc.cs.authP.size +
      rc.cs.chalP.size ≤ 2 ^ 240)
    (hTc : compTimeP rc.cb ≤ 2 ^ 500)
    (hSsig : rc.cb.Ssig ≤ 2 ^ 125) (hLp : rc.cb.Lp ≤ 2 ^ 125) (hLk : rc.cb.Lk ≤ 2 ^ 125)
    (hLa : rc.cb.La ≤ 2 ^ 125) (hLc : rc.cb.Lc ≤ 2 ^ 125) :
    Spec (BranchingProgram.primitive BranchingProgram.w8) registry
      (submissionOf DecConf.decMachine decMachine_det Ncost) :=
  spec_of_comps DecConf.time_decMachine_tight rc hR hSz hTc hSsig hLp hLk hLa hLc

end AdvancedEncryption.ExpLUT.Sub
