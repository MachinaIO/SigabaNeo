import PE.Impl.ExpLUT.Prog.DecTightData
/-!
# Tight clock of the `Dec` code: the table of a final step (part 3b)

`lutC true` (`2^22` rounds of `jBody true`, each with the 22 automorphism rounds and the
coefficient loop) from `dtBm`, certified by one kernel run of the abstract interpreter.
-/

namespace AdvancedEncryption.ExpLUT.Prog.DecTight

open SigabaNeo.Tape.RingVM

set_option maxRecDepth 100000 in
theorem dtChk_lutT : dtChk dtP (lutC true) dtBm dtXT dtTlutT = true := by decide +kernel

end AdvancedEncryption.ExpLUT.Prog.DecTight
