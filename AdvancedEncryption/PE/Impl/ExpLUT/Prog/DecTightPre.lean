import PE.Impl.ExpLUT.Prog.DecTightData

/-!
# Tight clock of the `Dec` code: the small blocks (part 3c)

Kernel certificates of the blocks outside the tables: the splits of `sk` and `ct`, `fixC`, the two
copies of `devalC`, `mulC i` and `tblC i` for **every** step `i < 16` (one bounded check each: their
bound vectors do not depend on `i`, the clock claim is the largest), the two copies closing a step,
and `finC`.
-/

namespace AdvancedEncryption.ExpLUT.Prog.DecTight

open SigabaNeo.Tape.RingVM

set_option maxRecDepth 100000

theorem dtChk_S1 : dtChk dtP splitSkC dtB0 dtB1 dtTS1 = true := by decide +kernel
theorem dtChk_S2 : dtChk dtP splitCtC dtB1 dtB2 dtTS2 = true := by decide +kernel
theorem dtChk_F : dtChk dtP fixC dtB2 dtB3 dtTF = true := by decide +kernel
theorem dtChk_c1 : dtChk dtP (.cp 177 61) dtB3 dtB4 dtTc1 = true := by decide +kernel
theorem dtChk_c2 : dtChk dtP (.cp 176 71) dtB4 dtBs dtTc2 = true := by decide +kernel

theorem dtChk_mul : ∀ i < 16, dtChk dtP (mulC i) dtBs dtBm1 dtTmul = true := by decide +kernel
theorem dtChk_tbl : ∀ i < 16, dtChk dtP (tblC i) dtBm1 dtBm dtTtbl = true := by decide +kernel

theorem dtChk_tailF :
    dtChk dtP (.seq (.cp 177 162) (.seq (.cp 176 163) .nop)) dtXF dtBs dtTtailF = true := by
  decide +kernel
theorem dtChk_tailT :
    dtChk dtP (.seq (.cp 177 162) (.seq (.cp 176 163) .nop)) dtXT dtBs dtTtailT = true := by
  decide +kernel

theorem dtChk_fin : dtChk dtP finC dtBs dtBend dtTfin = true := by decide +kernel

end AdvancedEncryption.ExpLUT.Prog.DecTight
