import PE.Impl.ExpLUT.Prog.DecDescConf
import PE.Impl.ExpLUT.Prog.DescTightBase

/-!
# Tight description length of the concrete `Dec` machine

Same state count as `DecConf.size_decProgram` (`size + 4 ≤ 2^28`; the compiled code alone has
`256728820 ≈ 2^27.94` states), but the entry width is `4 + 4·256 + 29` bits instead of
`4 + 4·256 + 2^28`: **`descLen_decMachine_tight : decMachine.descLen ≤ 2^447`**
(`log₂(6 · 2^28 · 3^256 · 1057) ≈ 446.38`; the floor `3^256 ≈ 2^405.75` dominates).
-/

set_option autoImplicit false

namespace AdvancedEncryption.ExpLUT.Prog.DecConf

open SigabaNeo AdvancedEncryption.ExpLUT.Prog.DescTight

set_option exponentiation.threshold 2000 in
theorem descTight_dec_num : 6 * 2 ^ 28 * 3 ^ 256 * (4 + 4 * 256 + 29) ≤ 2 ^ 447 := by
  norm_num

/-- **The description length of the concrete `Dec` machine**, tight entry width. -/
theorem descLen_decMachine_tight : decMachine.descLen ≤ 2 ^ 447 := by
  rw [decMachine, descLen_decMP_eq]
  exact (descTight_arith size_decProgram (by norm_num : (2 : ℕ) ^ 28 < 2 ^ 29)).trans
    descTight_dec_num

end AdvancedEncryption.ExpLUT.Prog.DecConf
