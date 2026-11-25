import PE.Impl.RingBTVW.Params.Strength.CheckA

/-! Block sizes `[8192, 9400)` of the strength check of `params3` at `confA`
(`Params/StrengthA.lean`), by kernel evaluation, in pieces of 256 (each piece is checked
separately, which bounds the memory of the kernel). -/

namespace AdvancedEncryption.RingBTVW.Params.Strength

open SigabaNeo.Lattices.Estimator

theorem scanA3_4_0 : allRange 8192 256 (chkA3) = true := by decide +kernel

theorem scanA3_4_1 : allRange 8448 256 (chkA3) = true := by decide +kernel

theorem scanA3_4_2 : allRange 8704 256 (chkA3) = true := by decide +kernel

theorem scanA3_4_3 : allRange 8960 256 (chkA3) = true := by decide +kernel

theorem scanA3_4_4 : allRange 9216 184 (chkA3) = true := by decide +kernel

theorem scanA3_4 : ∀ b, 8192 ≤ b → b < 9400 → chkA3 b = true :=
  range_glue (range_glue (range_glue (range_glue (allRange_spec scanA3_4_0)
    (allRange_spec scanA3_4_1))
    (allRange_spec scanA3_4_2))
    (allRange_spec scanA3_4_3))
    (allRange_spec scanA3_4_4)

end AdvancedEncryption.RingBTVW.Params.Strength
