import PE.Impl.RingBTVW.Params.Strength.CheckA

/-! Block sizes `[4096, 6144)` of the strength check of `params3` at `confA`
(`Params/StrengthA.lean`), by kernel evaluation, in pieces of 256 (each piece is checked
separately, which bounds the memory of the kernel). -/

namespace AdvancedEncryption.RingBTVW.Params.Strength

open SigabaNeo.Lattices.Estimator

theorem scanA3_2_0 : allRange 4096 256 (chkA3) = true := by decide +kernel

theorem scanA3_2_1 : allRange 4352 256 (chkA3) = true := by decide +kernel

theorem scanA3_2_2 : allRange 4608 256 (chkA3) = true := by decide +kernel

theorem scanA3_2_3 : allRange 4864 256 (chkA3) = true := by decide +kernel

theorem scanA3_2_4 : allRange 5120 256 (chkA3) = true := by decide +kernel

theorem scanA3_2_5 : allRange 5376 256 (chkA3) = true := by decide +kernel

theorem scanA3_2_6 : allRange 5632 256 (chkA3) = true := by decide +kernel

theorem scanA3_2_7 : allRange 5888 256 (chkA3) = true := by decide +kernel

theorem scanA3_2 : ∀ b, 4096 ≤ b → b < 6144 → chkA3 b = true :=
  range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (allRange_spec scanA3_2_0)
    (allRange_spec scanA3_2_1))
    (allRange_spec scanA3_2_2))
    (allRange_spec scanA3_2_3))
    (allRange_spec scanA3_2_4))
    (allRange_spec scanA3_2_5))
    (allRange_spec scanA3_2_6))
    (allRange_spec scanA3_2_7)

end AdvancedEncryption.RingBTVW.Params.Strength
