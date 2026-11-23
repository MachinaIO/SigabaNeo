import PE.Impl.DualUse.Params.Strength.CheckA

/-! Block sizes `[6144, 8192)` of the strength check of `params5` at `confA`
(`Params/StrengthA.lean`), by kernel evaluation, in pieces of 256 (each piece is checked
separately, which bounds the memory of the kernel). -/

namespace AdvancedEncryption.DualUse.Params.Strength

open SigabaNeo.Lattices.Estimator

theorem scanA5_3_0 : allRange 6144 256 (chkA5) = true := by decide +kernel

theorem scanA5_3_1 : allRange 6400 256 (chkA5) = true := by decide +kernel

theorem scanA5_3_2 : allRange 6656 256 (chkA5) = true := by decide +kernel

theorem scanA5_3_3 : allRange 6912 256 (chkA5) = true := by decide +kernel

theorem scanA5_3_4 : allRange 7168 256 (chkA5) = true := by decide +kernel

theorem scanA5_3_5 : allRange 7424 256 (chkA5) = true := by decide +kernel

theorem scanA5_3_6 : allRange 7680 256 (chkA5) = true := by decide +kernel

theorem scanA5_3_7 : allRange 7936 256 (chkA5) = true := by decide +kernel

theorem scanA5_3 : ∀ b, 6144 ≤ b → b < 8192 → chkA5 b = true :=
  range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (allRange_spec scanA5_3_0)
    (allRange_spec scanA5_3_1))
    (allRange_spec scanA5_3_2))
    (allRange_spec scanA5_3_3))
    (allRange_spec scanA5_3_4))
    (allRange_spec scanA5_3_5))
    (allRange_spec scanA5_3_6))
    (allRange_spec scanA5_3_7)

end AdvancedEncryption.DualUse.Params.Strength
