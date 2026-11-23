import PE.Impl.DualUse.Params.Strength.CheckA

/-! Block sizes `[0, 2048)` of the strength check of `params5` at `confA`
(`Params/StrengthA.lean`), by kernel evaluation, in pieces of 256 (each piece is checked
separately, which bounds the memory of the kernel). -/

namespace AdvancedEncryption.DualUse.Params.Strength

open SigabaNeo.Lattices.Estimator

theorem scanA5_0_0 : allRange 0 256 (chkA5) = true := by decide +kernel

theorem scanA5_0_1 : allRange 256 256 (chkA5) = true := by decide +kernel

theorem scanA5_0_2 : allRange 512 256 (chkA5) = true := by decide +kernel

theorem scanA5_0_3 : allRange 768 256 (chkA5) = true := by decide +kernel

theorem scanA5_0_4 : allRange 1024 256 (chkA5) = true := by decide +kernel

theorem scanA5_0_5 : allRange 1280 256 (chkA5) = true := by decide +kernel

theorem scanA5_0_6 : allRange 1536 256 (chkA5) = true := by decide +kernel

theorem scanA5_0_7 : allRange 1792 256 (chkA5) = true := by decide +kernel

theorem scanA5_0 : ∀ b, 0 ≤ b → b < 2048 → chkA5 b = true :=
  range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (allRange_spec scanA5_0_0)
    (allRange_spec scanA5_0_1))
    (allRange_spec scanA5_0_2))
    (allRange_spec scanA5_0_3))
    (allRange_spec scanA5_0_4))
    (allRange_spec scanA5_0_5))
    (allRange_spec scanA5_0_6))
    (allRange_spec scanA5_0_7)

end AdvancedEncryption.DualUse.Params.Strength
