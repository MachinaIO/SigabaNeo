import PE.Impl.DualUse.Params.Strength.CheckA

/-! Block sizes `[9400, 11500)` of the strength check of `params3` at `confA`
(`Params/StrengthA.lean`), by kernel evaluation, in pieces of 256 (each piece is checked
separately, which bounds the memory of the kernel). -/

namespace AdvancedEncryption.DualUse.Params.Strength

open SigabaNeo.Lattices.Estimator

theorem scanA3_5_0 : allRange 9400 256 (chkA3) = true := by decide +kernel

theorem scanA3_5_1 : allRange 9656 256 (chkA3) = true := by decide +kernel

theorem scanA3_5_2 : allRange 9912 256 (chkA3) = true := by decide +kernel

theorem scanA3_5_3 : allRange 10168 256 (chkA3) = true := by decide +kernel

theorem scanA3_5_4 : allRange 10424 256 (chkA3) = true := by decide +kernel

theorem scanA3_5_5 : allRange 10680 256 (chkA3) = true := by decide +kernel

theorem scanA3_5_6 : allRange 10936 256 (chkA3) = true := by decide +kernel

theorem scanA3_5_7 : allRange 11192 256 (chkA3) = true := by decide +kernel

theorem scanA3_5_8 : allRange 11448 52 (chkA3) = true := by decide +kernel

theorem scanA3_5 : ∀ b, 9400 ≤ b → b < 11500 → chkA3 b = true :=
  range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (allRange_spec scanA3_5_0)
    (allRange_spec scanA3_5_1))
    (allRange_spec scanA3_5_2))
    (allRange_spec scanA3_5_3))
    (allRange_spec scanA3_5_4))
    (allRange_spec scanA3_5_5))
    (allRange_spec scanA3_5_6))
    (allRange_spec scanA3_5_7))
    (allRange_spec scanA3_5_8)

end AdvancedEncryption.DualUse.Params.Strength
