import PE.Impl.RingBTVW.Params.Strength.CheckA

/-! Block sizes `[9400, 11500)` of the strength check of `params5` at `confA`
(`Params/StrengthA.lean`), by kernel evaluation, in pieces of 256 (each piece is checked
separately, which bounds the memory of the kernel). -/

namespace AdvancedEncryption.RingBTVW.Params.Strength

open SigabaNeo.Lattices.Estimator

theorem scanA5_5_0 : allRange 9400 256 (chkA5) = true := by decide +kernel

theorem scanA5_5_1 : allRange 9656 256 (chkA5) = true := by decide +kernel

theorem scanA5_5_2 : allRange 9912 256 (chkA5) = true := by decide +kernel

theorem scanA5_5_3 : allRange 10168 256 (chkA5) = true := by decide +kernel

theorem scanA5_5_4 : allRange 10424 256 (chkA5) = true := by decide +kernel

theorem scanA5_5_5 : allRange 10680 256 (chkA5) = true := by decide +kernel

theorem scanA5_5_6 : allRange 10936 256 (chkA5) = true := by decide +kernel

theorem scanA5_5_7 : allRange 11192 256 (chkA5) = true := by decide +kernel

theorem scanA5_5_8 : allRange 11448 52 (chkA5) = true := by decide +kernel

theorem scanA5_5 : ∀ b, 9400 ≤ b → b < 11500 → chkA5 b = true :=
  range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (allRange_spec scanA5_5_0)
    (allRange_spec scanA5_5_1))
    (allRange_spec scanA5_5_2))
    (allRange_spec scanA5_5_3))
    (allRange_spec scanA5_5_4))
    (allRange_spec scanA5_5_5))
    (allRange_spec scanA5_5_6))
    (allRange_spec scanA5_5_7))
    (allRange_spec scanA5_5_8)

end AdvancedEncryption.RingBTVW.Params.Strength
