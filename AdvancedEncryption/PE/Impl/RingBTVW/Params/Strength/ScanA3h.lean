import PE.Impl.RingBTVW.Params.Strength.CheckA

/-! Block sizes `[14000, 16386)` of the strength check of `params3` at `confA`
(`Params/StrengthA.lean`), by kernel evaluation, in pieces of 256 (each piece is checked
separately, which bounds the memory of the kernel). -/

namespace AdvancedEncryption.RingBTVW.Params.Strength

open SigabaNeo.Lattices.Estimator

theorem scanA3_7_0 : allRange 14000 256 (chkA3) = true := by decide +kernel

theorem scanA3_7_1 : allRange 14256 256 (chkA3) = true := by decide +kernel

theorem scanA3_7_2 : allRange 14512 256 (chkA3) = true := by decide +kernel

theorem scanA3_7_3 : allRange 14768 256 (chkA3) = true := by decide +kernel

theorem scanA3_7_4 : allRange 15024 256 (chkA3) = true := by decide +kernel

theorem scanA3_7_5 : allRange 15280 256 (chkA3) = true := by decide +kernel

theorem scanA3_7_6 : allRange 15536 256 (chkA3) = true := by decide +kernel

theorem scanA3_7_7 : allRange 15792 256 (chkA3) = true := by decide +kernel

theorem scanA3_7_8 : allRange 16048 256 (chkA3) = true := by decide +kernel

theorem scanA3_7_9 : allRange 16304 82 (chkA3) = true := by decide +kernel

theorem scanA3_7 : ∀ b, 14000 ≤ b → b < 16386 → chkA3 b = true :=
  range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (allRange_spec scanA3_7_0)
    (allRange_spec scanA3_7_1))
    (allRange_spec scanA3_7_2))
    (allRange_spec scanA3_7_3))
    (allRange_spec scanA3_7_4))
    (allRange_spec scanA3_7_5))
    (allRange_spec scanA3_7_6))
    (allRange_spec scanA3_7_7))
    (allRange_spec scanA3_7_8))
    (allRange_spec scanA3_7_9)

end AdvancedEncryption.RingBTVW.Params.Strength
