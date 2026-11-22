import PE.Impl.DualUse.Params.Strength.Check

/-! Block sizes `[11500, 14000)` of the strength check of `params3` (`Params/Strength.lean`), by
kernel evaluation, in pieces of 256 (each piece is checked separately, which bounds the memory
of the kernel). -/

namespace AdvancedEncryption.DualUse.Params.Strength

open SigabaNeo.Lattices.Estimator

theorem scan3_6_0 : allRange 11500 256 (chk3) = true := by decide +kernel

theorem scan3_6_1 : allRange 11756 256 (chk3) = true := by decide +kernel

theorem scan3_6_2 : allRange 12012 256 (chk3) = true := by decide +kernel

theorem scan3_6_3 : allRange 12268 256 (chk3) = true := by decide +kernel

theorem scan3_6_4 : allRange 12524 256 (chk3) = true := by decide +kernel

theorem scan3_6_5 : allRange 12780 256 (chk3) = true := by decide +kernel

theorem scan3_6_6 : allRange 13036 256 (chk3) = true := by decide +kernel

theorem scan3_6_7 : allRange 13292 256 (chk3) = true := by decide +kernel

theorem scan3_6_8 : allRange 13548 256 (chk3) = true := by decide +kernel

theorem scan3_6_9 : allRange 13804 196 (chk3) = true := by decide +kernel

theorem scan3_6 : ∀ b, 11500 ≤ b → b < 14000 → chk3 b = true :=
  range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (allRange_spec scan3_6_0)
    (allRange_spec scan3_6_1))
    (allRange_spec scan3_6_2))
    (allRange_spec scan3_6_3))
    (allRange_spec scan3_6_4))
    (allRange_spec scan3_6_5))
    (allRange_spec scan3_6_6))
    (allRange_spec scan3_6_7))
    (allRange_spec scan3_6_8))
    (allRange_spec scan3_6_9)

end AdvancedEncryption.DualUse.Params.Strength
