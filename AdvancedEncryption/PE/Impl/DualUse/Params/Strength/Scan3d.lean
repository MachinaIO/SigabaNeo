import PE.Impl.DualUse.Params.Strength.Check

/-! Block sizes `[6144, 8192)` of the strength check of `params3` (`Params/Strength.lean`), by
kernel evaluation, in pieces of 256 (each piece is checked separately, which bounds the memory
of the kernel). -/

namespace AdvancedEncryption.DualUse.Params.Strength

open SigabaNeo.Lattices.Estimator

theorem scan3_3_0 : allRange 6144 256 (chk3) = true := by decide +kernel

theorem scan3_3_1 : allRange 6400 256 (chk3) = true := by decide +kernel

theorem scan3_3_2 : allRange 6656 256 (chk3) = true := by decide +kernel

theorem scan3_3_3 : allRange 6912 256 (chk3) = true := by decide +kernel

theorem scan3_3_4 : allRange 7168 256 (chk3) = true := by decide +kernel

theorem scan3_3_5 : allRange 7424 256 (chk3) = true := by decide +kernel

theorem scan3_3_6 : allRange 7680 256 (chk3) = true := by decide +kernel

theorem scan3_3_7 : allRange 7936 256 (chk3) = true := by decide +kernel

theorem scan3_3 : ∀ b, 6144 ≤ b → b < 8192 → chk3 b = true :=
  range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (allRange_spec scan3_3_0)
    (allRange_spec scan3_3_1))
    (allRange_spec scan3_3_2))
    (allRange_spec scan3_3_3))
    (allRange_spec scan3_3_4))
    (allRange_spec scan3_3_5))
    (allRange_spec scan3_3_6))
    (allRange_spec scan3_3_7)

end AdvancedEncryption.DualUse.Params.Strength
