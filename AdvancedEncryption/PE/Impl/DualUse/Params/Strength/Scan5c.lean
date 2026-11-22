import PE.Impl.DualUse.Params.Strength.Check

/-! Block sizes `[4096, 6144)` of the strength check of `params5` (`Params/Strength.lean`), by
kernel evaluation, in pieces of 256 (each piece is checked separately, which bounds the memory
of the kernel). -/

namespace AdvancedEncryption.DualUse.Params.Strength

open SigabaNeo.Lattices.Estimator

theorem scan5_2_0 : allRange 4096 256 (chk5) = true := by decide +kernel

theorem scan5_2_1 : allRange 4352 256 (chk5) = true := by decide +kernel

theorem scan5_2_2 : allRange 4608 256 (chk5) = true := by decide +kernel

theorem scan5_2_3 : allRange 4864 256 (chk5) = true := by decide +kernel

theorem scan5_2_4 : allRange 5120 256 (chk5) = true := by decide +kernel

theorem scan5_2_5 : allRange 5376 256 (chk5) = true := by decide +kernel

theorem scan5_2_6 : allRange 5632 256 (chk5) = true := by decide +kernel

theorem scan5_2_7 : allRange 5888 256 (chk5) = true := by decide +kernel

theorem scan5_2 : ∀ b, 4096 ≤ b → b < 6144 → chk5 b = true :=
  range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (allRange_spec scan5_2_0)
    (allRange_spec scan5_2_1))
    (allRange_spec scan5_2_2))
    (allRange_spec scan5_2_3))
    (allRange_spec scan5_2_4))
    (allRange_spec scan5_2_5))
    (allRange_spec scan5_2_6))
    (allRange_spec scan5_2_7)

end AdvancedEncryption.DualUse.Params.Strength
