import PE.Impl.DualUse.Params.Strength.Check

/-! Block sizes `[2048, 4096)` of the strength check of `params5` (`Params/Strength.lean`), by
kernel evaluation, in pieces of 256 (each piece is checked separately, which bounds the memory
of the kernel). -/

namespace AdvancedEncryption.DualUse.Params.Strength

open SigabaNeo.Lattices.Estimator

theorem scan5_1_0 : allRange 2048 256 (chk5) = true := by decide +kernel

theorem scan5_1_1 : allRange 2304 256 (chk5) = true := by decide +kernel

theorem scan5_1_2 : allRange 2560 256 (chk5) = true := by decide +kernel

theorem scan5_1_3 : allRange 2816 256 (chk5) = true := by decide +kernel

theorem scan5_1_4 : allRange 3072 256 (chk5) = true := by decide +kernel

theorem scan5_1_5 : allRange 3328 256 (chk5) = true := by decide +kernel

theorem scan5_1_6 : allRange 3584 256 (chk5) = true := by decide +kernel

theorem scan5_1_7 : allRange 3840 256 (chk5) = true := by decide +kernel

theorem scan5_1 : ∀ b, 2048 ≤ b → b < 4096 → chk5 b = true :=
  range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (allRange_spec scan5_1_0)
    (allRange_spec scan5_1_1))
    (allRange_spec scan5_1_2))
    (allRange_spec scan5_1_3))
    (allRange_spec scan5_1_4))
    (allRange_spec scan5_1_5))
    (allRange_spec scan5_1_6))
    (allRange_spec scan5_1_7)

end AdvancedEncryption.DualUse.Params.Strength
