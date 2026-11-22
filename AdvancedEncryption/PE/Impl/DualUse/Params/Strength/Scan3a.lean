import PE.Impl.DualUse.Params.Strength.Check

/-! Block sizes `[0, 2048)` of the strength check of `params3` (`Params/Strength.lean`), by
kernel evaluation, in pieces of 256 (each piece is checked separately, which bounds the memory
of the kernel). -/

namespace AdvancedEncryption.DualUse.Params.Strength

open SigabaNeo.Lattices.Estimator

theorem scan3_0_0 : allRange 0 256 (chk3) = true := by decide +kernel

theorem scan3_0_1 : allRange 256 256 (chk3) = true := by decide +kernel

theorem scan3_0_2 : allRange 512 256 (chk3) = true := by decide +kernel

theorem scan3_0_3 : allRange 768 256 (chk3) = true := by decide +kernel

theorem scan3_0_4 : allRange 1024 256 (chk3) = true := by decide +kernel

theorem scan3_0_5 : allRange 1280 256 (chk3) = true := by decide +kernel

theorem scan3_0_6 : allRange 1536 256 (chk3) = true := by decide +kernel

theorem scan3_0_7 : allRange 1792 256 (chk3) = true := by decide +kernel

theorem scan3_0 : ∀ b, 0 ≤ b → b < 2048 → chk3 b = true :=
  range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (allRange_spec scan3_0_0)
    (allRange_spec scan3_0_1))
    (allRange_spec scan3_0_2))
    (allRange_spec scan3_0_3))
    (allRange_spec scan3_0_4))
    (allRange_spec scan3_0_5))
    (allRange_spec scan3_0_6))
    (allRange_spec scan3_0_7)

end AdvancedEncryption.DualUse.Params.Strength
