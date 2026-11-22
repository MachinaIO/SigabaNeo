import PE.Impl.DualUse.Params.Strength.Check

/-! Block sizes `[14000, 16386)` of the strength check of `params3` (`Params/Strength.lean`), by
kernel evaluation, in pieces of 256 (each piece is checked separately, which bounds the memory
of the kernel). -/

namespace AdvancedEncryption.DualUse.Params.Strength

open SigabaNeo.Lattices.Estimator

theorem scan3_7_0 : allRange 14000 256 (chk3) = true := by decide +kernel

theorem scan3_7_1 : allRange 14256 256 (chk3) = true := by decide +kernel

theorem scan3_7_2 : allRange 14512 256 (chk3) = true := by decide +kernel

theorem scan3_7_3 : allRange 14768 256 (chk3) = true := by decide +kernel

theorem scan3_7_4 : allRange 15024 256 (chk3) = true := by decide +kernel

theorem scan3_7_5 : allRange 15280 256 (chk3) = true := by decide +kernel

theorem scan3_7_6 : allRange 15536 256 (chk3) = true := by decide +kernel

theorem scan3_7_7 : allRange 15792 256 (chk3) = true := by decide +kernel

theorem scan3_7_8 : allRange 16048 256 (chk3) = true := by decide +kernel

theorem scan3_7_9 : allRange 16304 82 (chk3) = true := by decide +kernel

theorem scan3_7 : ∀ b, 14000 ≤ b → b < 16386 → chk3 b = true :=
  range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (allRange_spec scan3_7_0)
    (allRange_spec scan3_7_1))
    (allRange_spec scan3_7_2))
    (allRange_spec scan3_7_3))
    (allRange_spec scan3_7_4))
    (allRange_spec scan3_7_5))
    (allRange_spec scan3_7_6))
    (allRange_spec scan3_7_7))
    (allRange_spec scan3_7_8))
    (allRange_spec scan3_7_9)

end AdvancedEncryption.DualUse.Params.Strength
