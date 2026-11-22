import PE.Impl.DualUse.Params.Strength.Check

/-! Block sizes `[8192, 9400)` of the strength check of `params5` (`Params/Strength.lean`), by
kernel evaluation, in pieces of 256 (each piece is checked separately, which bounds the memory
of the kernel). -/

namespace AdvancedEncryption.DualUse.Params.Strength

open SigabaNeo.Lattices.Estimator

theorem scan5_4_0 : allRange 8192 256 (chk5) = true := by decide +kernel

theorem scan5_4_1 : allRange 8448 256 (chk5) = true := by decide +kernel

theorem scan5_4_2 : allRange 8704 256 (chk5) = true := by decide +kernel

theorem scan5_4_3 : allRange 8960 256 (chk5) = true := by decide +kernel

theorem scan5_4_4 : allRange 9216 184 (chk5) = true := by decide +kernel

theorem scan5_4 : ∀ b, 8192 ≤ b → b < 9400 → chk5 b = true :=
  range_glue (range_glue (range_glue (range_glue (allRange_spec scan5_4_0)
    (allRange_spec scan5_4_1))
    (allRange_spec scan5_4_2))
    (allRange_spec scan5_4_3))
    (allRange_spec scan5_4_4)

end AdvancedEncryption.DualUse.Params.Strength
