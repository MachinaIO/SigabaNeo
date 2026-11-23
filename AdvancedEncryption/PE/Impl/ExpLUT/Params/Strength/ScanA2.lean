import PE.Impl.ExpLUT.Params.Strength.Check

/-! Block sizes `[4096, 6144)` of the strength check `chkA` (`N = 2^24`, `Params/Strength.lean`),
by kernel evaluation, in pieces of at most 256 (each piece is checked separately, which bounds
the memory of the kernel). -/

namespace AdvancedEncryption.ExpLUT.Params

open SigabaNeo.Lattices.Estimator

theorem scanA_2_0 : allRange 4096 256 chkA = true := by decide +kernel

theorem scanA_2_1 : allRange 4352 256 chkA = true := by decide +kernel

theorem scanA_2_2 : allRange 4608 256 chkA = true := by decide +kernel

theorem scanA_2_3 : allRange 4864 256 chkA = true := by decide +kernel

theorem scanA_2_4 : allRange 5120 256 chkA = true := by decide +kernel

theorem scanA_2_5 : allRange 5376 256 chkA = true := by decide +kernel

theorem scanA_2_6 : allRange 5632 256 chkA = true := by decide +kernel

theorem scanA_2_7 : allRange 5888 256 chkA = true := by decide +kernel

theorem scanA_2 : ∀ b, 4096 ≤ b → b < 6144 → chkA b = true :=
  range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (allRange_spec scanA_2_0)
    (allRange_spec scanA_2_1))
    (allRange_spec scanA_2_2))
    (allRange_spec scanA_2_3))
    (allRange_spec scanA_2_4))
    (allRange_spec scanA_2_5))
    (allRange_spec scanA_2_6))
    (allRange_spec scanA_2_7)

end AdvancedEncryption.ExpLUT.Params
