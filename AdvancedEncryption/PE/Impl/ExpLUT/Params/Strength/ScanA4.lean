import PE.Impl.ExpLUT.Params.Strength.Check

/-! Block sizes `[8192, 10240)` of the strength check `chkA` (`N = 2^24`, `Params/Strength.lean`),
by kernel evaluation, in pieces of at most 256 (each piece is checked separately, which bounds
the memory of the kernel). -/

namespace AdvancedEncryption.ExpLUT.Params

open SigabaNeo.Lattices.Estimator

theorem scanA_4_0 : allRange 8192 256 chkA = true := by decide +kernel

theorem scanA_4_1 : allRange 8448 256 chkA = true := by decide +kernel

theorem scanA_4_2 : allRange 8704 256 chkA = true := by decide +kernel

theorem scanA_4_3 : allRange 8960 256 chkA = true := by decide +kernel

theorem scanA_4_4 : allRange 9216 256 chkA = true := by decide +kernel

theorem scanA_4_5 : allRange 9472 256 chkA = true := by decide +kernel

theorem scanA_4_6 : allRange 9728 256 chkA = true := by decide +kernel

theorem scanA_4_7 : allRange 9984 256 chkA = true := by decide +kernel

theorem scanA_4 : ∀ b, 8192 ≤ b → b < 10240 → chkA b = true :=
  range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (allRange_spec scanA_4_0)
    (allRange_spec scanA_4_1))
    (allRange_spec scanA_4_2))
    (allRange_spec scanA_4_3))
    (allRange_spec scanA_4_4))
    (allRange_spec scanA_4_5))
    (allRange_spec scanA_4_6))
    (allRange_spec scanA_4_7)

end AdvancedEncryption.ExpLUT.Params
