import PE.Impl.ExpLUT.Params.Strength.Check
/-! Block sizes `[2048, 4096)` of the strength check `chkA` (`N = 2^24`, `Params/Strength.lean`),
by kernel evaluation, in pieces of at most 256 (each piece is checked separately, which bounds
the memory of the kernel). -/

namespace AdvancedEncryption.ExpLUT.Params

open SigabaNeo.Lattices.Estimator

theorem scanA_1_0 : allRange 2048 256 chkA = true := by decide +kernel

theorem scanA_1_1 : allRange 2304 256 chkA = true := by decide +kernel

theorem scanA_1_2 : allRange 2560 256 chkA = true := by decide +kernel

theorem scanA_1_3 : allRange 2816 256 chkA = true := by decide +kernel

theorem scanA_1_4 : allRange 3072 256 chkA = true := by decide +kernel

theorem scanA_1_5 : allRange 3328 256 chkA = true := by decide +kernel

theorem scanA_1_6 : allRange 3584 256 chkA = true := by decide +kernel

theorem scanA_1_7 : allRange 3840 256 chkA = true := by decide +kernel

theorem scanA_1 : ∀ b, 2048 ≤ b → b < 4096 → chkA b = true :=
  range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (allRange_spec scanA_1_0)
    (allRange_spec scanA_1_1))
    (allRange_spec scanA_1_2))
    (allRange_spec scanA_1_3))
    (allRange_spec scanA_1_4))
    (allRange_spec scanA_1_5))
    (allRange_spec scanA_1_6))
    (allRange_spec scanA_1_7)

end AdvancedEncryption.ExpLUT.Params
