import PE.Impl.ExpLUT.Params.Strength.Check

/-! Block sizes `[10240, 12288)` of the strength check `chkA` (`N = 2^24`, `Params/Strength.lean`),
by kernel evaluation, in pieces of at most 256 (each piece is checked separately, which bounds
the memory of the kernel). -/

namespace AdvancedEncryption.ExpLUT.Params

open SigabaNeo.Lattices.Estimator

theorem scanA_5_0 : allRange 10240 256 chkA = true := by decide +kernel

theorem scanA_5_1 : allRange 10496 256 chkA = true := by decide +kernel

theorem scanA_5_2 : allRange 10752 256 chkA = true := by decide +kernel

theorem scanA_5_3 : allRange 11008 256 chkA = true := by decide +kernel

theorem scanA_5_4 : allRange 11264 256 chkA = true := by decide +kernel

theorem scanA_5_5 : allRange 11520 256 chkA = true := by decide +kernel

theorem scanA_5_6 : allRange 11776 256 chkA = true := by decide +kernel

theorem scanA_5_7 : allRange 12032 256 chkA = true := by decide +kernel

theorem scanA_5 : ∀ b, 10240 ≤ b → b < 12288 → chkA b = true :=
  range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (allRange_spec scanA_5_0)
    (allRange_spec scanA_5_1))
    (allRange_spec scanA_5_2))
    (allRange_spec scanA_5_3))
    (allRange_spec scanA_5_4))
    (allRange_spec scanA_5_5))
    (allRange_spec scanA_5_6))
    (allRange_spec scanA_5_7)

end AdvancedEncryption.ExpLUT.Params
