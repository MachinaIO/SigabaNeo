import PE.Impl.ExpLUT.Params.Strength.Check

/-! Block sizes `[12288, 14336)` of the strength check `chkA` (`N = 2^24`, `Params/Strength.lean`),
by kernel evaluation, in pieces of at most 256 (each piece is checked separately, which bounds
the memory of the kernel). -/

namespace AdvancedEncryption.ExpLUT.Params

open SigabaNeo.Lattices.Estimator

theorem scanA_6_0 : allRange 12288 256 chkA = true := by decide +kernel

theorem scanA_6_1 : allRange 12544 256 chkA = true := by decide +kernel

theorem scanA_6_2 : allRange 12800 256 chkA = true := by decide +kernel

theorem scanA_6_3 : allRange 13056 256 chkA = true := by decide +kernel

theorem scanA_6_4 : allRange 13312 256 chkA = true := by decide +kernel

theorem scanA_6_5 : allRange 13568 256 chkA = true := by decide +kernel

theorem scanA_6_6 : allRange 13824 256 chkA = true := by decide +kernel

theorem scanA_6_7 : allRange 14080 256 chkA = true := by decide +kernel

theorem scanA_6 : ∀ b, 12288 ≤ b → b < 14336 → chkA b = true :=
  range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (allRange_spec scanA_6_0)
    (allRange_spec scanA_6_1))
    (allRange_spec scanA_6_2))
    (allRange_spec scanA_6_3))
    (allRange_spec scanA_6_4))
    (allRange_spec scanA_6_5))
    (allRange_spec scanA_6_6))
    (allRange_spec scanA_6_7)

end AdvancedEncryption.ExpLUT.Params
