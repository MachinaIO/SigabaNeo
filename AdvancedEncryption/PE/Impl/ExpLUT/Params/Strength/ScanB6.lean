import PE.Impl.ExpLUT.Params.Strength.Check
/-! Block sizes `[12288, 14336)` of the strength check `chkB` (`N = 2^23`, `Params/Strength.lean`),
by kernel evaluation, in pieces of at most 256 (each piece is checked separately, which bounds
the memory of the kernel). -/

namespace AdvancedEncryption.ExpLUT.Params

open SigabaNeo.Lattices.Estimator

theorem scanB_6_0 : allRange 12288 256 chkB = true := by decide +kernel

theorem scanB_6_1 : allRange 12544 256 chkB = true := by decide +kernel

theorem scanB_6_2 : allRange 12800 256 chkB = true := by decide +kernel

theorem scanB_6_3 : allRange 13056 256 chkB = true := by decide +kernel

theorem scanB_6_4 : allRange 13312 256 chkB = true := by decide +kernel

theorem scanB_6_5 : allRange 13568 256 chkB = true := by decide +kernel

theorem scanB_6_6 : allRange 13824 256 chkB = true := by decide +kernel

theorem scanB_6_7 : allRange 14080 256 chkB = true := by decide +kernel

theorem scanB_6 : ∀ b, 12288 ≤ b → b < 14336 → chkB b = true :=
  range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (allRange_spec scanB_6_0)
    (allRange_spec scanB_6_1))
    (allRange_spec scanB_6_2))
    (allRange_spec scanB_6_3))
    (allRange_spec scanB_6_4))
    (allRange_spec scanB_6_5))
    (allRange_spec scanB_6_6))
    (allRange_spec scanB_6_7)

end AdvancedEncryption.ExpLUT.Params
