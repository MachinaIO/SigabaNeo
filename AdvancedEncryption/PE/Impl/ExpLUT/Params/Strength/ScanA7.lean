import PE.Impl.ExpLUT.Params.Strength.Check
/-! Block sizes `[14336, 16386)` of the strength check `chkA` (`N = 2^24`, `Params/Strength.lean`),
by kernel evaluation, in pieces of at most 256 (each piece is checked separately, which bounds
the memory of the kernel). -/

namespace AdvancedEncryption.ExpLUT.Params

open SigabaNeo.Lattices.Estimator

theorem scanA_7_0 : allRange 14336 256 chkA = true := by decide +kernel

theorem scanA_7_1 : allRange 14592 256 chkA = true := by decide +kernel

theorem scanA_7_2 : allRange 14848 256 chkA = true := by decide +kernel

theorem scanA_7_3 : allRange 15104 256 chkA = true := by decide +kernel

theorem scanA_7_4 : allRange 15360 256 chkA = true := by decide +kernel

theorem scanA_7_5 : allRange 15616 256 chkA = true := by decide +kernel

theorem scanA_7_6 : allRange 15872 256 chkA = true := by decide +kernel

theorem scanA_7_7 : allRange 16128 256 chkA = true := by decide +kernel

theorem scanA_7_8 : allRange 16384 2 chkA = true := by decide +kernel

theorem scanA_7 : ∀ b, 14336 ≤ b → b < 16386 → chkA b = true :=
  range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (allRange_spec scanA_7_0)
    (allRange_spec scanA_7_1))
    (allRange_spec scanA_7_2))
    (allRange_spec scanA_7_3))
    (allRange_spec scanA_7_4))
    (allRange_spec scanA_7_5))
    (allRange_spec scanA_7_6))
    (allRange_spec scanA_7_7))
    (allRange_spec scanA_7_8)

end AdvancedEncryption.ExpLUT.Params
