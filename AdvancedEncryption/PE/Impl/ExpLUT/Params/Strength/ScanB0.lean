import PE.Impl.ExpLUT.Params.Strength.Check

/-! Block sizes `[0, 2048)` of the strength check `chkB` (`N = 2^23`, `Params/Strength.lean`),
by kernel evaluation, in pieces of at most 256 (each piece is checked separately, which bounds
the memory of the kernel). -/

namespace AdvancedEncryption.ExpLUT.Params

open SigabaNeo.Lattices.Estimator

theorem scanB_0_0 : allRange 0 256 chkB = true := by decide +kernel

theorem scanB_0_1 : allRange 256 256 chkB = true := by decide +kernel

theorem scanB_0_2 : allRange 512 256 chkB = true := by decide +kernel

theorem scanB_0_3 : allRange 768 256 chkB = true := by decide +kernel

theorem scanB_0_4 : allRange 1024 256 chkB = true := by decide +kernel

theorem scanB_0_5 : allRange 1280 256 chkB = true := by decide +kernel

theorem scanB_0_6 : allRange 1536 256 chkB = true := by decide +kernel

theorem scanB_0_7 : allRange 1792 256 chkB = true := by decide +kernel

theorem scanB_0 : ∀ b, 0 ≤ b → b < 2048 → chkB b = true :=
  range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (allRange_spec scanB_0_0)
    (allRange_spec scanB_0_1))
    (allRange_spec scanB_0_2))
    (allRange_spec scanB_0_3))
    (allRange_spec scanB_0_4))
    (allRange_spec scanB_0_5))
    (allRange_spec scanB_0_6))
    (allRange_spec scanB_0_7)

end AdvancedEncryption.ExpLUT.Params
