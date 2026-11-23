import PE.Impl.ExpLUT.Params.Strength.Check

/-! Block sizes `[8192, 10240)` of the strength check `chkB` (`N = 2^23`, `Params/Strength.lean`),
by kernel evaluation, in pieces of at most 256 (each piece is checked separately, which bounds
the memory of the kernel). -/

namespace AdvancedEncryption.ExpLUT.Params

open SigabaNeo.Lattices.Estimator

theorem scanB_4_0 : allRange 8192 256 chkB = true := by decide +kernel

theorem scanB_4_1 : allRange 8448 256 chkB = true := by decide +kernel

theorem scanB_4_2 : allRange 8704 256 chkB = true := by decide +kernel

theorem scanB_4_3 : allRange 8960 256 chkB = true := by decide +kernel

theorem scanB_4_4 : allRange 9216 256 chkB = true := by decide +kernel

theorem scanB_4_5 : allRange 9472 256 chkB = true := by decide +kernel

theorem scanB_4_6 : allRange 9728 256 chkB = true := by decide +kernel

theorem scanB_4_7 : allRange 9984 256 chkB = true := by decide +kernel

theorem scanB_4 : ∀ b, 8192 ≤ b → b < 10240 → chkB b = true :=
  range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (allRange_spec scanB_4_0)
    (allRange_spec scanB_4_1))
    (allRange_spec scanB_4_2))
    (allRange_spec scanB_4_3))
    (allRange_spec scanB_4_4))
    (allRange_spec scanB_4_5))
    (allRange_spec scanB_4_6))
    (allRange_spec scanB_4_7)

end AdvancedEncryption.ExpLUT.Params
