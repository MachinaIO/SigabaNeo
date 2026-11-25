import PE.Impl.ExpLUT.Prog.EncMachine
import PE.Impl.ExpLUT.Prog.EncSamplersConf
/-! # The concrete package-P encryption machine -/
namespace AdvancedEncryption.ExpLUT.Prog.EncConf
open SigabaNeo AdvancedEncryption.ExpLUT.Params

/-- The explicit parser/sampler/encryptor at the package's dimensions and noise laws. -/
noncomputable def encMachine : Machine := EncW.encMP Dc 16 6 eFl

/-- Package P's encryption machine realizes its exact prescribed law. -/
theorem encSpec_encMachine : EncSpec Dc χc χc χfl encMachine := by
  rw [χc_eq, χfl_eq]
  exact EncW.encSpec_encMP Dc (by norm_num)
    (by show 6 ≤ Kc; rw [Kc_def]; norm_num) (by norm_num)
    (by show eFl < Kc; rw [eFl_def, Kc_def]; norm_num)
    (by show 0 < 22; norm_num)
    (by show 2 ≤ 2 ^ 24; norm_num)
    (by show (2 : ℕ) ^ 14 * 128 ≤ 2 * 2 ^ 24; norm_num)

end AdvancedEncryption.ExpLUT.Prog.EncConf
