import PE.Impl.ExpLUT.Prog.EncSamplers
import PE.Impl.ExpLUT.Prog.SetupConf
import PE.Impl.ExpLUT.AH.Conf
/-!
# The samplers of `Enc` and the cost of `Setup` at `Dc`

Package P's laws are the generic ones at `Dc`: `χc = cbdR Dc 16` and `χfl = floodR Dc eFl`
(`rfl`), so the ring samplers `cbdRP Dc 16 6` (leaves of `6` bits, `16 + 1 ≤ 2^5`) and
`floodP Dc eFl` (`eFl = 400 < 2^16`) realize them exactly (`law_χcP`, `law_χflP`). The `Setup`
machine with the binary sampler at `Dc`: clock `≤ 2^242`, description length `≤ 2^249`.
-/

namespace AdvancedEncryption.ExpLUT.Prog
namespace EncConf

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg
open AdvancedEncryption.RingBTVW.Prog AdvancedEncryption.ExpLUT.Params

theorem χc_eq : χc = cbdR Dc 16 := rfl

theorem χfl_eq : χfl = floodR Dc eFl := rfl

/-- **The sampler of `χc`.** -/
theorem law_χcP : AppendLaw (cbdRP Dc 16 6) 0 P5 (χc.map (rEnc Dc).enc) :=
  law_cbdRP Dc (by norm_num) (by show 6 ≤ Kc; rw [Kc_def]; norm_num) (by norm_num)

/-- **The sampler of `χfl`.** -/
theorem law_χflP : AppendLaw (floodP Dc eFl) 0 P5 (χfl.map (rEnc Dc).enc) :=
  law_floodP Dc (by show eFl < Kc; rw [eFl_def, Kc_def]; norm_num)

theorem Dc_K : Dc.K = 2 ^ 16 := by show Kc = _; rw [Kc_def]

theorem Dc_mb : Dc.mb = 3 * 2 ^ 40 + 408 := by
  show mbar = _; rw [mbar_def, Kc_def]; norm_num

/-- **The clock of `Setup` at `Dc`.** -/
theorem time_setupMP_Dc : (setupMP (binSampler Dc)).time ≤ 2 ^ 242 :=
  time_setupMP_conf Dc rfl Dc_K rfl Dc_mb

/-- **The description length of `Setup` at `Dc`.** -/
theorem descLen_setupMP_Dc : (setupMP (binSampler Dc)).descLen ≤ 2 ^ 249 :=
  descLen_setupMP_conf Dc rfl Dc_K rfl Dc_mb

end EncConf
end AdvancedEncryption.ExpLUT.Prog
