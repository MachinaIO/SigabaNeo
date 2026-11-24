import PE.Impl.DualUse.Prog.Decode
import PE.Impl.DualUse.Params.Conf

/-!
# The decoders at the concrete parameters

At `confP` = `confA` (`N = 2^36`, `K = 2^27`, `k = K + 1`, `d = 2^65`): the decoding machines of the
reductions run in at most `2^350` (`dec3M`, `< 2^291`) and `2^365` (`dec5M`) steps, with at most `2^16` states and `14` tapes
(`time_dec3M_conf`, `states_dec3M_conf`, `tapes_dec3M`, and the same for `dec5M`).
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo AdvancedEncryption.DualUse.Params

set_option maxRecDepth 100000
set_option exponentiation.threshold 1000

theorem m3_conf : m3 kp = 2 * (2 ^ 26 + 1) := by
  simp [m3, Fintype.card_prod, kp, Kp_def]

theorem confD : confP.d = 2 ^ 62 := dp_def

theorem m5_conf : m5 kp confP.d = 2 ^ 62 + (2 * (2 ^ 26 + 1) + (2 * (2 ^ 26 + 1) + 1)) := by
  simp [m5, Idx5, Fintype.card_sum, Fintype.card_prod, kp, Kp_def, confD]

theorem time_dec3M_conf : (dec3M Np Kp kp).time ≤ 2 ^ 350 := by
  refine time_dec3M_le.trans ?_
  simp only [m3_conf, encLen, Np_def, Kp_def]
  norm_num

theorem time_dec5M_conf : (dec5M Np Kp kp confP.d).time ≤ 2 ^ 365 := by
  refine (time_dec5M_le _).trans ?_
  simp only [m5_conf, encLen, Np_def, Kp_def]
  norm_num

theorem states_dec3M_conf : (dec3M Np Kp kp).states ≤ 2 ^ 16 := by
  refine (states_dec3M_le (m := 120) ?_ ?_).trans (by norm_num)
  · rw [Kp_def]; norm_num
  · simp only [m3_conf, Np_def, Kp_def]; norm_num

theorem states_dec5M_conf : (dec5M Np Kp kp confP.d).states ≤ 2 ^ 16 := by
  refine (states_dec5M_le _ (m := 130) ?_ ?_).trans (by norm_num)
  · rw [Kp_def]; norm_num
  · simp only [m5_conf, Np_def, Kp_def]; norm_num

end AdvancedEncryption.DualUse.Prog
