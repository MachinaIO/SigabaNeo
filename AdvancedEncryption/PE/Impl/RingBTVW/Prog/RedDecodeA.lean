import PE.Impl.RingBTVW.Prog.Decode
import PE.Impl.RingBTVW.Params.Conf

/-!
# The decoders of the reductions at `confA`

At `confP` (the sizes of `confA`: `N = 2^36`, `K = 2^27`, `k = K + 1`, `d = 2^65`): the decoding
machines `dec3M`, `dec5M` of the reductions (instance words of the decision problems to state
words) run in at most `2^380` steps, with at most `2^16` states and `14` tapes
(`time_dec3M_confA`, `states_dec3M_confA`, `tapes_dec3M`, and the same for `dec5M`).

Generic in the sizes (`…_A` with `N`, `K`, `k`, `d` given by hypotheses), then instantiated.
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo AdvancedEncryption.RingBTVW.Params

set_option maxRecDepth 100000
set_option exponentiation.threshold 1000

theorem m3_eqA {k : ℕ} (hk : k = 2 ^ 26 + 1) : m3 k = 2 * (2 ^ 26 + 1) := by
  subst hk; simp [m3, Fintype.card_prod]

theorem m5_eqA {k d : ℕ} (hk : k = 2 ^ 26 + 1) (hd : d = 2 ^ 62) :
    m5 k d = 2 ^ 62 + (2 * (2 ^ 26 + 1) + (2 * (2 ^ 26 + 1) + 1)) := by
  subst hk hd; simp [m5, Idx5, Fintype.card_sum, Fintype.card_prod]

theorem time_dec3M_A {N K k : ℕ} (hN : N = 2 ^ 34) (hK : K = 2 ^ 26) (hk : k = 2 ^ 26 + 1) :
    (dec3M N K k).time ≤ 2 ^ 380 := by
  refine time_dec3M_le.trans ?_
  rw [m3_eqA hk]
  simp only [encLen]
  subst hN hK
  norm_num

theorem time_dec5M_A {N K k d : ℕ} (hN : N = 2 ^ 34) (hK : K = 2 ^ 26) (hk : k = 2 ^ 26 + 1)
    (hd : d = 2 ^ 62) : (dec5M N K k d).time ≤ 2 ^ 380 := by
  refine (time_dec5M_le _).trans ?_
  rw [m5_eqA hk hd]
  simp only [encLen]
  subst hN hK
  norm_num

theorem states_dec3M_A {N K k : ℕ} (hN : N = 2 ^ 34) (hK : K = 2 ^ 26) (hk : k = 2 ^ 26 + 1) :
    (dec3M N K k).states ≤ 2 ^ 16 := by
  refine (states_dec3M_le (m := 130) ?_ ?_).trans (by norm_num)
  · subst hK; norm_num
  · rw [m3_eqA hk]; subst hN hK; norm_num

theorem states_dec5M_A {N K k d : ℕ} (hN : N = 2 ^ 34) (hK : K = 2 ^ 26) (hk : k = 2 ^ 26 + 1)
    (hd : d = 2 ^ 62) : (dec5M N K k d).states ≤ 2 ^ 16 := by
  refine (states_dec5M_le _ (m := 130) ?_ ?_).trans (by norm_num)
  · subst hK; norm_num
  · rw [m5_eqA hk hd]; subst hN hK; norm_num

theorem kp_eqA : kp = 2 ^ 26 + 1 := by rw [kp, Kp_def]

theorem time_dec3M_confA : (dec3M Np Kp kp).time ≤ 2 ^ 380 := time_dec3M_A Np_def Kp_def kp_eqA

theorem time_dec5M_confA : (dec5M Np Kp kp confP.d).time ≤ 2 ^ 380 :=
  time_dec5M_A Np_def Kp_def kp_eqA dp_def

theorem states_dec3M_confA : (dec3M Np Kp kp).states ≤ 2 ^ 16 :=
  states_dec3M_A Np_def Kp_def kp_eqA

theorem states_dec5M_confA : (dec5M Np Kp kp confP.d).states ≤ 2 ^ 16 :=
  states_dec5M_A Np_def Kp_def kp_eqA dp_def

end AdvancedEncryption.RingBTVW.Prog
