import PE.Impl.DualUse.Prog.TightConf
import PE.Impl.DualUse.PUCodes

/-!
# The clock of `Setup` at the parameters of branching programs (Stage II)

The per-tape clock bound of `Setup` (`time_setupMP_tight`, `setupCostT_le`) is the closed form
`setupF N K k d nI G₀ a s w E n_A` in the sizes, with `n_A` the number of attribute bits. Here it is
evaluated at the numerals of `confA` (`N = 2^36`, `K = 2^27`, `k = 2^27 + 1`, `d = 2^65`,
`n_A = 128`), with an input of at most `2^16` bits and the χ sampler of `confP` scaled to
`K = 2^27` (thresholds and fair bits `≤ K`, `64` scratch bits, linear constants `2^40`):

* `setupF_confA`: the closed form lies strictly between `2^370` and `2^371` (`decide +kernel` on
  numerals);
* `time_setupMP_A`: for any configuration with these sizes, **`(setupMP hk c X).time ≤ 2^371`**.

The bound is dominated by the `n = nBj = 8 n_A k³ N² K ≈ 2^190` fair bits of the `B_j`
(`≈ 78 n²` steps). The hypotheses on `N, K, k, d, n_A` are those of `confA`; while
`nA = 10` (Stage I) the statement holds vacuously and is instantiated at the switch.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg SigabaNeo.Tape.Sym
open TightS

set_option maxRecDepth 100000 in
/-- **The closed bound at `confA`**, between `2^370` and `2^371`. -/
theorem setupF_confA :
    2 ^ 370 < setupF (2 ^ 34) (2 ^ 26) (2 ^ 26 + 1) (2 ^ 62) (2 ^ 16) (2 ^ 26) (2 ^ 26) 64
      (2 ^ 40) (2 ^ 40) 128 ∧
    setupF (2 ^ 34) (2 ^ 26) (2 ^ 26 + 1) (2 ^ 62) (2 ^ 16) (2 ^ 26) (2 ^ 26) 64 (2 ^ 40) (2 ^ 40)
      128 < 2 ^ 371 := by
  decide +kernel

/-- **The clock of `Setup` from the closed form**, for any configuration: the loader, the
per-tape bound of `setupP` and the emitter are at most `setupF` at the sizes. -/
theorem time_setupMP_le_setupF {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)
    (X : ChiSampler c) (nI G0 : ℕ) {w E : ℕ} (hnI : nInS ≤ nI) (hG1 : 1 ≤ G0)
    (hGS : X.B.S₀ ≤ G0) (hLin : Lin X.B.T w E) :
    (setupMP hk c X).time ≤ setupF N K k c.d nI G0 X.B.a X.B.s w E nA := by
  have h := time_setupMP_tight hk c X nI G0 hnI hG1 hGS
  have h2 := setupCostT_le hk c X nI G0 hLin
  have eρ : ρS c X nI G0 = [0, N, K, k, c.d, nI, G0, X.B.a, X.B.s, nA] := rfl
  rw [eρ] at h h2
  rw [setupF_eq]
  exact h.trans (Nat.add_le_add (Nat.add_le_add_left h2 _) le_rfl)

/-- **The clock of `Setup` at the sizes of `confA`**: at most `2^371` steps. -/
theorem time_setupMP_A {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) (X : ChiSampler c)
    (hN : N = 2 ^ 34) (hK : K = 2 ^ 26) (hkk : k = 2 ^ 26 + 1) (hd : c.d = 2 ^ 62)
    (hA : nA = 128) (hnI : nInS ≤ 2 ^ 16) (hGS : X.B.S₀ ≤ 2 ^ 26) (ha : X.B.a = 2 ^ 26)
    (hs : X.B.s = 64) (hLin : Lin X.B.T (2 ^ 40) (2 ^ 40)) :
    (setupMP hk c X).time ≤ 2 ^ 371 := by
  have h := time_setupMP_le_setupF hk c X (2 ^ 16) (2 ^ 26) hnI (Nat.one_le_two_pow) hGS hLin
  refine h.trans (le_of_lt (lt_of_eq_of_lt ?_ setupF_confA.2))
  rw [hd, ha, hs, hA, hN, hK, hkk]

open AdvancedEncryption.DualUse.Params in
theorem nInS_le_2_16 : nInS ≤ 2 ^ 16 := by
  have h515 := length_paramsWord_pu
  simp only [nInS, DualUse.pw, encodeTuple, Turing.MultiTapeTM.length_encList] at h515 ⊢
  norm_num at h515 ⊢
  omega

open AdvancedEncryption.DualUse.Params in
/-- **The clock of `Setup` at `confP`** (the sizes of `confA`): at most `2^371` steps. -/
theorem time_setupMP_conf' : (setupMP hkp confP chiSamplerP).time ≤ 2 ^ 371 :=
  time_setupMP_A hkp confP chiSamplerP Np_def Kp_def (by rw [kp, Kp_def]) dp_def rfl
    nInS_le_2_16 (bChi_S₀.trans (by rw [Kp_def])) (bChi_a.trans Kp_def) bChi_s lin_bChi

end AdvancedEncryption.DualUse.Prog
