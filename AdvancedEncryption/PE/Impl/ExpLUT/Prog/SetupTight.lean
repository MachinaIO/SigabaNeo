import PE.Impl.ExpLUT.Prog.SetupConf
import PE.Impl.ExpLUT.Prog.DescTightBase

/-!
# Tight clock and description length of `Setup` at the concrete dimensions

* **`time_setupMP_conf_tight`**: the clock is at most `2^241`. The closed form `setupTFn` is linear in
  the tape cap `M` (dominant term `(2M + 3) · 22 N² K² · m̄ K`); the cap only has to cover
  `m̄ K · N K = 3 · 2^96 + 408 · 2^56` and the sampler scratch `S + 8K` with `S = 2^97`, so
  `M = 3 · 2^96 + 2^90` instead of `2^98` (`≈ 2^240.63`).
* **`descLen_setupMP_conf_tight`**: the description length is at most `2^233`. The state count is
  recounted with the exact sizes of the fixed blocks (`detCore = 28995`, `outP = 3597`,
  `ucTail = 1492`, … by `decide +kernel`, instead of the slack constant `2 · 10^6`) and each of
  the `34` counter templates `natP` at its own bit length (`195` states per bit) instead of the
  common `97`: `size + 4 ≤ 360000 < 2^19` (`size_setupP_tight`), and the entry width is
  `4 + 4·128 + 19` bits (`log₂(6 · 360000 · 3^128 · 535) ≈ 232.98`).
-/

set_option autoImplicit false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg SigabaNeo.Tape.Sym
open AdvancedEncryption.RingBTVW.Prog AdvancedEncryption.ExpLUT.Prog.DescTight


/-! ### The exact sizes of the fixed blocks (kernel-evaluated) -/

theorem stTight_forCoin : (forN (4 : Fin 7) 3 (coinAp 0 2)).size = 208 := by decide +kernel
theorem stTight_coinAp : (coinAp (0 : Fin 7) 2).size = 133 := by decide +kernel
theorem stTight_forZero : (forN (4 : Fin 7) 3 (bitAp 0 false)).size = 135 := by decide +kernel
theorem stTight_ucTail : ucTail.size = 1492 := by decide +kernel
theorem stTight_appUC : (appendTapeP (0 : Fin 40) 33 35 36).size = 279 := by decide +kernel
theorem stTight_detCore : detCore.size = 28995 := by decide +kernel
theorem stTight_outP : (outP).size = 3597 := by decide +kernel

theorem stTight_coinsF {n m : ℕ} (h : n < 2 ^ m) : (coinsF n).size ≤ 195 * m + 280 := by
  have h1 := size_natP_le (3 : Fin 7) 4 n m h
  have h2 := stTight_forCoin
  have e : (prog (.prim (.clear (3 : Fin 7)))).size = 36 := rfl
  simp only [coinsF, withCount, XProg.size_seq] at *
  omega

/-- The canonical uniform sampler, with a separate bit length for each counter. -/
theorem stTight_unifCanonP {N K n m1 m2 : ℕ} (h1 : n * (N * K) < 2 ^ m1) (hK : K < 2 ^ 17)
    (h2 : n * N < 2 ^ m2) : (unifCanonP N K n).size ≤ 195 * (m1 + m2 + 17) + 2123 := by
  have c1 := stTight_coinsF h1
  have c2 := size_natP_le (7 : Fin 40) 34 K 17 hK
  have c3 := size_natP_le (8 : Fin 40) 34 (n * N) m2 h2
  have c4 := stTight_ucTail
  have c5 := stTight_appUC
  simp only [unifCanonP, XProg.size_seq, XProg.size_frame, XProg.size_prog]
  omega

theorem stTight_entB {N K m : ℕ} (h : N * K - 1 < 2 ^ m) : (entB N K).size ≤ 195 * m + 340 := by
  have h1 := size_natP_le (3 : Fin 7) 4 (N * K - 1) m h
  have h2 := stTight_coinAp
  have h3 := stTight_forZero
  have e : (prog (.prim (.clear (3 : Fin 7)))).size = 36 := rfl
  simp only [entB, zerosF, withCount, XProg.size_seq] at *
  omega

set_option maxRecDepth 100000 in
/-- The closed form at the concrete dimensions with the cap `M = 3 · 2^96 + 2^90`. -/
theorem setupTFn_tight : setupTFn (2 ^ 24) (2 ^ 16) 22 (3 * 2 ^ 40 + 408)
    (bEntB (2 ^ 24) (2 ^ 16)) (2 ^ 11) (2 ^ 97) (3 * 2 ^ 96 + 2 ^ 90) ≤ 2 ^ 241 := by
  decide +kernel


set_option exponentiation.threshold 2000 in
theorem stTight_desc_num : 6 * 360000 * 3 ^ 128 * (4 + 4 * 128 + 19) ≤ 2 ^ 233 := by
  norm_num

section ConcTight

variable (D : Dims) (he : D.e = 24) (hK : D.K = 2 ^ 16) (hb : D.b = 22)
  (hmb : D.mb = 3 * 2 ^ 40 + 408)
include he hK hb hmb

theorem setupBounds_tight :
    SetupBounds D (binSampler D).B (2 ^ 11) (2 ^ 97) (3 * 2 ^ 96 + 2 ^ 90) := by
  have eB : (binSampler D).B = bEntB D.N D.K := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [nB2_eq, nH_eq, nA_eq, nA0_eq, nAin_eq, nAaut_eq, Dims.N, he, hK, hb, hmb]
    decide +kernel
  · rw [eB]; simp only [Dims.N, he, hK]; decide +kernel
  · rw [eB]; simp only [Dims.N, he, hK]; decide +kernel
  · rw [eB]; simp only [sT, Dims.N, he, hK, hmb]; decide +kernel
  · decide +kernel
  · simp only [Dims.N, he, hK]; decide +kernel
  · simp only [Dims.N, he, hK, hmb]; decide +kernel

/-- **The clock of `Setup` at the concrete dimensions**: at most `2^241` steps. -/
theorem time_setupMP_conf_tight : (setupMP (binSampler D)).time ≤ 2 ^ 241 := by
  have h := time_setupMP_le (binSampler D) (setupBounds_tight D he hK hb hmb) nInS_le
  have eB : (binSampler D).B = bEntB D.N D.K := rfl
  rw [setupTF_eq, eB] at h
  simp only [Dims.N, he, hK, hb, hmb] at h
  exact h.trans setupTFn_tight


/-- **The state count of `Setup`**, every counter charged at its own bit length:
`size + 4 ≤ 360000 < 2^19` (the sum of the bounds is `≈ 348670`). -/
theorem size_setupP_tight : (setupP (binSampler D)).size + 4 ≤ 360000 := by
  have hN : D.N = 2 ^ 24 := by simp only [Dims.N, he]
  have hK17 : D.K < 2 ^ 17 := by rw [hK]; decide
  have u1 := stTight_unifCanonP (N := D.N) (K := D.K) (n := D.mb) (m1 := 82) (m2 := 66) (by rw [hN, hK, hmb]; decide +kernel) hK17 (by rw [hN, hmb]; decide +kernel)
  have u2 := stTight_unifCanonP (N := D.N) (K := D.K) (n := nB2 D) (m1 := 82) (m2 := 66) (by rw [nB2_eq, hN, hK, hmb]; decide +kernel) hK17 (by rw [nB2_eq, hN, hK, hmb]; decide +kernel)
  have u3 := stTight_unifCanonP (N := D.N) (K := D.K) (n := nH D) (m1 := 64) (m2 := 48) (by rw [nH_eq, hN, hK, hb]; decide +kernel) hK17 (by rw [nH_eq, hN, hK, hb]; decide +kernel)
  have u4 := stTight_unifCanonP (N := D.N) (K := D.K) (n := nA D) (m1 := 62) (m2 := 46) (by rw [nA_eq, hN, hK]; decide +kernel) hK17 (by rw [nA_eq, hN, hK]; decide +kernel)
  have u5 := stTight_unifCanonP (N := D.N) (K := D.K) (n := nA0 D) (m1 := 59) (m2 := 43) (by rw [nA0_eq, hN, hK]; decide +kernel) hK17 (by rw [nA0_eq, hN, hK]; decide +kernel)
  have u6 := stTight_unifCanonP (N := D.N) (K := D.K) (n := nAin D) (m1 := 97) (m2 := 81) (by rw [nAin_eq, hN, hK]; decide +kernel) hK17 (by rw [nAin_eq, hN, hK]; decide +kernel)
  have u7 := stTight_unifCanonP (N := D.N) (K := D.K) (n := nAaut D) (m1 := 97) (m2 := 81) (by rw [nAaut_eq, hN, hK, hb]; decide +kernel) hK17 (by rw [nAaut_eq, hN, hK, hb]; decide +kernel)
  have u8 := stTight_unifCanonP (N := D.N) (K := D.K) (n := 2) (m1 := 42) (m2 := 26) (by rw [hN, hK]; decide +kernel) hK17 (by rw [hN]; decide +kernel)
  have hP : (binSampler D).P.size ≤ 195 * 40 + 340 :=
    stTight_entB (by rw [hN, hK]; decide +kernel)
  have hr := size_repF_le (binSampler D).P (n := D.mb * D.K) (m := 58) (by rw [hK, hmb]; decide +kernel)
  have t1 := size_natP_le (40 : Fin 128) 125 D.K 17 hK17
  have t2 := size_natP_le (41 : Fin 128) 125 D.N 25 (by rw [hN]; decide)
  have t3 := size_natP_le (42 : Fin 128) 125 (D.N * D.K) 41 (by rw [hN, hK]; decide +kernel)
  have t4 := size_natP_le (43 : Fin 128) 125 1 1 (by decide)
  have t5 := size_natP_le (44 : Fin 128) 125 D.mb 42 (by rw [hmb]; decide +kernel)
  have t6 := size_natP_le (45 : Fin 128) 125 D.K 17 hK17
  have t7 := size_natP_le (46 : Fin 128) 125 (D.K * (D.N * D.K)) 57 (by rw [hN, hK]; decide +kernel)
  have t8 := size_natP_le (47 : Fin 128) 125 (D.K - 1) 16 (by rw [hK]; decide)
  have t9 := size_natP_le (48 : Fin 128) 125 (D.N * D.K - 1) 40 (by rw [hN, hK]; decide +kernel)
  have e : (prog (.prim (.cons (48 : Fin 128) true))).size = 60 := rfl
  have hd := stTight_detCore
  have ho := stTight_outP
  simp only [setupP, tmplP, XProg.size_seq, XProg.size_frame, XProg.size_prog] at *
  omega

omit he hK hb hmb in
theorem stTight_descLen_eq : (setupMP (binSampler D)).descLen =
    6 * ((setupP (binSampler D)).size + 4) * 3 ^ 128 * 3 ^ 0 *
      Machine.entryBits 128 ((setupP (binSampler D)).size + 4) 0 := by
  rw [Machine.descLen, setupMP, states_toMachineT, XProg.card_state]
  rfl

/-- **The description length of `Setup` at the concrete dimensions**: at most `2^233` bits. -/
theorem descLen_setupMP_conf_tight : (setupMP (binSampler D)).descLen ≤ 2 ^ 233 := by
  rw [stTight_descLen_eq]
  exact (descTight_arith (size_setupP_tight D he hK hb hmb)
    (by norm_num : (360000 : ℕ) < 2 ^ 19)).trans stTight_desc_num

end ConcTight

end AdvancedEncryption.ExpLUT.Prog
