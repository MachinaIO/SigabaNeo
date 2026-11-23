import PE.Impl.DualUse.Prog.SizeConf
import PE.Impl.DualUse.Prog.SetupCostP
import PE.Impl.DualUse.Prog.EncCostP

/-!
# The clocks of `Setup` and `Enc` at `confP`

`time_setupMP_conf`, `time_encMP_conf`: closed bounds of the clocks of the compiled `Setup` and
`Enc` with the sampler `chiSamplerP`, from the uniform bounds `ub_setupP`, `ub_encP`; the
primitive programs are bounded by `tbC · (L + 1) ^ tbD` (constants by the kernel).
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg AdvancedEncryption.DualUse.Params
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow

/-! ### The primitive programs -/

theorem tb_le' {k : ℕ} {p : Prog k} (h : p.NoGrow) {C D : ℕ} (hC : Prog.tbC p ≤ C)
    (hD : Prog.tbD p ≤ D) (L : ℕ) : Prog.timeBound p L ≤ C * (L + 1) ^ D :=
  (Prog.timeBound_le p h L).trans (Nat.mul_le_mul hC (Nat.pow_le_pow_right (by omega) hD))

theorem tbs_splitP : Prog.tbD Prog.splitP ≤ 8 ∧ Prog.tbC Prog.splitP ≤ 2 ^ 20 := by decide +kernel
theorem tbs_joinP : Prog.tbD Prog.joinP ≤ 8 ∧ Prog.tbC Prog.joinP ≤ 2 ^ 20 := by decide +kernel
theorem tbs_subRWP : Prog.tbD Prog.subRWP ≤ 8 ∧ Prog.tbC Prog.subRWP ≤ 2 ^ 20 := by decide +kernel
theorem tbs_addRWP : Prog.tbD Prog.addRWP ≤ 8 ∧ Prog.tbC Prog.addRWP ≤ 2 ^ 20 := by decide +kernel
theorem tbs_gadP : Prog.tbD Prog.gadP ≤ 8 ∧ Prog.tbC Prog.gadP ≤ 2 ^ 20 := by decide +kernel
theorem tbs_matMulP : Prog.tbD Prog.matMulP ≤ 16 ∧ Prog.tbC Prog.matMulP ≤ 2 ^ 30 := by
  decide +kernel
theorem tbs_encCoreP : Prog.tbD encCoreP ≤ 32 ∧ Prog.tbC encCoreP ≤ 2 ^ 40 := by decide +kernel

theorem tb_splitP (L : ℕ) : Prog.timeBound Prog.splitP L ≤ 2 ^ 20 * (L + 1) ^ 8 :=
  tb_le' Prog.noGrow_splitP tbs_splitP.2 tbs_splitP.1 L
theorem tb_joinP (L : ℕ) : Prog.timeBound Prog.joinP L ≤ 2 ^ 20 * (L + 1) ^ 8 :=
  tb_le' Prog.noGrow_joinP tbs_joinP.2 tbs_joinP.1 L
theorem tb_subRWP (L : ℕ) : Prog.timeBound Prog.subRWP L ≤ 2 ^ 20 * (L + 1) ^ 8 :=
  tb_le' Prog.noGrow_subRWP tbs_subRWP.2 tbs_subRWP.1 L
theorem tb_addRWP (L : ℕ) : Prog.timeBound Prog.addRWP L ≤ 2 ^ 20 * (L + 1) ^ 8 :=
  tb_le' Prog.noGrow_addRWP tbs_addRWP.2 tbs_addRWP.1 L
theorem tb_gadP (L : ℕ) : Prog.timeBound Prog.gadP L ≤ 2 ^ 20 * (L + 1) ^ 8 :=
  tb_le' Prog.noGrow_gadP tbs_gadP.2 tbs_gadP.1 L
theorem tb_matMulP (L : ℕ) : Prog.timeBound Prog.matMulP L ≤ 2 ^ 30 * (L + 1) ^ 16 :=
  tb_le' Prog.noGrow_matMulP tbs_matMulP.2 tbs_matMulP.1 L
theorem tb_encCoreP (L : ℕ) : Prog.timeBound encCoreP L ≤ 2 ^ 40 * (L + 1) ^ 32 :=
  tb_le' noGrow_encCoreP tbs_encCoreP.2 tbs_encCoreP.1 L

/-! ### `Setup` -/

/-- A closed form above `timeC0`. -/
def timeC0L (oB oS d N K M : ℕ) : ℕ :=
  (2 * oB + 1) * (4 * M + 12) + (2 * (d * (N * K)) + 1) * (4 * M + 12) +
    (2 * oS + 1) * (4 * M + 12) + (2 * (N * K) + 1) * (4 * M + 12) +
    (2 * (d * (N * K)) + 1) * (4 * M + 12) + (2 * K + 1) * (4 * M + 12) +
    (2 * N + 1) * (4 * M + 12) + (2 * 1 + 1) * (4 * M + 12) + (2 * 1 + 1) * (4 * M + 12) +
    (2 * d + 1) * (4 * M + 12) + (2 * (1 * d * (N * K)) + 1) * (4 * M + 12) +
    (2 * (1 * d * N) + 1) * (4 * M + 12) +
    2 ^ 20 * (M + 1) ^ 8 + 2 ^ 20 * (M + 1) ^ 8 + 2 ^ 30 * (M + 1) ^ 16 +
    2 ^ 20 * (M + 1) ^ 8 + (2 * (M + 1) + 3) +
    (c0Tapes.length * (2 * (M + 1 + 1) + 3) + (2 * (M + 1 + 1) + 3))

theorem timeC0_le (oB oS d N K M : ℕ) : timeC0 oB oS d N K M ≤ timeC0L oB oS d N K M := by
  unfold timeC0 timeC0L
  have := tb_splitP M; have := tb_matMulP M; have := tb_addRWP M
  omega

/-- A closed form above `timeB1`. -/
def timeB1L (N K k M : ℕ) : ℕ :=
  (2 * K + 1) * (4 * M + 12) + (2 * N + 1) * (4 * M + 12) + (2 * (N * K) + 1) * (4 * M + 12) +
    (2 * k + 1) * (4 * M + 12) + (2 * rowL N K k + 1) * (4 * M + 12) +
    (2 * rowL N K k + 1) * (4 * M + 12) + (2 * (1 * (2 * k) * N) + 1) * (4 * M + 12) +
    (2 * (N * K + rowL N K k + rowL N K k) + 1) * (4 * M + 12) +
    2 ^ 20 * (M + 1) ^ 8 + 2 ^ 20 * (M + 1) ^ 8 + 2 ^ 20 * (M + 1) ^ 8 +
    (2 * (N * K - 1) + 1) * (4 * M + 12) + (2 * (M + 1) + 3) +
    2 ^ 20 * (M + 1 + 1) ^ 8 +
    (b1Tapes.length * (2 * (M + 1 + 1) + 3) + (2 * (M + 1 + 1) + 3))

theorem timeB1_le (N K k M : ℕ) : timeB1 N K k M ≤ timeB1L N K k M := by
  unfold timeB1 timeB1L
  have := tb_splitP M; have := tb_gadP M; have := tb_subRWP M; have := tb_joinP (M + 1)
  omega

/-- `detT` with the closed forms of `timeC0`, `timeB1`. -/
def detTL (N K k M : ℕ) : ℕ :=
  let A1 := apGS M
  let A2 := apGS A1
  let C1 := A2 + 1
  let A3 := apGS C1
  let B1 := A3 + 1
  let A4 := apGS B1
  let A5 := apGS A4
  let A6 := apGS A5
  let F1 := apGS A6
  let A7 := apGS F1
  let A8 := apGS A7
  (2 * (M + 1) + 3) + (((2 * (M + 1) + 3) + appT M) + (((2 * (A1 + 1) + 3) + appT A1) +
    (timeC0L 0 (2 * k * (N * K)) (2 * k) N K A2 + ((2 * (C1 + 1) + 3) + ((2 * (C1 + 1) + 3) +
    (((2 * (C1 + 1) + 3) + appT C1) + (timeB1L N K k A3 + ((2 * (B1 + 1) + 3) + ((2 * (B1 + 1) + 3) +
    (((2 * (B1 + 1) + 3) + appT B1) + (((2 * (A4 + 1) + 3) + appT A4) +
    (((2 * (A5 + 1) + 3) + appT A5) + (appT A6 + (((2 * (F1 + 1) + 3) + appT F1) +
    (((2 * (A7 + 1) + 3) + appT A7) + appT A8)))))))))))))))

theorem detT_le (N K k M : ℕ) : detT N K k M ≤ detTL N K k M := by
  unfold detT detTL
  have h1 := timeC0_le 0 (2 * k * (N * K)) (2 * k) N K (apGS (apGS M))
  have h2 := timeB1_le N K k (apGS (apGS (apGS M) + 1))
  dsimp only
  omega

/-- The linear forms of the coins' clock. -/
abbrev linC (n x : ℕ) : ℕ := (8 * n + 8 + n * (6 + 3)) * (x + x + (n * 1 + n * 0 + 3 + 3))

/-- The linear forms of a counted sampler's clock. -/
abbrev linX (a s w E n x : ℕ) : ℕ :=
  (8 * n + 8 + n * (w + 3)) * (x + x + (n * a + n * s + E + 3))

/-- `setupST` with the linear bounds of the samplers. -/
def setupSTL {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) (a s w E M : ℕ) : ℕ :=
  let M1 := M + nRowD N K c.d * 1 + nRowD N K c.d * 0
  let M2 := M1 + nRowC N K k * 1 + nRowC N K k * 0
  let M3 := M2 + N * a + N * s
  let M4 := M3 + (Enum.list (α := RingBTVW.Col k)).length * N * a +
    (Enum.list (α := RingBTVW.Col k)).length * N * s
  let M5 := M4 + nBj (N := N) hk * 1 + nBj (N := N) hk * 0
  linC (nRowD N K c.d) M + (linC (nRowC N K k) M1 + (linX a s w E N M2 +
    (linX a s w E ((Enum.list (α := RingBTVW.Col k)).length * N) M3 +
    (linC (nBj (N := N) hk) M4 + linC (N * K) M5))))

theorem setupST_le {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) {Bχ : Bnd} {w E : ℕ}
    (hB : Lin Bχ.T w E) (M : ℕ) : setupST hk c Bχ M ≤ setupSTL hk c Bχ.a Bχ.s w E M := by
  unfold setupST setupSTL
  exact Nat.add_le_add (lin_bCoins _ _ _) (Nat.add_le_add (lin_bCoins _ _ _)
    (Nat.add_le_add (lin_Bcount hB _ _ _) (Nat.add_le_add (lin_Bcount hB _ _ _)
      (Nat.add_le_add (lin_bCoins _ _ _) (lin_bCoins _ _ _)))))

theorem chiB : chiSamplerP.B = bChi := rfl

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4000 in
theorem setupS_conf : setupS hkp confP chiSamplerP.B (2 ^ 181) ≤ 2 ^ 182 := by
  simp only [setupS, bCoins, Bnd.count, bCoin, chiB, bChi_a, bChi_s, nRowD, nRowC, nBj]
  comp_unfold
  norm_num

end AdvancedEncryption.DualUse.Prog

namespace AdvancedEncryption.DualUse.Prog
open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg AdvancedEncryption.DualUse.Params

theorem detTL_mono (N K k : ℕ) {M M' : ℕ} (h : M ≤ M') : detTL N K k M ≤ detTL N K k M' := by
  simp only [detTL, timeC0L, timeB1L, appT, forT, loopT, stepT, apGS]
  gcongr

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 4000 in
theorem detTL_conf : detTL Np Kp kp (2 ^ 182) ≤ 2 ^ 3100 := by
  rw [kp_eq, Np_def, Kp_def]
  simp only [detTL, timeC0L, timeB1L, appT, forT, loopT, stepT, apGS, c0Tapes, b1Tapes, rowL]
  norm_num

theorem nRowD_conf : nRowD Np Kp confP.d = 2 ^ 61 * (2 ^ 34 * 2 ^ 25) := by
  simp only [nRowD, len_fin, confP_d, Np_def, Kp_def, Nat.one_mul]
theorem nRowC_conf : nRowC Np Kp kp = 2 * (2 ^ 25 + 1) * (2 ^ 34 * 2 ^ 25) := by
  simp only [nRowC, len_fin, len_col, Np_def, kp_eq, Kp_def, Nat.one_mul]
theorem nBj_conf : nBj (N := Np) (K := Kp) hkp = 10 * (2 * (2 * (2 ^ 25 + 1) * ((2 ^ 25 + 1) * 2 ^ 34))) *
    (2 * (2 ^ 25 + 1) * (2 ^ 34 * 2 ^ 25)) := by
  simp only [nBj, nRowC, Enum.length_prod, len_fin, len_col, len_Attr, len_Index, Np_def, kp_eq, Kp_def,
    Nat.one_mul]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 4000 in
theorem setupSTL_conf : setupSTL hkp confP Kp 64 (2 ^ 40) (2 ^ 40) (2 ^ 181) ≤ 2 ^ 600 := by
  unfold setupSTL
  rw [nRowD_conf, nRowC_conf, nBj_conf, len_col, kp_eq, Np_def, Kp_def]
  simp only [linC, linX]
  norm_num

theorem detG_le (M : ℕ) : detG M ≤ 2 ^ 30 * (M + 1) := by
  simp only [detG, apGS]; omega

theorem nInS_le : nInS ≤ 2 ^ 181 := by
  have h515 := length_paramsWord_date
  simp only [nInS, DualUse.pw, encodeTuple, Turing.MultiTapeTM.length_encList] at h515 ⊢
  norm_num at h515 ⊢
  omega

set_option exponentiation.threshold 4000 in
/-- **The clock of `Setup` at `confP`.** -/
theorem time_setupMP_conf : (setupMP hkp confP chiSamplerP).time ≤ 2 ^ 3200 := by
  obtain ⟨c1, c2, c3, c4, c5, c6, -, -, -⟩ := setup_counts
  have hK : bChi.S₀ ≤ 2 ^ 181 := bChi_S₀.trans (by rw [Kp_def]; norm_num)
  have hn := nInS_le
  have hSz : sizeC0 0 (2 * kp * (Np * Kp)) (2 * kp) Np Kp ≤ 2 ^ 181 ∧ sizeB1 Np Kp kp ≤ 2 ^ 181 := by
    rw [kp_eq, Np_def, Kp_def]; simp only [sizeC0, sizeB1, rowL]; norm_num
  have hS : 2 ^ 181 ≤ setupS hkp confP chiSamplerP.B (2 ^ 181) := by
    simp only [setupS]; omega
  have u := ub_setupP hkp confP (X := chiSamplerP) (2 ^ 181)
    (by simp only [bCoins, Bnd.count, bCoin]; omega) (by simp only [bCoins, Bnd.count, bCoin]; omega)
    (by show max bChi.S₀ _ ≤ _; omega) (by show max bChi.S₀ _ ≤ _; omega)
    (by simp only [bCoins, Bnd.count, bCoin]; omega) (by simp only [bCoins, Bnd.count, bCoin]; omega)
    preserves6_chiP (by simp only [apGS]; omega) (by simp only [apGS]; omega)
    (Prog.inputBound 94 nInS) (fun i => by
      simp only [Prog.inputBound, Function.update_apply]; split_ifs <;> omega)
  rw [time_setupMP]
  have hT := u.1
  have hL := (u.2 91).trans (detG_le _)
  have hST := (setupST_le hkp confP (Bχ := chiSamplerP.B) lin_bChi (2 ^ 181)).trans
    (le_of_eq (by rw [chiB, bChi_a, bChi_s]))
  have hSc := setupS_conf
  have hD := (detT_le Np Kp kp (setupS hkp confP chiSamplerP.B (2 ^ 181))).trans
    ((detTL_mono Np Kp kp hSc).trans detTL_conf)
  have hST' := hST.trans setupSTL_conf
  have hL' : 2 ^ 30 * (setupS hkp confP chiSamplerP.B (2 ^ 181) + 1) ≤ 2 ^ 30 * (2 ^ 182 + 1) := by
    gcongr
  calc 2 * nInS + 2 + timeBoundT (setupP hkp confP chiSamplerP) (Prog.inputBound 94 nInS) +
        (2 * lenBoundT (setupP hkp confP chiSamplerP) (Prog.inputBound 94 nInS) 91 + 2)
      ≤ 2 * 2 ^ 181 + 2 + (2 ^ 600 + 2 ^ 3100) + (2 * (2 ^ 30 * (2 ^ 182 + 1)) + 2) := by
        gcongr
        · exact hT.trans (Nat.add_le_add hST' hD)
        · exact hL.trans hL'
    _ ≤ 2 ^ 3200 := by norm_num

end AdvancedEncryption.DualUse.Prog
