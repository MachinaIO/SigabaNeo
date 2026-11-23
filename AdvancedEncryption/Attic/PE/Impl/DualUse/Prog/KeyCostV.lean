import PE.Impl.DualUse.Prog.KeyTrySimConf

/-!
# The key component of the reductions at `confP`, per tape

`time_keyP_conf` (`KeyCostP`) bounds the key component of the reductions at `confP` by
`2^T + 2^2045`: the simulated key try charged uniformly (`tbC · (2M + 1)^8`, `M ≈ 2^251`). With the
`W_f` block leaving only tapes `0`, `2` nonblank (as `wfB2` does, `wfB2_clear`):

* `pEval_wKS_conf`: the sweeps of the simulated key try at `confP` are at most `2^240` (checked by
  evaluation), so the key try costs at most `(2 · 2^251 + 3) · 2^240`;
* `winRV_conf`: the window branch after the `W_f` block takes at most `2^512` steps;
* **`time_keyP_confV`**: the key component takes at most **`2^T + 2^520`** steps on queries of at most
  `confP.L` bits, and leaves at most `2^252` bits on tape `0`;
* **`size_keyP_confV`**: for a `W_f` block of at most `2^30` states and a window width
  `384 ≤ Wg ≤ 2^20`, the key component has at most `264 · lenPK + 2^140 ≈ 2^182.4` states (the
  prefixes of the public key dominate).
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg AdvancedEncryption.DualUse.Params
open AdvancedEncryption.DualUse.Algo AdvancedEncryption.DualUse.Algo.Params
open SigabaNeo.Lattices.Algo
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPWord

set_option maxRecDepth 100000
set_option exponentiation.threshold 3000

theorem lenPK_le' : lenPK hkp confP ≤ 2 ^ 175 := by rw [lenPK_eq]; norm_num

theorem simTop_conf : simTop hkp confP (2 ^ 250) ≤ 2 ^ 251 := by
  have := lenPK_le'
  simp only [simTop]
  generalize lenPK hkp confP = P at *
  have : (2 : ℕ) ^ 175 + 1 ≤ 2 ^ 250 := by norm_num
  have : (2 : ℕ) ^ 251 = 2 ^ 250 + 2 ^ 250 := by norm_num
  omega

theorem simTop_ge : 2 ^ 250 ≤ simTop hkp confP (2 ^ 250) := by simp only [simTop]; omega

/-- The arithmetic of `winRV_conf`. -/
theorem winRV_arith (P T m W : ℕ) (hP : P ≤ 2 ^ 175) (hT : T ≤ 2 ^ 251) (hm : m ≤ 2 ^ 120)
    (hW : W ≤ 2 ^ 240) :
    prefT P (2 ^ 250) + (2 ^ 25 + 1) * (2 * (T + 2 ^ 25 + 1) + 3) +
      (2 ^ 25 + 1) * (2 * (T + 2 ^ 25 + 1) + 3) + 21 * ((2 * T + 1) * (4 * T + 12)) +
      (coinT T m + (2 * T + 3) * W) + (25 * (2 * (T + 1) + 3) + (2 * (T + 1) + 3)) ≤ 2 ^ 512 := by
  unfold prefT coinT
  calc _ ≤ (2 * (2 ^ 250 + 1) + 3) + (2 ^ 175 * (6 * (2 ^ 250 + 1 + 2 ^ 175) + 13) +
          2 * (2 ^ 250 + 1 + 2 ^ 175) + 3) + (2 * (2 ^ 250 + 1 + 2 ^ 175 + 1) + 3) +
        (2 ^ 25 + 1) * (2 * (2 ^ 251 + 2 ^ 25 + 1) + 3) +
        (2 ^ 25 + 1) * (2 * (2 ^ 251 + 2 ^ 25 + 1) + 3) +
        21 * ((2 * 2 ^ 251 + 1) * (4 * 2 ^ 251 + 12)) +
        ((2 * (2 * (2 ^ 251 + 1) + 3) + (2 ^ 120 * (8 * 2 ^ 251 + 34) + 2)) +
          (2 * 2 ^ 251 + 3) * 2 ^ 240) +
        (25 * (2 * (2 ^ 251 + 1) + 3) + (2 * (2 ^ 251 + 1) + 3)) := by gcongr
    _ ≤ 2 ^ 512 := by norm_num

/-- **The window branch after the `W_f` block at `confP`, per tape.** -/
theorem winRV_conf : winRV hkp confP (2 ^ 250) cfP (2 ^ 240) ≤ 2 ^ 512 :=
  (winRV_le hkp confP (2 ^ 250) cfP (2 ^ 240) lenPK_le' simTop_conf length_sW_cfP.le
    length_powW_cfP.le mBp_le).trans
    (winRV_arith (2 ^ 175) (2 ^ 251) (2 ^ 120) (2 ^ 240) le_rfl le_rfl le_rfl le_rfl)

theorem tmpl_simTop : ∀ x ∈ keyTmpl hkp confP cfP, x.2 ≤ simTop hkp confP (2 ^ 250) :=
  fun x hx => (le_tmplMax _ x hx).trans (tmplMax_conf.trans
    ((show (2 : ℕ) ^ 182 ≤ 2 ^ 250 by norm_num).trans simTop_ge))

/-- **`winRest` at `confP`, per tape**, from `v02 (2^250)`. -/
theorem ph_winRest_conf :
    Ph (winRest hkp confP cfP) (v02 (2 ^ 250)) (2 ^ 512) (fun _ => 2 ^ 251) :=
  (ph_winRest_v hkp confP (2 ^ 250) cfP pEval_wKS_conf (length_sW_cfP.trans_le Kp_def.ge)
    (length_powW_cfP.trans_le Kp_def.ge)
    (Kp_def.le.trans ((by norm_num : (2 : ℕ) ^ 25 ≤ 2 ^ 250).trans simTop_ge)) tmpl_simTop).mono
    le_rfl winRV_conf (fun _ => simTop_conf)

/-- The arithmetic of `dumT_confV`. -/
theorem dumT_arith {M : ℕ} (hM : M ≤ 2 ^ 240) :
    (2 * (M + 1) + 3) + prefT (2 ^ 175) M + putT (2 ^ 130) (M + 1 + 2 ^ 175) +
      (2 * (M + 1 + 2 ^ 175 + 2 ^ 130 + 1 + 1) + 3) +
      (2 * (M + 1 + 2 ^ 175 + 2 ^ 130 + 1 + 1 + 1) + 3) ≤ 2 ^ 420 := by
  unfold prefT putT
  calc _ ≤ (2 * (2 ^ 240 + 1) + 3) + ((2 * (2 ^ 240 + 1) + 3) +
          (2 ^ 175 * (6 * (2 ^ 240 + 1 + 2 ^ 175) + 13) + 2 * (2 ^ 240 + 1 + 2 ^ 175) + 3) +
          (2 * (2 ^ 240 + 1 + 2 ^ 175 + 1) + 3)) +
        (2 ^ 130 + 1) * (2 * (2 ^ 240 + 1 + 2 ^ 175 + 2 ^ 130 + 1) + 3) +
        (2 * (2 ^ 240 + 1 + 2 ^ 175 + 2 ^ 130 + 1 + 1) + 3) +
        (2 * (2 ^ 240 + 1 + 2 ^ 175 + 2 ^ 130 + 1 + 1 + 1) + 3) := by gcongr
    _ ≤ 2 ^ 420 := by norm_num

/-- The dummy branch from tapes below `M ≤ 2^240`. -/
theorem dumT_confV {M : ℕ} (hM : M ≤ 2 ^ 240) : dumT hkp confP M ≤ 2 ^ 420 :=
  (dumT_le hkp confP M lenPK_le' lenDummy_le).trans (dumT_arith hM)

/-! ### The key component -/

/-- **The time and length bounds of the key component at `confP`, per tape**: for a `W_f` block
taking at most `2^T` steps on its input and leaving only tapes `0`, `2` nonblank, at most `2^250`
bits. -/
theorem time_keyP_confV {sdP : XProg 82} {Ls : ℕ}
    (hsT : timeBoundT sdP (io2 (R := 80) Ls 0 0) ≤ 2 ^ 500)
    (hsL : lenBoundT sdP (io2 (R := 80) Ls 0 0) ≤ io2 (2 ^ 240) 0 0)
    {wfB : XProg 256} {Wg T : ℕ} (hW1 : 384 ≤ Wg) (hW2 : Wg ≤ 2 ^ 200)
    (hwT : timeBoundT wfB (wfIn (2 ^ 240) (frontL confP.L Wg)) ≤ 2 ^ T)
    (hwL : lenBoundT wfB (wfIn (2 ^ 240) (frontL confP.L Wg)) ≤ v02 (2 ^ 250)) :
    timeBoundT (keyP hkp confP sdP wfB Wg cfP) (io2 (R := 254) Ls confP.L 0) ≤ 2 ^ T + 2 ^ 520 ∧
      lenBoundT (keyP hkp confP sdP wfB Wg cfP) (io2 (R := 254) Ls confP.L 0) ≤
        io2 (2 ^ 252) 0 0 := by
  have hM := keyM_conf hW1 hW2
  obtain ⟨ht, hl⟩ := time_keyPV hkp confP hsT hsL Wg cfP confP.L hwT hwL ph_winRest_conf
  generalize keyM hkp confP (2 ^ 240) Wg cfP = M at *
  have hd1 := dumT_confV hM
  have hd2 : dumD hkp confP M + 1 ≤ 2 ^ 241 := (dumT_conf hM).2
  have hf := frontT_conf hW1 hW2
  have hL : branchLV hkp confP (2 ^ 251) M ≤ 2 ^ 252 := by
    unfold branchLV
    exact max_le (by norm_num) (max_le (hM.trans (by norm_num)) (hd2.trans (by norm_num)))
  refine ⟨ht.trans ?_, hl.trans fun i => ?_⟩
  · have hc : clrT (branchLV hkp confP (2 ^ 251) M) ≤ 2 ^ 262 := by
      unfold clrT
      calc _ ≤ 256 * (2 * (2 ^ 252 + 1) + 3) + (2 * (2 ^ 252 + 1) + 3) := by gcongr
        _ ≤ 2 ^ 262 := by norm_num
    have hb : branchTV hkp confP (2 ^ T) (2 ^ 512) M ≤
        2 * (M + 1) + 3 + 2 ^ T + 2 ^ 512 + (longT M + dumT hkp confP M) + 2 := by
      unfold branchTV
      generalize longT M = Lo
      generalize dumT hkp confP M = Du
      generalize (2 : ℕ) ^ T = U
      generalize (2 : ℕ) ^ 512 = V
      have := max_le_add_of_nonneg (a := Lo) (b := Du) (Nat.zero_le _) (Nat.zero_le _)
      have := max_le_add_of_nonneg (a := 2 * (M + 1) + 3 + U + V)
        (b := max Lo Du + 1) (Nat.zero_le _) (Nat.zero_le _)
      omega
    have hlong : longT M ≤ 2 ^ 250 := by
      unfold longT
      calc _ ≤ 1 * (2 * (2 ^ 240 + 1) + 3) + (2 * (2 ^ 240 + 1) + 3) := by gcongr
        _ ≤ 2 ^ 250 := by norm_num
    have hM' : 2 * (M + 1) + 3 ≤ 2 ^ 250 := by
      calc _ ≤ 2 * (2 ^ 240 + 1) + 3 := by gcongr
        _ ≤ 2 ^ 250 := by norm_num
    generalize (2 : ℕ) ^ T = U at *
    generalize branchTV hkp confP U (2 ^ 512) M = Bt at *
    generalize clrT (branchLV hkp confP (2 ^ 251) M) = Cl at *
    generalize frontT confP.L Wg confP.L = Ft at *
    generalize longT M = Lo at *
    generalize dumT hkp confP M = Du at *
    have : (2 : ℕ) ^ 500 + 2 ^ 470 + 2 ^ 250 + 2 ^ 512 + 2 ^ 250 + 2 ^ 420 + 2 + 2 ^ 262 ≤ 2 ^ 520 := by
      norm_num
    omega
  · simp only [io2]
    split_ifs
    · exact hL
    · exact le_rfl
    · exact le_rfl

/-- **The states of the key component at `confP`**, for a `W_f` block of at most `2^30` states and
a window width `384 ≤ Wg ≤ 2^20`: the prefixes of the public key dominate. -/
theorem size_keyP_confV (sdP : XProg 82) (hsd : sdP.size ≤ 2 ^ 25) (wfB : XProg 256)
    (hwf : wfB.size ≤ 2 ^ 30) {Wg : ℕ} (hW1 : 384 ≤ Wg) (hW2 : Wg ≤ 2 ^ 20) :
    (keyP hkp confP sdP wfB Wg cfP).size ≤ 264 * lenPK hkp confP + 2 ^ 140 := by
  have hm : ∀ x ∈ keyTmpl hkp confP cfP, x.2 < 2 ^ 183 := fun x hx =>
    ((le_tmplMax _ x hx).trans tmplMax_conf).trans_lt (by norm_num)
  refine (size_keyP_le hkp confP sdP wfB Wg cfP 183 hm).trans ?_
  have hf : (frontP confP.L Wg).size ≤ 2 ^ 60 := by
    refine (size_frontP_le _ _).trans ?_
    have h1 := lookCount_frontTbl_le confP.L hW1
    have h2 := confP_L_le
    generalize Prog.lookCount (frontTbl confP.L Wg) [false] = X at *
    generalize confP.L = n at *
    have h1 : X ≤ 2 ^ 20 * (2 ^ 20 + 6 + 375 * (2 * 2 ^ 20)) + 2 :=
      h1.trans (by gcongr)
    calc 60 * (n + X + 30) ≤ 60 * (2 ^ 20 + (2 ^ 20 * (2 ^ 20 + 6 + 375 * (2 * 2 ^ 20)) + 2) + 30) := by
          gcongr
      _ ≤ 2 ^ 60 := by norm_num
  have hd := lenDummy_le
  have hs := length_sW_cfP
  have hp := length_powW_cfP
  generalize ((keyEnc (N := Np) (K := Kp) confP).enc (dummyKey confP)).length = D at *
  generalize (frontP confP.L Wg).size = F at *
  generalize sdP.size = S at *
  generalize wfB.size = Wz at *
  generalize lenPK hkp confP = P
  generalize cfP.sW.length = s at *
  generalize (powW Kp (cfP.B - 1)).length = p at *
  have : (2 : ℕ) ^ 25 + 2 ^ 60 + 2 ^ 30 + 60 * (2 ^ 25 + 2 ^ 25 + 2 ^ 130) + 20 * (195 * 183 + 36) +
    2 ^ 18 ≤ 2 ^ 140 := by norm_num
  omega

end AdvancedEncryption.DualUse.Prog
