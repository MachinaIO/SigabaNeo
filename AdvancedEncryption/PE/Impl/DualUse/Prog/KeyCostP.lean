import PE.Impl.DualUse.Prog.KeyCostC

/-!
# The key component at the concrete parameters

At `confP` with the key-try configuration `cfP`, a window width `384 ≤ Wg ≤ 2^200`, the SimData
block bounded by `2^500` steps and `2^240` bits, and the `W_f` block bounded at its input
(`wfIn (2^240) (frontL confP.L Wg)`) by `2^T` steps and `2^250` bits per tape:

* the cut of the key queries: `confP.L = dateBound ≤ 2^20` (`dateBound_le`);
* the front end: at most `2^231` primitives in its table, its output at most `2^232` bits, its time
  at most `2^470` (`lookCount_conf`, `frontL_conf`, `frontT_conf`);
* **`time_keyP_conf`**: the key component takes at most `2^T + 2^2045` steps on queries of at most
  `confP.L` bits and leaves at most `2^252` bits on tape `0`; the bulk of `2^2045` is the uniform
  bound `20000 (2M + 1)^8` of the key try at `M ≈ 2^250`;
* **`size_keyP_conf`**: it has at most `2^240` states when `wfB` has at most `2^200`.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg AdvancedEncryption.DualUse.Params
open AdvancedEncryption.DualUse.Algo AdvancedEncryption.DualUse.Algo.Params
open SigabaNeo.Lattices.Algo
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow

set_option maxRecDepth 100000
set_option exponentiation.threshold 3000

theorem winR3_le : winR3 hkp confP (2 ^ 250) cfP ≤ 2 ^ 251 := by rw [winR3_eq]; norm_num

/-- The key try at `M ≤ 2^251`. -/
theorem keyTryT_conf {M : ℕ} (hM : M ≤ 2 ^ 251) : keyTryT M ≤ 2 ^ 2039 := by
  refine (keyTryT_le M).trans ?_
  have h1 : (M + 1) ^ 2 ≤ (2 ^ 252) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : (2 * M + 1) ^ 8 ≤ (2 ^ 253) ^ 8 := Nat.pow_le_pow_left (by omega) 8
  rw [← pow_mul] at h1 h2
  calc 23 * (M + 1) ^ 2 + 20000 * (2 * M + 1) ^ 8 ≤ 23 * 2 ^ (252 * 2) + 20000 * 2 ^ (253 * 8) := by
        gcongr
    _ ≤ 2 ^ 2039 := by norm_num

/-- The arithmetic of `winRT_rest_conf`. -/
theorem rest_arith (L R1 R A : ℕ) (hL : L ≤ 2 ^ 175) (h1 : R1 ≤ 2 ^ 251) (h3 : R ≤ 2 ^ 251)
    (hA : A ≤ 20 * ((2 * 2 ^ 182 + 1) * (4 * 2 ^ 251 + 12)) + (2 * (2 ^ 251 + 1) + 3)) :
    prefT L (2 ^ 250) + putT (2 ^ 25) R1 + putT (2 ^ 25) (R1 + 2 ^ 25 + 1) + A +
      (25 * (2 * (2 * R + 1) + 3) + (2 * (2 * R + 1) + 3)) ≤ 2 ^ 600 := by
  unfold prefT putT
  calc _ ≤ 2 * (2 ^ 250 + 1) + 3 + (2 ^ 175 * (6 * (2 ^ 250 + 1 + 2 ^ 175) + 13) +
          2 * (2 ^ 250 + 1 + 2 ^ 175) + 3) + (2 * (2 ^ 250 + 1 + 2 ^ 175 + 1) + 3) +
        (2 ^ 25 + 1) * (2 * (2 ^ 251 + 2 ^ 25 + 1) + 3) +
        (2 ^ 25 + 1) * (2 * (2 ^ 251 + 2 ^ 25 + 1 + 2 ^ 25 + 1) + 3) +
        (20 * ((2 * 2 ^ 182 + 1) * (4 * 2 ^ 251 + 12)) + (2 * (2 ^ 251 + 1) + 3)) +
        (25 * (2 * (2 * 2 ^ 251 + 1) + 3) + (2 * (2 * 2 ^ 251 + 1) + 3)) := by gcongr
    _ ≤ 2 ^ 600 := by norm_num

/-- The window branch after the `W_f` block but the key try, at `G = 2^250`. -/
theorem winRT_rest_conf :
    prefT (lenPK hkp confP) (2 ^ 250) + putT cfP.sW.length (winR1 hkp confP (2 ^ 250)) +
      putT (powW Kp (cfP.B - 1)).length (winR1 hkp confP (2 ^ 250) + cfP.sW.length + 1) +
      tmplT (keyTmpl hkp confP cfP) (winR3 hkp confP (2 ^ 250) cfP) +
      (keyClr.length * (2 * (2 * winR3 hkp confP (2 ^ 250) cfP + 1) + 3) +
        (2 * (2 * winR3 hkp confP (2 ^ 250) cfP + 1) + 3)) ≤ 2 ^ 600 := by
  have ht := tmplT_le (keyTmpl hkp confP cfP) (winR3 hkp confP (2 ^ 250) cfP) (2 ^ 182)
    (fun x hx => (le_tmplMax _ x hx).trans tmplMax_conf)
  have h3 := winR3_le
  have hl : (keyTmpl hkp confP cfP).length = 20 := rfl
  have hc : keyClr.length = 25 := rfl
  have hL : lenPK hkp confP ≤ 2 ^ 175 := by rw [lenPK_eq]; norm_num
  rw [hl] at ht
  rw [hc, length_sW_cfP]
  rw [length_powW_cfP]
  have h1 : winR1 hkp confP (2 ^ 250) ≤ 2 ^ 251 := by
    unfold winR1
    calc _ ≤ 2 ^ 250 + 1 + 2 ^ 175 := by gcongr
      _ ≤ 2 ^ 251 := by norm_num
  have hA : tmplT (keyTmpl hkp confP cfP) (winR3 hkp confP (2 ^ 250) cfP) ≤
      20 * ((2 * 2 ^ 182 + 1) * (4 * 2 ^ 251 + 12)) + (2 * (2 ^ 251 + 1) + 3) := ht.trans (by gcongr)
  exact rest_arith _ _ _ _ hL h1 h3 hA

/-- **The window branch after the `W_f` block** at `G = 2^250`. -/
theorem winRT_conf : winRT hkp confP (2 ^ 250) cfP ≤ 2 ^ 2040 := by
  have e : winRT hkp confP (2 ^ 250) cfP =
      (prefT (lenPK hkp confP) (2 ^ 250) + putT cfP.sW.length (winR1 hkp confP (2 ^ 250)) +
        putT (powW Kp (cfP.B - 1)).length (winR1 hkp confP (2 ^ 250) + cfP.sW.length + 1) +
        tmplT (keyTmpl hkp confP cfP) (winR3 hkp confP (2 ^ 250) cfP) +
        (keyClr.length * (2 * (2 * winR3 hkp confP (2 ^ 250) cfP + 1) + 3) +
          (2 * (2 * winR3 hkp confP (2 ^ 250) cfP + 1) + 3))) +
        keyTryT (winR3 hkp confP (2 ^ 250) cfP) := by
    unfold winRT; ring
  rw [e]
  exact (Nat.add_le_add winRT_rest_conf (keyTryT_conf winR3_le)).trans (by norm_num)

/-- The dummy branch from tapes below `M ≤ 2^240`. -/
theorem dumT_conf {M : ℕ} (hM : M ≤ 2 ^ 240) :
    dumT hkp confP M ≤ 2 ^ 600 ∧ dumD hkp confP M + 1 ≤ 2 ^ 241 := by
  have hd := lenDummy_le
  have hL : lenPK hkp confP ≤ 2 ^ 175 := by rw [lenPK_eq]; norm_num
  unfold dumT dumD prefT putT
  generalize lenPK hkp confP = L at *
  generalize ((keyEnc (N := Np) (K := Kp) confP).enc (dummyKey confP)).length = D at *
  have e1 : L * (6 * (M + 1 + L) + 13) ≤ 2 ^ 175 * (6 * (2 ^ 240 + 1 + 2 ^ 175) + 13) :=
    Nat.mul_le_mul hL (by gcongr)
  have e2 : (D + 1) * (2 * (M + 1 + L + D + 1) + 3) ≤
      (2 ^ 130 + 1) * (2 * (2 ^ 240 + 1 + 2 ^ 175 + 2 ^ 130 + 1) + 3) :=
    Nat.mul_le_mul (by gcongr) (by gcongr)
  generalize L * (6 * (M + 1 + L) + 13) = P at *
  generalize (D + 1) * (2 * (M + 1 + L + D + 1) + 3) = Q at *
  norm_num at e1 e2 hM hL hd ⊢
  constructor <;> linarith

/-! ### The key component -/

/-- **The time and length bounds of the key component at `confP`.** -/
theorem time_keyP_conf {sdP : XProg 82} {Ls : ℕ}
    (hsT : timeBoundT sdP (io2 (R := 80) Ls 0 0) ≤ 2 ^ 500)
    (hsL : lenBoundT sdP (io2 (R := 80) Ls 0 0) ≤ io2 (2 ^ 240) 0 0)
    {wfB : XProg 256} {Wg T : ℕ} (hW1 : 384 ≤ Wg) (hW2 : Wg ≤ 2 ^ 200)
    (hwT : timeBoundT wfB (wfIn (2 ^ 240) (frontL confP.L Wg)) ≤ 2 ^ T)
    (hwL : ∀ i, lenBoundT wfB (wfIn (2 ^ 240) (frontL confP.L Wg)) i ≤ 2 ^ 250) :
    timeBoundT (keyP hkp confP sdP wfB Wg cfP) (io2 (R := 254) Ls confP.L 0) ≤ 2 ^ T + 2 ^ 2045 ∧
      lenBoundT (keyP hkp confP sdP wfB Wg cfP) (io2 (R := 254) Ls confP.L 0) ≤
        io2 (2 ^ 252) 0 0 := by
  have hM := keyM_conf hW1 hW2
  obtain ⟨ht, hl⟩ := time_keyPT hkp confP hsT hsL Wg cfP confP.L hwT hwL (hM.trans (by norm_num))
  generalize keyM hkp confP (2 ^ 240) Wg cfP = M at *
  have hw := winRT_conf
  have hr : 2 * winR3 hkp confP (2 ^ 250) cfP ≤ 2 ^ 252 := by rw [winR3_eq]; norm_num
  obtain ⟨hd1, hd2⟩ := dumT_conf hM
  have hf := frontT_conf hW1 hW2
  have hL : branchLT hkp confP (2 ^ 250) cfP M ≤ 2 ^ 252 := by
    unfold branchLT
    exact max_le hr (max_le (hM.trans (by norm_num)) (hd2.trans (by norm_num)))
  refine ⟨ht.trans ?_, hl.trans fun i => ?_⟩
  · have hc : clrT (branchLT hkp confP (2 ^ 250) cfP M) ≤ 2 ^ 262 := by
      unfold clrT
      calc _ ≤ 256 * (2 * (2 ^ 252 + 1) + 3) + (2 * (2 ^ 252 + 1) + 3) := by gcongr
        _ ≤ 2 ^ 262 := by norm_num
    have hb : branchTT hkp confP (2 ^ T) (2 ^ 250) cfP M ≤
        2 * (M + 1) + 3 + 2 ^ T + winRT hkp confP (2 ^ 250) cfP + (longT M + dumT hkp confP M) + 2 := by
      unfold branchTT
      have := max_le_add_of_nonneg (a := longT M) (b := dumT hkp confP M) (Nat.zero_le _) (Nat.zero_le _)
      have := max_le_add_of_nonneg (a := 2 * (M + 1) + 3 + 2 ^ T + winRT hkp confP (2 ^ 250) cfP)
        (b := max (longT M) (dumT hkp confP M) + 1) (Nat.zero_le _) (Nat.zero_le _)
      omega
    have hlong : longT M ≤ 2 ^ 250 := by
      unfold longT
      calc _ ≤ 1 * (2 * (2 ^ 240 + 1) + 3) + (2 * (2 ^ 240 + 1) + 3) := by gcongr
        _ ≤ 2 ^ 250 := by norm_num
    have hM' : 2 * (M + 1) + 3 ≤ 2 ^ 250 := by
      calc _ ≤ 2 * (2 ^ 240 + 1) + 3 := by gcongr
        _ ≤ 2 ^ 250 := by norm_num
    have e : (2 : ℕ) ^ 2040 = 2 ^ 2040 := rfl
    generalize (2 : ℕ) ^ T = U at *
    generalize branchTT hkp confP U (2 ^ 250) cfP M = Bt at *
    generalize winRT hkp confP (2 ^ 250) cfP = Wr at *
    generalize clrT (branchLT hkp confP (2 ^ 250) cfP M) = Cl at *
    generalize frontT confP.L Wg confP.L = Ft at *
    generalize longT M = Lo at *
    generalize dumT hkp confP M = Du at *
    norm_num at hw hd1 hc hf hlong hM' ⊢
    linarith
  · simp only [io2]
    split_ifs
    · exact hL
    · exact le_rfl
    · exact le_rfl

/-- **The states of the key component at `confP`**, for a `W_f` block of at most `2^200` states. -/
theorem size_keyP_conf (sdP : XProg 82) (hsd : sdP.size ≤ 2 ^ 25) (wfB : XProg 256)
    (hwf : wfB.size ≤ 2 ^ 200) {Wg : ℕ} (hW1 : 384 ≤ Wg) (hW2 : Wg ≤ 2 ^ 200) :
    (keyP hkp confP sdP wfB Wg cfP).size ≤ 2 ^ 240 := by
  have hm : ∀ x ∈ keyTmpl hkp confP cfP, x.2 < 2 ^ 183 := fun x hx =>
    ((le_tmplMax _ x hx).trans tmplMax_conf).trans_lt (by norm_num)
  refine (size_keyP_le hkp confP sdP wfB Wg cfP 183 hm).trans ?_
  have hf := size_frontP_conf hW1 hW2
  have hd := lenDummy_le
  rw [lenPK_eq, length_sW_cfP]
  simp only [show cfP.B = Bp from rfl, powW, length_toBits, Kp_def]
  generalize ((keyEnc (N := Np) (K := Kp) confP).enc (dummyKey confP)).length = D at *
  generalize (frontP confP.L Wg).size = F at *
  generalize sdP.size = S at *
  generalize wfB.size = Wz at *
  norm_num at hf hsd hwf hd ⊢
  linarith

end AdvancedEncryption.DualUse.Prog
