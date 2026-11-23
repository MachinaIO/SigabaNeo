import PE.Impl.DualUse.Prog.CompCost
import PE.Impl.DualUse.Prog.KeyPTimeT
import PE.Impl.DualUse.Prog.KeyCfgP
import PE.Impl.DualUse.ReductionCompsBound

/-!
# The constants of the key component at the concrete parameters

At `confP` with the key-try configuration `cfP` and a window width `384 ≤ Wg ≤ 2^200`:

* the cut of the key queries: `confP.L = bpLen ≤ 2^20` (`bpLen_le`, `confP_L_le`);
* the front end: at most `2^231` primitives in its table, its output at most `2^232` bits, its time
  at most `2^470`, at most `2^238` states (`lookCount_conf`, `frontL_conf`, `frontT_conf`,
  `size_frontP_conf`);
* the words of the key try: `lenPK hkp confP` (`lenPK_eq`, about `2^174.3`), the dummy key
  (`≤ 2^130`), the norm word and `powW` (`2^25` bits), the templates (`≤ 2^182`), the uniform bound
  `keyM … ≤ 2^240` (`keyM_conf`), the bound before the key try at `G = 2^250` (`winR3_eq`).

The bounds of the key component itself are in `PE.Impl.DualUse.Prog.KeyCostP`.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg AdvancedEncryption.DualUse.Params
open AdvancedEncryption.DualUse.Algo AdvancedEncryption.DualUse.Algo.Params
open SigabaNeo.Lattices.Algo
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPWord

set_option maxRecDepth 100000
set_option exponentiation.threshold 3000

/-! ### The cut and the front end -/

/-- **The cut of the key queries**: every window predicate with a date, encoded with the
parameters, has at most `2^20` bits. -/
theorem bpLen_le : bpLen ≤ 2 ^ 20 := by
  unfold bpLen
  apply Finset.sup_le
  intro wx _
  have h0 := length_encodeTuple3 (paramsWord PUniv params) (winWord wx.1)
    (PUniv.encAttr wx.2)
  have h3 := length_paramsWord_date
  have h1 := length_winWord_le wx.1
  have h2 : (PUniv.encAttr wx.2).length = 10 := length_encAttr wx.2
  generalize (encodeTuple [paramsWord PUniv params, winWord wx.1,
    PUniv.encAttr wx.2]).length = E at *
  generalize (paramsWord PUniv params).length = P at *
  generalize (winWord wx.1).length = Q at *
  generalize (PUniv.encAttr wx.2).length = R at *
  have : (2 : ℕ) ^ 20 = 1048576 := by norm_num
  omega

theorem confP_L_le : confP.L ≤ 2 ^ 20 := by rw [confP_L]; exact bpLen_le

section Front

variable {Wg : ℕ} (hW1 : 384 ≤ Wg) (hW2 : Wg ≤ 2 ^ 200)
include hW1 hW2

theorem lookCount_conf : Prog.lookCount (frontTbl confP.L Wg) [false] ≤ 2 ^ 231 := by
  refine (lookCount_frontTbl_le _ hW1).trans ?_
  have := confP_L_le
  calc 2 ^ 20 * (confP.L + 6 + 375 * (2 * Wg)) + 2 ≤
        2 ^ 20 * (2 ^ 20 + 6 + 375 * (2 * 2 ^ 200)) + 2 := by gcongr
    _ ≤ 2 ^ 231 := by norm_num

theorem frontL_conf : frontL confP.L Wg ≤ 2 ^ 232 := by
  unfold frontL
  have h1 := lookCount_conf hW1 hW2
  have h2 := confP_L_le
  generalize Prog.lookCount (frontTbl confP.L Wg) [false] = X at *
  generalize confP.L = n at *
  calc n + 1 + (X + 12) ≤ 2 ^ 20 + 1 + (2 ^ 231 + 12) := by gcongr
    _ ≤ 2 ^ 232 := by norm_num

theorem frontT_conf : frontT confP.L Wg confP.L ≤ 2 ^ 470 := by
  unfold frontT
  have h1 := lookCount_conf hW1 hW2
  have h2 := confP_L_le
  generalize Prog.lookCount (frontTbl confP.L Wg) [false] = X at *
  generalize confP.L = n at *
  calc 20 * n + ((n + 2) * (2 * (n + 2) + 5) + 10 * (2 * (n + 11) + 5) +
          (X + 12) * (2 * (n + 1 + (X + 12)) + 5)) ≤
        20 * 2 ^ 20 + ((2 ^ 20 + 2) * (2 * (2 ^ 20 + 2) + 5) + 10 * (2 * (2 ^ 20 + 11) + 5) +
          (2 ^ 231 + 12) * (2 * (2 ^ 20 + 1 + (2 ^ 231 + 12)) + 5)) := by gcongr
    _ ≤ 2 ^ 470 := by norm_num

/-- The states of the front end. -/
theorem size_frontP_conf : (frontP confP.L Wg).size ≤ 2 ^ 238 := by
  refine (size_frontP_le _ _).trans ?_
  have h1 := lookCount_conf hW1 hW2
  have h2 := confP_L_le
  generalize Prog.lookCount (frontTbl confP.L Wg) [false] = X at *
  generalize confP.L = n at *
  calc 60 * (n + X + 30) ≤ 60 * (2 ^ 20 + 2 ^ 231 + 30) := by gcongr
    _ ≤ 2 ^ 238 := by norm_num

end Front

/-! ### The constants of the key component -/

theorem lenPK_eq : lenPK hkp confP = 29931556208626396671394777597180314650064272740057088 := by
  simp only [lenPK, fixLen]; comp_unfold; norm_num

theorem lenDummy_le : ((keyEnc (N := Np) (K := Kp) confP).enc (dummyKey confP)).length ≤ 2 ^ 130 := by
  rw [length_enc_fixLen]; simp only [fixLen]; comp_unfold; norm_num

theorem length_sW_cfP : cfP.sW.length = 2 ^ 25 := by
  show SpW.length = _; rw [length_SpW, Kp_def]

theorem length_powW_cfP : (powW Kp (cfP.B - 1)).length = 2 ^ 25 := by
  rw [powW, length_toBits, Kp_def]

theorem tmplMax_conf : tmplMax (keyTmpl hkp confP cfP) ≤ 2 ^ 182 := by
  simp only [tmplMax, keyTmpl, cfP, lenPK_eq]
  have hm : mBp ≤ 2 ^ 130 := by simp only [mBp, Bp_def, dp_def, Np_def, kp, Kp_def]; norm_num
  have hB : Bp ≤ 2 ^ 30 := by rw [Bp_def]; norm_num
  simp only [nT, confP_d, kp, Kp_def, Np_def, max_le_iff]
  refine ⟨?_, ?_, ?_, hB.trans (by norm_num), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, hm.trans (by norm_num), ?_⟩ <;> norm_num

theorem keyM_conf {Wg : ℕ} (hW1 : 384 ≤ Wg) (hW2 : Wg ≤ 2 ^ 200) :
    keyM hkp confP (2 ^ 240) Wg cfP ≤ 2 ^ 240 := by
  unfold keyM
  exact max_le (max_le le_rfl ((frontL_conf hW1 hW2).trans (by norm_num)))
    (tmplMax_conf.trans (by norm_num))

/-! ### The window branch -/

theorem winR3_eq : winR3 hkp confP (2 ^ 250) cfP =
    2 ^ 250 + 1 + 29931556208626396671394777597180314650064272740057088 + 2 ^ 25 + 1 + 2 ^ 25 + 1 := by
  simp only [winR3, winR1, lenPK_eq, length_sW_cfP]
  simp only [powW, length_toBits, Kp_def]

theorem tmplT_le {n : ℕ} : ∀ (l : List (Fin n × ℕ)) (M X : ℕ), (∀ x ∈ l, x.2 ≤ X) →
    tmplT l M ≤ l.length * ((2 * X + 1) * (4 * M + 12)) + (2 * (M + 1) + 3)
  | [], M, X, _ => by simp [tmplT]
  | x :: l, M, X, h => by
    have h1 : (2 * x.2 + 1) * (4 * M + 12) ≤ (2 * X + 1) * (4 * M + 12) :=
      Nat.mul_le_mul_right _ (by have := h x (by simp); omega)
    have h2 := tmplT_le l M X (fun y hy => h y (by simp [hy]))
    show (2 * x.2 + 1) * (4 * M + 12) + tmplT l M ≤
      (l.length + 1) * ((2 * X + 1) * (4 * M + 12)) + (2 * (M + 1) + 3)
    generalize (2 * x.2 + 1) * (4 * M + 12) = P at *
    generalize (2 * X + 1) * (4 * M + 12) = Q at *
    rw [Nat.add_one_mul]
    generalize l.length * Q = R at *
    omega

end AdvancedEncryption.DualUse.Prog
