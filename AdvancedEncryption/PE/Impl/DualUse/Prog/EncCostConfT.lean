import PE.Impl.DualUse.Prog.EncCostT
import PE.Impl.DualUse.Prog.CostConf

/-!
# The clock of `Enc` at `confP`, with the per-tape bound of the core

`time_encMP_confT : (encMP hkp confP chiSamplerP).time ≤ 2 ^ 421` (against `2 ^ 8000` from the
uniform bound of the core, `time_encMP_conf`).

The input has at most `2^176` bits (`nInE_leT`); the parser leaves every tape below `64 · 2^176`
and the samplers add at most `2^176` bits (`encS_confT`), so every tape at the entry of the core is
at most `G = 2^182 + 2^176`. The core takes at most `(2 G + 3) · W` steps with
`W = pEval ρ wE ≤ 7 · 2^235` sweeps (`pEval_wE_conf`; exactly `≈ 6.875 · 2^235`), dominated by
`44 N² K² k J` (`N = 2^34`, `K = 2^25`, `k = 2^25 + 1`, `J = 40 k² N ≈ 2^89.3` encodings): the
BGG+ encodings, `J` rows of `2k` schoolbook ring products each. So the core costs about
`2^420.9` steps; the parser, the samplers, the templates and the output frame are below `2^381`.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg SigabaNeo.Tape.Sym
  AdvancedEncryption.DualUse.Params
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow

/-! ### Sizes at `confP` -/

theorem parse_countsT : 2 * DualUse.pw.length + 1 ≤ 2 ^ 20 ∧
    (Enum.list (α := Fin 1)).length * ((Enum.list (α := Fin confP.d)).length * (Np * Kp)) ≤ 2 ^ 121 ∧
    (Enum.list (α := Fin 1)).length * ((Enum.list (α := TrapCol kp)).length * (Np * Kp)) ≤ 2 ^ 121 ∧
    (Enum.list (α := (Sdw (N := Np) hkp).Attr × (Sdw (N := Np) hkp).ctBits.Index)).length *
      ((Enum.list (α := Fin 1)).length * ((Enum.list (α := RingBTVW.Col kp)).length * (Np * Kp)))
        ≤ 21 * 2 ^ 170 := by
  simp only [DualUse.pw, length_paramsWord_date]
  comp_unfold
  norm_num

theorem nInE_leT : nInE hkp confP ≤ 2 ^ 176 := by
  obtain ⟨h0, h1, h2, h3⟩ := parse_countsT
  have h4 : Np * Kp = 2 ^ 59 := by rw [Np_def, Kp_def]; norm_num
  unfold nInE
  omega

theorem tmpl_confT : ∀ p ∈ tmplList hkp confP, p.2 ≤ 2 ^ 176 := by
  intro p hp
  simp only [tmplList, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
  all_goals ((try simp only [ctLen, nTrap, nJenc]) <;> (try comp_unfold) <;>
    (try simp only [confP_d, kp, Kp_def, Np_def]) <;> norm_num)

theorem encSN_confT (M : ℕ) : encSN hkp confP Kp 64 M ≤ M + 2 ^ 176 := by
  have hd : (Enum.list (α := Fin confP.d)).length = 2 ^ 61 := by rw [len_fin, confP_d]
  have hc : (Enum.list (α := RingBTVW.Col kp)).length = 2 * (2 ^ 25 + 1) := by
    rw [len_col, kp_eq]
  dsimp only [encSN]
  rw [hd, hc, nR_conf, nE_conf, (bEntB_as _ _).1, (bEntB_as _ _).2, (bEntF_as _ _).1,
    (bEntF_as _ _).2, confP_w, Np_def, Kp_def]
  simp only [Nat.add_assoc]
  exact Nat.add_le_add_left (by norm_num) M

theorem pEval_head (G : ℕ) (r : List ℕ) : pEval (G :: r) wE = pEval (0 :: r) wE := by
  simp only [wE, pEval, mEval, List.headD, List.tail, pow_zero]

theorem wE_num : pEval [0, 2 ^ 34, 2 ^ 25, 2 ^ 25 + 1, 2 ^ 61,
    1 + (2 * (2 ^ 25 + 1) + 2 * (2 ^ 25 + 1)), 10 * (2 * (2 * (2 ^ 25 + 1) * ((2 ^ 25 + 1) * 2 ^ 34))),
    0, 2 ^ 25 + 1 - 2 ^ 25, 2 ^ 34 * 2 ^ 25 - 2 ^ 25] wE ≤ 7 * 2 ^ 235 := by decide +kernel

/-- The values of the variables of the core at `confP`. -/
theorem ρE_conf (G : ℕ) : ρE hkp confP G = [G, 2 ^ 34, 2 ^ 25, 2 ^ 25 + 1, 2 ^ 61,
    1 + (2 * (2 ^ 25 + 1) + 2 * (2 ^ 25 + 1)), 10 * (2 * (2 * (2 ^ 25 + 1) * ((2 ^ 25 + 1) * 2 ^ 34))),
    0, 2 ^ 25 + 1 - 2 ^ 25, 2 ^ 34 * 2 ^ 25 - 2 ^ 25] := by
  simp only [ρE, nTrap, nJenc, Enum.length_prod, len_Attr, len_Index, len_trap, confP_d, kp_eq,
    Np_def, Kp_def]

/-- **The sweeps of the core at `confP`**: `pEval ρ wE ≈ 6.875 · 2^235`. -/
theorem pEval_wE_conf (G : ℕ) : pEval (ρE hkp confP G) wE ≤ 7 * 2 ^ 235 := by
  rw [ρE_conf, pEval_head]; exact wE_num

/-! ### The clock -/

/-- `encSTL` with the counts as variables. -/
def encSTLv (N K D C R E ba bs fa fs a s w Eχ wB EB wF EF M : ℕ) : ℕ :=
  let S1 := M + N * K * 1 + N * K * 0
  let S2 := S1 + D * N * a + D * N * s
  let S3 := S2 + N * a + N * s
  let S4 := S3 + C * N * a + C * N * s
  let S5 := S4 + C * N * a + C * N * s
  let S6 := S5 + R * ba + R * bs
  linC (N * K) M + (linX a s w Eχ (D * N) S1 + (linX a s w Eχ N S2 + (linX a s w Eχ (C * N) S3 +
    (linX a s w Eχ (C * N) S4 + (linX ba bs wB EB R S5 +
    (linX fa fs wF EF E S6 + linX a s w Eχ N (S6 + E * fa + E * fs)))))))

theorem encSTL_eqv {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)
    {a s w Eχ wB EB wF EF M D C R E : ℕ}
    (hd : (Enum.list (α := Fin c.d)).length = D)
    (hc : (Enum.list (α := RingBTVW.Col k)).length = C) (hR : nR hk c = R)
    (hE : nE (N := N) hk = E) :
    encSTL hk c a s w Eχ wB EB wF EF M = encSTLv N K D C R E (bEntB N K).a (bEntB N K).s
      (bEntF K c.w).a (bEntF K c.w).s a s w Eχ wB EB wF EF M := by
  unfold encSTL encSTLv
  rw [hd, hc, hR, hE]

set_option exponentiation.threshold 500 in
theorem encST_confT : encST hkp confP chiSamplerP.B (parseEG (2 ^ 176)) ≤ 2 ^ 380 := by
  have hPG := parseEG_eq (2 ^ 176)
  refine (encST_le hkp confP (Bχ := chiSamplerP.B) lin_bChi (lin_bEntB _ _) (lin_bEntF _ _) _).trans ?_
  rw [chiB, bChi_a, bChi_s]
  have hd : (Enum.list (α := Fin confP.d)).length = 2 ^ 61 := by rw [len_fin, confP_d]
  have hc : (Enum.list (α := AdvancedEncryption.RingBTVW.Col kp)).length = 2 * (2 ^ 25 + 1) := by
    rw [len_col, kp_eq]
  rw [encSTL_eqv hkp confP hd hc nR_conf nE_conf, (bEntB_as _ _).1, (bEntB_as _ _).2,
    (bEntF_as _ _).1, (bEntF_as _ _).2, confP_w, Np_def, Kp_def, hPG]
  unfold encSTLv linX linC
  norm_num

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 500 in
/-- **The clock of `Enc` at `confP`**, with the per-tape bound of the core. -/
theorem time_encMP_confT : (encMP hkp confP chiSamplerP).time ≤ 2 ^ 421 := by
  obtain ⟨h0, h1, h2, h3⟩ := parse_countsT
  obtain ⟨-, e2, e3, e4, e5, e6, e7⟩ := enc_counts
  have e1 : Np * Kp ≤ 2 ^ 175 := by rw [Np_def, Kp_def]; norm_num
  have hn := nInE_leT
  have hK : bChi.S₀ ≤ 2 ^ 176 := bChi_S₀.trans (by rw [Kp_def]; norm_num)
  have hPG := parseEG_eq (2 ^ 176)
  have hSE : parseEG (2 ^ 176) ≤ encS hkp confP chiSamplerP.B (parseEG (2 ^ 176)) := by
    rw [encS_eq]; dsimp only [encSN]; omega
  have h176 : (2 : ℕ) ^ 176 ≤ 64 * 2 ^ 176 := by norm_num
  have u := ub_encPT hkp confP (X := chiSamplerP) (2 ^ 176) preserves6_chiP (by omega) (by omega)
    (by omega) (by omega) (by omega) (by norm_num)
    (by show max 1 _ ≤ _; rw [hPG]; omega) (by show max bChi.S₀ _ ≤ _; rw [hPG]; omega)
    (by show max bChi.S₀ _ ≤ _; rw [hPG]; omega) (by show max bChi.S₀ _ ≤ _; rw [hPG]; omega)
    (by simp only [Bnd.count, bEntB, Bnd.seq, bZeros, bCoin, Bnd.prim]; rw [hPG]; omega)
    (by simp only [Bnd.count, bEntF, Bnd.seq, bZeros, bCoins, bCoin, Bnd.prim]; rw [hPG]; omega)
    (fun p hp => (tmpl_confT p hp).trans (le_trans (by rw [hPG]; exact h176) hSE))
    (Prog.inputBound 120 (nInE hkp confP)) (fun i => by
      simp only [Prog.inputBound, Function.update_apply]; split_ifs <;> omega)
  rw [time_encMP]
  have hT := u.1
  have hL := u.2 122
  have hE : encS hkp confP chiSamplerP.B (parseEG (2 ^ 176)) ≤ 2 ^ 182 + 2 ^ 176 := by
    rw [encS_eq, chiB, bChi_a, bChi_s]
    refine (encSN_confT _).trans ?_
    rw [hPG]; norm_num
  have hST := encST_confT
  have hPT : parseET hkp confP (2 ^ 176) ≤ 2 ^ 380 :=
    (parseET_le hkp confP (2 ^ 175) _ (h0.trans (by norm_num)) (h1.trans (by norm_num))
      (h2.trans (by norm_num)) (h3.trans (by norm_num)) e1 (by norm_num)).trans (by norm_num)
  generalize encS hkp confP chiSamplerP.B (parseEG (2 ^ 176)) = X at hE hT hL
  have hW := pEval_wE_conf X
  generalize pEval (ρE hkp confP X) wE = W at hT hW
  have hNL : natLT (tmplList hkp confP) X ≤ 27 * ((2 * 2 ^ 176 + 1) * (4 * X + 12)) + (2 * (X + 1) + 3) := by
    have h := natLT_le (tmplList hkp confP) X (2 ^ 176) tmpl_confT
    have hl : (tmplList hkp confP).length = 27 := rfl
    rwa [hl] at h
  have hA := appT_le X
  calc 2 * nInE hkp confP + 2 + timeBoundT (encP hkp confP chiSamplerP)
        (Prog.inputBound 120 (nInE hkp confP)) +
        (2 * lenBoundT (encP hkp confP chiSamplerP) (Prog.inputBound 120 (nInE hkp confP)) 122 + 2)
      ≤ 2 * 2 ^ 176 + 2 + (2 ^ 380 + (2 ^ 380 +
          (27 * ((2 * 2 ^ 176 + 1) * (4 * (2 ^ 182 + 2 ^ 176) + 12)) + (2 * ((2 ^ 182 + 2 ^ 176) + 1) + 3) +
          ((2 * (2 ^ 182 + 2 ^ 176) + 3) * (7 * 2 ^ 235) + 200 * ((2 ^ 182 + 2 ^ 176) + 1) ^ 2)))) +
          (2 * (4 * (2 ^ 182 + 2 ^ 176) + 1) + 2) := by
        refine Nat.add_le_add (Nat.add_le_add (by omega) (hT.trans ?_)) (by omega)
        refine Nat.add_le_add hPT (Nat.add_le_add hST (Nat.add_le_add (hNL.trans ?_)
          (Nat.add_le_add (Nat.mul_le_mul (by omega) hW) (hA.trans ?_))))
        · gcongr
        · gcongr
    _ ≤ 2 ^ 421 := by norm_num

end AdvancedEncryption.DualUse.Prog
