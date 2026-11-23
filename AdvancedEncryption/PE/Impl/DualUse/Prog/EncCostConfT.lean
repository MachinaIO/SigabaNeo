import PE.Impl.DualUse.Prog.EncCostT
import PE.Impl.DualUse.Prog.CostConf

/-!
# The clock of `Enc` at `confP`, with the per-tape bound of the core

`time_encMP_confT : (encMP hkp confP chiSamplerP).time ≤ 2 ^ 416` (against `2 ^ 8000` from the
uniform bound of the core, `time_encMP_conf`).

The input has at most `41 · 2^170` bits (`nInE_leT`, about `2^175.3`); the parser adds its chunks
(`ub_encParsePT`, at most `21 · 2^170` bits, almost all the `B_j`) and the samplers at most
`21 · 2^170` bits (`encSN_confT`, almost all the flooding errors `e_j`), so every tape at the entry
of the core is at most `G ≤ 83 · 2^170` (about `2^176.4`; the longest is about `2^174.3`). The core
takes at most `(2 G + 3) · W` steps with `W = pEval ρ wE ≤ 7 · 2^235` sweeps (`pEval_wE_conf`;
exactly `≈ 6.875 · 2^235`), dominated by `44 N² K² k J` (`N = 2^34`, `K = 2^25`, `k = 2^25 + 1`,
`J = 40 k² N ≈ 2^89.3` encodings): the BGG+ encodings, `J` rows of `2k` schoolbook ring products
each. So the core costs about `2^415.2` steps; the parser, the samplers, the templates and the
output frame are below `2^381`.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg SigabaNeo.Tape.Sym
  AdvancedEncryption.DualUse.Params
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow

/-! ### Sizes at `confP` -/

theorem pwE_len : 2 * DualUse.pw.length + 1 = 2 * 515 + 1 := by
  simp only [DualUse.pw, length_paramsWord_date]

theorem c1_conf : (Enum.list (α := Fin 1)).length * ((Enum.list (α := Fin confP.d)).length *
    (Np * Kp)) = 1 * (2 ^ 61 * (2 ^ 34 * 2 ^ 25)) := by
  simp only [len_fin, confP_d, Np_def, Kp_def]

theorem c2_conf : (Enum.list (α := Fin 1)).length * ((Enum.list (α := TrapCol kp)).length *
    (Np * Kp)) = 1 * ((1 + (2 * (2 ^ 25 + 1) + 2 * (2 ^ 25 + 1))) * (2 ^ 34 * 2 ^ 25)) := by
  simp only [len_fin, len_trap, kp_eq, Np_def, Kp_def]

theorem c3_conf : (Enum.list (α := (Sdw (N := Np) hkp).Attr × (Sdw (N := Np) hkp).ctBits.Index)).length *
    ((Enum.list (α := Fin 1)).length * ((Enum.list (α := RingBTVW.Col kp)).length * (Np * Kp))) =
      10 * (2 * (2 * (2 ^ 25 + 1) * ((2 ^ 25 + 1) * 2 ^ 34))) *
        (1 * (2 * (2 ^ 25 + 1) * (2 ^ 34 * 2 ^ 25))) := by
  simp only [Enum.length_prod, len_Attr, len_Index, len_fin, kp_eq, Np_def, Kp_def]

theorem nk_conf : Np * Kp = 2 ^ 34 * 2 ^ 25 := by rw [Np_def, Kp_def]

theorem nInE_leT : nInE hkp confP ≤ 41 * 2 ^ 170 := by
  unfold nInE
  rw [pwE_len, c1_conf, c2_conf, c3_conf, nk_conf]
  norm_num

theorem tmpl_confT : ∀ p ∈ tmplList hkp confP, p.2 ≤ 21 * 2 ^ 170 := by
  intro p hp
  simp only [tmplList, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
  all_goals ((try simp only [ctLen, nTrap, nJenc]) <;> (try comp_unfold) <;>
    (try simp only [confP_d, kp, Kp_def, Np_def]) <;> norm_num)

theorem encSN_confT (M : ℕ) : encSN hkp confP Kp 64 M ≤ M + 21 * 2 ^ 170 := by
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

/-- The bound after the parser at `confP` (from `41 · 2^170`). -/
def PE0 : ℕ := parseEGv (1 * (2 ^ 61 * (2 ^ 34 * 2 ^ 25)))
  (1 * ((1 + (2 * (2 ^ 25 + 1) + 2 * (2 ^ 25 + 1))) * (2 ^ 34 * 2 ^ 25)))
  (10 * (2 * (2 * (2 ^ 25 + 1) * ((2 ^ 25 + 1) * 2 ^ 34))) * (1 * (2 * (2 ^ 25 + 1) * (2 ^ 34 * 2 ^ 25))))
  (2 ^ 34 * 2 ^ 25) (41 * 2 ^ 170)

/-- The time of the parser at `confP`. -/
def TE0 : ℕ := parseETv (2 * 515 + 1) (1 * (2 ^ 61 * (2 ^ 34 * 2 ^ 25)))
  (1 * ((1 + (2 * (2 ^ 25 + 1) + 2 * (2 ^ 25 + 1))) * (2 ^ 34 * 2 ^ 25)))
  (10 * (2 * (2 * (2 ^ 25 + 1) * ((2 ^ 25 + 1) * 2 ^ 34))) * (1 * (2 * (2 ^ 25 + 1) * (2 ^ 34 * 2 ^ 25))))
  (2 ^ 34 * 2 ^ 25) (41 * 2 ^ 170)

theorem PE0_le : 41 * 2 ^ 170 ≤ PE0 ∧ PE0 ≤ 62 * 2 ^ 170 := by
  unfold PE0 parseEGv; norm_num

set_option exponentiation.threshold 500 in
theorem TE0_le : TE0 ≤ 2 ^ 380 := by
  unfold TE0 parseETv ufCTT dropCT forT loopT ufTb
  norm_num

set_option exponentiation.threshold 500 in
theorem encST_confT : encST hkp confP chiSamplerP.B PE0 ≤ 2 ^ 380 := by
  refine (encST_le hkp confP (Bχ := chiSamplerP.B) lin_bChi (lin_bEntB _ _) (lin_bEntF _ _) _).trans ?_
  rw [chiB, bChi_a, bChi_s]
  have hd : (Enum.list (α := Fin confP.d)).length = 2 ^ 61 := by rw [len_fin, confP_d]
  have hc : (Enum.list (α := AdvancedEncryption.RingBTVW.Col kp)).length = 2 * (2 ^ 25 + 1) := by
    rw [len_col, kp_eq]
  rw [encSTL_eqv hkp confP hd hc nR_conf nE_conf, (bEntB_as _ _).1, (bEntB_as _ _).2,
    (bEntF_as _ _).1, (bEntF_as _ _).2, confP_w, Np_def, Kp_def]
  unfold encSTLv linX linC PE0 parseEGv
  norm_num

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 500 in
/-- **The clock of `Enc` at `confP`**, with the per-tape bound of the core. -/
theorem time_encMP_confT : (encMP hkp confP chiSamplerP).time ≤ 2 ^ 416 := by
  have hn := nInE_leT
  obtain ⟨hP1, hP2⟩ := PE0_le
  have hK : bChi.S₀ ≤ 2 ^ 25 := bChi_S₀.trans (by rw [Kp_def])
  have c1 : (Enum.list (α := Fin confP.d)).length * Np ≤ 2 ^ 150 := by
    rw [len_fin, confP_d, Np_def]; norm_num
  have c2 : (Enum.list (α := AdvancedEncryption.RingBTVW.Col kp)).length * Np ≤ 2 ^ 150 := by
    rw [len_col, kp_eq, Np_def]; norm_num
  have c3 : Np ≤ 2 ^ 150 := by rw [Np_def]; norm_num
  have c4 : nR hkp confP ≤ 2 ^ 150 := by rw [nR_conf]; norm_num
  have c5 : nE (N := Np) hkp ≤ 2 ^ 150 := by rw [nE_conf]; norm_num
  have c6 : (2 : ℕ) ^ 150 ≤ 41 * 2 ^ 170 := by norm_num
  have c7 : Kp = 2 ^ 25 := Kp_def
  have c8 : confP.w = 512 := confP_w
  have hb0 : 2 * DualUse.pw.length + 1 ≤ 41 * 2 ^ 170 := by rw [pwE_len]; norm_num
  have hb1 : (Enum.list (α := Fin 1)).length * ((Enum.list (α := Fin confP.d)).length *
      (Np * Kp)) ≤ 41 * 2 ^ 170 := by rw [c1_conf]; norm_num
  have hb2 : (Enum.list (α := Fin 1)).length * ((Enum.list (α := TrapCol kp)).length *
      (Np * Kp)) ≤ 41 * 2 ^ 170 := by rw [c2_conf]; norm_num
  have hb3 : (Enum.list (α := (Sdw (N := Np) hkp).Attr × (Sdw (N := Np) hkp).ctBits.Index)).length *
      ((Enum.list (α := Fin 1)).length * ((Enum.list (α := RingBTVW.Col kp)).length * (Np * Kp))) ≤
        41 * 2 ^ 170 := by rw [c3_conf]; norm_num
  have hb4 : Np * Kp ≤ 41 * 2 ^ 170 := by rw [nk_conf]; norm_num
  have hSE : PE0 ≤ encS hkp confP chiSamplerP.B PE0 := by
    rw [encS_eq]; dsimp only [encSN]; omega
  have u := ub_encPT hkp confP (X := chiSamplerP) (41 * 2 ^ 170) preserves6_chiP hb0 hb1 hb2 hb3
    hb4 (by norm_num) (P := PE0) (T := TE0)
    (by rw [c1_conf, c2_conf, c3_conf, nk_conf]; rfl)
    (by rw [pwE_len, c1_conf, c2_conf, c3_conf, nk_conf]; rfl)
    (by show max 1 _ ≤ _; omega) (by show max bChi.S₀ _ ≤ _; omega)
    (by show max bChi.S₀ _ ≤ _; omega) (by show max bChi.S₀ _ ≤ _; omega)
    (by simp only [Bnd.count, bEntB, Bnd.seq, bZeros, bCoin, Bnd.prim]; omega)
    (by simp only [Bnd.count, bEntF, Bnd.seq, bZeros, bCoins, bCoin, Bnd.prim]; omega)
    (fun p hp => (tmpl_confT p hp).trans (by omega))
    (Prog.inputBound 120 (nInE hkp confP)) (fun i => by
      simp only [Prog.inputBound, Function.update_apply]; split_ifs <;> omega)
  rw [time_encMP]
  have hT := u.1
  have hL := u.2 122
  have hE : encS hkp confP chiSamplerP.B PE0 ≤ 83 * 2 ^ 170 := by
    rw [encS_eq, chiB, bChi_a, bChi_s]
    exact (encSN_confT _).trans ((Nat.add_le_add_right hP2 _).trans (by norm_num))
  have hST := encST_confT
  have hPT := TE0_le
  generalize encS hkp confP chiSamplerP.B PE0 = X at hE hT hL
  have hW := pEval_wE_conf X
  generalize pEval (ρE hkp confP X) wE = W at hT hW
  have hNL : natLT (tmplList hkp confP) X ≤
      27 * ((2 * (21 * 2 ^ 170) + 1) * (4 * X + 12)) + (2 * (X + 1) + 3) := by
    have h := natLT_le (tmplList hkp confP) X (21 * 2 ^ 170) tmpl_confT
    have hl : (tmplList hkp confP).length = 27 := rfl
    rwa [hl] at h
  have hA := appT_le X
  calc 2 * nInE hkp confP + 2 + timeBoundT (encP hkp confP chiSamplerP)
        (Prog.inputBound 120 (nInE hkp confP)) +
        (2 * lenBoundT (encP hkp confP chiSamplerP) (Prog.inputBound 120 (nInE hkp confP)) 122 + 2)
      ≤ 2 * (41 * 2 ^ 170) + 2 + (2 ^ 380 + (2 ^ 380 +
          (27 * ((2 * (21 * 2 ^ 170) + 1) * (4 * (83 * 2 ^ 170) + 12)) + (2 * ((83 * 2 ^ 170) + 1) + 3) +
          ((2 * (83 * 2 ^ 170) + 3) * (7 * 2 ^ 235) + 200 * ((83 * 2 ^ 170) + 1) ^ 2)))) +
          (2 * (4 * (83 * 2 ^ 170) + 1) + 2) := by
        refine Nat.add_le_add (Nat.add_le_add (by omega) (hT.trans ?_)) (by omega)
        refine Nat.add_le_add hPT (Nat.add_le_add hST (Nat.add_le_add (hNL.trans ?_)
          (Nat.add_le_add (Nat.mul_le_mul (by omega) hW) (hA.trans ?_))))
        · gcongr
        · gcongr
    _ ≤ 2 ^ 416 := by norm_num

end AdvancedEncryption.DualUse.Prog
