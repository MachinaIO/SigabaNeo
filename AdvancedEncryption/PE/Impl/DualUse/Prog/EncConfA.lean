import PE.Impl.DualUse.Prog.EncCostConfT
import PE.Impl.DualUse.Prog.SetupEncDescA
import PE.Impl.DualUse.PUCodes

/-!
# The clock of `Enc` at the parameters of branching programs (Stage II)

`time_encMP_A`: **`(encMP hkp confP chiSamplerP).time ≤ 2^452`** at the sizes of `confA`
(`N = 2^36`, `K = 2^27`, `k = 2^27 + 1`, `d = 2^65`, `n_A = 128`, flooding width `768`, a password
of at most `2^20` bits), by the argument of `time_encMP_confT`:

* the input has at most `3 · 2^190` bits (`nInE_leA`; the `B_j`, `n_A · 4k²N · 2kNK ≈ 2^190`);
  the parser adds its chunks and the samplers at most `2^191` bits (the flooding errors), so every
  tape at the entry of the core is at most `G ≤ 7 · 2^190`;
* the core takes at most `(2 G + 3) · W` steps, `W` the sweeps of the certificate at `confA`
  (`hW`: `W ≤ 45 · 2^252`, dominated by `44 N² K² k J` with `J = 4 n_A k² N ≈ 2^99`);
* the parser, the samplers, the templates and the output frame are below `2^400`.

So the clock is about `630 · 2^442 ≈ 2^451.3`. The hypotheses on the values of `Np`, `Kp`, `dp`,
`nA`, `confP.w` are those of `confA`; while `nA = 10` (Stage I) the statement holds vacuously.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg SigabaNeo.Tape.Sym
  AdvancedEncryption.DualUse.Params
open AdvancedEncryption.PE

section ConfA

variable (hN : Np = 2 ^ 36) (hK : Kp = 2 ^ 27) (hd : confP.d = 2 ^ 65) (hA : nA = 128)
  (hw : confP.w = 768) (hpw : DualUse.pw.length ≤ 2 ^ 20)

/-- The `B_j` field at `confA`. -/
abbrev c3A : ℕ := 128 * (2 * (2 * (2 ^ 27 + 1) * ((2 ^ 27 + 1) * 2 ^ 36))) *
  (1 * (2 * (2 ^ 27 + 1) * (2 ^ 36 * 2 ^ 27)))

/-- The other fields at `confA`. -/
abbrev c1A : ℕ := 1 * (2 ^ 65 * (2 ^ 36 * 2 ^ 27))
abbrev c2A : ℕ := 1 * ((1 + (2 * (2 ^ 27 + 1) + 2 * (2 ^ 27 + 1))) * (2 ^ 36 * 2 ^ 27))

include hN hK hd in
theorem c1_A : (Enum.list (α := Fin 1)).length * ((Enum.list (α := Fin confP.d)).length *
    (Np * Kp)) = c1A := by
  simp only [len_fin, hd, hN, hK]

include hN hK in
theorem c2_A : (Enum.list (α := Fin 1)).length * ((Enum.list (α := TrapCol kp)).length *
    (Np * Kp)) = c2A := by
  simp only [len_fin, len_trap, kp_A hN hK, hN, hK]

include hN hK hA in
theorem c3_A : (Enum.list (α := (Sdw (N := Np) hkp).Attr × (Sdw (N := Np) hkp).ctBits.Index)).length *
    ((Enum.list (α := Fin 1)).length * ((Enum.list (α := RingBTVW.Col kp)).length * (Np * Kp))) =
      c3A := by
  rw [show (Enum.list (α := (Sdw (N := Np) hkp).Attr × (Sdw (N := Np) hkp).ctBits.Index)).length =
    nJenc (N := Np) hkp from rfl, nJenc_eqA, hA, len_fin, len_col, kp_A hN hK, hN, hK]

include hN hK hd hA hpw in
theorem nInE_leA : nInE hkp confP ≤ 3 * 2 ^ 190 := by
  unfold nInE
  rw [c1_A hN hK hd, c2_A hN hK, c3_A hN hK hA, hN, hK, hA]
  have : 2 * DualUse.pw.length + 1 ≤ 2 * 2 ^ 20 + 1 := by omega
  refine (Nat.add_le_add_right this _).trans ?_
  norm_num

include hN hK hd hA in
theorem tmpl_A : ∀ p ∈ tmplList hkp confP, p.2 ≤ 2 * 2 ^ 190 := by
  have ek := kp_A hN hK
  have eJ : nJenc (N := Np) hkp = 128 * (2 * (2 * (2 ^ 27 + 1) * ((2 ^ 27 + 1) * 2 ^ 36))) := by
    rw [nJenc_eqA, hA, ek, hN]
  intro p hp
  simp only [tmplList, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
  all_goals (try simp only [ctLen, nTrap_eqA, eJ])
  all_goals (try rw [hd])
  all_goals (try rw [hA])
  all_goals (try rw [ek])
  all_goals (try rw [hN])
  all_goals (try rw [hK])
  all_goals norm_num

include hN hK hd hA hw in
theorem encSN_A (M : ℕ) : encSN hkp confP Kp 64 M ≤ M + 2 ^ 191 := by
  have hdl : (Enum.list (α := Fin confP.d)).length = 2 ^ 65 := by rw [len_fin, hd]
  have hcl : (Enum.list (α := RingBTVW.Col kp)).length = 2 * (2 ^ 27 + 1) := by
    rw [len_col, kp_A hN hK]
  dsimp only [encSN]
  rw [hdl, hcl, nR_eqA, nE_eqA, (bEntB_as _ _).1, (bEntB_as _ _).2, (bEntF_as _ _).1,
    (bEntF_as _ _).2, hw, hA, hd, kp_A hN hK, hN, hK]
  simp only [Nat.add_assoc]
  exact Nat.add_le_add_left (by norm_num) M

/-- The bound after the parser at `confA` (from `3 · 2^190`). -/
def PEA : ℕ := 3 * 2 ^ 190 + c1A + c2A + c3A + 2 ^ 36 * 2 ^ 27 + 128 + 1

/-- The time of the parser at `confA`. -/
def TEA (p : ℕ) : ℕ := parseETv p c1A c2A c3A (2 ^ 36 * 2 ^ 27) (3 * 2 ^ 190)

include hA in
theorem parseEGv_A : parseEGv c1A c2A c3A (2 ^ 36 * 2 ^ 27) (3 * 2 ^ 190) = PEA := by
  unfold parseEGv PEA; rw [hA]

theorem PEA_le : 3 * 2 ^ 190 ≤ PEA ∧ PEA ≤ 5 * 2 ^ 190 := by
  unfold PEA; norm_num

theorem TEA_mono {p q : ℕ} (h : p ≤ q) : TEA p ≤ TEA q := by
  unfold TEA parseETv dropCT
  gcongr

set_option exponentiation.threshold 500 in
include hA in
theorem TEA_le (p : ℕ) (hp : p ≤ 2 ^ 22) : TEA p ≤ 2 ^ 390 := by
  refine (TEA_mono hp).trans ?_
  unfold TEA parseETv ufCTT dropCT forT loopT ufTb
  rw [hA]
  norm_num

set_option exponentiation.threshold 500 in
include hN hK hd hA hw in
theorem encST_A : encST hkp confP chiSamplerP.B PEA ≤ 2 ^ 400 := by
  refine (encST_le hkp confP (Bχ := chiSamplerP.B) (lin_bChi_of_le (by rw [hK]))
    (lin_bEntB _ _) (lin_bEntF _ _) _).trans ?_
  rw [chiB, bChi_a, bChi_s]
  have hdl : (Enum.list (α := Fin confP.d)).length = 2 ^ 65 := by rw [len_fin, hd]
  have hcl : (Enum.list (α := AdvancedEncryption.RingBTVW.Col kp)).length = 2 * (2 ^ 27 + 1) := by
    rw [len_col, kp_A hN hK]
  have hR : nR hkp confP = 128 * (2 * (2 ^ 27 + 1)) * 2 ^ 65 := by
    rw [nR_eqA, hA, hd, kp_A hN hK]
  have hE : nE (N := Np) hkp = 128 * (2 * (2 * (2 ^ 27 + 1) * ((2 ^ 27 + 1) * 2 ^ 36))) *
      (2 * (2 ^ 27 + 1)) * 2 ^ 36 := by
    rw [nE_eqA, hA, kp_A hN hK, hN]
  rw [encSTL_eqv hkp confP hdl hcl hR hE, (bEntB_as _ _).1, (bEntB_as _ _).2,
    (bEntF_as _ _).1, (bEntF_as _ _).2, hw, hN, hK]
  unfold encSTLv linX linC PEA
  norm_num

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 500 in
include hN hK hd hA hw hpw in
/-- **The clock of `Enc` at the sizes of `confA`**, from a bound `W` of the sweeps of the core. -/
theorem time_encMP_A_of (hW : ∀ G, pEval (ρE hkp confP G) wE ≤ 45 * 2 ^ 252) :
    (encMP hkp confP chiSamplerP).time ≤ 2 ^ 452 := by
  have hn := nInE_leA hN hK hd hA hpw
  obtain ⟨hP1, hP2⟩ := PEA_le
  have hK27 : Kp = 2 ^ 27 := hK
  have hKc : bChi.S₀ ≤ 2 ^ 27 := bChi_S₀.trans (by rw [hK])
  have e1 := c1_A hN hK hd
  have e2 := c2_A hN hK
  have e3 := c3_A hN hK hA
  have enk : Np * Kp = 2 ^ 36 * 2 ^ 27 := by rw [hN, hK]
  have c1 : (Enum.list (α := Fin confP.d)).length * Np ≤ 2 ^ 150 := by
    rw [len_fin, hd, hN]; norm_num
  have c2 : (Enum.list (α := AdvancedEncryption.RingBTVW.Col kp)).length * Np ≤ 2 ^ 150 := by
    rw [len_col, kp_A hN hK, hN]; norm_num
  have c3 : Np ≤ 2 ^ 150 := by rw [hN]; norm_num
  have c4 : nR hkp confP ≤ 2 ^ 170 := by rw [nR_eqA, hA, hd, kp_A hN hK]; norm_num
  have c5 : nE (N := Np) hkp ≤ 2 ^ 170 := by rw [nE_eqA, hA, kp_A hN hK, hN]; norm_num
  have c6 : (2 : ℕ) ^ 170 ≤ 3 * 2 ^ 190 := by norm_num
  have hb0 : 2 * DualUse.pw.length + 1 ≤ 3 * 2 ^ 190 := by
    have : 2 * DualUse.pw.length + 1 ≤ 2 * 2 ^ 20 + 1 := by omega
    exact this.trans (by norm_num)
  have hb1 : (Enum.list (α := Fin 1)).length * ((Enum.list (α := Fin confP.d)).length *
      (Np * Kp)) ≤ 3 * 2 ^ 190 := by rw [e1]; norm_num
  have hb2 : (Enum.list (α := Fin 1)).length * ((Enum.list (α := TrapCol kp)).length *
      (Np * Kp)) ≤ 3 * 2 ^ 190 := by rw [e2]; norm_num
  have hb3 : (Enum.list (α := (Sdw (N := Np) hkp).Attr × (Sdw (N := Np) hkp).ctBits.Index)).length *
      ((Enum.list (α := Fin 1)).length * ((Enum.list (α := RingBTVW.Col kp)).length * (Np * Kp))) ≤
        3 * 2 ^ 190 := by rw [e3]; norm_num
  have hb4 : Np * Kp ≤ 3 * 2 ^ 190 := by rw [enk]; norm_num
  have hSE : PEA ≤ encS hkp confP chiSamplerP.B PEA := by
    rw [encS_eq]; dsimp only [encSN]; omega
  have hpwl : 2 * DualUse.pw.length + 1 ≤ 2 ^ 22 := by omega
  have u := ub_encPT hkp confP (X := chiSamplerP) (3 * 2 ^ 190) preserves6_chiP hb0 hb1 hb2 hb3
    hb4 (by rw [hA]; norm_num) (P := PEA) (T := TEA (2 * DualUse.pw.length + 1))
    (by rw [e1, e2, e3, enk]; exact parseEGv_A hA)
    (by rw [e1, e2, e3, enk]; rfl)
    (by show max 1 _ ≤ _; omega) (by show max bChi.S₀ _ ≤ _; omega)
    (by show max bChi.S₀ _ ≤ _; omega) (by show max bChi.S₀ _ ≤ _; omega)
    (by simp only [Bnd.count, bEntB, Bnd.seq, bZeros, bCoin, Bnd.prim]; omega)
    (by simp only [Bnd.count, bEntF, Bnd.seq, bZeros, bCoins, bCoin, Bnd.prim]; omega)
    (fun p hp => (tmpl_A hN hK hd hA p hp).trans (by omega))
    (Prog.inputBound 120 (nInE hkp confP)) (fun i => by
      simp only [Prog.inputBound, Function.update_apply]; split_ifs <;> omega)
  rw [time_encMP]
  have hT := u.1
  have hL := u.2 122
  have hE : encS hkp confP chiSamplerP.B PEA ≤ 7 * 2 ^ 190 := by
    rw [encS_eq, chiB, bChi_a, bChi_s]
    exact (encSN_A hN hK hd hA hw _).trans ((Nat.add_le_add_right hP2 _).trans (by norm_num))
  have hST := encST_A hN hK hd hA hw
  have hPT := TEA_le hA _ hpwl
  generalize encS hkp confP chiSamplerP.B PEA = X at hE hT hL
  have hW' := hW X
  generalize pEval (ρE hkp confP X) wE = W at hT hW'
  have hNL : natLT (tmplList hkp confP) X ≤
      27 * ((2 * (2 * 2 ^ 190) + 1) * (4 * X + 12)) + (2 * (X + 1) + 3) := by
    have h := natLT_le (tmplList hkp confP) X (2 * 2 ^ 190) (tmpl_A hN hK hd hA)
    have hl : (tmplList hkp confP).length = 27 := rfl
    rwa [hl] at h
  have hAp := appT_le X
  calc 2 * nInE hkp confP + 2 + timeBoundT (encP hkp confP chiSamplerP)
        (Prog.inputBound 120 (nInE hkp confP)) +
        (2 * lenBoundT (encP hkp confP chiSamplerP) (Prog.inputBound 120 (nInE hkp confP)) 122 + 2)
      ≤ 2 * (3 * 2 ^ 190) + 2 + (2 ^ 390 + (2 ^ 400 +
          (27 * ((2 * (2 * 2 ^ 190) + 1) * (4 * (7 * 2 ^ 190) + 12)) + (2 * ((7 * 2 ^ 190) + 1) + 3) +
          ((2 * (7 * 2 ^ 190) + 3) * (45 * 2 ^ 252) + 200 * ((7 * 2 ^ 190) + 1) ^ 2)))) +
          (2 * (4 * (7 * 2 ^ 190) + 1) + 2) := by
        refine Nat.add_le_add (Nat.add_le_add (by omega) (hT.trans ?_)) (by omega)
        refine Nat.add_le_add hPT (Nat.add_le_add hST (Nat.add_le_add (hNL.trans ?_)
          (Nat.add_le_add (Nat.mul_le_mul (by omega) hW') (hAp.trans ?_))))
        · gcongr
        · gcongr
    _ ≤ 2 ^ 452 := by norm_num

include hN hK hd hA in
/-- The values of the variables of the core at `confA`. -/
theorem ρE_A (G : ℕ) : ρE hkp confP G = [G, 2 ^ 36, 2 ^ 27, 2 ^ 27 + 1, 2 ^ 65,
    1 + (2 * (2 ^ 27 + 1) + 2 * (2 ^ 27 + 1)), 128 * (2 * (2 * (2 ^ 27 + 1) * ((2 ^ 27 + 1) * 2 ^ 36))),
    128, 2 ^ 27 + 1 - 2 ^ 27, 2 ^ 36 * 2 ^ 27 - 2 ^ 27] := by
  simp only [ρE, nTrap_eqA, nJenc_eqA]
  rw [hA, hd, kp_A hN hK, hN, hK]

theorem wE_numA : pEval [0, 2 ^ 36, 2 ^ 27, 2 ^ 27 + 1, 2 ^ 65,
    1 + (2 * (2 ^ 27 + 1) + 2 * (2 ^ 27 + 1)), 128 * (2 * (2 * (2 ^ 27 + 1) * ((2 ^ 27 + 1) * 2 ^ 36))),
    128, 2 ^ 27 + 1 - 2 ^ 27, 2 ^ 36 * 2 ^ 27 - 2 ^ 27] wE ≤ 45 * 2 ^ 252 := by decide +kernel

include hN hK hd hA in
/-- **The sweeps of the core at `confA`**: `pEval ρ wE ≈ 44.0000025 · 2^252`. -/
theorem pEval_wE_A (G : ℕ) : pEval (ρE hkp confP G) wE ≤ 45 * 2 ^ 252 := by
  rw [ρE_A hN hK hd hA, pEval_head]; exact wE_numA

include hN hK hd hA hw hpw in
/-- **The clock of `Enc` at the sizes of `confA`**: at most `2^452` steps. -/
theorem time_encMP_A : (encMP hkp confP chiSamplerP).time ≤ 2 ^ 452 :=
  time_encMP_A_of hN hK hd hA hw hpw (pEval_wE_A hN hK hd hA)

end ConfA


open AdvancedEncryption.DualUse.Params in
theorem pw_len_le : DualUse.pw.length ≤ 2 ^ 20 := by
  have h := length_paramsWord_pu
  rw [DualUse.pw, h]; norm_num

open AdvancedEncryption.DualUse.Params in
/-- **The clock of `Enc` at `confP`** (the sizes of `confA`): at most `2^452` steps. -/
theorem time_encMP_confT : (encMP hkp confP chiSamplerP).time ≤ 2 ^ 452 :=
  time_encMP_A Np_def Kp_def dp_def rfl rfl pw_len_le

open AdvancedEncryption.DualUse.Params in
/-- **The description length of `Setup` at `confP`**: at most `2^300`. -/
theorem descLen_setupMP_conf : (setupMP hkp confP chiSamplerP).descLen ≤ 2 ^ 300 :=
  descLen_setupMP_A Np_def Kp_def dp_def rfl

open AdvancedEncryption.DualUse.Params in
/-- **The description length of `Enc` at `confP`**: at most `2^300`. -/
theorem descLen_encMP_conf : (encMP hkp confP chiSamplerP).descLen ≤ 2 ^ 300 :=
  descLen_encMP_A Np_def Kp_def dp_def rfl rfl pw_len_le
end AdvancedEncryption.DualUse.Prog
