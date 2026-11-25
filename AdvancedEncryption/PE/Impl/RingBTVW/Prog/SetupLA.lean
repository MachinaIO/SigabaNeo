import PE.Impl.RingBTVW.Prog.SetupL
import PE.Impl.RingBTVW.Prog.CompLib

/-!
# The setup components of the reductions at `confA`

At `confP` (the sizes of `confA`: `N = 2^36`, `K = 2^27`, `k = K + 1`, `d = 2^65`, `w = 768`,
`nA = 128`), on inputs of at most `2^193` bits (every packed secret of the three reductions is
shorter, `nS3_conf`, `nSI_conf`, `nS5_conf`) and an attribute of `nA` bits, the lifted setup
components `setup3D`, `setupID`, `setup5D` take at most `2^394` steps and leave at most `2^195`
bits on tape `0`, every other tape blank (`time_setup3D_conf`, `len_setup3D_conf`, …); they have
at most `2^25` states (`size_setup3D_conf`, …).

The closed forms of the tails are evaluated generically (`lbTail3_numA`, … with `N`, `K`, `k`,
`c.d`, `c.w` given by hypotheses, then `norm_num` on numerals) and instantiated at `confP`.
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg AdvancedEncryption.RingBTVW.Params
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

set_option exponentiation.threshold 1000

/-! ### The closed forms of the tails at the sizes of `confA` -/

section EvalA

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

theorem lbTail3_numA (hN : N = 2 ^ 34) (hK : K = 2 ^ 26) (hk' : k = 2 ^ 26 + 1)
    (hd : c.d = 2 ^ 62) (hw : c.w = 768) {A : ℕ} (hA : A = 2 ^ 26) :
    (lbTail3 hk c (Bnd.prim A 64) ⟨2 ^ 40, 2 ^ 40⟩).w ≤ 2 ^ 197 ∧
      (lbTail3 hk c (Bnd.prim A 64) ⟨2 ^ 40, 2 ^ 40⟩).E ≤ 2 ^ 195 := by
  simp only [lbTail3, lbRest, LB.seq, LB.cnt, lbCoins, lbZeros, lbEntB, lbEntF, LB.coin, LB.prim,
    bRest, bCoins, bZeros, bCoin, bEntB, bEntF, Bnd.seq, Bnd.count, Bnd.prim, nW_eq, nR_eq, nE_eq,
    lenFin, len_col, hd, hw]
  subst hN hK hk' hA
  norm_num

theorem lbTailI_numA (hN : N = 2 ^ 34) (hK : K = 2 ^ 26) (hk' : k = 2 ^ 26 + 1)
    (hd : c.d = 2 ^ 62) (hw : c.w = 768) {A : ℕ} (hA : A = 2 ^ 26) :
    (lbTailI hk c (Bnd.prim A 64) ⟨2 ^ 40, 2 ^ 40⟩).w ≤ 2 ^ 197 ∧
      (lbTailI hk c (Bnd.prim A 64) ⟨2 ^ 40, 2 ^ 40⟩).E ≤ 2 ^ 195 := by
  simp only [lbTailI, lbEncCoins, lbCt, LB.seq, LB.cnt, lbCoins, lbZeros, lbEntB, lbEntF, LB.coin,
    LB.prim, bEncCoins, bCt, bCoins, bZeros, bCoin, bEntB, bEntF, Bnd.seq, Bnd.count, Bnd.prim,
    nW_eq, nR_eq, nE_eq, nPsi_eq, nC0_eq, nC1_eq, nCj_eq, lenFin, len_col, len_trap, hd, hw]
  subst hN hK hk' hA
  norm_num

theorem bTail3_as_numA (hN : N = 2 ^ 34) (hK : K = 2 ^ 26) (hk' : k = 2 ^ 26 + 1)
    (hd : c.d = 2 ^ 62) (hw : c.w = 768) {A : ℕ} (hA : A = 2 ^ 26) :
    (bTail3 hk c (Bnd.prim A 64)).a ≤ 2 ^ 194 ∧ (bTail3 hk c (Bnd.prim A 64)).s ≤ 2 ^ 194 := by
  simp only [bTail3, bRest, Bnd.seq, Bnd.count, Bnd.prim, bCoins, bZeros, bEntB, bEntF, bCoin,
    nW_eq, nR_eq, nE_eq, lenFin, len_col, hd, hw]
  subst hN hK hk' hA
  norm_num

theorem bTailI_as_numA (hN : N = 2 ^ 34) (hK : K = 2 ^ 26) (hk' : k = 2 ^ 26 + 1)
    (hd : c.d = 2 ^ 62) (hw : c.w = 768) {A : ℕ} (hA : A = 2 ^ 26) :
    (bTailI hk c (Bnd.prim A 64)).a ≤ 2 ^ 194 ∧ (bTailI hk c (Bnd.prim A 64)).s ≤ 2 ^ 194 := by
  simp only [bTailI, bEncCoins, bCt, Bnd.seq, Bnd.count, Bnd.prim, bCoins, bZeros, bEntB, bEntF,
    bCoin, nW_eq, nR_eq, nE_eq, nPsi_eq, nC0_eq, nC1_eq, nCj_eq, lenFin, len_col, len_trap, hd, hw]
  subst hN hK hk' hA
  norm_num

theorem tail5_numA (hN : N = 2 ^ 34) (hK : K = 2 ^ 26) (hk' : k = 2 ^ 26 + 1)
    (hd : c.d = 2 ^ 62) (hw : c.w = 768) :
    wTail5 hk c ≤ 2 ^ 197 ∧ eTail5 hk c ≤ 2 ^ 195 ∧ s5 hk c ≤ 2 ^ 194 ∧
      N * K + (nW hk c + (nR hk c * (1 + (N * K - 1)) +
        nE (N := N) hk * (min c.w K + (K - c.w)))) ≤ 2 ^ 194 := by
  simp only [wTail5, eTail5, s5, nW_eq, nR_eq, nE_eq, lenFin, len_col, hd, hw]
  subst hN hK hk'
  norm_num

theorem cntSum_numA (hN : N = 2 ^ 34) (hK : K = 2 ^ 26) (hk' : k = 2 ^ 26 + 1)
    (hd : c.d = 2 ^ 62) (hw : c.w = 768) : 128 + K + cntSum hk c ≤ 2 ^ 194 := by
  simp only [cntSum, nW_eq, nR_eq, nE_eq, nPsi_eq, nC0_eq, nC1_eq, nCj_eq, lenFin, len_col, len_trap,
    hd, hw]
  subst hN hK hk'
  norm_num

end EvalA

theorem lbTail3_confA : (lbTail3 hkp confP bChi ⟨2 ^ 40, 2 ^ 40⟩).w ≤ 2 ^ 197 ∧
    (lbTail3 hkp confP bChi ⟨2 ^ 40, 2 ^ 40⟩).E ≤ 2 ^ 195 := by
  rw [lbTail3_congr hkp confP _ bChi_a bChi_s]
  exact lbTail3_numA hkp confP Np_def Kp_def kp_eq confP_d confP_w Kp_def

theorem lbTailI_confA : (lbTailI hkp confP bChi ⟨2 ^ 40, 2 ^ 40⟩).w ≤ 2 ^ 197 ∧
    (lbTailI hkp confP bChi ⟨2 ^ 40, 2 ^ 40⟩).E ≤ 2 ^ 195 := by
  rw [lbTailI_congr hkp confP _ bChi_a bChi_s]
  exact lbTailI_numA hkp confP Np_def Kp_def kp_eq confP_d confP_w Kp_def

theorem bTail3_as_confA :
    (bTail3 hkp confP bChi).a ≤ 2 ^ 194 ∧ (bTail3 hkp confP bChi).s ≤ 2 ^ 194 := by
  rw [(bTail3_as hkp confP bChi).1, (bTail3_as hkp confP bChi).2, bChi_a, bChi_s]
  exact bTail3_as_numA hkp confP Np_def Kp_def kp_eq confP_d confP_w Kp_def

theorem bTailI_as_confA :
    (bTailI hkp confP bChi).a ≤ 2 ^ 194 ∧ (bTailI hkp confP bChi).s ≤ 2 ^ 194 := by
  rw [(bTailI_as hkp confP bChi).1, (bTailI_as hkp confP bChi).2, bChi_a, bChi_s]
  exact bTailI_as_numA hkp confP Np_def Kp_def kp_eq confP_d confP_w Kp_def

theorem tail5_confA : wTail5 hkp confP ≤ 2 ^ 197 ∧ eTail5 hkp confP ≤ 2 ^ 195 ∧
    s5 hkp confP ≤ 2 ^ 194 ∧ Np * Kp + (nW hkp confP + (nR hkp confP * (1 + (Np * Kp - 1)) +
      nE (N := Np) hkp * (min confP.w Kp + (Kp - confP.w)))) ≤ 2 ^ 194 :=
  tail5_numA hkp confP Np_def Kp_def kp_eq confP_d confP_w

theorem cntSum_confA : 128 + Kp + cntSum hkp confP ≤ 2 ^ 194 :=
  cntSum_numA hkp confP Np_def Kp_def kp_eq confP_d confP_w

/-- The arithmetic of the setup bounds. -/
theorem setup_arithA {s w E M : ℕ} (hs : s ≤ 2 ^ 194) (hw : w ≤ 2 ^ 197) (hE : E ≤ 2 ^ 195)
    (hM : M ≤ 2 ^ 195) :
    (2 * (2 ^ 193 + 128 + 1) + 3) + ((tApp (2 ^ 193) s 128 + w * (2 ^ 193 + 128 + s + E)) +
      6 * (2 * (M + 1) + 3)) ≤ 2 ^ 394 := by
  have h := Nat.mul_le_mul hw (show 2 ^ 193 + 128 + s + E ≤ 2 ^ 193 + 128 + 2 ^ 194 + 2 ^ 195 by
    omega)
  have e1 : (2 : ℕ) ^ 197 * (2 ^ 193 + 128 + 2 ^ 194 + 2 ^ 195) ≤ 2 ^ 393 := by norm_num
  have e2 : (2 : ℕ) ^ 393 + 2 ^ 393 = 2 ^ 394 := by norm_num
  have e3 : (2 : ℕ) ^ 200 ≤ 2 ^ 393 := by norm_num
  have e4 : (2 : ℕ) ^ 193 + 2 ^ 194 + 2 ^ 195 ≤ 2 ^ 196 := by norm_num
  unfold tApp tBit
  generalize w * (2 ^ 193 + 128 + s + E) = P at *
  generalize (2 : ℕ) ^ 393 = Z at *
  have hsm : s * 1 ≤ 2 ^ 194 := by omega
  generalize (2 : ℕ) ^ 194 = Y at *
  generalize (2 : ℕ) ^ 195 = Y' at *
  generalize (2 : ℕ) ^ 193 = Y'' at *
  generalize (2 : ℕ) ^ 196 = Y''' at *
  generalize (2 : ℕ) ^ 200 = Y'''' at *
  omega

/-! ### The bounds at `confP` -/

section Time

variable {a b : ℕ}

set_option maxRecDepth 100000

theorem shp_le195 {x S : ℕ} (hx : x ≤ 2 ^ 193 + 128 + 2 ^ 194) (hS : S ≤ 2 ^ 194 + 2 ^ 194)
    (i : Fin 7) : shp (0 : Fin 7) x S i ≤ 2 ^ 195 := by
  have : (2 : ℕ) ^ 195 = 2 ^ 194 + 2 ^ 194 := by norm_num
  have : (2 : ℕ) ^ 193 + 128 ≤ 2 ^ 194 := by norm_num
  simp only [shp]; split_ifs <;> omega

theorem hs_confA {S₀ : ℕ} (h : S₀ ≤ Kp + cntSum hkp confP) : max nA S₀ ≤ 2 ^ 194 := by
  have := cntSum_confA
  rw [show nA = 128 from rfl]
  omega

theorem bounds_setup3D :
    timeBoundT (dropHead (setup3P hkp confP chiP)) (io2 (R := 5) (2 ^ 193) nA 0) ≤ 2 ^ 394 ∧
      lenBoundT (dropHead (setup3P hkp confP chiP)) (io2 (R := 5) (2 ^ 193) nA 0) ≤
        io2 (2 ^ 195) 0 0 := by
  have hL := len_appendTail (atbb_tail3P hkp confP bChi atbb_chiP preserves6_chiP) (2 ^ 193) nA
  have hs : max nA (bTail3 hkp confP bChi).S₀ ≤ 2 ^ 194 :=
    hs_confA ((bTail3_S₀ hkp confP bChi).trans (Nat.add_le_add_right bChi_S₀ _))
  obtain ⟨ha3, hs3⟩ := bTail3_as_confA
  have hM : ∀ i, lenBoundT (setup3P hkp confP chiP) (io2 (R := 5) (2 ^ 193) nA 0) i ≤ 2 ^ 195 :=
    fun i => (hL i).trans (shp_le195 (by rw [show nA = 128 from rfl]; omega) (by omega) i)
  refine ⟨(time_dropHead _ _ _ _ hM).trans ?_, len_dropHead _ _ _ _ (hM 0)⟩
  have h3 := time_setup3P_conf (2 ^ 193) nA
  unfold time3 at h3
  have hT := hasLB_tail3 hkp confP bChi ⟨2 ^ 40, 2 ^ 40⟩ lin_bChi (2 ^ 193 + nA)
    (max nA (bTail3 hkp confP bChi).S₀)
  obtain ⟨hw, hE⟩ := lbTail3_confA
  have e : nA = 128 := rfl
  rw [e] at h3 hT hs ⊢
  exact le_trans (Nat.add_le_add_left (Nat.add_le_add_right (h3.trans (Nat.add_le_add_left hT _)) _) _)
    (setup_arithA hs hw hE (le_refl (2 ^ 195)))

theorem bounds_setupID :
    timeBoundT (dropHead (setupIP hkp confP chiP)) (io2 (R := 5) (2 ^ 193) nA 0) ≤ 2 ^ 394 ∧
      lenBoundT (dropHead (setupIP hkp confP chiP)) (io2 (R := 5) (2 ^ 193) nA 0) ≤
        io2 (2 ^ 195) 0 0 := by
  have hL := len_appendTail (atbb_tailIP hkp confP bChi atbb_chiP preserves6_chiP) (2 ^ 193) nA
  have hs : max nA (bTailI hkp confP bChi).S₀ ≤ 2 ^ 194 :=
    hs_confA ((bTailI_S₀ hkp confP bChi).trans (Nat.add_le_add_right bChi_S₀ _))
  obtain ⟨ha3, hs3⟩ := bTailI_as_confA
  have hM : ∀ i, lenBoundT (setupIP hkp confP chiP) (io2 (R := 5) (2 ^ 193) nA 0) i ≤ 2 ^ 195 :=
    fun i => (hL i).trans (shp_le195 (by rw [show nA = 128 from rfl]; omega) (by omega) i)
  refine ⟨(time_dropHead _ _ _ _ hM).trans ?_, len_dropHead _ _ _ _ (hM 0)⟩
  have h3 := time_setupIP_conf (2 ^ 193) nA
  unfold timeI at h3
  have hT := hasLB_tailI hkp confP bChi ⟨2 ^ 40, 2 ^ 40⟩ lin_bChi (2 ^ 193 + nA)
    (max nA (bTailI hkp confP bChi).S₀)
  obtain ⟨hw, hE⟩ := lbTailI_confA
  have e : nA = 128 := rfl
  rw [e] at h3 hT hs ⊢
  exact le_trans (Nat.add_le_add_left (Nat.add_le_add_right (h3.trans (Nat.add_le_add_left hT _)) _) _)
    (setup_arithA hs hw hE (le_refl (2 ^ 195)))

theorem bounds_setup5D :
    timeBoundT (dropHead (setup5P hkp confP)) (io2 (R := 5) (2 ^ 193) nA 0) ≤ 2 ^ 394 ∧
      lenBoundT (dropHead (setup5P hkp confP)) (io2 (R := 5) (2 ^ 193) nA 0) ≤
        io2 (2 ^ 195) 0 0 := by
  obtain ⟨hw, hE, hs5, ha5⟩ := tail5_confA
  have hs : max nA (s5 hkp confP) ≤ 2 ^ 194 := by
    rw [show nA = 128 from rfl]
    have : (128 : ℕ) ≤ 2 ^ 194 := by norm_num
    omega
  have hℓ : io2 (R := 5) (2 ^ 193) nA 0 ≤ shp (0 : Fin 7) (2 ^ 193) (max nA (s5 hkp confP)) :=
    fun i => by simp only [io2, shp]; split_ifs <;> simp_all <;> omega
  obtain ⟨-, h2⟩ := appendTape_bounds (le_max_left nA _) hℓ (by simp [io2])
  have hL : lenBoundT (setup5P hkp confP) (io2 (R := 5) (2 ^ 193) nA 0) ≤ _ :=
    (lenBoundT_mono _ h2).trans ((atb_tail5P hkp confP) _ _ (le_max_right _ _)).2
  have hM : ∀ i, lenBoundT (setup5P hkp confP) (io2 (R := 5) (2 ^ 193) nA 0) i ≤ 2 ^ 195 :=
    fun i => (hL i).trans (by
      refine shp_le195 ?_ ?_ i
      · rw [show nA = 128 from rfl]; omega
      · omega)
  refine ⟨(time_dropHead _ _ _ _ hM).trans ?_, len_dropHead _ _ _ _ (hM 0)⟩
  have h5 := time_setup5P hkp confP (2 ^ 193) nA
  unfold time5 at h5
  have hT := lin_tTail5 hkp confP (2 ^ 193 + nA) (max nA (s5 hkp confP))
  have e : nA = 128 := rfl
  rw [e] at h5 hT hs ⊢
  exact le_trans (Nat.add_le_add_left (Nat.add_le_add_right (h5.trans (Nat.add_le_add_left hT _)) _) _)
    (setup_arithA hs hw hE (le_refl (2 ^ 195)))

theorem time_setup3D_conf (ha : a ≤ 2 ^ 193) (hb : b ≤ nA) :
    timeBoundT setup3D (io2 a b 0) ≤ 2 ^ 394 :=
  (timeBoundT_mono _ (io2_mono ha hb)).trans (by rw [setup3D, timeBoundT_liftP]; exact bounds_setup3D.1)

theorem len_setup3D_conf (ha : a ≤ 2 ^ 193) (hb : b ≤ nA) :
    lenBoundT setup3D (io2 a b 0) ≤ io2 (2 ^ 195) 0 0 :=
  (lenBoundT_mono _ (io2_mono ha hb)).trans (lenBoundT_liftP_le _ _ bounds_setup3D.2)

theorem time_setupID_conf (ha : a ≤ 2 ^ 193) (hb : b ≤ nA) :
    timeBoundT setupID (io2 a b 0) ≤ 2 ^ 394 :=
  (timeBoundT_mono _ (io2_mono ha hb)).trans (by rw [setupID, timeBoundT_liftP]; exact bounds_setupID.1)

theorem len_setupID_conf (ha : a ≤ 2 ^ 193) (hb : b ≤ nA) :
    lenBoundT setupID (io2 a b 0) ≤ io2 (2 ^ 195) 0 0 :=
  (lenBoundT_mono _ (io2_mono ha hb)).trans (lenBoundT_liftP_le _ _ bounds_setupID.2)

theorem time_setup5D_conf (ha : a ≤ 2 ^ 193) (hb : b ≤ nA) :
    timeBoundT setup5D (io2 a b 0) ≤ 2 ^ 394 :=
  (timeBoundT_mono _ (io2_mono ha hb)).trans (by rw [setup5D, timeBoundT_liftP]; exact bounds_setup5D.1)

theorem len_setup5D_conf (ha : a ≤ 2 ^ 193) (hb : b ≤ nA) :
    lenBoundT setup5D (io2 a b 0) ≤ io2 (2 ^ 195) 0 0 :=
  (lenBoundT_mono _ (io2_mono ha hb)).trans (lenBoundT_liftP_le _ _ bounds_setup5D.2)

end Time

/-! ### The secret words fit the input bound -/

section Words

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000

theorem nS3_conf :
    fencLen ((inst3Enc (N := Np) (K := Kp) (k := kp)).prod (sec3Enc hkp confP)) + 132 ≤ 2 ^ 193 := by
  simp only [fencLen]
  comp_unfold
  norm_num

theorem nSI_conf :
    fencLen ((inst3Enc (N := Np) (K := Kp) (k := kp)).prod (secIEnc hkp confP)) + 132 ≤ 2 ^ 193 := by
  simp only [fencLen]
  comp_unfold
  norm_num

theorem nS5_conf :
    fencLen ((inst5Enc (N := Np) (K := Kp) (k := kp) confP.d).prod (sec5Enc hkp confP)) + 132 ≤
      2 ^ 193 := by
  simp only [fencLen]
  comp_unfold
  norm_num

end Words

/-! ### State counts of the setups -/

section SetupSizes

theorem counts_le : (Encode.Enum.list (α := Fin 1)).length *
      ((Encode.Enum.list (α := Fin confP.d)).length * (Np * Kp)) ≤ 2 ^ 194 ∧
    nW hkp confP ≤ 2 ^ 194 ∧ Np * Kp ≤ 2 ^ 194 ∧
    (Encode.Enum.list (α := Fin confP.d)).length * Np ≤ 2 ^ 194 ∧ Np ≤ 2 ^ 194 ∧
    (Encode.Enum.list (α := RingBTVW.Fresh.Col kp)).length * Np ≤ 2 ^ 194 ∧ nR hkp confP ≤ 2 ^ 194 ∧
    nE (N := Np) hkp ≤ 2 ^ 194 ∧ Kp + confP.w ≤ 2 ^ 194 ∧ nPsi (N := Np) hkp ≤ 2 ^ 194 ∧
    nC0 (N := Np) (K := Kp) confP ≤ 2 ^ 194 ∧ nC1 (N := Np) (K := Kp) (k := kp) ≤ 2 ^ 194 ∧
    nCj (N := Np) hkp ≤ 2 ^ 194 := by
  have h := cntSum_confA
  simp only [cntSum] at h
  omega

theorem size_setup3D_conf : setup3D.size ≤ 2 ^ 25 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -, -, -⟩ := counts_le
  have hB : (2 : ℕ) ^ 194 < 2 ^ 240 := by norm_num
  have hR : SZ (restP hkp confP chiP) _ :=
    (sz_coinsF h3 hB).seq ((sz_repF h4 hB sz_chiP).seq
      (((sz_repF h5 hB sz_chiP).seq ((sz_repF h6 hB sz_chiP).seq (sz_repF h6 hB sz_chiP))).seq
        ((sz_repF h7 hB (sz_entB h3 hB)).seq (sz_repF h5 hB sz_chiP))))
  have hT : SZ (tail3P hkp confP chiP) _ :=
    (sz_coinsF h1 hB).seq ((sz_coinsF h2 hB).seq ((sz_coinsF h3 hB).seq
      (hR.seq (sz_repF h8 hB (sz_entF h9 hB)))))
  rw [setup3D, liftP, size_frame]
  exact ((sz_prim _).seq ((sz_appendTapeP.seq hT).seq sz_clrS)).mono (by norm_num)

theorem size_setupID_conf : setupID.size ≤ 2 ^ 25 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := counts_le
  have hB : (2 : ℕ) ^ 194 < 2 ^ 240 := by norm_num
  have hE : SZ (encCoinsP hkp confP chiP) _ :=
    (sz_coinsF h3 hB).seq ((sz_repF h4 hB sz_chiP).seq
      (((sz_repF h5 hB sz_chiP).seq ((sz_repF h6 hB sz_chiP).seq (sz_repF h6 hB sz_chiP))).seq
        ((sz_repF h7 hB (sz_entB h3 hB)).seq ((sz_repF h8 hB (sz_entF h9 hB)).seq
          (sz_repF h5 hB sz_chiP)))))
  have hC : SZ (ctP hkp confP) _ :=
    (sz_coinsF h10 hB).seq ((sz_coinsF h11 hB).seq ((sz_coinsF h12 hB).seq
      ((sz_coinsF h13 hB).seq (sz_coinsF h3 hB))))
  have hT : SZ (tailIP hkp confP chiP) _ :=
    (sz_coinsF h1 hB).seq ((sz_coinsF h2 hB).seq ((sz_coinsF h3 hB).seq (hE.seq hC)))
  rw [setupID, liftP, size_frame]
  exact ((sz_prim _).seq ((sz_appendTapeP.seq hT).seq sz_clrS)).mono (by norm_num)

theorem size_setup5D_conf : setup5D.size ≤ 2 ^ 25 := by
  obtain ⟨-, h2, h3, -, -, -, h7, h8, h9, -, -, -, -⟩ := counts_le
  have hB : (2 : ℕ) ^ 194 < 2 ^ 240 := by norm_num
  have hT : SZ (tail5P hkp confP) _ :=
    (sz_coinsF h3 hB).seq ((sz_coinsF h2 hB).seq
      ((sz_repF h7 hB (sz_entB h3 hB)).seq (sz_repF h8 hB (sz_entF h9 hB))))
  rw [setup5D, liftP, size_frame]
  exact ((sz_prim _).seq ((sz_appendTapeP.seq hT).seq sz_clrS)).mono (by norm_num)

end SetupSizes

end AdvancedEncryption.RingBTVW.Prog
