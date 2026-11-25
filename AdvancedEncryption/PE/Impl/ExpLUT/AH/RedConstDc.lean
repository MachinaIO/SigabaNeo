import PE.Impl.ExpLUT.AH.RedCompsR
import PE.Impl.ExpLUT.Prog.KeySizeConf

/-!
# The reduction's constant at `Dc` from coarse component bounds (package G2)

**`hC_of_bounds`**: for raw components at `Dc` on at most `300` scratch tapes, whose five programs
have at most `2^240` states together (`2 (|setupP| + |pubP|) + |keyP| + |authP| + |chalP|`), whose
time at the input bounds is at most `2^500` (`compTimeP`) and whose length bounds are all at most
`2^125`, the constant of the reduction satisfies `64 · 2^256 · const ≤ 2^1155`, the hypothesis of
`attributeHiding_Dc_raw` (in fact `const ≤ 2^821`).
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Generic
open AdvancedEncryption.DualUse (compStatesG compBoundG postStatesG glue3)
open AdvancedEncryption.DualUse.Prog (encLen)

set_option exponentiation.threshold 2000 in
theorem compStatesG_le_Dc {sP Sz2 Lc t : ℕ} (hsP : sP ≤ 2 ^ 16) (hSz : Sz2 ≤ 2 ^ 240)
    (hLc : Lc ≤ 2 ^ 125) (ht : t ≤ 504) : compStatesG 128 1 515 sP Sz2 Lc t ≤ 2 ^ 257 := by
  unfold compStatesG glue3 postStatesG
  calc (t + 1) + 2 * sP + 2 * (1546 + 288 * (128 + 1)) +
        4 * 27 * (515 + 3) * (28 + (4479 + 1656 * 128 + 984 * 1 + 264 * Lc) + Sz2) +
        3 * (t + 1) + 108
      ≤ (504 + 1) + 2 * 2 ^ 16 + 2 * (1546 + 288 * (128 + 1)) +
        4 * 27 * (515 + 3) * (28 + (4479 + 1656 * 128 + 984 * 1 + 264 * 2 ^ 125) + 2 ^ 240) +
        3 * (504 + 1) + 108 := by gcongr
    _ ≤ 2 ^ 257 := by norm_num

set_option exponentiation.threshold 2000 in
theorem compBoundG_le_Dc {sP tP p R Sz2 Lc Sl t : ℕ} (hsP : sP ≤ 2 ^ 16) (htP : tP ≤ 2 ^ 270)
    (hp : p ≤ 14) (hR : R ≤ 300) (hSz : Sz2 ≤ 2 ^ 240) (hLc : Lc ≤ 2 ^ 125) (hSl : Sl ≤ 2 ^ 504)
    (ht : t ≤ 504) : compBoundG 128 1 515 sP tP p R Sz2 Lc Sl t ≤ 2 ^ 821 := by
  have hs := compStatesG_le_Dc hsP hSz hLc ht
  have hz : Nat.size (compStatesG 128 1 515 sP Sz2 Lc t) ≤ 258 :=
    Nat.size_le.mpr (lt_of_le_of_lt hs (by norm_num))
  have h3 : 3 ^ (p + R + 30) ≤ 3 ^ 344 := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold compBoundG
  calc 60 * compStatesG 128 1 515 sP Sz2 Lc t * 3 ^ (p + R + 30) *
        (5 + 4 * (p + R + 30) + Nat.size (compStatesG 128 1 515 sP Sz2 Lc t)) +
        11 * tP + 11 * Sl + 24
      ≤ 60 * 2 ^ 257 * 3 ^ 344 * (5 + 4 * 344 + 258) + 11 * 2 ^ 270 + 11 * 2 ^ 504 + 24 := by
        gcongr
        omega
    _ ≤ 2 ^ 821 := by norm_num

variable {kb : KeyBoxes Dc} {L : ℕ} {impl : Impl sig} {χfl : PMF (Rg Dc)}

set_option exponentiation.threshold 2000 in
/-- **The reduction's constant from coarse component bounds** (`const ≤ 2^821`). -/
theorem const_le_of_bounds (rc : RawComps Dc kb L impl χfl) (hR : rc.R ≤ 300)
    (hSz : 2 * (rc.cs.setupP.size + rc.cs.pubP.size) + rc.cs.keyP.size + rc.cs.authP.size +
      rc.cs.chalP.size ≤ 2 ^ 240)
    (hT : compTimeP rc.cb ≤ 2 ^ 500)
    (hSsig : rc.cb.Ssig ≤ 2 ^ 125) (hLp : rc.cb.Lp ≤ 2 ^ 125) (hLk : rc.cb.Lk ≤ 2 ^ 125)
    (hLa : rc.cb.La ≤ 2 ^ 125) (hLc : rc.cb.Lc ≤ 2 ^ 125) (hW : (rc.toRedComps nDc encLen_le_nDc).W ≤ 2 ^ 125)
    (hnS : (rc.toRedComps nDc encLen_le_nDc).nS ≤ 2 ^ 125) (hL : L ≤ 2 ^ 125)
    (hLa' : (rc.toRedComps nDc encLen_le_nDc).La ≤ 2 ^ 125) :
    (rc.toRedComps nDc encLen_le_nDc).const ≤ 2 ^ 821 := by
  have h := (rc.toRedComps nDc encLen_le_nDc).const_le (2 ^ 16) (2 ^ 270) 14 (2 ^ 240) (2 ^ 500)
    (2 ^ 125) 504 states_decR_Dc time_decR_Dc (le_of_eq (tapes_decR Dc nDc)) hSz hT
    (by norm_num) hSsig hLp hLk hLa hLc hW hnS hL hLa'
    (Nat.pow_le_pow_right (by norm_num) (by norm_num)) (by norm_num)
  exact h.trans (compBoundG_le_Dc (le_refl _) le_rfl le_rfl hR le_rfl hL (by norm_num) le_rfl)

set_option exponentiation.threshold 2000 in
/-- **The hypothesis of `attributeHiding_Dc_raw` from coarse component bounds.** -/
theorem hC_of_bounds (rc : RawComps Dc kb L impl χfl)
    (h : (rc.toRedComps nDc encLen_le_nDc).const ≤ 2 ^ 821) :
    64 * ((2 : ℝ) ^ 128) ^ 2 * ((rc.toRedComps nDc encLen_le_nDc).const : ℝ) ≤ (2 : ℝ) ^ 1155 := by
  have hr : ((rc.toRedComps nDc encLen_le_nDc).const : ℝ) ≤ (2 : ℝ) ^ 821 := by exact_mod_cast h
  calc 64 * ((2 : ℝ) ^ 128) ^ 2 * ((rc.toRedComps nDc encLen_le_nDc).const : ℝ)
      ≤ 64 * ((2 : ℝ) ^ 128) ^ 2 * (2 : ℝ) ^ 821 := by gcongr
    _ ≤ (2 : ℝ) ^ 1155 := by norm_num

/-! ### The fixed sizes at `Dc` -/

open AdvancedEncryption.ExpLUT.Params

set_option exponentiation.threshold 2000 in
theorem rawEnc_size_Dc : codecSize (rawEnc Dc) ≤ 2 ^ 110 := by
  simp only [codecSize, BCol, Wb, Jh, Col, Pos, Dig, PrI, len_sum, Enum.length_prod, len_fin]
  have hr : (circParamsD Dc).rows ≤ 2 ^ 51 := rowsD_Dc_le
  have ht : (setting Dc).τ = Dc.K := rfl
  have hb : (setting Dc).b = Dc.b := rfl
  rw [ht, hb]
  generalize (circParamsD Dc).rows = r at hr
  have hK : Dc.K = 2 ^ 16 := by show Kc = _; rw [Kc_def]
  have hN : Dc.N = 2 ^ 24 := rfl
  have hmb : Dc.mb ≤ 2 ^ 42 := by show mbar ≤ _; rw [mbar_def, Kc_def]; norm_num [en]
  have hbb : Dc.b = 22 := rfl
  rw [hK, hN, hbb]
  generalize Dc.mb = m at hmb
  norm_num [AdvancedEncryption.PE.BranchingProgram.w8,
    AdvancedEncryption.PE.BranchingProgram.Width.len]
  nlinarith

set_option exponentiation.threshold 2000 in
theorem ctEnc_size_Dc : codecSize (ctEnc Dc) ≤ 2 ^ 110 := by
  simp only [codecSize, BCol, Wb, Jh, Col, Pos, Dig, len_sum, Enum.length_prod, len_fin]
  have hK : Dc.K = 2 ^ 16 := by show Kc = _; rw [Kc_def]
  have hN : Dc.N = 2 ^ 24 := rfl
  have hmb : Dc.mb ≤ 2 ^ 42 := by show mbar ≤ _; rw [mbar_def, Kc_def]; norm_num [en]
  have hbb : Dc.b = 22 := rfl
  rw [hK, hN, hbb]
  generalize Dc.mb = m at hmb
  norm_num [AdvancedEncryption.PE.BranchingProgram.w8,
    AdvancedEncryption.PE.BranchingProgram.Width.len]
  nlinarith

set_option exponentiation.threshold 2000 in
theorem WR_Dc_le : WR Dc ≤ 2 ^ 125 := by
  have hr := rowsD_Dc_le
  have hK : Dc.K = 2 ^ 16 := by show Kc = _; rw [Kc_def]
  have hN : Dc.N = 2 ^ 24 := rfl
  unfold WR
  rw [hK, hN]
  generalize rowsD Dc = r at hr
  nlinarith

theorem toRedComps_W {D : Dims} {kb : KeyBoxes D} {L : ℕ} {χfl : PMF (Rg D)}
    (rc : RawComps D kb L impl χfl) (n : ℕ) (hn : encLen (rowsD D) D.N D.K ≤ n) :
    (rc.toRedComps n hn).W = WR D := rfl

theorem toRedComps_nS {D : Dims} {kb : KeyBoxes D} {L : ℕ} {χfl : PMF (Rg D)}
    (rc : RawComps D kb L impl χfl) (n : ℕ) (hn : encLen (rowsD D) D.N D.K ≤ n) :
    (rc.toRedComps n hn).nS = codecSize (rawEnc D) := rfl

theorem toRedComps_La {D : Dims} {kb : KeyBoxes D} {L : ℕ} {χfl : PMF (Rg D)}
    (rc : RawComps D kb L impl χfl) (n : ℕ) (hn : encLen (rowsD D) D.N D.K ≤ n) :
    (rc.toRedComps n hn).La =
      codecSize (mpkEnc D) + (codecSize (mpkEnc D) + codecSize (keyEnc D)) +
        codecSize (ctEnc D) := rfl

set_option exponentiation.threshold 2000 in
/-- **The reduction's constant from the components' own bounds** (sizes `≤ 2^240`, time
`≤ 2^500`, lengths `≤ 2^125`, at most `300` scratch tapes). -/
theorem const_le_Dc (rc : RawComps Dc kb predLen impl χfl) (hR : rc.R ≤ 300)
    (hSz : 2 * (rc.cs.setupP.size + rc.cs.pubP.size) + rc.cs.keyP.size + rc.cs.authP.size +
      rc.cs.chalP.size ≤ 2 ^ 240)
    (hT : compTimeP rc.cb ≤ 2 ^ 500)
    (hSsig : rc.cb.Ssig ≤ 2 ^ 125) (hLp : rc.cb.Lp ≤ 2 ^ 125) (hLk : rc.cb.Lk ≤ 2 ^ 125)
    (hLa : rc.cb.La ≤ 2 ^ 125) (hLc : rc.cb.Lc ≤ 2 ^ 125) :
    (rc.toRedComps nDc encLen_le_nDc).const ≤ 2 ^ 821 := by
  have h1 := keyCodec_bounds_Dc
  have h2 := ctEnc_size_Dc
  refine const_le_of_bounds rc hR hSz hT hSsig hLp hLk hLa hLc ?_ ?_ ?_ ?_
  · rw [toRedComps_W]; exact WR_Dc_le
  · rw [toRedComps_nS]; exact rawEnc_size_Dc.trans (by norm_num)
  · norm_num [predLen]
  · rw [toRedComps_La]; omega

end AdvancedEncryption.ExpLUT.Prog
