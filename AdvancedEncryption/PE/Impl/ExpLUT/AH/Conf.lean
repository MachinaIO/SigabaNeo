import PE.Impl.ExpLUT.AH.Assembly
import PE.Impl.ExpLUT.AH.Sim
import PE.Impl.ExpLUT.Params.Noise
import PE.Impl.ExpLUT.Params.Strength

/-!
# Package G at the concrete parameters

`Dc`: the dimensions of package P (`N = 2^24`, `K = Kc = 2^16`, `W = 2^22`, `m̄ = mbar`); its
setting is P's `confS` (`setting_Dc`, by definition), so P's noise and box lemmas apply.

* **Box coverage** (`KbCover kb B`: the small box shifted by any family with coefficients within
  `B` stays in the big box; P's boxes `Small`/`Big` have it at `B = coverBound = 2^18500` by
  `add_mem_of_eq`): `realCovW_of` (the real trapdoor shifts by at most `τ n = 2^40`) and
  `simCovW_of` (Lemma 11's `T_sim` for `R̂_F` of Corollary 1 with binary programming, `T = 16`:
  shift `≤ W τ n D^b (B_R̂ + 2) ≤ 2^18500`, `rhatBound_le`, `simShift_le`). **The cover bound
  `2^18500` suffices** for both.
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices Matrix Cslib Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.ExpLUT.Params
open scoped ENNReal

theorem two_le_Kc : 2 ≤ Kc := by rw [Kc_def]; norm_num

/-- **The concrete dimensions** (package P). -/
def Dc : Dims where
  e := en
  K := Kc
  b := bc
  mb := mbar
  hK := two_le_Kc
  hb := bc_le_Kc
  h2 := h2c
  hlt := hltc

theorem setting_Dc : setting Dc = confS := rfl

theorem Dc_b : Dc.b = 22 := rfl

instance : Nonempty (Wb Dc) := ⟨⟨0, by show 0 < mbar; rw [mbar_def]; positivity⟩⟩

/-- The norm of the concrete setting. -/
noncomputable def NDc : NormSpec (setting Dc) := confN

theorem NDc_nrm (a : Rg Dc) : NDc.nrm a = cnorm a := confN_nrm a

/-- **Box coverage**: the small box shifted by any family with coefficients within `B` stays in
the big box. -/
def KbCover {D : Dims} (kb : KeyBoxes D) (B : ℕ) : Prop :=
  ∀ x ∈ kb.Small, ∀ s : PIdx (Wb D) (Jh D) D.K (2 ^ D.b) → Rg D, (∀ p, cnorm (s p) ≤ B) →
    x + s ∈ kb.Big

theorem χbin_short : ∀ a ∈ (χbin Dc).support, cnorm a ≤ 1 := by
  intro a ha
  rw [χbin_eq_bitLaw] at ha
  simp only [bitLaw, PMF.mem_support_map_iff] at ha
  obtain ⟨b, -, rfl⟩ := ha
  rw [← NDc_nrm]
  cases b
  · simp [bitVal, NDc.nrm_zero]
  · simpa [bitVal] using (NDc_nrm 1).trans_le (χT_short 1 (by
      simp only [χT, PMF.mem_support_map_iff]; exact ⟨true, by simp, rfl⟩))

/-- **The real trapdoor shifts by at most `τ n = 2^40 ≤ 2^18500`.** -/
theorem realShift_le_Dc (T : Matrix (Wb Dc) (Fin (setting Dc).τ) (Rg Dc))
    (hT : ∀ w c, cnorm (T w c) ≤ 1) (y : Fin (setting Dc).E.W → Rg Dc)
    (p : PIdx (Wb Dc) (Jh Dc) (setting Dc).τ (setting Dc).E.W) :
    cnorm (realTrap (J := Jh Dc) T (gadDec y) p) ≤ coverBound := by
  have h := rowBnd_realTrap (J := Jh Dc) NDc T 1 (fun w c => by rw [NDc_nrm]; exact hT w c)
    (gadDec y) (fun ic => NDc.nrm_digit _ _) p
  rw [NDc_nrm] at h
  refine h.trans ?_
  show Kc * (2 ^ en * 1) ≤ 2 ^ eSh
  calc Kc * (2 ^ en * 1) ≤ 2 ^ 16 * 2 ^ 24 := by rw [mul_one]; exact Nat.mul_le_mul_right _ Kc_le
    _ = 2 ^ 40 := by norm_num
    _ ≤ 2 ^ eSh := pow_le_pow' (by rw [eSh_def]; norm_num)

/-- **The real trapdoor is covered.** -/
theorem realCovW_of {kb : KeyBoxes Dc} (hkb : KbCover kb coverBound) : RealCovW Dc kb := by
  intro v hv C _ x' hx' y
  obtain ⟨-, -, hT⟩ := mem_support_setupLawW hv
  exact hkb x' hx' _ fun p => realShift_le_Dc v.2.T (fun w c => χbin_short _ (hT w c)) y p

/-- **Lemma 11's trapdoor shifts by at most `2^18500`** for the programmed public keys and the
branching programs of predicate words (`T = 16`, binary programming). -/
theorem simShift_le_Dc (x : Pos → ℕ) (P : PubData (setting Dc) (Wb Dc) (Jh Dc))
    (zr : PrI (setting Dc) Pos → Wb Dc → Bool) (core : Core (setting Dc) (Wb Dc) (Jh Dc))
    (fl : FloodV (setting Dc) Pos) (C : List Bool) (y : Fin (setting Dc).E.W → Rg Dc)
    (p : PIdx (Wb Dc) (Jh Dc) (setting Dc).τ (setting Dc).E.W) :
    cnorm (simTrap (helperMap Dc) (view2 (helperMap Dc) wSt P x zr core fl).1 (bpOf (progOf C))
      (simKey (helperMap Dc) (view2 (helperMap Dc) wSt P x zr core fl).1 (bpOf (progOf C))
        (view2 (helperMap Dc) wSt P x zr core fl).2 x (ExpLUT.progOf zr)) (gadDec y) p) ≤
      coverBound := by
  have h1 : NDc.nrm 1 ≤ 1 := by
    rw [NDc_nrm]; exact χT_short 1 (by
      simp only [χT, PMF.mem_support_map_iff]; exact ⟨true, by simp, rfl⟩)
  have hD : 1 ≤ (setting Dc).gfac := le_trans (by norm_num) two_le_gfac
  have hR := matBnd_simKey (helperMap Dc) h1 hD (view2 (helperMap Dc) wSt P x zr core fl).1
    (bpOf (progOf C)) (view2 (helperMap Dc) wSt P x zr core fl).2 x
    (progBnd_progOf (J := Jh Dc) NDc h1 zr)
  have hs := rowBnd_simTrap (helperMap Dc) h1 hD (view2 (helperMap Dc) wSt P x zr core fl).1
    (bpOf (progOf C)) hR (gadDec y) p
  rw [NDc_nrm] at hs
  refine hs.trans (le_trans ?_ (simShift_rhat_le (T := 16) le_rfl))
  set B := (stepBound confS 1 1 1)^[16] 1
  have hv := vBound_iterate_le (S := confS) two_le_gfac (max B 1) confS.b
  have hmax : max B 1 + 1 ≤ B + 2 := by omega
  show confS.E.W * confS.τ * (confS.E.n * (vBound confS)^[confS.b] (max B 1)) ≤
    confS.E.W * confS.τ * confS.E.n * (confS.gfac ^ confS.b * (B + 2))
  rw [mul_assoc (confS.E.W * confS.τ)]
  refine Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ?_)
  calc (vBound confS)^[confS.b] (max B 1) ≤ confS.gfac ^ confS.b * (max B 1 + 1) := by omega
    _ ≤ confS.gfac ^ confS.b * (B + 2) := Nat.mul_le_mul_left _ hmax

/-- **Lemma 11's trapdoor is covered.** -/
theorem simCovW_of {kb : KeyBoxes Dc} (hkb : KbCover kb coverBound) : SimCovW Dc kb := by
  intro x P zr core fl C _ x' hx' y
  exact hkb x' hx' _ fun p => simShift_le_Dc x P zr core fl C y p

end AdvancedEncryption.ExpLUT.Prog
