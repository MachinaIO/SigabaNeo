import PE.Impl.ExpLUT.Prog.KeyTightPubY
/-!
# KeyGen: the deterministic attempt at the cap `2^121` (tight)

`KeyTightTail` with RedKeyT's back end ported to the cap `My = 2^121` (`KeyTightPubY`) and the
tight real-trapdoor correction `KeyTight.tCorrectionC` at the same cap.

* `kyTryCert : Cert (compile (candidateTryC Dc Bk rSmall)) … (2^374)`;
* `ktSampleCert`, `ktPackPostCert` (output `≤ 2^121`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 1000
set_option maxRecDepth 100000

namespace AdvancedEncryption.ExpLUT.Prog.KeyTightY

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open AdvancedEncryption.ExpLUT.Prog
open AdvancedEncryption.ExpLUT.Prog.KeyTime
open AdvancedEncryption.ExpLUT.Prog.RedKeyT
open AdvancedEncryption.ExpLUT.Params

/-- The prepared public-key bound. -/
abbrev V14 : ℕ := 2 ^ 120

/-! ### The input envelope -/

def inY (r : Fin 64) : ℕ := if r = 14 then V14 else My

theorem inY_inputs : RingInputs My Dc.N Dc.K (layout My Dc.N Dc.K inY) := by
  apply layout_inputs
  · intro r; unfold inY; split_ifs <;> norm_num
  · rw [rkNK]; norm_num
  · rw [rkN]; norm_num
  · rw [rkK]; norm_num

theorem prepared_le_inY : preparedBounds ≤ layout My Dc.N Dc.K inY := by
  have h := preparedBounds_inputs
  apply le_layout My Dc.N Dc.K inY preparedBounds (fun t => (h.top t).trans (by norm_num))
  · simpa [rkK] using h.templateK
  · simpa [rkN] using h.templateN
  · simpa [rkNK] using h.zeros.le
  · simpa [rkNK] using h.ones
  · intro r
    unfold inY
    split_ifs
    · exact h.top _
    · exact (h.top _).trans (by norm_num)

/-! ### Coins and the candidate decoder -/

theorem inY_coin : inY rCoin = My := by simp [inY]

theorem ktSample_gen (n : ℕ) (hn : n ≤ 2 ^ 106) : Cert (KeyCore.sampleP n)
    (layout My Dc.N Dc.K inY) (layout My Dc.N Dc.K inY) (2 ^ 236) :=
  (rktSampleP My Dc.N Dc.K n inY inY_inputs (by rw [inY_coin]; exact le_MxY hn (by norm_num))
    (by norm_num)).mono le_rfl le_rfl (rktCoinTimeY n hn)

theorem ktSampleCert : Cert (KeyCore.sampleP (nPI Dc * Dc.N * Bk)) (layout My Dc.N Dc.K inY)
    (layout My Dc.N Dc.K inY) (2 ^ 236) := ktSample_gen _ coinCount_le

theorem ktCandOut_le :
    candOut Dc Bk My (layout My Dc.N Dc.K inY) ≤ stdXY V14 My My My := by
  have hi := candOut_inputs Dc Bk My (layout My Dc.N Dc.K inY) inY_inputs (by norm_num)
    (candidateInitWeight_Dc.trans (by norm_num)) nPIqY
  have hc := candOut_consts Dc Bk My (layout My Dc.N Dc.K inY)
  apply le_stdXY _ _ _ _ _ (top_of_inputs hi) hc.1.le hc.2.le
  · rw [candOut_keep _ _ _ _ 14 (Or.inl rfl), layout_register]; simp [inY]
  · exact top_of_inputs hi 17
  · exact top_of_inputs hi 18
  · exact top_of_inputs hi 19

theorem ktCandCert : Cert (MVM.compile (candidateC Dc Bk)) (layout My Dc.N Dc.K inY)
    (layout My Dc.N Dc.K (stdXY V14 My My My)) (2 ^ 339) :=
  (rktCandidateC Dc Bk My (layout My Dc.N Dc.K inY) inY_inputs (by norm_num)
    (candidateInitWeight_Dc.trans (by norm_num)) Bk_lt_Kc.le (by rw [rkNK]; norm_num)
    nPIqY).mono le_rfl (layout_mono _ _ _ ktCandOut_le) candT_leY

/-! ### The digits, `17 := z` -/

theorem ktS0_inputs : RingInputs My Dc.N Dc.K (layout My Dc.N Dc.K (stdXY V14 My My My)) :=
  stdX_inputsY _ _ _ _ (by norm_num) le_rfl le_rfl le_rfl

noncomputable abbrev KDy : Fin 64 → ℕ := digitsTailResult Dc My (pubRowsXY (stdXY V14 My My My))

theorem KDy_inputs : RingInputs My Dc.N Dc.K (layout My Dc.N Dc.K KDy) := by
  have hpi : RingInputs My Dc.N Dc.K (layout My Dc.N Dc.K (pubRowsXY (stdXY V14 My My My))) := by
    apply (publicBase_inputs _ _ _ _ ktS0_inputs).update_layout
    rw [pubRowsLenY, rkNK]; norm_num
  exact digitsTailResult_inputs Dc My _ hpi
    (le_MxY ((Nat.sub_le (codecSize (mpkEnc Dc)) _).trans keyCodec_bounds_Dc.1) (by norm_num))
    (by unfold targetTailLength; rw [rkW, rkNK]; norm_num) (by rw [rkW]; norm_num)
    (by rw [rkW, rkNK, rkK]; norm_num)

theorem KDy_fields : KDy rB1 = 1 ∧ KDy rZ = Dc.N * Dc.K ∧ KDy 14 = V14 ∧
    KDy rDq = 2 ^ 78 := by
  have hc := digits_consts Dc My (stdXY V14 My My My)
  have hk := digits_keep Dc My (stdXY V14 My My My) 14 (Or.inl rfl)
  have hf := digitsTailResult_fields Dc My (pubRowsXY (stdXY V14 My My My))
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hc.1.trans (stdX_rB1Y _ _ _ _)
  · exact hc.2.trans (stdX_rZY _ _ _ _)
  · exact hk.trans (stdX_14Y _ _ _ _)
  · show digitsTailResult Dc My (pubRowsXY _) rDq = _
    rw [hf.1, rkW, rkNK, rkK]; norm_num

theorem ktDigitsCert : Cert (MVM.compile (keyDigitsC Dc))
    (layout My Dc.N Dc.K (stdXY V14 My My My)) (layout My Dc.N Dc.K KDy) (2 ^ 373) :=
  rktKeyDigitsCY (stdXY V14 My My My) ktS0_inputs (stdX_rB1Y _ _ _ _) (stdX_rZY _ _ _ _)

theorem ktCp17Cert : Cert (MVM.compile (.cp 17 rDq)) (layout My Dc.N Dc.K KDy)
    (layout My Dc.N Dc.K (stdXY V14 (2 ^ 78) My My)) (2 * My + 5) := by
  obtain ⟨f1, fz, f14, fq⟩ := KDy_fields
  apply (layout_copy_update My Dc.N Dc.K KDy KDy_inputs.top 17 rDq).mono le_rfl
    (layout_mono _ _ _ _) le_rfl
  apply le_stdXY
  · intro r
    by_cases hr : r = 17
    · subst hr; rw [Function.update_self]; exact top_of_inputs KDy_inputs rDq
    · rw [Function.update_of_ne hr]; exact top_of_inputs KDy_inputs r
  · rw [Function.update_of_ne (by decide), f1]
  · rw [Function.update_of_ne (by decide), fz]
  · rw [Function.update_of_ne (by decide), f14]
  · rw [Function.update_self, fq]
  · rw [Function.update_of_ne (by decide)]; exact top_of_inputs KDy_inputs 18
  · rw [Function.update_of_ne (by decide)]; exact top_of_inputs KDy_inputs 19

/-! ### The real correction, `18 := p − T z` -/

theorem ktS1_inputs : RingInputs My Dc.N Dc.K (layout My Dc.N Dc.K (stdXY V14 (2 ^ 78) My My)) :=
  stdX_inputsY _ _ _ _ (by norm_num) (by norm_num) le_rfl le_rfl

/-- `KeyTight.tStepT` over the dimensions only. -/
def tStepNK (N K M I : ℕ) : ℕ :=
  3 * (2 * (2 * M + 5)) + 2 * gatherTime M N K I K + gatherTime M N K I 1 +
    ((32 * K + 4) * (2 * M + 5) + ((32 * (2 * N) + 4) * (2 * M + 5) +
      KeyTight.tAutDotT M N K K (2 * N))) + (2 * (2 * M + 5) + gatherTime M N K I 1) + appendAllowance M

theorem tStepT_eq (D : Dims) (M I : ℕ) : KeyTight.tStepT D M I = tStepNK D.N D.K M I := rfl

theorem tStepNK_num : tStepNK (2 ^ 24) (2 ^ 16) My (2 ^ 66) ≤ 2 ^ 269 := by decide +kernel

theorem tStepT_Dc : KeyTight.tStepT Dc My (2 ^ 66) ≤ 2 ^ 269 := by
  rw [tStepT_eq, rkN, rkK]; exact tStepNK_num

theorem ktCorrTime (P : ℕ) (hP : P ≤ 2 ^ 66) :
    (2 * My + 5) + (P * KeyTight.tStepT Dc My (2 ^ 66) + (2 * My + 5)) ≤ 2 ^ 336 := by
  have h := Nat.mul_le_mul hP tStepT_Dc
  calc _ ≤ (2 * My + 5) + (2 ^ 66 * 2 ^ 269 + (2 * My + 5)) := by omega
    _ ≤ 2 ^ 336 := by norm_num

theorem ktCorrCert : Cert (MVM.compile (correctionC Dc))
    (layout My Dc.N Dc.K (stdXY V14 (2 ^ 78) My My))
    (layout My Dc.N Dc.K (stdXY V14 (2 ^ 78) (2 ^ 106) My)) (2 ^ 336) := by
  have hc := correction_counts_Dc
  have hNK : Dc.N * Dc.K ≤ My := by rw [rkNK]; norm_num
  let b := stdXY V14 (2 ^ 78) My My
  have hM (r : Fin 64) (a3 : r ≠ rB1) (a4 : r ≠ rZ) (a5 : r ≠ 14)
      (a6 : r ≠ 17) (a7 : r ≠ 18) (a8 : r ≠ 19) : b r = My :=
    stdX_otherY _ _ _ _ r a3 a4 a5 a6 a7 a8
  have hs : (Enum.list (α := PIdxD Dc)).length * (Dc.N * Dc.K) ≤ 2 ^ 106 := by
    rw [rkNK]; calc _ ≤ 2 ^ 66 * 2 ^ 40 := Nat.mul_le_mul_right _ hc.2.2
      _ = 2 ^ 106 := by norm_num
  have p := KeyTight.tCorrectionC Dc My (2 ^ 66) b ktS1_inputs (stdX_rB1Y _ _ _ _) (stdX_rZY _ _ _ _).le
    (by rw [hM rQx (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)];
        exact hNK)
    (by rw [hM rQy (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)];
        exact hNK)
    (hs.trans (by norm_num)) (by rw [rkNK]; norm_num) (by rw [rkNK, rkK]; norm_num)
    (by rw [rkN]; norm_num) hc.1 hc.2.1 hc.2.2
  have hout : Function.update (correctionBase My b) 18
      ((Enum.list (α := PIdxD Dc)).length * (Dc.N * Dc.K)) ≤ stdXY V14 (2 ^ 78) (2 ^ 106) My := by
    have hi := (correctionBase_inputs My Dc.N Dc.K b ktS1_inputs).update_layout 18 _
      (hs.trans (by norm_num))
    have kb (r : Fin 64) (hr : r ∉ correctionScratch) (h18 : r ≠ 18) :
        Function.update (correctionBase My b) 18
          ((Enum.list (α := PIdxD Dc)).length * (Dc.N * Dc.K)) r = b r := by
      rw [Function.update_of_ne h18]; simp [correctionBase, hr]
    apply le_stdXY _ _ _ _ _ (top_of_inputs hi)
    · rw [kb _ (by decide) (by decide)]; exact (stdX_rB1Y _ _ _ _).le
    · rw [kb _ (by decide) (by decide)]; exact (stdX_rZY _ _ _ _).le
    · rw [kb _ (by decide) (by decide)]; exact (stdX_14Y _ _ _ _).le
    · rw [kb _ (by decide) (by decide)]; exact (stdX_17Y _ _ _ _).le
    · rw [Function.update_self]; exact hs
    · exact top_of_inputs hi 19
  exact p.mono le_rfl (layout_mono _ _ _ hout) (ktCorrTime _ hc.2.2)

/-! ### Assembly and acceptance -/

theorem ktS2_inputs :
    RingInputs My Dc.N Dc.K (layout My Dc.N Dc.K (stdXY V14 (2 ^ 78) (2 ^ 106) My)) :=
  stdX_inputsY _ _ _ _ (by norm_num) (by norm_num) (by norm_num) le_rfl

theorem ktS3_inputs :
    RingInputs My Dc.N Dc.K (layout My Dc.N Dc.K (stdXY V14 My My (2 ^ 120))) :=
  stdX_inputsY _ _ _ _ (by norm_num) le_rfl le_rfl (by norm_num)

theorem ktAsmCert : Cert (MVM.compile (assembleC Dc))
    (layout My Dc.N Dc.K (stdXY V14 (2 ^ 78) (2 ^ 106) My))
    (layout My Dc.N Dc.K (stdXY V14 My My (2 ^ 120))) (2 ^ 315) := by
  have hs : (stdXY V14 (2 ^ 78) (2 ^ 106) My) 18 + (stdXY V14 (2 ^ 78) (2 ^ 106) My) 17 ≤ My := by
    rw [stdX_18Y, stdX_17Y]; norm_num
  have p := rktAssembleCY (stdXY V14 (2 ^ 78) (2 ^ 106) My) ktS2_inputs (stdX_rB1Y _ _ _ _)
    (stdX_rZY _ _ _ _).le hs
  have hl := assemblyIndices_bounds.2
  have hlen : (assemblyIndices Dc).length * (Dc.N * Dc.K) ≤ 2 ^ 106 := by
    rw [rkNK]; calc _ ≤ 2 ^ 66 * 2 ^ 40 := Nat.mul_le_mul_right _ hl
      _ = 2 ^ 106 := by norm_num
  have ha : RingInputs My Dc.N Dc.K (layout My Dc.N Dc.K
      (asmXY (Dc.N * Dc.K) (assemblyIndices Dc).length (stdXY V14 (2 ^ 78) (2 ^ 106) My))) :=
    (((gatherBase_inputs _ _ _ _ (ktS2_inputs.update_layout 0 _ hs)).update_layout 4 _
      (le_MxY hlen (by norm_num))).update_layout 19 _ (le_MxY hlen (by norm_num)))
  obtain ⟨k1, kz, k14, k19⟩ := asmX_keepY (Dc.N * Dc.K) (assemblyIndices Dc).length
    (stdXY V14 (2 ^ 78) (2 ^ 106) My)
  refine p.mono le_rfl (layout_mono _ _ _ ?_) le_rfl
  apply le_stdXY _ _ _ _ _ (top_of_inputs ha)
  · rw [k1, stdX_rB1Y]
  · rw [kz, stdX_rZY]
  · rw [k14, stdX_14Y]
  · exact top_of_inputs ha 17
  · exact top_of_inputs ha 18
  · rw [k19]; exact hlen.trans (by norm_num)

theorem ktAccCert : Cert (MVM.compile (acceptC Dc Bk rSmall))
    (layout My Dc.N Dc.K (stdXY V14 My My (2 ^ 120)))
    (layout My Dc.N Dc.K (stdXY V14 My My (2 ^ 120))) (2 ^ 335) := by
  have hm : 1 ≤ My := by norm_num
  have hc := correction_counts_Dc.2.2
  have hkey := keyCodec_bounds_Dc.2.2
  have p := rktAcceptC Dc My Bk rSmall (2 ^ 66) (stdXY V14 My My (2 ^ 120)) ktS3_inputs
    (stdX_rB1Y _ _ _ _) (stdX_rZY _ _ _ _).le hm Bk_lt_Kc.le hc (by norm_num)
    (le_MxY hkey (by norm_num))
  have hi := acceptInitResult_inputs Dc My Bk (stdXY V14 My My (2 ^ 120)) ktS3_inputs hm
    Bk_lt_Kc.le (le_MxY hc (by norm_num))
  have ha : RingInputs My Dc.N Dc.K (layout My Dc.N Dc.K (accOut Dc My Bk
      (stdXY V14 My My (2 ^ 120)))) :=
    ((bxBase_inputs _ _ _ _ hi).update_layout rTx 1 hm).update_layout 19 _
      (max_le (le_MxY (by rw [stdX_19Y]) (by norm_num)) (le_MxY hkey (by norm_num)))
  obtain ⟨k1, kz, k14, k19⟩ := accOut_keep Dc My Bk (stdXY V14 My My (2 ^ 120))
  refine p.mono le_rfl (layout_mono _ _ _ ?_) accT_leY
  apply le_stdXY _ _ _ _ _ (top_of_inputs ha)
  · rw [k1, stdX_rB1Y]
  · rw [kz, stdX_rZY]
  · rw [k14, stdX_14Y]
  · exact top_of_inputs ha 17
  · exact top_of_inputs ha 18
  · rw [k19, stdX_19Y]; exact max_le le_rfl hkey

/-! ### Packing and the epilogue -/

theorem ktPackPostCert : Cert (.seq (MVM.compile packKeyC) (.prog MVM.IO.post))
    (layout My Dc.N Dc.K (stdXY V14 My My (2 ^ 120))) (outputBounds (2 ^ 121)) (2 ^ 249) := by
  have hs : (stdXY V14 My My (2 ^ 120)) 14 + (stdXY V14 My My (2 ^ 120)) 19 ≤ My := by
    rw [stdX_14Y, stdX_19Y]; norm_num
  have p0 := compile_packKeyC My Dc.N Dc.K (stdXY V14 My My (2 ^ 120)) ktS3_inputs hs
  have hp := ktS3_inputs.update_layout 0
    ((stdXY V14 My My (2 ^ 120)) 14 + (stdXY V14 My My (2 ^ 120)) 19) hs
  have p1 := cert_vmPost My (layout My Dc.N Dc.K (packedResult (stdXY V14 My My (2 ^ 120))))
    hp.top
  have he : layout My Dc.N Dc.K (packedResult (stdXY V14 My My (2 ^ 120))) 41 = 2 ^ 121 := by
    change packedResult (stdXY V14 My My (2 ^ 120)) 0 = _
    simp only [packedResult, Function.update_self, stdX_14Y, stdX_19Y]
    norm_num
  rw [he] at p1
  exact (p0.seq p1).mono le_rfl le_rfl (by norm_num [appendAllowance])

/-! ### The attempt -/

theorem ktTryCert : Cert (MVM.compile (candidateTryC Dc Bk rSmall))
    (layout My Dc.N Dc.K inY) (layout My Dc.N Dc.K (stdXY V14 My My (2 ^ 120))) (2 ^ 374) := by
  have all := ktCandCert.seq
    ((((ktDigitsCert.seq (ktCp17Cert.seq ktCorrCert)).seq ktAsmCert).seq ktAccCert))
  exact all.mono le_rfl le_rfl (by norm_num)

/-- **The attempt after preparation**: coins, the candidate, one try, the packed output. -/
theorem ktAttemptCert :
    Cert (.seq (.seq (KeyCore.sampleP (nPI Dc * Dc.N * Bk))
        (MVM.compile (candidateTryC Dc Bk rSmall)))
      (.seq (MVM.compile packKeyC) (.prog MVM.IO.post)))
      preparedBounds (outputBounds (2 ^ 121)) (2 ^ 375) := by
  have all := (ktSampleCert.seq ktTryCert).seq ktPackPostCert
  exact all.mono prepared_le_inY le_rfl (by norm_num)

end AdvancedEncryption.ExpLUT.Prog.KeyTightY
