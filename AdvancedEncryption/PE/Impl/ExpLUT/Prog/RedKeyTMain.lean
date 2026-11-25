import PE.Impl.ExpLUT.Prog.RedKeyTTail
/-!
# Module 9: **`rkTailCert_of`** — the back-end certificate from the interface `RkTailIn`

`RkTailIn a → RkTailCert a rkLt rkTt`, `rkLt = 2^102 + 2^120 ≤ 2^125`, `rkTt = 2^436 ≤ 2^449`.

Envelopes (all registers at the cap `Mx = 2^150` except the listed ones):
`(stdX (2 ^ 102) Mx Mx Mx) = stdX 2^102 Mx Mx Mx` after the candidate decoder; `(stdX (2 ^ 102) (2 ^ 78) Mx Mx) = stdX 2^102 2^78 Mx Mx` after the
digits (`17 := z`); `(stdX (2 ^ 102) (2 ^ 78) (2 ^ 106) Mx) = stdX 2^102 2^78 2^106 Mx` after `mvSubC` (`18 := p − X u`);
`(stdX (2 ^ 102) Mx Mx (2 ^ 120)) = stdX 2^102 Mx Mx 2^120` after the assembly (`19 := key`), kept by the acceptance step.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 1000
set_option maxRecDepth 100000

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyT

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open AdvancedEncryption.ExpLUT.Prog
open AdvancedEncryption.ExpLUT.Prog.KeyTime
open AdvancedEncryption.ExpLUT.Params


theorem le_Mx {n k : ℕ} (h : n ≤ 2 ^ k) (hk : k ≤ 150) : n ≤ Mx :=
  h.trans (Nat.pow_le_pow_right (by norm_num) hk)

/-! ### Coins and the candidate decoder -/

theorem nPIq_gen (Q x : ℕ) (hQ : Q ≤ 2 ^ 66) (hx : x = 2 ^ 40) : Q * x ≤ Mx := by
  subst hx; calc Q * 2 ^ 40 ≤ 2 ^ 66 * 2 ^ 40 := Nat.mul_le_mul_right _ hQ
    _ ≤ Mx := by norm_num

theorem nPIq : nPI Dc * (Dc.N * Dc.K) ≤ Mx := nPIq_gen _ _ correction_counts_Dc.2.2 rkNK

theorem candOut_inputs (D : Dims) (B M : ℕ) (a : Fin 105 → ℕ) (h : RingInputs M D.N D.K a)
    (hM : 1 ≤ M) (hw : ((candidateInitOps D B).map (fun op ↦ op.2.weightBound)).sum ≤ M)
    (hq : nPI D * (D.N * D.K) ≤ M) :
    RingInputs M D.N D.K (layout M D.N D.K (candOut D B M a)) := by
  have hi := candidateInitResult_inputs D B M D.N D.K a h hM hw
  have hb : RingInputs M D.N D.K (layout M D.N D.K (fun r ↦ candidateInitResult D B M a (tR r))) :=
    layout_inputs _ _ _ _ (fun r ↦ hi.top (tR r)) hi.ring hi.dimension hi.width
  exact ((decodeQueueBase_inputs M D.N D.K _ hb).update_layout rDq _ hq).update_layout 9 _ hq

theorem candOut_le_S0 :
    candOut Dc Bk Mx (layout Mx Dc.N Dc.K inX) ≤ (stdX (2 ^ 102) Mx Mx Mx) := by
  have hi := candOut_inputs Dc Bk Mx (layout Mx Dc.N Dc.K inX) inX_inputs (by norm_num)
    (candidateInitWeight_Dc.trans (by norm_num))
    nPIq
  have hc := candOut_consts Dc Bk Mx (layout Mx Dc.N Dc.K inX)
  apply le_stdX _ _ _ _ _ (top_of_inputs hi) hc.1.le hc.2.le
  · rw [candOut_keep _ _ _ _ 14 (Or.inl rfl), layout_register]; simp [inX]
  · exact top_of_inputs hi 17
  · exact top_of_inputs hi 18
  · exact top_of_inputs hi 19

theorem coinCount_le : nPI Dc * Dc.N * Bk ≤ 2 ^ 106 := KeyCore.keyCoinCount_Dc.le

theorem inX_coin : inX rCoin = Mx := by simp [inX]

theorem rkSample_gen (n : ℕ) (hn : n ≤ 2 ^ 106) : Cert (KeyCore.sampleP n)
    (layout Mx Dc.N Dc.K inX) (layout Mx Dc.N Dc.K inX) (2 ^ 264) :=
  (rktSampleP Mx Dc.N Dc.K n inX inX_inputs (by rw [inX_coin]; exact le_Mx hn (by norm_num))
    (by norm_num)).mono le_rfl le_rfl (rktCoinTime n hn)

theorem rkSampleCert : Cert (KeyCore.sampleP (nPI Dc * Dc.N * Bk)) (layout Mx Dc.N Dc.K inX)
    (layout Mx Dc.N Dc.K inX) (2 ^ 264) := rkSample_gen _ coinCount_le

theorem rkCandCert : Cert (MVM.compile (candidateC Dc Bk)) (layout Mx Dc.N Dc.K inX)
    (layout Mx Dc.N Dc.K (stdX (2 ^ 102) Mx Mx Mx)) (2 ^ 397) :=
  (rktCandidateC Dc Bk Mx (layout Mx Dc.N Dc.K inX) inX_inputs (by norm_num)
    (candidateInitWeight_Dc.trans (by norm_num)) Bk_lt_Kc.le (by rw [rkNK]; norm_num)
    nPIq).mono
      le_rfl (layout_mono _ _ _ candOut_le_S0) candT_le

/-! ### The digits, `17 := z` -/

theorem S0_inputs : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K (stdX (2 ^ 102) Mx Mx Mx)) :=
  stdX_inputs _ _ _ _ (by norm_num) le_rfl le_rfl le_rfl

noncomputable abbrev KD : Fin 64 → ℕ := digitsTailResult Dc Mx (pubRowsX (stdX (2 ^ 102) Mx Mx Mx))

theorem KD_inputs : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K KD) := by
  have hpi : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K (pubRowsX (stdX (2 ^ 102) Mx Mx Mx))) := by
    apply (publicBase_inputs _ _ _ _ S0_inputs).update_layout
    rw [pubRowsLen, rkNK]; norm_num
  exact digitsTailResult_inputs Dc Mx _ hpi
    (le_Mx ((Nat.sub_le (codecSize (mpkEnc Dc)) _).trans keyCodec_bounds_Dc.1) (by norm_num))
    (by unfold targetTailLength; rw [rkW, rkNK]; norm_num) (by rw [rkW]; norm_num)
    (by rw [rkW, rkNK, rkK]; norm_num)

theorem KD_fields : KD rB1 = 1 ∧ KD rZ = Dc.N * Dc.K ∧ KD 14 = 2 ^ 102 ∧
    KD rDq = 2 ^ 78 := by
  have hc := digits_consts Dc Mx (stdX (2 ^ 102) Mx Mx Mx)
  have hk := digits_keep Dc Mx (stdX (2 ^ 102) Mx Mx Mx) 14 (Or.inl rfl)
  have hf := digitsTailResult_fields Dc Mx (pubRowsX (stdX (2 ^ 102) Mx Mx Mx))
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hc.1.trans (stdX_rB1 _ _ _ _)
  · exact hc.2.trans (stdX_rZ _ _ _ _)
  · exact hk.trans (stdX_14 _ _ _ _)
  · show digitsTailResult Dc Mx (pubRowsX _) rDq = _
    rw [hf.1, rkW, rkNK, rkK]; norm_num

theorem rkDigitsCert : Cert (MVM.compile (keyDigitsC Dc)) (layout Mx Dc.N Dc.K (stdX (2 ^ 102) Mx Mx Mx))
    (layout Mx Dc.N Dc.K KD) (2 ^ 433) :=
  rktKeyDigitsC (stdX (2 ^ 102) Mx Mx Mx) S0_inputs (stdX_rB1 _ _ _ _) (stdX_rZ _ _ _ _)

theorem rkCp17Cert : Cert (MVM.compile (.cp 17 rDq)) (layout Mx Dc.N Dc.K KD)
    (layout Mx Dc.N Dc.K (stdX (2 ^ 102) (2 ^ 78) Mx Mx)) (2 * Mx + 5) := by
  obtain ⟨f1, fz, f14, fq⟩ := KD_fields
  apply (layout_copy_update Mx Dc.N Dc.K KD KD_inputs.top 17 rDq).mono le_rfl
    (layout_mono _ _ _ _) le_rfl
  apply le_stdX
  · intro r
    by_cases hr : r = 17
    · subst hr; rw [Function.update_self]; exact top_of_inputs KD_inputs rDq
    · rw [Function.update_of_ne hr]; exact top_of_inputs KD_inputs r
  · rw [Function.update_of_ne (by decide), f1]
  · rw [Function.update_of_ne (by decide), fz]
  · rw [Function.update_of_ne (by decide), f14]
  · rw [Function.update_self, fq]
  · rw [Function.update_of_ne (by decide)]; exact top_of_inputs KD_inputs 18
  · rw [Function.update_of_ne (by decide)]; exact top_of_inputs KD_inputs 19

/-! ### The correction `18 := p − X u` -/

theorem S1_inputs : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K (stdX (2 ^ 102) (2 ^ 78) Mx Mx)) :=
  stdX_inputs _ _ _ _ (by norm_num) (by norm_num) le_rfl le_rfl

theorem rkUCert : Cert (MVM.compile (uC Dc)) (layout Mx Dc.N Dc.K (stdX (2 ^ 102) (2 ^ 78) Mx Mx))
    (layout Mx Dc.N Dc.K (stdX (2 ^ 102) (2 ^ 78) Mx Mx)) (2 ^ 434) :=
  rktUC _ _ _ _ (by norm_num) (by norm_num) le_rfl le_rfl

theorem natT66 (n : ℕ) (hn : n ≤ 2 ^ 66) : (32 * n + 4) * (2 * Mx + 5) ≤ 2 ^ 225 := natT_le n hn

theorem rkCorrCert (z p : ℕ) (hz : z ≤ 2 ^ 66) (hp : p ≤ 2 ^ 66) :
    Cert (MVM.compile (.seq (natC rVm rB1 z) (.seq (natC rVn rB1 p) mvSubC)))
      (layout Mx Dc.N Dc.K (stdX (2 ^ 102) (2 ^ 78) Mx Mx)) (layout Mx Dc.N Dc.K (stdX (2 ^ 102) (2 ^ 78) (2 ^ 106) Mx)) (2 ^ 417) := by
  have hzM : z ≤ Mx := le_Mx hz (by norm_num)
  have hpM : p ≤ Mx := le_Mx hp (by norm_num)
  have hNK : Dc.N * Dc.K ≤ Mx := by rw [rkNK]; norm_num
  have p1 := layout_nat_update Mx Dc.N Dc.K (stdX (2 ^ 102) (2 ^ 78) Mx Mx) S1_inputs rVm rB1 (by decide) z
    (stdX_rB1 _ _ _ _) hzM
  let B1 := Function.update (stdX (2 ^ 102) (2 ^ 78) Mx Mx) rVm z
  have h1 : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K B1) := S1_inputs.update_layout _ _ hzM
  have p2 := layout_nat_update Mx Dc.N Dc.K B1 h1 rVn rB1 (by decide) p
    (by simp [B1, stdX]) hpM
  let B2 := Function.update B1 rVn p
  have h2 : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K B2) := h1.update_layout _ _ hpM
  have k2 (r : Fin 64) (a1 : r ≠ rVn) (a2 : r ≠ rVm) : B2 r = (stdX (2 ^ 102) (2 ^ 78) Mx Mx) r := by
    simp only [B2, B1, Function.update_of_ne a1, Function.update_of_ne a2]
  have hM (r : Fin 64) (a1 : r ≠ rVn) (a2 : r ≠ rVm) (a3 : r ≠ rB1) (a4 : r ≠ rZ) (a5 : r ≠ 14)
      (a6 : r ≠ 17) (a7 : r ≠ 18) (a8 : r ≠ 19) : B2 r = Mx := by
    rw [k2 r a1 a2, stdX_other _ _ _ _ r a3 a4 a5 a6 a7 a8]
  have p3 := rktMvSubC Mx Dc.N Dc.K (2 ^ 66) (2 ^ 66) B2 h2
    (by rw [k2 _ (by decide) (by decide), stdX_rZ])
    (by rw [hM rQx (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact hNK)
    (by rw [hM rQy (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact hNK)
    (by rw [hM rIa (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact hNK)
    (by rw [hM rQb (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact top_of_inputs h2 rVu)
    (by rw [hM rQc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact top_of_inputs h2 rVm)
    (by simp only [B2, B1, Function.update_of_ne (by decide : rVm ≠ rVn), Function.update_self]
        exact hz)
    (by rw [hM rQa (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact top_of_inputs h2 16)
    (by simp only [B2, Function.update_self]; exact hp)
    (by rw [rkNK]; norm_num)
  have hout : Function.update B2 18 (2 ^ 66 * (Dc.N * Dc.K)) ≤ (stdX (2 ^ 102) (2 ^ 78) (2 ^ 106) Mx) := by
    have h3 : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K (Function.update B2 18
        (2 ^ 66 * (Dc.N * Dc.K)))) := h2.update_layout _ _ (by rw [rkNK]; norm_num)
    apply le_stdX _ _ _ _ _ (top_of_inputs h3)
    · rw [Function.update_of_ne (by decide), k2 _ (by decide) (by decide), stdX_rB1]
    · rw [Function.update_of_ne (by decide), k2 _ (by decide) (by decide), stdX_rZ]
    · rw [Function.update_of_ne (by decide), k2 _ (by decide) (by decide), stdX_14]
    · rw [Function.update_of_ne (by decide), k2 _ (by decide) (by decide), stdX_17]
    · rw [Function.update_self, rkNK]; norm_num
    · rw [Function.update_of_ne (by decide), k2 _ (by decide) (by decide), stdX_19]
  have hT := mvSubT_var Dc.N Dc.K (2 ^ 66) (2 ^ 66) rkN.le rkK.le le_rfl le_rfl
  refine (p1.seq (p2.seq p3)).mono le_rfl (layout_mono _ _ _ hout) ?_
  calc _ ≤ 2 ^ 225 + (2 ^ 225 + 2 ^ 416) :=
        Nat.add_le_add (natT66 z hz) (Nat.add_le_add (natT66 p hp) hT)
    _ ≤ 2 ^ 417 := by norm_num

/-! ### Assembly and acceptance -/

theorem S2_inputs : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K (stdX (2 ^ 102) (2 ^ 78) (2 ^ 106) Mx)) :=
  stdX_inputs _ _ _ _ (by norm_num) (by norm_num) (by norm_num) le_rfl

theorem S3_inputs : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K (stdX (2 ^ 102) Mx Mx (2 ^ 120))) :=
  stdX_inputs _ _ _ _ (by norm_num) le_rfl le_rfl (by norm_num)

theorem asmX_keep (NK L : ℕ) (b : Fin 64 → ℕ) :
    asmX NK L b rB1 = b rB1 ∧ asmX NK L b rZ = b rZ ∧ asmX NK L b 14 = b 14 ∧
    asmX NK L b 19 = L * NK := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [asmX, gatherBase, Function.update_apply]

theorem rkAsmCert : Cert (MVM.compile (assembleC Dc)) (layout Mx Dc.N Dc.K (stdX (2 ^ 102) (2 ^ 78) (2 ^ 106) Mx))
    (layout Mx Dc.N Dc.K (stdX (2 ^ 102) Mx Mx (2 ^ 120))) (2 ^ 373) := by
  have hNK : Dc.N * Dc.K ≤ Mx := by rw [rkNK]; norm_num
  have hs : (stdX (2 ^ 102) (2 ^ 78) (2 ^ 106) Mx) 18 + (stdX (2 ^ 102) (2 ^ 78) (2 ^ 106) Mx) 17 ≤ Mx := by rw [stdX_18, stdX_17]; norm_num
  have p := rktAssembleC (stdX (2 ^ 102) (2 ^ 78) (2 ^ 106) Mx) S2_inputs (stdX_rB1 _ _ _ _) (stdX_rZ _ _ _ _).le hs
  have hl := assemblyIndices_bounds.2
  have hlen : (assemblyIndices Dc).length * (Dc.N * Dc.K) ≤ 2 ^ 106 := by
    rw [rkNK]; calc _ ≤ 2 ^ 66 * 2 ^ 40 := Nat.mul_le_mul_right _ hl
      _ = 2 ^ 106 := by norm_num
  have ha : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K
      (asmX (Dc.N * Dc.K) (assemblyIndices Dc).length (stdX (2 ^ 102) (2 ^ 78) (2 ^ 106) Mx))) :=
    (((gatherBase_inputs _ _ _ _ (S2_inputs.update_layout 0 _ hs)).update_layout 4 _
      (le_Mx hlen (by norm_num))).update_layout 19 _ (le_Mx hlen (by norm_num)))
  obtain ⟨k1, kz, k14, k19⟩ := asmX_keep (Dc.N * Dc.K) (assemblyIndices Dc).length (stdX (2 ^ 102) (2 ^ 78) (2 ^ 106) Mx)
  refine p.mono le_rfl (layout_mono _ _ _ ?_) le_rfl
  apply le_stdX _ _ _ _ _ (top_of_inputs ha)
  · rw [k1, stdX_rB1]
  · rw [kz, stdX_rZ]
  · rw [k14, stdX_14]
  · exact top_of_inputs ha 17
  · exact top_of_inputs ha 18
  · rw [k19]; exact hlen.trans (by norm_num)

theorem rkAccCert : Cert (MVM.compile (acceptC Dc Bk rSmall)) (layout Mx Dc.N Dc.K (stdX (2 ^ 102) Mx Mx (2 ^ 120)))
    (layout Mx Dc.N Dc.K (stdX (2 ^ 102) Mx Mx (2 ^ 120))) (2 ^ 371) := by
  have hm : 1 ≤ Mx := by norm_num
  have hc := correction_counts_Dc.2.2
  have hkey := keyCodec_bounds_Dc.2.2
  have p := rktAcceptC Dc Mx Bk rSmall (2 ^ 66) (stdX (2 ^ 102) Mx Mx (2 ^ 120)) S3_inputs (stdX_rB1 _ _ _ _)
    (stdX_rZ _ _ _ _).le hm Bk_lt_Kc.le hc (by norm_num) (le_Mx hkey (by norm_num))
  have hi := acceptInitResult_inputs Dc Mx Bk (stdX (2 ^ 102) Mx Mx (2 ^ 120)) S3_inputs hm Bk_lt_Kc.le (le_Mx hc (by norm_num))
  have ha : RingInputs Mx Dc.N Dc.K (layout Mx Dc.N Dc.K (accOut Dc Mx Bk (stdX (2 ^ 102) Mx Mx (2 ^ 120)))) :=
    ((bxBase_inputs _ _ _ _ hi).update_layout rTx 1 hm).update_layout 19 _
      (max_le (le_Mx (by rw [stdX_19]) (by norm_num)) (le_Mx hkey (by norm_num)))
  obtain ⟨k1, kz, k14, k19⟩ := accOut_keep Dc Mx Bk (stdX (2 ^ 102) Mx Mx (2 ^ 120))
  refine p.mono le_rfl (layout_mono _ _ _ ?_) accT_le
  apply le_stdX _ _ _ _ _ (top_of_inputs ha)
  · rw [k1, stdX_rB1]
  · rw [kz, stdX_rZ]
  · rw [k14, stdX_14]
  · exact top_of_inputs ha 17
  · exact top_of_inputs ha 18
  · rw [k19, stdX_19]; exact max_le le_rfl hkey

/-! ### Packing and the epilogue -/

/-- The output bound of the component. -/
def rkLt : ℕ := 2 ^ 102 + 2 ^ 120

theorem rkPackPostCert : Cert (.seq (MVM.compile packKeyC) (.prog MVM.IO.post))
    (layout Mx Dc.N Dc.K (stdX (2 ^ 102) Mx Mx (2 ^ 120))) (outputBounds rkLt) (2 ^ 306) := by
  have hs : (stdX (2 ^ 102) Mx Mx (2 ^ 120)) 14 + (stdX (2 ^ 102) Mx Mx (2 ^ 120)) 19 ≤ Mx := by rw [stdX_14, stdX_19]; norm_num
  have p0 := compile_packKeyC Mx Dc.N Dc.K (stdX (2 ^ 102) Mx Mx (2 ^ 120)) S3_inputs hs
  have hp := S3_inputs.update_layout 0 ((stdX (2 ^ 102) Mx Mx (2 ^ 120)) 14 + (stdX (2 ^ 102) Mx Mx (2 ^ 120)) 19) hs
  have p1 := cert_vmPost Mx (layout Mx Dc.N Dc.K (packedResult (stdX (2 ^ 102) Mx Mx (2 ^ 120)))) hp.top
  have he : layout Mx Dc.N Dc.K (packedResult (stdX (2 ^ 102) Mx Mx (2 ^ 120))) 41 = rkLt := by
    change packedResult (stdX (2 ^ 102) Mx Mx (2 ^ 120)) 0 = _
    simp only [packedResult, Function.update_self, stdX_14, stdX_19, rkLt]
  rw [he] at p1
  exact (p0.seq p1).mono le_rfl le_rfl (by norm_num [appendAllowance])

/-! ### The simulated try and the whole back end -/

theorem rkSimTryCert : Cert (MVM.compile (simTryKeyC Dc (uC Dc) Bk rSmall))
    (layout Mx Dc.N Dc.K (stdX (2 ^ 102) Mx Mx Mx)) (layout Mx Dc.N Dc.K (stdX (2 ^ 102) Mx Mx (2 ^ 120))) (2 ^ 435) := by
  have hz := correction_counts_Dc.2.1
  have hp := correction_counts_Dc.2.2
  have corr := rkCorrCert (Enum.list (α := ZIdxS Dc)).length (Enum.list (α := PIdxS Dc)).length
    hz hp
  have all := ((rkDigitsCert.seq (rkCp17Cert.seq (rkUCert.seq corr))).seq rkAsmCert).seq rkAccCert
  exact all.mono le_rfl le_rfl (by norm_num)

/-- The clock of the component's back end. -/
def rkTt : ℕ := 2 ^ 436

/-- **The back-end certificate from the interface.** -/
theorem rkTailCert_of {a : Fin 105 → ℕ} (ha : RkTailIn a) : RkTailCert a rkLt rkTt := by
  have all := rkSampleCert.seq ((rkCandCert.seq rkSimTryCert).seq rkPackPostCert)
  exact all.mono (le_inX ha) le_rfl (by norm_num [rkTt])

theorem rkLt_le : rkLt ≤ 2 ^ 125 := by norm_num [rkLt]
theorem rkTt_le : rkTt ≤ 2 ^ 449 := by norm_num [rkTt]

end AdvancedEncryption.ExpLUT.Prog.RedKeyT
