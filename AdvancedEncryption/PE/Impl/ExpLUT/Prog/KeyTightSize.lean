import PE.Impl.ExpLUT.Prog.KeyTimeFront
import PE.Impl.ExpLUT.Prog.RedKeyTSize

/-!
# KeyGen: a tight state count and description length

F3 (`KeySizeConf.size_keyProgram_Dc_pow`) charges every `natC r u n` with `3 n + 1` states, so the
codec-size constants (`≈ 2^102 … 2^106`) and the index constants of the gathers dominate, and
`descLen_arithA` bounds `Nat.size S` by `S` itself (`descLen ≈ S²`).

Here `natC` is charged logarithmically (`RedKeyT.wtNatC`), the gathers by `RedKeyT.wtGatherC`, and
the public rows by `RedKeyT.wtKeyDigitsC_Dc`; `Nat.size S` is bounded by `log₂`.

* `KeyTight.wtKeyPrepareC_Dc`, `wtCorrectionC_Dc`, `wtAssembleC_Dc'`, `wtAcceptC_Dc`,
  `wtInvalidKeyC_Dc`, `wtCandidateTryC_Dc`;
* `KeyTight.size_keyProgram_tight : (keyProgram Dc Bk rSmall).size ≤ 2^115`;
* **`KeyCore.descLen_keyMachine_tight : keyMachine.descLen ≤ 2^295`**.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 100000
set_option exponentiation.threshold 2000

namespace AdvancedEncryption.ExpLUT.Prog.KeyTight

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open AdvancedEncryption.ExpLUT.Prog
open AdvancedEncryption.ExpLUT.Prog.RedKeyT (wtNatC wtGatherC lt200_of_le66 dcN dcK dcW dcNK
  wtKeyDigitsC_Dc wtCandidateC_Dc)
open AdvancedEncryption.ExpLUT.Params PE.BranchingProgram

/-! ### Reading fields and the master-key input -/

theorem wtReadFieldC (src dst : Fin 64) (off len : ℕ) (ho : off < 2 ^ 200) (hl : len < 2 ^ 200) :
    codeWeight (readFieldC src dst off len) ≤ 810 := by
  have h1 := wtNatC 30 rB1 off ho
  have h2 := wtNatC 30 rB1 len hl
  simp only [readFieldC, takeC, codeWeight]
  omega

theorem wtKeyInputC (D : Dims) (hm : codecSize (mpkEnc D) < 2 ^ 199)
    (ht : codecSize (matE D (Wb D) (Fin D.K)) < 2 ^ 199) :
    codeWeight (keyInputC D) ≤ 1700 := by
  have h1 := wtReadFieldC 0 17 0 (codecSize (mpkEnc D)) (by omega) (by omega)
  have h2 := wtReadFieldC 0 16 (codecSize (mpkEnc D)) (codecSize (matE D (Wb D) (Fin D.K)))
    (by omega) (by omega)
  simp only [keyInputC, bitsC, codeWeight]
  omega

theorem wtReadPublicFieldC (D : Dims) (hm : codecSize (mpkEnc D) < 2 ^ 200) (dst : Fin 64)
    (j : ℕ) : codeWeight (readPublicFieldC D dst j) ≤ 810 := by
  have hl := take_sum_add_getD_le_sum (publicFieldLengths D) j
  rw [publicFieldLengths_sum] at hl
  change codeWeight (readFieldC 17 dst _ _) ≤ _
  exact wtReadFieldC _ _ _ _ (by omega) (by omega)

theorem wtEvalFieldsC (D : Dims) (hm : codecSize (mpkEnc D) < 2 ^ 200) :
    codeWeight (evalFieldsC D) ≤ 3240 := by
  have h1 := wtReadPublicFieldC D hm 2 1
  have h3 := wtReadPublicFieldC D hm 4 3
  have h4 := wtReadPublicFieldC D hm 0 4
  have h5 := wtReadPublicFieldC D hm 1 5
  simp only [evalFieldsC, codeWeight]
  omega

theorem wtKeyPrepareC_of (D : Dims) (E : ℕ) (hm : codecSize (mpkEnc D) < 2 ^ 199)
    (ht : codecSize (matE D (Wb D) (Fin D.K)) < 2 ^ 199)
    (he : ((evalInitOps D).map (fun op ↦ op.2.weightBound)).sum ≤ E) :
    codeWeight (keyPrepareC D) ≤ E + 2 ^ 21 := by
  have hi := wtKeyInputC D hm ht
  have hf := wtEvalFieldsC D (by omega)
  have hto := weight_templateOpsC (evalInitOps D)
  have hs : codeWeight evalScratchC + codeWeight evalC ≤ 2 ^ 20 := by decide +kernel
  simp only [keyPrepareC, keyEvalPrepareC, evalReadyC, evalPublicC, evalInitC,
    bitsC, codeWeight]
  omega

theorem evalInitWeight_Dc_tight :
    ((evalInitOps Dc).map (fun op ↦ op.2.weightBound)).sum ≤ 2 ^ 94 := by
  rw [evalInitWeight_eq]
  norm_num [Dc, Kc, gD, SigabaNeo.Lattices.gGen, tlK]

theorem wtKeyPrepareC_Dc : codeWeight (keyPrepareC Dc) ≤ 2 ^ 95 := by
  have hm : codecSize (mpkEnc Dc) < 2 ^ 199 :=
    lt_of_le_of_lt keyCodec_bounds_Dc.1 (by norm_num)
  have ht : codecSize (matE Dc (Wb Dc) (Fin Dc.K)) < 2 ^ 199 :=
    lt_of_le_of_lt keyCodec_bounds_Dc.2.1 (by norm_num)
  exact (wtKeyPrepareC_of Dc _ hm ht evalInitWeight_Dc_tight).trans (by norm_num)

/-! ### The real-trapdoor correction -/

theorem wtLoadFamilyC (N K : ℕ) (src dst : Fin 64) (js : List ℕ)
    (h : ∀ j ∈ js, j * (N * K) < 2 ^ 200) :
    codeWeight (loadFamilyC N K src dst js) ≤ js.length * 407 + 4 := by
  have := wtGatherC N K js h
  simp only [loadFamilyC, saveQueueC, codeWeight]
  omega

/-- Generic in `D`: every index of the three loads is below `S`, `S · N K < 2^200`. -/
theorem wtCorrectionInlC (D : Dims) (S : ℕ)
    (hT : (Enum.list (α := Wb D × Fin D.K)).length ≤ S)
    (hZ : (Enum.list (α := ZIdx (setting D).τ (setting D).E.W)).length ≤ S)
    (hP : (Enum.list (α := PIdxD D)).length ≤ S) (hS : S * (D.N * D.K) < 2 ^ 200)
    (hK : D.K < 2 ^ 200) (hE : 2 * D.N < 2 ^ 200)
    (i : Fin (setting D).E.W) (row : Wb D) :
    codeWeight (correctionInlC D i row) ≤ 3 * ((D.K + 1) * 407 + 4) + 900 := by
  have hidx : ∀ j, j ≤ S → j * (D.N * D.K) < 2 ^ 200 := fun j hj =>
    lt_of_le_of_lt (Nat.mul_le_mul_right _ hj) hS
  have hk := wtNatC rQc rB1 D.K hK
  have he := wtNatC rQk rB1 (rowExponent D i.val)
    (lt_of_lt_of_le (rowExponent_lt D i.val) hE.le)
  have ha : codeWeight autDotC ≤ 98 := by decide
  simp only [correctionInlC, correctionLoadC, codeWeight]
  refine le_trans (Nat.add_le_add (Nat.add_le_add (wtLoadFamilyC _ _ _ _ _ ?_)
    (Nat.add_le_add (wtLoadFamilyC _ _ _ _ _ ?_) (wtLoadFamilyC _ _ _ _ _ ?_)))
    (Nat.add_le_add hk (Nat.add_le_add he ha))) ?_
  · intro j hj
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hj
    exact hidx _ ((Enum.index_lt _).le.trans hT)
  · intro j hj
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hj
    exact hidx _ ((Enum.index_lt _).le.trans hZ)
  · intro j hj
    simp only [List.mem_singleton] at hj
    subst j
    exact hidx _ ((@Enum.index_lt _ _ (fun a b => Classical.propDecidable (a = b)) _).le.trans hP)
  · have l1 : ((Enum.list (α := Fin D.K)).map (fun c ↦ Enum.index (row, c))).length ≤
        D.K + 1 := by
      rw [List.length_map]; change (List.finRange D.K).length ≤ D.K + 1; simp
    have l2 : ((Enum.list (α := Fin (setting D).τ)).map (fun c ↦ Enum.index (i, c))).length ≤
        D.K + 1 := by
      rw [List.length_map]; change (List.finRange D.K).length ≤ D.K + 1; simp
    have m1 := Nat.mul_le_mul_right 407 l1
    have m2 := Nat.mul_le_mul_right 407 l2
    simp only [List.length_singleton]
    omega

theorem wtCorrectionCoordC (D : Dims) (S : ℕ)
    (hT : (Enum.list (α := Wb D × Fin D.K)).length ≤ S)
    (hZ : (Enum.list (α := ZIdx (setting D).τ (setting D).E.W)).length ≤ S)
    (hP : (Enum.list (α := PIdxD D)).length ≤ S) (hS : S * (D.N * D.K) < 2 ^ 200)
    (hK : D.K < 2 ^ 200) (hE : 2 * D.N < 2 ^ 200)
    (q : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W) :
    codeWeight (correctionCoordC D q) ≤ 3 * ((D.K + 1) * 407 + 4) + 900 := by
  let : DecidableEq (PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W) := Classical.decEq _
  rcases q with ⟨i, row⟩ | q
  · exact wtCorrectionInlC D S hT hZ hP hS hK hE i row
  · unfold correctionCoordC
    apply (wtLoadFamilyC D.N D.K _ _ _ ?_).trans
    · simp only [List.length_singleton]; omega
    · intro j hj
      simp only [List.mem_singleton] at hj
      subst j
      exact lt_of_le_of_lt (Nat.mul_le_mul_right _ ((Enum.index_lt _).le.trans hP)) hS

theorem wtCorrectionAppendC (D : Dims) (S W : ℕ)
    (hq : ∀ q, codeWeight (correctionCoordC D q) ≤ W) : ∀ qs,
    codeWeight (correctionAppendC D qs) ≤ qs.length * (W + 1) + 1
  | [] => by simp [correctionAppendC, codeWeight]
  | q :: qs => by
    have h1 := hq q
    have ih := wtCorrectionAppendC D S W hq qs
    simp only [correctionAppendC, codeWeight, List.length_cons]
    nlinarith

/-- The per-coordinate weight (opaque, so that `omega` treats `S * W` as one atom). -/
def corrCoordW (K : ℕ) : ℕ := 3 * ((K + 1) * 407 + 4) + 900

theorem wtCorrectionC_of (D : Dims) (S : ℕ)
    (hT : (Enum.list (α := Wb D × Fin D.K)).length ≤ S)
    (hZ : (Enum.list (α := ZIdx (setting D).τ (setting D).E.W)).length ≤ S)
    (hP : (Enum.list (α := PIdxD D)).length ≤ S) (hS : S * (D.N * D.K) < 2 ^ 200)
    (hK : D.K < 2 ^ 200) (hE : 2 * D.N < 2 ^ 200) :
    codeWeight (correctionC D) ≤ S * (corrCoordW D.K + 1) + 2 := by
  have h := wtCorrectionAppendC D S (corrCoordW D.K)
    (wtCorrectionCoordC D S hT hZ hP hS hK hE) Enum.list
  have hm := Nat.mul_le_mul_right (corrCoordW D.K + 1) hP
  simp only [correctionC, codeWeight]
  omega

theorem wtCorrectionC_Dc : codeWeight (correctionC Dc) ≤ 2 ^ 93 := by
  have hc := correction_counts_Dc
  have h := wtCorrectionC_of Dc (2 ^ 66) hc.1 hc.2.1 hc.2.2 (lt200_of_le66 le_rfl)
    (by rw [dcK]; norm_num) (by rw [dcN]; norm_num)
  rw [corrCoordW, dcK] at h
  exact h.trans (by norm_num)

/-! ### Assembly, acceptance, the invalid branch -/

theorem wtAssembleC_of (D : Dims) (S : ℕ)
    (hL : (Enum.list (α := KCol (Wb D) (Jh D) (setting D).τ (setting D).E.W)).length ≤ S)
    (hA : (Enum.list (α := AssemblySource D)).length ≤ S) (hS : S * (D.N * D.K) < 2 ^ 200) :
    codeWeight (assembleC D) ≤ S * 407 + 10 := by
  let : DecidableEq (PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W) := Classical.decEq _
  have hg := wtGatherC D.N D.K (Enum.list.map (Enum.index ∘ assemblySelection D)) (by
    intro j hj
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hj
    exact lt_of_le_of_lt (Nat.mul_le_mul_right _ ((Enum.index_lt _).le.trans hA)) hS)
  rw [List.length_map] at hg
  have hm := Nat.mul_le_mul_right 407 hL
  simp only [assembleC, saveQueueC, codeWeight]
  omega

theorem wtAssembleC_Dc' : codeWeight (assembleC Dc) ≤ 2 ^ 75 :=
  (wtAssembleC_of Dc (2 ^ 66) assembly_lengths_Dc.1 assembly_lengths_Dc.2
    (lt200_of_le66 le_rfl)).trans (by norm_num)

theorem wtAcceptC_of (D : Dims) (B r : ℕ) (hk : codecSize (keyEnc D) < 2 ^ 200) :
    codeWeight (acceptC D B r) ≤ D.K + 3 * D.N + 3 * B + 3 * (D.K - B) +
      3 * (Enum.list (α := PIdxD D)).length + 520 := by
  have hi := weight_acceptInitC D B r
  have hz := wtNatC 19 rB1 (codecSize (keyEnc D)) hk
  have hb := weight_boxFamilyC
  simp only [acceptC, codeWeight]
  omega

theorem wtAcceptC_le (D : Dims) (B r : ℕ) (hk : codecSize (keyEnc D) < 2 ^ 200)
    (hK : D.K ≤ 2 ^ 16) (hN : D.N ≤ 2 ^ 24) (hB : B ≤ 2 ^ 16)
    (hP : (Enum.list (α := PIdxD D)).length ≤ 2 ^ 66) :
    codeWeight (acceptC D B r) ≤ 2 ^ 69 := by
  have h := wtAcceptC_of D B r hk
  have hKB : D.K - B ≤ 2 ^ 16 := (Nat.sub_le _ _).trans hK
  omega

theorem wtAcceptC_Dc (r : ℕ) : codeWeight (acceptC Dc Bk r) ≤ 2 ^ 69 :=
  wtAcceptC_le Dc Bk r (lt_of_le_of_lt keyCodec_bounds_Dc.2.2 (by norm_num)) dcK.le dcN.le
    (by rw [← dcK]; exact Bk_lt_Kc.le) correction_counts_Dc.2.2

theorem wtInvalidKeyC_Dc : codeWeight (invalidKeyC Dc) ≤ 2200 := by
  have hm : codecSize (mpkEnc Dc) < 2 ^ 199 :=
    lt_of_le_of_lt keyCodec_bounds_Dc.1 (by norm_num)
  have ht : codecSize (matE Dc (Wb Dc) (Fin Dc.K)) < 2 ^ 199 :=
    lt_of_le_of_lt keyCodec_bounds_Dc.2.1 (by norm_num)
  have hi := wtKeyInputC Dc hm ht
  have hn := wtNatC 19 rB1 (codecSize (keyEnc Dc))
    (lt_of_le_of_lt keyCodec_bounds_Dc.2.2 (by norm_num))
  simp only [invalidKeyC, packKeyC, codeWeight]
  omega

/-! ### The deterministic attempt -/

theorem wtCandidateTryC_of (D : Dims) (B r Wc Wd Wr Wa Wx : ℕ)
    (hc : codeWeight (candidateC D B) ≤ Wc) (hd : codeWeight (keyDigitsC D) ≤ Wd)
    (hr : codeWeight (correctionC D) ≤ Wr) (ha : codeWeight (assembleC D) ≤ Wa)
    (hx : codeWeight (acceptC D B r) ≤ Wx) :
    codeWeight (candidateTryC D B r) ≤ Wc + Wd + Wr + Wa + Wx + 1 := by
  simp only [candidateTryC, tryKeyC, proposalKeyC, proposalC, codeWeight]
  omega

theorem wtCandidateTryC_Dc (r : ℕ) :
    codeWeight (candidateTryC Dc Bk r) ≤ 2 ^ 98 + 2 ^ 97 := by
  have hd : codeWeight (keyDigitsC Dc) ≤ (2 ^ 22 * (2 ^ 66 * 1300 + 1) + 1) + 1000 + 1000 := by
    have hp := RedKeyT.wtPublicRowsAppendC_Dc Enum.list
    have hl : (Enum.list (α := Fin (setting Dc).E.W)).length = 2 ^ 22 := by rw [len_fin, dcW]
    rw [hl] at hp
    exact RedKeyT.wtKeyDigitsC_of Dc (2 ^ 22 * (2 ^ 66 * 1300 + 1) + 1) 1000 hp RedKeyT.wtTargetC_Dc
      (wtNatC rQc rB1 _ (by rw [dcW]; norm_num)) (wtNatC rQk rB1 _ (by rw [dcK]; norm_num))
  exact (wtCandidateTryC_of Dc Bk r _ _ _ _ _ wtCandidateC_Dc hd wtCorrectionC_Dc
    wtAssembleC_Dc' (wtAcceptC_Dc r)).trans (by norm_num)

/-! ### The whole program -/

/-- F3's composition (`size_keyProgram`) with the three code weights as parameters. -/
theorem size_keyProgram_of (D : Dims) (B r m Wp Wc Wi : ℕ)
    (hp : codeWeight (keyPrepareC D) ≤ Wp) (hc : codeWeight (candidateTryC D B r) ≤ Wc)
    (hi : codeWeight (invalidKeyC D) ≤ Wi) (hn : nPI D * D.N * B < 2 ^ m) :
    (KeyCore.keyProgram D B r).size ≤ 100000 * (Wp + Wc + Wi) + 12600 * (D.N * D.K) +
      195 * m + 500 * Nat.log2 predLen + 620000 := by
  have hp' := (size_compile_weight (keyPrepareC D)).trans (Nat.mul_le_mul_left 100000 hp)
  have hc' := (size_compile_weight (candidateTryC D B r)).trans (Nat.mul_le_mul_left 100000 hc)
  have hi' := (size_compile_weight (invalidKeyC D)).trans (Nat.mul_le_mul_left 100000 hi)
  have hs := KeyCore.size_sampleP _ m hn
  have he := KeyCore.size_enter_post D
  have ho := size_compile_weight packKeyC
  simp only [packKeyC, codeWeight] at ho
  have hparse := KeyCore.size_parse
  have hframe := KeyCore.size_frameKeyP
  have hcheck := KeyCore.size_checkP
  simp only [KeyCore.keyProgram, KeyCore.chooseP, KeyCore.validP, KeyCore.invalidP,
    KeyCore.outputProgram, KeyCore.program, XProg.size_seq, XProg.size_prog, XProg.size_ifBit,
    packKeyC]
  omega

theorem log2_predLen_le : Nat.log2 predLen ≤ 30 := by
  have h : predLen < 2 ^ 31 := by norm_num [predLen]
  have := (Nat.log2_lt (by norm_num [predLen])).mpr h
  omega

theorem size_keyProgram_tight :
    (KeyCore.keyProgram Dc Bk rSmall).size ≤ 2 ^ 115 + 2 ^ 114 := by
  have h := size_keyProgram_of Dc Bk rSmall 106 _ _ _ wtKeyPrepareC_Dc (wtCandidateTryC_Dc rSmall)
    wtInvalidKeyC_Dc KeyCore.keyCoinCount_Dc
  have hl := log2_predLen_le
  rw [dcNK] at h
  have : 100000 * (2 ^ 95 + (2 ^ 98 + 2 ^ 97) + 2200) + 12600 * 2 ^ 40 + 195 * 106 + 500 * 30 +
      620000 ≤ (2 : ℕ) ^ 115 + 2 ^ 114 := by norm_num
  omega

theorem size_keyGuard_tight (n : ℕ) (hn : n ≤ 2 ^ 103) :
    (KeyCore.keyGuardP Dc Bk rSmall n).size + (n + 3) + 2 ≤ 2 ^ 116 := by
  have hg := KeyCore.size_guardP_le n
  have hk := size_keyProgram_tight
  have h1 := SigabaNeo.Tape.Prog.size_prim_le' (k := 105) (.clear 103)
  have h0 := SigabaNeo.Tape.Prog.size_prim_le' (k := 105) (.clear 0)
  have e := KeyCore.size_keyGuardP Dc Bk rSmall n
  have : 60 * (2 ^ 103 + 10) + 2 ^ 103 + (2 ^ 115 + 2 ^ 114) + 200 ≤ (2 : ℕ) ^ 116 := by norm_num
  omega

/-! ### Description length with `Nat.size` bounded logarithmically -/

theorem descLen_arithLog {k S E : ℕ} (h : S ≤ 2 ^ E) :
    6 * S * 3 ^ k * 3 ^ 0 * Machine.entryBits k S 0 ≤ 6 * 2 ^ E * 3 ^ k * (5 + 4 * k + E) := by
  have hs : Nat.size S ≤ E + 1 := Nat.size_le.mpr (lt_of_le_of_lt h (by
    rw [pow_succ]; have := Nat.one_le_two_pow (n := E); omega))
  unfold Machine.entryBits
  simp only [pow_zero, mul_one, Nat.mul_zero, Nat.add_zero, Nat.size_zero]
  exact Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 6 h)) (by omega)

theorem descLen_num : 6 * 2 ^ 116 * 3 ^ 105 * (5 + 4 * 105 + 116) ≤ (2 : ℕ) ^ 295 := by
  norm_num

end AdvancedEncryption.ExpLUT.Prog.KeyTight

namespace AdvancedEncryption.ExpLUT.Prog.KeyCore

/-- **The tight description length of the KeyGen machine.** -/
theorem descLen_keyMachine_tight : keyMachine.descLen ≤ 2 ^ 295 := by
  rw [keyMachine_eq, descLen_toMachineB105]
  exact (KeyTight.descLen_arithLog (KeyTight.size_keyGuard_tight _ keyInputBound_Dc)).trans
    KeyTight.descLen_num

end AdvancedEncryption.ExpLUT.Prog.KeyCore
