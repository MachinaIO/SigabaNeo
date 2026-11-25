import PE.Impl.ExpLUT.Prog.RedKeyMTail
import PE.Impl.ExpLUT.Prog.KeySizeConf
/-!
# Module 9: the state count of the back end `rkTailP` (`≤ 2^195`)

F3's weight bounds charge `natC r u n` with `3 n + 1` states (`weight_natC`). The gathers then
cost `|js| · 3 J · N K` (`J` the largest index), which is `≈ 2^174` per gather at `Dc`, too much
for `2^22` rows. Here `natC` is charged logarithmically (`wtNatC_lt`: `n < 2^B ⇒ ≤ 2 B + 1`), and
the gathers, the public rows, `keyDigitsC`, the assembly and the `u` routine are recounted.

* **`size_rkTailP_Dc : (rkTailP Dc Bk rSmall).size ≤ 2^195`**.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 100000
set_option exponentiation.threshold 1000

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyT

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open AdvancedEncryption.ExpLUT.Prog
open AdvancedEncryption.ExpLUT.Params

/-! ### `natC` is logarithmic -/

theorem wtNatC_lt (r u : Fin 64) : ∀ (B n : ℕ), n < 2 ^ B → codeWeight (natC r u n) ≤ 2 * B + 1
  | 0, n, h => by
    have : n = 0 := by simpa using h
    subst this; simp [natC, codeWeight]
  | B + 1, 0, _ => by simp [natC, codeWeight]
  | B + 1, n + 1, h => by
    rw [natC]
    have ih := wtNatC_lt r u B ((n + 1) / 2) (by rw [pow_succ] at h; omega)
    split_ifs <;> simp only [codeWeight] <;> omega

/-- The uniform constant: every `natC` of the back end has an argument `< 2^200`. -/
theorem wtNatC (r u : Fin 64) (n : ℕ) (h : n < 2 ^ 200) : codeWeight (natC r u n) ≤ 401 :=
  wtNatC_lt r u 200 n h

/-! ### Gathers -/

theorem wtFetchRingC (N K j : ℕ) (h : j * (N * K) < 2 ^ 200) :
    codeWeight (fetchRingC N K j) ≤ 405 := by
  have := wtNatC 2 rB1 _ h
  simp only [fetchRingC, codeWeight]
  omega

theorem wtGatherAppendC (N K : ℕ) : ∀ js : List ℕ,
    (∀ j ∈ js, j * (N * K) < 2 ^ 200) →
    codeWeight (gatherAppendC N K js) ≤ js.length * 407 + 1
  | [], _ => by simp [gatherAppendC, codeWeight]
  | j :: js, h => by
    have hf := wtFetchRingC N K j (h j (by simp))
    have ih := wtGatherAppendC N K js (fun i hi => h i (by simp [hi]))
    simp only [gatherAppendC, codeWeight, List.length_cons]
    nlinarith

theorem wtGatherC (N K : ℕ) (js : List ℕ) (h : ∀ j ∈ js, j * (N * K) < 2 ^ 200) :
    codeWeight (gatherC N K js) ≤ js.length * 407 + 2 := by
  have := wtGatherAppendC N K js h
  simp only [gatherC, codeWeight]
  omega

/-- A selected gather: indices below `S`, `S · N K < 2^200`. -/
theorem wtSelGather {α β : Type} [Enum α] [Enum β] [DecidableEq α]
    (N K S : ℕ) (f : β → α) (hα : (Enum.list (α := α)).length ≤ S)
    (hβ : (Enum.list (α := β)).length ≤ S) (hS : S * (N * K) < 2 ^ 200) :
    codeWeight (gatherC N K (Enum.list.map (Enum.index ∘ f))) ≤ S * 407 + 2 := by
  apply (wtGatherC N K _ ?_).trans
  · simp only [List.length_map]
    have := Nat.mul_le_mul_right 407 hβ
    omega
  · intro j hj
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hj
    exact lt_of_le_of_lt (Nat.mul_le_mul_right _ ((Enum.index_lt (f a)).le.trans hα)) hS

theorem wtPrefixC (n : ℕ) (h : n < 2 ^ 200) : codeWeight (prefixC n) ≤ 405 := by
  have := wtNatC 2 rB1 n h
  simp only [prefixC, takeC, codeWeight]
  omega

/-! ### The concrete sizes at `Dc` -/

theorem dcN : Dc.N = 2 ^ 24 := by norm_num [Dc, Dims.N, Params.en]
theorem dcK : Dc.K = 2 ^ 16 := by norm_num [Dc, Params.Kc]
theorem dcW : (setting Dc).E.W = 2 ^ 22 := by change 2 ^ Dc.b = _; norm_num [Dc, Params.bc]

theorem dcNK : Dc.N * Dc.K = 2 ^ 40 := by rw [dcN, dcK]; norm_num

theorem lt200_of_le66 {n : ℕ} (h : n ≤ 2 ^ 66) : n * (Dc.N * Dc.K) < 2 ^ 200 := by
  rw [dcNK]
  calc n * 2 ^ 40 ≤ 2 ^ 66 * 2 ^ 40 := Nat.mul_le_mul_right _ h
    _ < 2 ^ 200 := by norm_num

theorem lt200_of_le {n m : ℕ} (h : n ≤ m) (hm : m < 2 ^ 200) : n < 2 ^ 200 := lt_of_le_of_lt h hm

/-! ### Public rows -/

theorem wtGatherBHC_Dc (i : ℕ) : codeWeight (gatherBHC Dc i) ≤ 2 ^ 66 * 407 + 1000 := by
  unfold gatherBHC gatherAutC
  have hs := publicSizeInputs_Dc
  have hg := wtSelGather Dc.N Dc.K (2 ^ 66) (bhSelection Dc) hs.source hs.rows (lt200_of_le66 le_rfl)
  have hn := wtNatC rQc rB1 (Enum.list.map (Enum.index ∘ bhSelection Dc)).length
    (by simp only [List.length_map]; exact lt_of_le_of_lt hs.rows (by norm_num))
  have hk := wtNatC rQk rB1 (rowExponent Dc i)
    (lt_of_lt_of_le (rowExponent_lt Dc i) (by rw [dcN]; norm_num))
  simp only [autGatheredC, autQC, autQBody, codeWeight] at hn hk ⊢
  omega

theorem bhPrefixLength_lt : bhPrefixLength Dc < 2 ^ 200 := by
  unfold bhPrefixLength
  exact lt200_of_le66 publicSizeInputs_Dc.source

theorem wtPositiveCoeffC_Dc (i : Fin (setting Dc).E.W) :
    codeWeight (positiveCoeffC Dc i) ≤ 2 ^ 66 * 407 + 2000 := by
  have hp := wtPrefixC _ bhPrefixLength_lt
  have hg := wtGatherBHC_Dc i.val
  have hf : (2 * Dc.K) * (Dc.N * Dc.K) < 2 ^ 200 := by rw [dcNK, dcK]; norm_num
  have ha : codeWeight (appendAFC Dc.N Dc.K (decide (i = (setting Dc).row0))) ≤ 410 := by
    have h1 := wtPrefixC _ hf
    have h2 := wtNatC 6 rB1 _ hf
    cases decide (i = (setting Dc).row0) <;>
      simp only [appendAFC, Bool.false_eq_true, ↓reduceIte, codeWeight] <;> omega
  simp only [positiveCoeffC, mpkBHC, codeWeight]
  omega

theorem wtNegativeReadyC_Dc :
    codeWeight (negativeReadyC Dc.N Dc.K (Enum.list (α := Jh Dc)).length) ≤ 3000 := by
  have h1 := wtNatC 7 rB1 (Dc.N * Dc.K - 1) (by rw [dcNK]; omega)
  have h2 := wtNatC 2 rB1 Dc.K (by rw [dcK]; norm_num)
  have h3 := wtNatC 6 rB1 (Dc.K * (Dc.N * Dc.K)) (by rw [dcNK, dcK]; norm_num)
  have h4 := wtNatC 2 rB1 (Enum.list (α := Jh Dc)).length
    (lt_of_le_of_lt publicSizeInputs_Dc.helpers (by norm_num))
  simp only [negativeReadyC, ringOneC, bitsC, negativeCoeffC, powersC, powersBody, repAppC,
    codeWeight] at h1 h2 h3 h4 ⊢
  omega

theorem wtPublicRowC_Dc (i : Fin (setting Dc).E.W) :
    codeWeight (publicRowC Dc i) ≤ 2 ^ 66 * 1300 := by
  let : DecidableEq (PIdx (Wb Dc) (Jh Dc) (setting Dc).τ (setting Dc).E.W) := Classical.decEq _
  have hs := publicSizeInputs_Dc
  have hp := wtPositiveCoeffC_Dc i
  have hn := wtNegativeReadyC_Dc
  have g1 : codeWeight (positiveGatherC Dc i) ≤ 2 ^ 66 * 407 + 2 :=
    wtSelGather _ _ _ (positiveSelection Dc i) hs.candidate hs.positive (lt200_of_le66 le_rfl)
  have g2 : codeWeight (negativeGatherC Dc i) ≤ 2 ^ 66 * 407 + 2 :=
    wtSelGather _ _ _ (negativeSelection Dc i) hs.candidate hs.negative (lt200_of_le66 le_rfl)
  have hc := wtNatC rQc rB1 (Enum.list (α := PublicPos (Wb Dc) (Jh Dc) (setting Dc).τ)).length
    (lt_of_le_of_lt hs.positive (by norm_num))
  have hd := wtNatC 12 rB1 (Enum.list (α := Jh Dc × Col (setting Dc).τ)).length
    (lt_of_le_of_lt hs.negative (by norm_num))
  have hsd : codeWeight signedDotC ≤ 100 := by decide
  simp only [publicRowC, saveQueueC, rowCountsC, codeWeight]
  omega

theorem wtPublicRowsAppendC_Dc : ∀ is : List (Fin (setting Dc).E.W),
    codeWeight (publicRowsAppendC Dc is) ≤ is.length * (2 ^ 66 * 1300 + 1) + 1
  | [] => by simp [publicRowsAppendC, codeWeight]
  | i :: is => by
    have hi := wtPublicRowC_Dc i
    have ih := wtPublicRowsAppendC_Dc is
    simp only [publicRowsAppendC, codeWeight, List.length_cons]
    nlinarith

theorem mpkDOffset_lt : mpkDOffset Dc < 2 ^ 200 :=
  lt_of_le_of_lt ((Nat.sub_le _ _).trans keyCodec_bounds_Dc.1) (by norm_num)

theorem wtTargetC_Dc : codeWeight (targetC Dc) ≤ 1000 := by
  have h1 := wtNatC 2 rB1 _ mpkDOffset_lt
  have h2 := wtNatC 2 rB1 (((setting Dc).E.W - 1) * (Dc.N * Dc.K))
    (by rw [dcW, dcNK]; norm_num)
  simp only [targetC, targetHeadC, codeWeight]
  omega

/-- Generic in `D`, so that `simp` never sees the concrete row list. -/
theorem wtKeyDigitsC_of (D : Dims) (R T : ℕ) (hp : codeWeight (publicRowsAppendC D Enum.list) ≤ R)
    (ht : codeWeight (targetC D) ≤ T) (hw : codeWeight (natC rQc rB1 (setting D).E.W) ≤ 401)
    (hk : codeWeight (natC rQk rB1 D.K) ≤ 401) : codeWeight (keyDigitsC D) ≤ R + T + 1000 := by
  have hd : codeWeight decRowsC ≤ 100 := by decide
  simp only [keyDigitsC, publicRowsC, codeWeight]
  omega

theorem wtKeyDigitsC_Dc : codeWeight (keyDigitsC Dc) ≤ 2 ^ 100 := by
  have hp := wtPublicRowsAppendC_Dc Enum.list
  have hl : (Enum.list (α := Fin (setting Dc).E.W)).length = 2 ^ 22 := by rw [len_fin, dcW]
  rw [hl] at hp
  apply (wtKeyDigitsC_of Dc _ _ hp wtTargetC_Dc (wtNatC rQc rB1 _ (by rw [dcW]; norm_num))
    (wtNatC rQk rB1 _ (by rw [dcK]; norm_num))).trans
  norm_num

/-! ### The `u` routine (crude `natC` bounds suffice) -/

theorem wtURowC (K k : ℕ) : codeWeight (uRowC K k) ≤ 9 * K + 3 * k + 100 := by
  have h1 := weight_natC rQc rB1 K
  have h2 := weight_natC rQk rB1 k
  simp only [uRowC, uGadC, uPubC, gadRecC, grBody, autQC, autQBody, ipC, ipBody, codeWeight]
  omega

theorem wtURowsC (K E : ℕ) (e : ℕ → ℕ) : ∀ is : List ℕ, (∀ i ∈ is, e i ≤ E) →
    codeWeight (uRowsC K e is) ≤ is.length * (9 * K + 3 * E + 101) + 1
  | [], _ => by simp [uRowsC, codeWeight]
  | i :: is, h => by
    have hi := (wtURowC K (e i)).trans (by have := h i (by simp); omega :
      9 * K + 3 * e i + 100 ≤ 9 * K + 3 * E + 100)
    have ih := wtURowsC K E e is (fun j hj => h j (by simp [hj]))
    simp only [uRowsC, codeWeight, List.length_cons]
    nlinarith

theorem wtUC_of (D : Dims) (R G : ℕ)
    (hr : codeWeight (uRowsC D.K (rowExponent D)
      (List.ofFn fun i : Fin (setting D).E.W => i.val)) ≤ R)
    (hg : codeWeight (gatherC D.N D.K (bRowIdx D)) ≤ G) :
    codeWeight (uC D) ≤ R + G + 3 * (D.N * D.K) + 3 * bhPrefixLength D +
      3 * (setting D).E.W + 3 * D.K + 300 := by
  have h1 := weight_ringOneC D.N D.K
  have h2 := weight_prefixC (bhPrefixLength D)
  have h3 := weight_natC rQc rB1 (setting D).E.W
  have h4 := weight_natC rQk rB1 D.K
  have hd : codeWeight decRowsC ≤ 100 := by decide
  simp only [uC, bRowC, saveQueueC, codeWeight]
  linarith

theorem wtUC_Dc : codeWeight (uC Dc) ≤ 2 ^ 120 := by
  have hr := wtURowsC Dc.K (2 * Dc.N) (rowExponent Dc)
    (List.ofFn fun i : Fin (setting Dc).E.W => i.val) (fun i _ => (rowExponent_lt Dc i).le)
  have hlen : (List.ofFn fun i : Fin (setting Dc).E.W => i.val).length = 2 ^ 22 := by
    rw [List.length_ofFn, dcW]
  have hg := wtGatherC Dc.N Dc.K (bRowIdx Dc) (by
    intro j hj
    simp only [bRowIdx, List.mem_map, List.mem_ofFn] at hj
    obtain ⟨x, _, rfl⟩ := hj
    exact lt200_of_le66 ((Enum.index_lt x).le.trans publicSizeInputs_Dc.source))
  have hl : (bRowIdx Dc).length = 2 ^ 16 := by
    rw [bRowIdx, List.length_map, List.length_ofFn, dcK]
  have hp : bhPrefixLength Dc ≤ 2 ^ 110 := by
    unfold bhPrefixLength
    rw [dcNK]
    calc _ ≤ 2 ^ 66 * 2 ^ 40 := Nat.mul_le_mul_right _ publicSizeInputs_Dc.source
      _ ≤ 2 ^ 110 := by norm_num
  apply (wtUC_of Dc _ _ hr hg).trans
  rw [hlen, hl, dcNK, dcW, dcK, dcN]
  generalize bhPrefixLength Dc = x at hp ⊢
  linarith

/-! ### The simulated try and the back end -/

theorem wtSimTry_of (D : Dims) (B r Wd Wu Wa : ℕ) (hd : codeWeight (keyDigitsC D) ≤ Wd)
    (hu : codeWeight (uC D) ≤ Wu) (ha : codeWeight (assembleC D) ≤ Wa) :
    codeWeight (simTryKeyC D (uC D) B r) ≤ Wd + Wu + Wa +
      3 * (Enum.list (α := ZIdxS D)).length + 3 * (Enum.list (α := PIdxS D)).length +
      (D.K + 3 * D.N + 3 * B + 3 * (D.K - B) + 3 * (Enum.list (α := PIdxD D)).length +
        3 * codecSize (keyEnc D) + 119) + 200 := by
  have h1 := weight_natC rVm rB1 (Enum.list (α := ZIdxS D)).length
  have h2 := weight_natC rVn rB1 (Enum.list (α := PIdxS D)).length
  have h3 := weight_acceptC D B r
  have hm : codeWeight mvSubC ≤ 100 := by decide
  simp only [simTryKeyC, simProposalKeyC, simProposalC, simCorrectionC, codeWeight]
  linarith

theorem wtRkTryC_of (D : Dims) (B r Wc Wt : ℕ) (hc : codeWeight (candidateC D B) ≤ Wc)
    (ht : codeWeight (simTryKeyC D (uC D) B r) ≤ Wt) : codeWeight (rkTryC D B r) ≤ Wc + Wt := by
  simp only [rkTryC, codeWeight]
  omega

theorem wtCandidateC_le (D : Dims) (B P : ℕ) (hK : D.K ≤ 2 ^ 16) (hN : D.N ≤ 2 ^ 24)
    (hB : B ≤ 2 ^ 16) (hP : nPI D ≤ P) :
    codeWeight (candidateC D B) ≤ 3 * 2 ^ 16 + 3 * 2 ^ 16 + 3 * 2 ^ 24 + 4 * 2 ^ 40 + 3 * P + 120 := by
  have hc := weight_candidateC D B
  have e2 : D.K - B ≤ 2 ^ 16 := (Nat.sub_le _ _).trans hK
  have e3 : D.N * D.K ≤ 2 ^ 24 * 2 ^ 16 := Nat.mul_le_mul hN hK
  linarith

theorem numA : 3 * 2 ^ 16 + 3 * 2 ^ 16 + 3 * 2 ^ 24 + 4 * 2 ^ 40 + 3 * 2 ^ 66 + 120 ≤ 2 ^ 70 := by
  norm_num

theorem wtCandidateC_Dc : codeWeight (candidateC Dc Bk) ≤ 2 ^ 70 :=
  (wtCandidateC_le Dc Bk (2 ^ 66) dcK.le dcN.le (by rw [← dcK]; exact Bk_lt_Kc.le)
    correction_counts_Dc.2.2).trans numA

theorem wtAssembleC_le (D : Dims) (L S : ℕ) (hL : (Enum.list (α := KColt D)).length ≤ L)
    (hS : (Enum.list (α := AssemblySource D)).length ≤ S) (hNK : D.N * D.K ≤ 2 ^ 40) :
    codeWeight (assembleC D) ≤ L * (3 * S * 2 ^ 40 + 6) + 5 :=
  (weight_assembleC D).trans (Nat.add_le_add_right (Nat.mul_le_mul hL (Nat.add_le_add_right
    (Nat.mul_le_mul (Nat.mul_le_mul_left 3 hS) hNK) 6)) 5)

theorem numB : 2 ^ 66 * (3 * 2 ^ 66 * 2 ^ 40 + 6) + 5 ≤ 2 ^ 174 := by norm_num

theorem wtAssembleC_Dc : codeWeight (assembleC Dc) ≤ 2 ^ 174 :=
  (wtAssembleC_le Dc _ _ assembly_lengths_Dc.1 assembly_lengths_Dc.2 dcNK.le).trans numB

theorem wtSimTry_le (D : Dims) (B r Wd Wu Wa Z P P2 C : ℕ) (hd : codeWeight (keyDigitsC D) ≤ Wd)
    (hu : codeWeight (uC D) ≤ Wu) (ha : codeWeight (assembleC D) ≤ Wa)
    (hZ : (Enum.list (α := ZIdxS D)).length ≤ Z) (hP : (Enum.list (α := PIdxS D)).length ≤ P)
    (hP2 : (Enum.list (α := PIdxD D)).length ≤ P2) (hC : codecSize (keyEnc D) ≤ C)
    (hK : D.K ≤ 2 ^ 16) (hN : D.N ≤ 2 ^ 24) (hB : B ≤ 2 ^ 16) :
    codeWeight (simTryKeyC D (uC D) B r) ≤ Wd + Wu + Wa + 3 * Z + 3 * P +
      (2 ^ 16 + 3 * 2 ^ 24 + 3 * 2 ^ 16 + 3 * 2 ^ 16 + 3 * P2 + 3 * C + 119) + 200 := by
  have ht := wtSimTry_of D B r Wd Wu Wa hd hu ha
  have e2 : D.K - B ≤ 2 ^ 16 := (Nat.sub_le _ _).trans hK
  linarith

theorem numC : 2 ^ 100 + 2 ^ 120 + 2 ^ 174 + 3 * 2 ^ 66 + 3 * 2 ^ 66 +
    (2 ^ 16 + 3 * 2 ^ 24 + 3 * 2 ^ 16 + 3 * 2 ^ 16 + 3 * 2 ^ 66 + 3 * 2 ^ 120 + 119) + 200 ≤
    2 ^ 175 := by norm_num

theorem wtSimTry_Dc : codeWeight (simTryKeyC Dc (uC Dc) Bk rSmall) ≤ 2 ^ 175 := by
  have hB : Bk ≤ 2 ^ 16 := by rw [← dcK]; exact Bk_lt_Kc.le
  have hz := correction_counts_Dc.2.1
  have hp := correction_counts_Dc.2.2
  have h := wtSimTry_le Dc Bk rSmall _ _ _ (2 ^ 66) (2 ^ 66) (2 ^ 66) (2 ^ 120) wtKeyDigitsC_Dc
    wtUC_Dc wtAssembleC_Dc hz hp hp keyCodec_bounds_Dc.2.2 dcK.le dcN.le hB
  exact h.trans numC

theorem numD : (2 : ℕ) ^ 70 + 2 ^ 175 ≤ 2 ^ 176 := by norm_num

theorem wtRkTryC_Dc : codeWeight (rkTryC Dc Bk rSmall) ≤ 2 ^ 176 := by
  have h := wtRkTryC_of Dc Bk rSmall _ _ wtCandidateC_Dc wtSimTry_Dc
  exact h.trans numD

theorem numE : 195 * 106 + 1108 + (100000 * 2 ^ 176 + (100000 * 2 + (108000 + 6300 * 2 ^ 40))) ≤
    (2 : ℕ) ^ 195 := by norm_num

/-- **The state count of the back end.** -/
theorem size_rkTailP_Dc : (rkTailP Dc Bk rSmall).size ≤ 2 ^ 195 := by
  have hs := KeyCore.size_sampleP _ 106 KeyCore.keyCoinCount_Dc
  have ht := (size_compile_weight (rkTryC Dc Bk rSmall)).trans
    (Nat.mul_le_mul_left 100000 wtRkTryC_Dc)
  have hp := size_compile_weight packKeyC
  have hpw : codeWeight packKeyC = 2 := rfl
  rw [hpw] at hp
  have he := KeyCore.size_enter_post Dc
  rw [dcNK] at he
  have hpost : (MVM.IO.post).size ≤ 108000 + 6300 * 2 ^ 40 := le_trans (Nat.le_add_left _ _) he
  rw [rkTailP, XProg.size_seq, XProg.size_seq, XProg.size_seq, XProg.size_prog]
  exact (Nat.add_le_add hs (Nat.add_le_add ht (Nat.add_le_add hp hpost))).trans numE

end AdvancedEncryption.ExpLUT.Prog.RedKeyT
