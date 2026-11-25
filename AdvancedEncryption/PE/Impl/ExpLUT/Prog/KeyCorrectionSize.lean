import PE.Impl.ExpLUT.Prog.KeyGatherSize

/-! State bounds for the complete actual trapdoor-correction traversal. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AdvancedEncryption.ExpLUT.Prog
open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib

theorem weight_loadFamilyC_indices (N K : ℕ) (src dst : Fin 64) (M J : ℕ) (js : List ℕ)
    (hM : js.length ≤ M) (hJ : ∀ j ∈ js, j ≤ J) :
    codeWeight (loadFamilyC N K src dst js) ≤ M * (3 * J * (N * K) + 6) + 4 := by
  have h := (weight_gatherC N K J js hJ).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hM) 2)
  simp only [loadFamilyC, saveQueueC, codeWeight]
  omega

def correctionLoadBudget (D : Dims) (S : ℕ) : ℕ :=
  3 * ((D.K + 1) * (3 * S * (D.N * D.K) + 6) + 4)

theorem weight_correctionLoadC (D : Dims) (S : ℕ)
    (hT : (Enum.list (α := Wb D × Fin D.K)).length ≤ S)
    (hZ : (Enum.list (α := ZIdx (setting D).τ (setting D).E.W)).length ≤ S)
    (hP : (Enum.list (α := PIdxD D)).length ≤ S)
    (i : Fin (setting D).E.W) (row : Wb D) :
    codeWeight (correctionLoadC D i row) ≤ correctionLoadBudget D S := by
  let : DecidableEq (PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W) := Classical.decEq _
  simp only [correctionLoadC, codeWeight, correctionLoadBudget]
  apply le_trans (Nat.add_le_add (weight_loadFamilyC_indices D.N D.K _ _ (D.K + 1) S _ ?_ ?_)
    (Nat.add_le_add (weight_loadFamilyC_indices D.N D.K _ _ (D.K + 1) S _ ?_ ?_)
      (weight_loadFamilyC_indices D.N D.K _ _ (D.K + 1) S _ ?_ ?_)))
  · omega
  · simp [len_fin]
  · intro j hj
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hj
    exact (Enum.index_lt (row, c)).le.trans hT
  · rw [List.length_map]
    change (List.finRange D.K).length ≤ D.K + 1
    simp
  · intro j hj
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hj
    exact (Enum.index_lt (i, c)).le.trans hZ
  · simp
  · intro j hj
    simp only [List.mem_singleton] at hj
    subst j
    exact (Enum.index_lt (Sum.inl (i, row) : PIdx (Wb D) (Jh D) (setting D).τ
      (setting D).E.W)).le.trans hP

def correctionCoordBudget (D : Dims) (S : ℕ) : ℕ :=
  correctionLoadBudget D S + 3 * D.K + 6 * D.N + 100

theorem weight_correctionInlC (D : Dims) (S : ℕ)
    (hT : (Enum.list (α := Wb D × Fin D.K)).length ≤ S)
    (hZ : (Enum.list (α := ZIdx (setting D).τ (setting D).E.W)).length ≤ S)
    (hP : (Enum.list (α := PIdxD D)).length ≤ S)
    (i : Fin (setting D).E.W) (row : Wb D) :
    codeWeight (correctionInlC D i row) ≤ correctionCoordBudget D S := by
  have hl := weight_correctionLoadC D S hT hZ hP i row
  have hk := weight_natC rQc rB1 D.K
  have he := weight_natC rQk rB1 (rowExponent D i.val)
  have hx := rowExponent_lt D i.val
  have ha : codeWeight autDotC ≤ 98 := by decide
  simp only [correctionInlC, codeWeight, correctionCoordBudget]
  omega

theorem weight_correctionCoordC (D : Dims) (S : ℕ)
    (hT : (Enum.list (α := Wb D × Fin D.K)).length ≤ S)
    (hZ : (Enum.list (α := ZIdx (setting D).τ (setting D).E.W)).length ≤ S)
    (hP : (Enum.list (α := PIdxD D)).length ≤ S)
    (q : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W) :
    codeWeight (correctionCoordC D q) ≤ correctionCoordBudget D S := by
  let : DecidableEq (PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W) := Classical.decEq _
  rcases q with ⟨i, row⟩ | q
  · exact weight_correctionInlC D S hT hZ hP i row
  · unfold correctionCoordC
    apply (weight_loadFamilyC_indices D.N D.K _ _ (D.K + 1) S _ (by simp) ?_).trans
    · simp only [correctionCoordBudget, correctionLoadBudget]
      omega
    · intro j hj
      simp only [List.mem_singleton] at hj
      subst j
      exact (Enum.index_lt (Sum.inr q : PIdx (Wb D) (Jh D) (setting D).τ
        (setting D).E.W)).le.trans hP

theorem weight_correctionAppendC (D : Dims) (S : ℕ)
    (hT : (Enum.list (α := Wb D × Fin D.K)).length ≤ S)
    (hZ : (Enum.list (α := ZIdx (setting D).τ (setting D).E.W)).length ≤ S)
    (hP : (Enum.list (α := PIdxD D)).length ≤ S) : ∀ qs,
    codeWeight (correctionAppendC D qs) ≤ qs.length * (correctionCoordBudget D S + 1) + 1
  | [] => by simp [correctionAppendC, codeWeight]
  | q :: qs => by
    have hq := weight_correctionCoordC D S hT hZ hP q
    have ih := weight_correctionAppendC D S hT hZ hP qs
    simp only [correctionAppendC, codeWeight, List.length_cons]
    nlinarith

theorem size_correctionC (D : Dims) (S : ℕ)
    (hT : (Enum.list (α := Wb D × Fin D.K)).length ≤ S)
    (hZ : (Enum.list (α := ZIdx (setting D).τ (setting D).E.W)).length ≤ S)
    (hP : (Enum.list (α := PIdxD D)).length ≤ S) :
    (compile (correctionC D)).size ≤ 100000 * (S * (correctionCoordBudget D S + 1) + 2) := by
  apply (size_compile_weight _).trans
  apply Nat.mul_le_mul_left
  have h := weight_correctionAppendC D S hT hZ hP Enum.list
  have hp := Nat.mul_le_mul_right (correctionCoordBudget D S + 1) hP
  simp only [correctionC, codeWeight]
  omega

open Params

theorem correction_source_lengths (D : Dims) :
    (Enum.list (α := Wb D × Fin D.K)).length = D.mb * D.K ∧
    (Enum.list (α := ZIdx (setting D).τ (setting D).E.W)).length = 2 ^ D.b * D.K ∧
    (Enum.list (α := PIdxD D)).length =
      2 ^ D.b * D.mb + (2 ^ D.b * (D.b * 2 * (2 * D.K)) + 2 * D.K) := by
  change (Enum.list (α := Wb D × Fin D.K)).length = _ ∧
    (Enum.list (α := ZIdx D.K (2 ^ D.b))).length = _ ∧
    (Enum.list (α := PIdx (Wb D) (Jh D) D.K (2 ^ D.b))).length = _
  simp only [ZIdx, PIdx, Wb, Jh, Col, len_sum, Enum.length_prod, len_fin]
  simp

theorem correction_counts_Dc :
    (Enum.list (α := Wb Dc × Fin Dc.K)).length ≤ 2 ^ 66 ∧
    (Enum.list (α := ZIdx (setting Dc).τ (setting Dc).E.W)).length ≤ 2 ^ 66 ∧
    (Enum.list (α := PIdxD Dc)).length ≤ 2 ^ 66 := by
  have h := correction_source_lengths Dc
  refine ⟨h.1.le.trans ?_, h.2.1.le.trans ?_, h.2.2.le.trans ?_⟩ <;>
    norm_num [Dc, Kc, mbar]

end AdvancedEncryption.ExpLUT.Prog
