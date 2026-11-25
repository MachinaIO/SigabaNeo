import PE.Impl.ExpLUT.Prog.KeyTimeShift
/-! Actual three-source loading for a trapdoor correction coordinate. -/
set_option exponentiation.threshold 1000
set_option maxRecDepth 100000

namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib

theorem index_classical {α : Type} [Enum α] (d : DecidableEq α) (x : α) :
    @Enum.index α _ d x = @Enum.index α _ (Classical.decEq α) x := by
  have he : d = Classical.decEq α := Subsingleton.elim _ _
  rw [he]

open Classical in
noncomputable def correctionLoadResult (D : Dims) (M : ℕ)
    (i : Fin (setting D).E.W) (row : Wb D) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  familyResult M D.N D.K
    [Enum.index (Sum.inl (i, row) : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W)] 9 rIa
    (familyResult M D.N D.K
      ((Enum.list (α := Fin (setting D).τ)).map (fun c ↦ Enum.index (i, c))) 17 rQb
      (familyResult M D.N D.K
        ((Enum.list (α := Fin D.K)).map (fun c ↦ Enum.index (row, c))) 16 rQa b))

theorem compile_correctionLoadC (D : Dims) (M I : ℕ)
    (i : Fin (setting D).E.W) (row : Wb D) (b : Fin 64 → ℕ)
    (h : RingInputs M D.N D.K (layout M D.N D.K b))
    (hb : b rB1 = 1) (hz : b rZ ≤ D.N * D.K)
    (hi : I * (D.N * D.K) ≤ M) (hk : D.K * (D.N * D.K) ≤ M)
    (hT : (Enum.list (α := Wb D × Fin D.K)).length ≤ I)
    (hZ : (Enum.list (α := ZIdx (setting D).τ (setting D).E.W)).length ≤ I)
    (hP : (Enum.list (α := PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W)).length ≤ I) :
    Cert (MVM.compile (correctionLoadC D i row)) (layout M D.N D.K b)
      (layout M D.N D.K (correctionLoadResult D M i row b))
      (3 * (2 * (2 * M + 5)) + 2 * gatherTime M D.N D.K I D.K +
        gatherTime M D.N D.K I 1) := by
  classical
  let : DecidableEq (PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W) := Classical.decEq _
  let ts := (Enum.list (α := Fin D.K)).map (fun c ↦ Enum.index (row, c))
  let zs := (Enum.list (α := Fin (setting D).τ)).map (fun c ↦ Enum.index (i, c))
  let ps := [Enum.index (Sum.inl (i, row) : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W)]
  have htlen : ts.length = D.K := by simp [ts, len_fin]
  have hzlen : zs.length = D.K := by
    change ((List.finRange D.K).map _).length = D.K
    simp
  let c := familyResult M D.N D.K ts 16 rQa b
  let d := familyResult M D.N D.K zs 17 rQb c
  have hts : ts.length * (D.N * D.K) ≤ M := by simpa [htlen] using hk
  have hzs : zs.length * (D.N * D.K) ≤ M := by simpa [hzlen] using hk
  have hps : ps.length * (D.N * D.K) ≤ M := by simpa [ps] using h.ring
  have hc := familyResult_inputs M D.N D.K ts 16 rQa b h hts
  have hd := familyResult_inputs M D.N D.K zs 17 rQb c hc hzs
  have p0 := compile_loadFamilyC M D.N D.K I ts 16 rQa b h hb hz hi
    (by intro j hj; obtain ⟨x, _, rfl⟩ := List.mem_map.mp hj
        exact (Enum.index_lt (row, x)).le.trans hT) hts
  have p1 := compile_loadFamilyC M D.N D.K I zs 17 rQb c hc
    (by simpa [c, familyResult, gatherBase] using hb)
    (by simpa [c, familyResult, gatherBase] using hz) hi
    (by intro j hj; obtain ⟨x, _, rfl⟩ := List.mem_map.mp hj
        exact (Enum.index_lt (i, x)).le.trans hZ) hzs
  have p2 := compile_loadFamilyC M D.N D.K I ps 9 rIa d hd
    (by simpa [d, c, familyResult, gatherBase] using hb)
    (by simpa [d, c, familyResult, gatherBase] using hz) hi
    (by intro j hj; simp only [ps, List.mem_singleton] at hj; subst j
        exact (Enum.index_lt (Sum.inl (i, row) : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W)).le.trans hP) hps
  rw [correctionLoadC]
  have ht : (2 * (2 * M + 5) + gatherTime M D.N D.K I ts.length) +
      ((2 * (2 * M + 5) + gatherTime M D.N D.K I zs.length) +
      (2 * (2 * M + 5) + gatherTime M D.N D.K I ps.length)) ≤
      3 * (2 * (2 * M + 5)) + 2 * gatherTime M D.N D.K I D.K +
        gatherTime M D.N D.K I 1 := by
    rw [htlen, hzlen]; simp only [ps, List.length_singleton]; omega
  simpa only [MVM.compile, ts, zs, ps, c, d, correctionLoadResult, index_classical] using
    (p0.seq (p1.seq p2)).mono le_rfl le_rfl ht

theorem correctionLoadResult_lengths (D : Dims) (M : ℕ)
    (i : Fin (setting D).E.W) (row : Wb D) (b : Fin 64 → ℕ) :
    correctionLoadResult D M i row b rQa = D.K * (D.N * D.K) ∧
    correctionLoadResult D M i row b rQb = D.K * (D.N * D.K) ∧
    correctionLoadResult D M i row b rIa = D.N * D.K := by
  classical
  have hzlen : (Enum.list (α := Fin (setting D).τ)).length = D.K := by
    change (List.finRange D.K).length = D.K
    simp
  have htlen : (Enum.list (α := Fin D.K)).length = D.K := len_fin _
  simp only [correctionLoadResult, familyResult, gatherBase, List.length_map,
    List.length_singleton, htlen, hzlen, Function.update_apply]
  norm_num

theorem correctionLoadResult_inputs (D : Dims) (M : ℕ)
    (i : Fin (setting D).E.W) (row : Wb D) (b : Fin 64 → ℕ)
    (h : RingInputs M D.N D.K (layout M D.N D.K b))
    (hk : D.K * (D.N * D.K) ≤ M) :
    RingInputs M D.N D.K (layout M D.N D.K (correctionLoadResult D M i row b)) := by
  classical
  unfold correctionLoadResult
  apply familyResult_inputs
  · apply familyResult_inputs
    · apply familyResult_inputs _ _ _ _ _ _ _ h
      simpa [len_fin] using hk
    · have hzlen : (Enum.list (α := Fin (setting D).τ)).length = D.K := by
        change (List.finRange D.K).length = D.K
        simp
      simpa only [List.length_map, hzlen] using hk
  · simpa using h.ring

theorem correctionLoadResult_other (D : Dims) (M : ℕ)
    (i : Fin (setting D).E.W) (row : Wb D) (b : Fin 64 → ℕ) (r : Fin 64)
    (hr : r ∉ [0, 1, 2, 3, 4, rQa, rQb, rIa]) :
    correctionLoadResult D M i row b r = b r := by
  classical
  simp only [List.mem_cons, not_or] at hr
  simp [correctionLoadResult, familyResult, gatherBase, Function.update_of_ne, hr.1,
    hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
    hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2]

theorem correctionLoadTime_Dc : 3 * (2 * (2 * 2 ^ 120 + 5)) +
    2 * gatherTime (2 ^ 120) Dc.N Dc.K (2 ^ 66) Dc.K +
    gatherTime (2 ^ 120) Dc.N Dc.K (2 ^ 66) 1 ≤ 2 ^ 318 := by
  rw [show Dc.N = 2 ^ 24 by norm_num [Dc, Dims.N, Params.en],
    show Dc.K = 2 ^ 16 by norm_num [Dc, Params.Kc]]
  norm_num [gatherTime, gatherStepTime, fetchTime, moveAllowance, appendAllowance]

theorem compile_correctionLoadC_Dc (i : Fin (setting Dc).E.W) (row : Wb Dc)
    (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hb : b rB1 = 1) (hz : b rZ ≤ Dc.N * Dc.K) :
    Cert (MVM.compile (correctionLoadC Dc i row)) (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K (correctionLoadResult Dc (2 ^ 120) i row b))
      (2 ^ 318) := by
  have hs := correction_counts_Dc
  have hp := compile_correctionLoadC Dc (2 ^ 120) (2 ^ 66) i row b h hb hz
    (by norm_num [Dc, Dims.N, Params.Kc, Params.en, Params.bc])
    (by norm_num [Dc, Dims.N, Params.Kc, Params.en, Params.bc]) hs.1 hs.2.1 hs.2.2

  exact hp.mono le_rfl le_rfl correctionLoadTime_Dc

end AdvancedEncryption.ExpLUT.Prog.KeyTime
