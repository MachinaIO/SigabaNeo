import PE.Impl.ExpLUT.Prog.KeyTimeCorrectionLoad
/-! Runtime of a complete actual trapdoor-coordinate correction. -/
set_option exponentiation.threshold 1000
set_option maxRecDepth 4000

namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib

noncomputable def correctionReady (D : Dims) (M : ℕ)
    (i : Fin (setting D).E.W) (row : Wb D) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (Function.update (correctionLoadResult D M i row b) rQc D.K)
    rQk (rowExponent D i.val)

noncomputable def correctionInlResult (D : Dims) (M : ℕ)
    (i : Fin (setting D).E.W) (row : Wb D) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  autDotResult D.N D.K D.K (correctionReady D M i row b)

def correctionInlTime (D : Dims) (M I e : ℕ) :=
  3 * (2 * (2 * M + 5)) + 2 * gatherTime M D.N D.K I D.K +
    gatherTime M D.N D.K I 1 +
    ((32 * D.K + 4) * (2 * M + 5) +
    ((32 * e + 4) * (2 * M + 5) + autDotTime M D.N D.K D.K))

theorem compile_correctionInlC (D : Dims) (M I : ℕ)
    (i : Fin (setting D).E.W) (row : Wb D) (b : Fin 64 → ℕ)
    (h : RingInputs M D.N D.K (layout M D.N D.K b))
    (hb : b rB1 = 1) (hz : b rZ ≤ D.N * D.K)
    (hx : D.N * D.K ≤ b rQx) (hy : D.N * D.K ≤ b rQy)
    (hi : I * (D.N * D.K) ≤ M) (hk : 2 * (D.K * (D.N * D.K)) ≤ M)
    (he : rowExponent D i.val ≤ M)
    (hT : (Enum.list (α := Wb D × Fin D.K)).length ≤ I)
    (hZ : (Enum.list (α := ZIdx (setting D).τ (setting D).E.W)).length ≤ I)
    (hP : (Enum.list (α := PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W)).length ≤ I) :
    Cert (MVM.compile (correctionInlC D i row)) (layout M D.N D.K b)
      (layout M D.N D.K (correctionInlResult D M i row b))
      (correctionInlTime D M I (rowExponent D i.val)) := by
  let c := correctionLoadResult D M i row b
  let d := Function.update c rQc D.K
  let e := correctionReady D M i row b
  have hc := correctionLoadResult_inputs D M i row b h (by omega)
  have hd := hc.update_layout rQc D.K h.width
  have he' := hd.update_layout rQk (rowExponent D i.val) he
  have hcB : c rB1 = 1 := (correctionLoadResult_other D M i row b rB1 (by decide)).trans hb
  have keep (r : Fin 64) (hr : r ∉ [0, 1, 2, 3, 4, rQa, rQb, rIa, rQc, rQk]) :
      e r = b r := by
    have hrc : r ≠ rQc := by simpa only [List.mem_cons, List.mem_singleton] using
      (show r ≠ rQc from fun heq ↦ hr (by simp [heq]))
    have hrk : r ≠ rQk := fun heq ↦ hr (by simp [heq])
    simp only [e, correctionReady, Function.update_of_ne hrc, Function.update_of_ne hrk]
    apply correctionLoadResult_other
    intro hm; apply hr
    simp only [List.mem_cons] at hm ⊢
    tauto
  have lengths := correctionLoadResult_lengths D M i row b
  have caps : QueueArithmeticCaps D.N D.K e := by
    constructor
    · rw [keep rQx (by decide)]; exact hx
    · rw [keep rQy (by decide)]; exact hy
    · simp only [e, correctionReady, Function.update_of_ne (show rIa ≠ rQk by decide),
        Function.update_of_ne (show rIa ≠ rQc by decide)]
      exact lengths.2.2.ge
    · rw [keep rZ (by decide), keep rQx (by decide)]; exact hz.trans hx
    · rw [keep rZ (by decide), keep rQy (by decide)]; exact hz.trans hy
  have p0 := compile_correctionLoadC D M I i row b h hb hz hi (by omega) hT hZ hP
  have p1 := layout_nat_update M D.N D.K c hc rQc rB1 (by decide) D.K hcB h.width
  have p2 := layout_nat_update M D.N D.K d hd rQk rB1 (by decide) (rowExponent D i.val)
    (by simpa [d] using hcB) he
  have p3 := compile_autDotC M D.N D.K D.K e he' caps
    (by simp [e, correctionReady]) (by
      simp only [e, correctionReady, Function.update_of_ne (show rQa ≠ rQk by decide),
        Function.update_of_ne (show rQa ≠ rQc by decide), lengths.1]
      omega)
  rw [correctionInlC]
  exact p0.seq (p1.seq (p2.seq p3))

theorem correctionInlResult_acc (D : Dims) (M : ℕ)
    (i : Fin (setting D).E.W) (row : Wb D) (b : Fin 64 → ℕ) :
    correctionInlResult D M i row b rIa = D.N * D.K := by
  simpa [correctionInlResult, autDotResult, correctionReady] using
    (correctionLoadResult_lengths D M i row b).2.2

set_option exponentiation.threshold 1000 in
theorem correctionInlTime_Dc (i : Fin (setting Dc).E.W) :
    correctionInlTime Dc (2 ^ 120) (2 ^ 66) (rowExponent Dc i.val) ≤ 2 ^ 416 := by
  have hl := correctionLoadTime_Dc
  have he := (rowExponent_lt Dc i.val).le
  have hn : Dc.N = 2 ^ 24 := by norm_num [Dc, Dims.N, Params.en]
  have hk : Dc.K = 2 ^ 16 := by norm_num [Dc, Params.Kc]
  have hd : autDotTime (2 ^ 120) Dc.N Dc.K Dc.K ≤ 2 ^ 414 := by
    rw [hn, hk]
    apply le_trans _ autDotTime_concrete
    unfold autDotTime autQueueTime innerProductTime
    gcongr <;> norm_num
  unfold correctionInlTime
  calc
    _ ≤ 2 ^ 318 + ((32 * Dc.K + 4) * (2 * 2 ^ 120 + 5) +
        ((32 * (2 * Dc.N) + 4) * (2 * 2 ^ 120 + 5) + 2 ^ 414)) := by gcongr
    _ ≤ 2 ^ 416 := by rw [hn, hk]; norm_num

theorem compile_correctionInlC_Dc (i : Fin (setting Dc).E.W) (row : Wb Dc)
    (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hb : b rB1 = 1) (hz : b rZ ≤ Dc.N * Dc.K)
    (hx : Dc.N * Dc.K ≤ b rQx) (hy : Dc.N * Dc.K ≤ b rQy) :
    Cert (MVM.compile (correctionInlC Dc i row)) (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K (correctionInlResult Dc (2 ^ 120) i row b))
      (2 ^ 416) := by
  have hs := correction_counts_Dc
  have he : rowExponent Dc i.val ≤ 2 ^ 120 := (rowExponent_lt Dc i.val).le.trans
    (by norm_num [Dc, Dims.N, Params.en])
  exact (compile_correctionInlC Dc (2 ^ 120) (2 ^ 66) i row b h hb hz hx hy
    (by norm_num [Dc, Dims.N, Params.en, Params.Kc])
    (by norm_num [Dc, Dims.N, Params.en, Params.Kc]) he hs.1 hs.2.1 hs.2.2).mono
      le_rfl le_rfl (correctionInlTime_Dc i)

theorem correctionInlResult_inputs (D : Dims) (M : ℕ)
    (i : Fin (setting D).E.W) (row : Wb D) (b : Fin 64 → ℕ)
    (h : RingInputs M D.N D.K (layout M D.N D.K b))
    (hk : 2 * (D.K * (D.N * D.K)) ≤ M) (he : rowExponent D i.val ≤ M) :
    RingInputs M D.N D.K (layout M D.N D.K (correctionInlResult D M i row b)) := by
  have hc := correctionLoadResult_inputs D M i row b h (by omega)
  have hd := (hc.update_layout rQc D.K h.width).update_layout rQk _ he
  have hf := hd.update_layout 56 D.K h.width
  have hl := (correctionLoadResult_lengths D M i row b).1
  unfold correctionInlResult autDotResult
  apply hf.update_layout rQa
  simpa [correctionReady, hl, two_mul] using hk

theorem correctionInlResult_other (D : Dims) (M : ℕ)
    (i : Fin (setting D).E.W) (row : Wb D) (b : Fin 64 → ℕ) (r : Fin 64)
    (hr : r ∉ [0, 1, 2, 3, 4, rQa, rQb, rIa, rQc, rQk, 56]) :
    correctionInlResult D M i row b r = b r := by
  have hn (s : Fin 64) (hs : s ∈ [0, 1, 2, 3, 4, rQa, rQb, rIa, rQc, rQk, 56]) :
      r ≠ s := fun he ↦ hr (he.symm ▸ hs)
  simp only [correctionInlResult, autDotResult, correctionReady,
    Function.update_of_ne (hn rQa (by simp)), Function.update_of_ne (hn 56 (by simp)),
    Function.update_of_ne (hn rQc (by simp)), Function.update_of_ne (hn rQk (by simp))]
  apply correctionLoadResult_other
  intro hm; apply hr
  simp only [List.mem_cons] at hm ⊢
  tauto

open Classical in
noncomputable def correctionCoordResult (D : Dims) (M : ℕ)
    (q : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  match q with
  | .inl (i, row) => correctionInlResult D M i row b
  | .inr q => familyResult M D.N D.K
      [Enum.index (.inr q : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W)] 9 rIa b

theorem compile_correctionCoordC_Dc
    (q : PIdx (Wb Dc) (Jh Dc) (setting Dc).τ (setting Dc).E.W) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hb : b rB1 = 1) (hz : b rZ ≤ Dc.N * Dc.K)
    (hx : Dc.N * Dc.K ≤ b rQx) (hy : Dc.N * Dc.K ≤ b rQy) :
    Cert (MVM.compile (correctionCoordC Dc q)) (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K (correctionCoordResult Dc (2 ^ 120) q b))
      (2 ^ 416) := by
  classical
  let : DecidableEq (PIdx (Wb Dc) (Jh Dc) (setting Dc).τ (setting Dc).E.W) := Classical.decEq _
  rcases q with ⟨i, row⟩ | q
  · exact compile_correctionInlC_Dc i row b h hb hz hx hy
  · let js := [Enum.index (.inr q : PIdx (Wb Dc) (Jh Dc) (setting Dc).τ (setting Dc).E.W)]
    have hp := compile_loadFamilyC (2 ^ 120) Dc.N Dc.K (2 ^ 66) js 9 rIa b h hb hz
      (by norm_num [Dc, Dims.N, Params.en, Params.Kc])
      (by intro j hj; simp only [js, List.mem_singleton] at hj; subst j
          exact (Enum.index_lt _).le.trans correction_counts_Dc.2.2)
      (by simpa [js] using h.ring)
    have ht : 2 * (2 * 2 ^ 120 + 5) + gatherTime (2 ^ 120) Dc.N Dc.K (2 ^ 66) 1 ≤ 2 ^ 416 := by
      have hl := correctionLoadTime_Dc
      have hnum : 2 ^ 318 ≤ (2 ^ 416 : ℕ) := by norm_num
      omega
    have ht' : 2 * (2 * 2 ^ 120 + 5) +
        gatherTime (2 ^ 120) Dc.N Dc.K (2 ^ 66) js.length ≤ 2 ^ 416 := by
      simpa only [js, List.length_singleton] using ht
    simpa only [correctionCoordC, correctionCoordResult, js, index_classical] using
      hp.mono le_rfl le_rfl ht'

theorem correctionCoordResult_acc (D : Dims) (M : ℕ)
    (q : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W) (b : Fin 64 → ℕ) :
    correctionCoordResult D M q b rIa = D.N * D.K := by
  rcases q with ⟨i, row⟩ | q
  · exact correctionInlResult_acc D M i row b
  · simp [correctionCoordResult]

theorem correctionCoordResult_inputs (D : Dims) (M : ℕ)
    (q : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W) (b : Fin 64 → ℕ)
    (h : RingInputs M D.N D.K (layout M D.N D.K b))
    (hk : 2 * (D.K * (D.N * D.K)) ≤ M) (he : 2 * D.N ≤ M) :
    RingInputs M D.N D.K (layout M D.N D.K (correctionCoordResult D M q b)) := by
  rcases q with ⟨i, row⟩ | q
  · exact correctionInlResult_inputs D M i row b h hk ((rowExponent_lt D i.val).le.trans he)
  · apply familyResult_inputs _ _ _ _ _ _ _ h
    simpa using h.ring

theorem correctionCoordResult_other (D : Dims) (M : ℕ)
    (q : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W) (b : Fin 64 → ℕ) (r : Fin 64)
    (hr : r ∉ [0, 1, 2, 3, 4, rQa, rQb, rIa, rQc, rQk, 56]) :
    correctionCoordResult D M q b r = b r := by
  rcases q with ⟨i, row⟩ | q
  · exact correctionInlResult_other D M i row b r hr
  · have hn (s : Fin 64) (hs : s ∈ [0, 1, 2, 3, 4, rQa, rQb, rIa, rQc, rQk, 56]) :
        r ≠ s := fun he ↦ hr (he.symm ▸ hs)
    simp only [correctionCoordResult, familyResult, gatherBase,
      Function.update_of_ne (hn rIa (by simp)), Function.update_of_ne (hn 0 (by simp)),
      Function.update_of_ne (hn 1 (by simp)), Function.update_of_ne (hn 2 (by simp)),
      Function.update_of_ne (hn 3 (by simp)), Function.update_of_ne (hn 4 (by simp))]

end AdvancedEncryption.ExpLUT.Prog.KeyTime
