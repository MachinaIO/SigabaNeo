import PE.Impl.ExpLUT.Prog.KeyTimeDecodeQueue

/-! Actual candidate initialization, decoding and delivery to the proposal register. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM SigabaNeo.Lattices.Algo

noncomputable def candidateInitResult (D : Dims) (B M : ℕ) (a : Fin 105 → ℕ) : Fin 105 → ℕ :=
  templateBounds M (candidateInitOps D B) (initBitsResult a)

theorem candidateInitOps_valid (D : Dims) (B M : ℕ)
    (hw : ((candidateInitOps D B).map (fun op ↦ op.2.weightBound)).sum ≤ M) :
    ∀ op ∈ candidateInitOps D B, op.1 ≠ 5 ∧ op.1 ≠ rB1 ∧ op.2.value.length ≤ M := by
  intro op hop
  have hlen : op.2.value.length ≤ M :=
    (template_length_le_weight op.2).trans
      ((List.single_le_sum (fun x _ ↦ Nat.zero_le x) op.2.weightBound
        (List.mem_map.mpr ⟨op, hop, rfl⟩)).trans hw)
  refine ⟨?_, ?_, hlen⟩ <;> simp only [candidateInitOps, List.mem_cons, List.not_mem_nil, or_false] at hop
  all_goals rcases hop with h | h | h | h | h | h
  all_goals subst op; dsimp only [Prod.fst]; decide

theorem candidateInitWeight (D : Dims) (B : ℕ) :
    ((candidateInitOps D B).map (fun op ↦ op.2.weightBound)).sum =
      3 * B + 3 * (D.K - B) + 3 * D.N + 4 * (D.N * D.K) + 3 * nPI D + 7 := by
  simp [candidateInitOps, TemplateWord.weightBound, length_encRM]
  ring

theorem candidateInitWeight_Dc :
    ((candidateInitOps Dc Params.Bk).map (fun op ↦ op.2.weightBound)).sum ≤ 2 ^ 120 := by
  have hc : nPI Dc ≤ 2 ^ 66 := correction_counts_Dc.2.2
  rw [candidateInitWeight]
  have hK : Dc.K = 2 ^ 16 := by norm_num [Dc, Params.Kc]
  have hN : Dc.N = 2 ^ 24 := rfl
  rw [hK, hN, Params.Bk_def]
  norm_num
  omega

theorem compile_candidateInitC (D : Dims) (B M : ℕ) (a : Fin 105 → ℕ)
    (hM : 1 ≤ M) (ha : ∀ t, a t ≤ M)
    (hw : ((candidateInitOps D B).map (fun op ↦ op.2.weightBound)).sum ≤ M) :
    Cert (MVM.compile (candidateInitC D B)) a (candidateInitResult D B M a)
      ((5 + templateTimeWeight (candidateInitOps D B)) * (2 * M + 5)) := by
  have p0 := compile_clr_cert 6 a M ha
  have p1 := compile_bitsC 5 rB1 6 (by decide) (by decide) (by decide) M hM
    (Function.update a (tR 6) 0) (update_top a M ha (tR 6) 0 (Nat.zero_le _))
  have p2 := compile_templateOps (candidateInitOps D B) M (initBitsResult a)
    (initBits_top M hM a ha) (initBits_sources a).1 (initBits_sources a).2
    (candidateInitOps_valid D B M hw)
  rw [candidateInitC]
  exact (p0.seq (p1.seq p2)).mono le_rfl le_rfl (by nlinarith)

theorem candidateInitResult_inputs (D : Dims) (B M N K : ℕ) (a : Fin 105 → ℕ)
    (h : RingInputs M N K a) (hM : 1 ≤ M)
    (hw : ((candidateInitOps D B).map (fun op ↦ op.2.weightBound)).sum ≤ M) :
    RingInputs M N K (candidateInitResult D B M a) := by
  have ht := templateBounds_top (candidateInitOps D B) M (initBitsResult a)
    (initBits_top M hM a h.top) (fun op hop ↦ (candidateInitOps_valid D B M hw op hop).2.2)
  have he : ∀ j : Fin 105, j.val < 39 → candidateInitResult D B M a j = a j := by
    intro j hj
    rw [candidateInitResult, templateBounds_low _ _ _ j hj, initBitsResult_low _ j hj]
  refine ⟨ht, h.ring, h.dimension, h.width, ?_, ?_, ?_, ?_⟩
  · rw [he 35 (by decide)]; exact h.templateK
  · rw [he 36 (by decide)]; exact h.templateN
  · rw [he 37 (by decide)]; exact h.zeros
  · rw [he 38 (by decide)]; exact h.ones

theorem candidateInitResult_lengths (D : Dims) (B M : ℕ) (a : Fin 105 → ℕ) :
    candidateInitResult D B M a (tR rTBk) = B ∧
    candidateInitResult D B M a (tR rTKmB) = D.K - B ∧
    candidateInitResult D B M a (tR rTN) = D.N ∧
    candidateInitResult D B M a (tR rDqn) = nPI D := by
  simp [candidateInitResult, templateBounds, candidateInitOps, TemplateWord.value, natResult_register]

set_option exponentiation.threshold 1000 in
theorem compile_candidateInitC_Dc (a : Fin 105 → ℕ) (ha : ∀ t, a t ≤ 2 ^ 120) :
    Cert (MVM.compile (candidateInitC Dc Params.Bk)) a
      (candidateInitResult Dc Params.Bk (2 ^ 120) a) (2 ^ 250) := by
  have hp := compile_candidateInitC Dc Params.Bk (2 ^ 120) a (by norm_num) ha candidateInitWeight_Dc
  have ht := templateTimeWeight_le (candidateInitOps Dc Params.Bk)
  have hw := candidateInitWeight_Dc
  apply hp.mono le_rfl le_rfl
  calc
    _ ≤ (5 + (32 * 2 ^ 120 + 1)) * (2 * 2 ^ 120 + 5) := by gcongr; omega
    _ ≤ 2 ^ 250 := by norm_num

set_option exponentiation.threshold 1000 in
/-- Candidate decoding starts from arbitrary bounded scratch and returns a bounded proposal input. -/
theorem compile_candidateC_Dc (a : Fin 105 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) a) :
    Cert (MVM.compile (candidateC Dc Params.Bk)) a preparedBounds (2 ^ 414) := by
  let ai := candidateInitResult Dc Params.Bk (2 ^ 120) a
  let b := fun r ↦ ai (tR r)
  have hi := candidateInitResult_inputs Dc Params.Bk (2 ^ 120) (2 ^ 24) (2 ^ 16)
    a h (by norm_num) candidateInitWeight_Dc
  obtain ⟨hB, hKB, hN, hQ⟩ := candidateInitResult_lengths Dc Params.Bk (2 ^ 120) a
  have hb : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) :=
    layout_inputs _ _ _ b (fun r ↦ hi.top (tR r)) hi.ring hi.dimension hi.width
  have hin := le_layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b ai hi.top
    hi.templateK hi.templateN hi.zeros.le hi.ones (fun _ ↦ le_rfl)
  have hk : b rTBk + b rTKmB ≤ 2 ^ 16 := by
    change ai (tR rTBk) + ai (tR rTKmB) ≤ _
    dsimp only [ai]
    rw [hB, hKB]
    norm_num [Dc, Params.Kc, Params.Bk_def]
  have hn : b rTN ≤ 2 ^ 24 := by change ai (tR rTN) ≤ _; dsimp only [ai]; rw [hN]; rfl
  have hq : b rDqn ≤ 2 ^ 66 := by change ai (tR rDqn) ≤ _; dsimp only [ai]; rw [hQ]; exact correction_counts_Dc.2.2
  have hqb := (decodeQueueBase_inputs (2 ^ 120) (2 ^ 24) (2 ^ 16) b hb).update_layout
    rDq (2 ^ 66 * (2 ^ 24 * 2 ^ 16)) (by norm_num)
  have hout : layout (2 ^ 120) (2 ^ 24) (2 ^ 16)
      (Function.update (decodeQueueBase (2 ^ 120) b) rDq (2 ^ 66 * (2 ^ 24 * 2 ^ 16))) ≤
      preparedBounds := by
    apply layout_mono
    intro r
    simpa only [layout_register] using hqb.top (tR r)
  have p0 := compile_candidateInitC_Dc a h.top
  have p1 := (compile_decQC_concrete b hb hk hn hq).mono hin hout le_rfl
  have p2 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) (fun _ ↦ 2 ^ 120)
    preparedBounds_inputs.top 9 rDq le_rfl
  rw [candidateC]
  exact (p0.seq (p1.seq p2)).mono le_rfl le_rfl (by norm_num)

end AdvancedEncryption.ExpLUT.Prog.KeyTime
