import PE.Impl.ExpLUT.Prog.KeyTimeAccept
/-! Candidate certificates that retain the constants needed by the real key attempt. -/
set_option exponentiation.threshold 1000
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM SigabaNeo.Lattices.Algo

theorem candidateInitResult_constants (D : Dims) (B M : ℕ) (a : Fin 105 → ℕ) :
    candidateInitResult D B M a (tR rB1) = 1 ∧
    candidateInitResult D B M a (tR rZ) = D.N * D.K := by
  simp [candidateInitResult, templateBounds, candidateInitOps, TemplateWord.value,
    natResult_register, initBitsResult, bitsResult]

noncomputable def candidateDecoded (a : Fin 105 → ℕ) : Fin 64 → ℕ :=
  Function.update (decodeQueueBase (2 ^ 120)
    (fun r ↦ candidateInitResult Dc Params.Bk (2 ^ 120) a (tR r)))
    rDq (2 ^ 66 * (2 ^ 24 * 2 ^ 16))

noncomputable def candidateResult (a : Fin 105 → ℕ) : Fin 64 → ℕ :=
  Function.update (candidateDecoded a) 9 (2 ^ 66 * (2 ^ 24 * 2 ^ 16))

theorem compile_candidateC_precise (a : Fin 105 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) a) :
    Cert (MVM.compile (candidateC Dc Params.Bk)) a
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) (candidateResult a)) (2 ^ 414) := by
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
  have p0 := compile_candidateInitC_Dc a h.top
  have p1 := (compile_decQC_concrete b hb hk hn hq).mono hin le_rfl le_rfl
  have p2 := layout_copy_update (2 ^ 120) (2 ^ 24) (2 ^ 16) (candidateDecoded a)
    hqb.top 9 rDq
  simp only [candidateDecoded, Function.update_self] at p2
  rw [candidateC]
  exact (p0.seq (p1.seq p2)).mono le_rfl le_rfl (by norm_num)

theorem candidateResult_inputs (a : Fin 105 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) a) :
    RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K (candidateResult a)) := by
  have hi := candidateInitResult_inputs Dc Params.Bk (2 ^ 120) (2 ^ 24) (2 ^ 16)
    a h (by norm_num) candidateInitWeight_Dc
  let b := fun r ↦ candidateInitResult Dc Params.Bk (2 ^ 120) a (tR r)
  have hb := layout_inputs (2 ^ 120) (2 ^ 24) (2 ^ 16) b
    (fun r ↦ hi.top (tR r)) hi.ring hi.dimension hi.width
  have hd := (decodeQueueBase_inputs _ _ _ b hb).update_layout
    rDq (2 ^ 66 * (2 ^ 24 * 2 ^ 16)) (by norm_num)
  have hn : Dc.N = 2 ^ 24 := by norm_num [Dc, Dims.N, Params.en]
  have hk : Dc.K = 2 ^ 16 := by norm_num [Dc, Params.Kc]
  rw [hn, hk]
  exact hd.update_layout 9 _ (by norm_num)

theorem candidateDelivery_constants (M L : ℕ) (b : Fin 64 → ℕ) :
    let c := Function.update (decodeQueueBase M b) rDq L
    let d := Function.update c 9 L
    d rB1 = b rB1 ∧ d rZ = b rZ := by
  simp [decodeQueueBase]

theorem candidateResult_constants (a : Fin 105 → ℕ) :
    candidateResult a rB1 = 1 ∧ candidateResult a rZ = Dc.N * Dc.K := by
  have hd := candidateDelivery_constants (2 ^ 120) (2 ^ 66 * (2 ^ 24 * 2 ^ 16))
    (fun r ↦ candidateInitResult Dc Params.Bk (2 ^ 120) a (tR r))
  have hi := candidateInitResult_constants Dc Params.Bk (2 ^ 120) a
  exact ⟨hd.1.trans hi.1, hd.2.trans hi.2⟩

noncomputable def candidateTryResult (a : Fin 105 → ℕ) := tryKeyResult Params.Bk (candidateResult a)

theorem compile_candidateTryC_Dc (r : ℕ) (a : Fin 105 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) a) :
    Cert (MVM.compile (candidateTryC Dc Params.Bk r)) a
      (layout (2 ^ 120) Dc.N Dc.K (candidateTryResult a)) (2 ^ 501) := by
  have hn : Dc.N = 2 ^ 24 := by norm_num [Dc, Dims.N, Params.en]
  have hk : Dc.K = 2 ^ 16 := by norm_num [Dc, Params.Kc]
  have hf := candidateResult_constants a
  have p0 : Cert (MVM.compile (candidateC Dc Params.Bk)) a
      (layout (2 ^ 120) Dc.N Dc.K (candidateResult a)) (2 ^ 414) := by
    rw [hn, hk]; exact compile_candidateC_precise a h
  have p1 := compile_tryKeyC_Dc Params.Bk r (candidateResult a) (candidateResult_inputs a h)
    hf.1 hf.2.le (by norm_num [Dc, Params.Kc, Params.Bk_def])
  exact (p0.seq p1).mono le_rfl le_rfl (by norm_num)

theorem cert_keyCore_program_Dc (r : ℕ) (a : Fin 105 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) a) :
    Cert (KeyCore.program Dc Params.Bk r) a
      (layout (2 ^ 120) Dc.N Dc.K (candidateTryResult preparedBounds)) (2 ^ 502) := by
  have p0 := compile_keyPrepareC_Dc a h
  have p1 := cert_sampleP _ KeyCore.keyCoinCount_Dc.le
  have p2 := compile_candidateTryC_Dc r preparedBounds preparedBounds_inputs
  exact (p0.seq (p1.seq p2)).mono le_rfl le_rfl (by norm_num)

theorem tryKeyResult_inputs (B : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b)) (hB : B ≤ Dc.K) :
    RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K (tryKeyResult B b)) :=
  acceptResult_inputs B (proposalKeyResult b) (proposalKeyResult_inputs b h) hB

theorem candidateTryResult_inputs (a : Fin 105 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) a) :
    RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K (candidateTryResult a)) :=
  tryKeyResult_inputs Params.Bk (candidateResult a) (candidateResult_inputs a h)
    (by norm_num [Dc, Params.Kc, Params.Bk_def])

end AdvancedEncryption.ExpLUT.Prog.KeyTime
