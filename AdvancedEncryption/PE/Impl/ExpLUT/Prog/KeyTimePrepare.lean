import PE.Impl.ExpLUT.Prog.KeyTimeEvalReady
/-! The actual complete KeyGen input loader and public-evaluation preparation. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM

theorem RingInputs.initBits {M N K : ℕ} {a : Fin 105 → ℕ}
    (h : RingInputs M N K a) (hM : 1 ≤ M) : RingInputs M N K (initBitsResult a) := by
  refine ⟨initBits_top M hM a h.top, h.ring, h.dimension, h.width, ?_, ?_, ?_, ?_⟩
  · rw [initBitsResult_low a 35 (by decide)]; exact h.templateK
  · rw [initBitsResult_low a 36 (by decide)]; exact h.templateN
  · rw [initBitsResult_low a 37 (by decide)]; exact h.zeros
  · rw [initBitsResult_low a 38 (by decide)]; exact h.ones

noncomputable def keyInputResult (D : Dims) (M : ℕ) (a : Fin 105 → ℕ) : Fin 105 → ℕ :=
  fieldResult 0 16 (codecSize (matE D (Wb D) (Fin D.K))) M
    (fieldResult 0 17 (codecSize (mpkEnc D)) M (initBitsResult a))

theorem keyInputResult_inputs (D : Dims) (M N K : ℕ) (a : Fin 105 → ℕ)
    (h : RingInputs M N K a) (hM : 1 ≤ M)
    (hp : codecSize (mpkEnc D) ≤ M) (ht : codecSize (matE D (Wb D) (Fin D.K)) ≤ M) :
    RingInputs M N K (keyInputResult D M a) :=
  ((h.initBits hM).field 0 17 _ hp).field 0 16 _ ht

set_option exponentiation.threshold 1000 in
theorem compile_keyInputC_Dc (a : Fin 105 → ℕ) (ha : ∀ t, a t ≤ 2 ^ 120) :
    Cert (MVM.compile (keyInputC Dc)) a (keyInputResult Dc (2 ^ 120) a) (2 ^ 250) := by
  let ai := initBitsResult a
  let ap := fieldResult 0 17 (codecSize (mpkEnc Dc)) (2 ^ 120) ai
  have hi := initBits_top (2 ^ 120) (by norm_num) a ha
  have hbit := (initBits_sources a).2
  have hp := keyCodec_bounds_Dc.1
  have ht := keyCodec_bounds_Dc.2.1
  have hpt := fieldResult_top 0 17 _ (2 ^ 120) ai hi hp
  have hpb : ap (tR rB1) = 1 :=
    (fieldResult_other 0 17 rB1 (codecSize (mpkEnc Dc)) (2 ^ 120) ai
      (by decide) (by decide) (by decide)).trans hbit
  have p0 := compile_clr_cert 6 a (2 ^ 120) ha
  have p1 := compile_bitsC 5 rB1 6 (by decide) (by decide) (by decide) (2 ^ 120)
    (by norm_num) (Function.update a (tR 6) 0)
    (update_top a (2 ^ 120) ha (tR 6) 0 (Nat.zero_le _))
  have p2 := compile_readFieldC 0 17 (by decide) (by decide) 0 (codecSize (mpkEnc Dc))
    (2 ^ 120) ai hi hbit (by omega) hp
  have p3 := compile_readFieldC 0 16 (by decide) (by decide) (codecSize (mpkEnc Dc))
    (codecSize (matE Dc (Wb Dc) (Fin Dc.K))) (2 ^ 120) ap hpt hpb hp ht
  rw [keyInputC]
  apply (p0.seq (p1.seq (p2.seq p3))).mono le_rfl le_rfl
  calc
    _ ≤ (2 * (2 ^ 120 + 1) + 3) +
        (4 * (2 * 2 ^ 120 + 5) +
          ((42 * (0 + 2 ^ 120) + 50) * (2 * 2 ^ 120 + 5) +
            (42 * (2 ^ 120 + 2 ^ 120) + 50) * (2 * 2 ^ 120 + 5))) := by gcongr
    _ ≤ 2 ^ 250 := by norm_num

/-- Only the four physical ring templates are distinguished after complete preparation. -/
def preparedBounds : Fin 105 → ℕ :=
  layout (2 ^ 120) (2 ^ 24) (2 ^ 16) (fun _ ↦ 2 ^ 120)

theorem preparedBounds_inputs : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) preparedBounds :=
  layout_inputs _ _ _ _ (fun _ ↦ le_rfl) (by norm_num) (by norm_num) (by norm_num)

set_option exponentiation.threshold 1000 in
theorem compile_keyEvalPrepareC_Dc (a : Fin 105 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) a) :
    Cert (MVM.compile (keyEvalPrepareC Dc)) a preparedBounds (2 ^ 460) := by
  have p0 := (compile_evalReadyC_Dc a h).mono le_rfl
    (layout_mono _ _ _ evaluatorEnvelope_top) le_rfl
  have p1 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) (fun _ ↦ 2 ^ 120)
    preparedBounds_inputs.top 8 rA le_rfl
  have p2 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) (fun _ ↦ 2 ^ 120)
    preparedBounds_inputs.top 14 17 le_rfl
  rw [keyEvalPrepareC]
  exact (p0.seq (p1.seq p2)).mono le_rfl le_rfl (by norm_num)

set_option exponentiation.threshold 1000 in
/-- Complete actual preparation from the saved MSK and predicate; no small scratch assumption. -/
theorem compile_keyPrepareC_Dc (a : Fin 105 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) a) :
    Cert (MVM.compile (keyPrepareC Dc)) a preparedBounds (2 ^ 461) := by
  have p0 := compile_keyInputC_Dc a h.top
  have hi := keyInputResult_inputs Dc (2 ^ 120) (2 ^ 24) (2 ^ 16) a h (by norm_num)
    keyCodec_bounds_Dc.1 keyCodec_bounds_Dc.2.1
  have p1 := compile_keyEvalPrepareC_Dc _ hi
  rw [keyPrepareC]
  exact (p0.seq p1).mono le_rfl le_rfl (by norm_num)

end AdvancedEncryption.ExpLUT.Prog.KeyTime
