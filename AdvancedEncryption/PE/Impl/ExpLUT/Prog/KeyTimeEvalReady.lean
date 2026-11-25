import PE.Impl.ExpLUT.Prog.KeyTimeEval

/-! The actual public evaluator enters its runtime envelope after clearing dead scratch. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM

def scratchCaps (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (b) rX0 0) rX1 0) rAc0 0) rAc1 0) rDA 0) rAl 0) rCi 0) rCj 0) rP 0) rPw2 0) rCt 0) rCst 0) rCj2 0

theorem compile_evalScratchC (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) :
    Cert (MVM.compile evalScratchC) (layout M N K b) (layout M N K (scratchCaps b))
      (13 * (2 * M + 5)) := by
  have p0 := layout_clear_update M N K b h.top rX0
  let b1 := Function.update b rX0 0
  have h1 : RingInputs M N K (layout M N K b1) := h.update_layout rX0 0 (Nat.zero_le _)
  have p1 := layout_clear_update M N K b1 h1.top rX1
  let b2 := Function.update b1 rX1 0
  have h2 : RingInputs M N K (layout M N K b2) := h1.update_layout rX1 0 (Nat.zero_le _)
  have p2 := layout_clear_update M N K b2 h2.top rAc0
  let b3 := Function.update b2 rAc0 0
  have h3 : RingInputs M N K (layout M N K b3) := h2.update_layout rAc0 0 (Nat.zero_le _)
  have p3 := layout_clear_update M N K b3 h3.top rAc1
  let b4 := Function.update b3 rAc1 0
  have h4 : RingInputs M N K (layout M N K b4) := h3.update_layout rAc1 0 (Nat.zero_le _)
  have p4 := layout_clear_update M N K b4 h4.top rDA
  let b5 := Function.update b4 rDA 0
  have h5 : RingInputs M N K (layout M N K b5) := h4.update_layout rDA 0 (Nat.zero_le _)
  have p5 := layout_clear_update M N K b5 h5.top rAl
  let b6 := Function.update b5 rAl 0
  have h6 : RingInputs M N K (layout M N K b6) := h5.update_layout rAl 0 (Nat.zero_le _)
  have p6 := layout_clear_update M N K b6 h6.top rCi
  let b7 := Function.update b6 rCi 0
  have h7 : RingInputs M N K (layout M N K b7) := h6.update_layout rCi 0 (Nat.zero_le _)
  have p7 := layout_clear_update M N K b7 h7.top rCj
  let b8 := Function.update b7 rCj 0
  have h8 : RingInputs M N K (layout M N K b8) := h7.update_layout rCj 0 (Nat.zero_le _)
  have p8 := layout_clear_update M N K b8 h8.top rP
  let b9 := Function.update b8 rP 0
  have h9 : RingInputs M N K (layout M N K b9) := h8.update_layout rP 0 (Nat.zero_le _)
  have p9 := layout_clear_update M N K b9 h9.top rPw2
  let b10 := Function.update b9 rPw2 0
  have h10 : RingInputs M N K (layout M N K b10) := h9.update_layout rPw2 0 (Nat.zero_le _)
  have p10 := layout_clear_update M N K b10 h10.top rCt
  let b11 := Function.update b10 rCt 0
  have h11 : RingInputs M N K (layout M N K b11) := h10.update_layout rCt 0 (Nat.zero_le _)
  have p11 := layout_clear_update M N K b11 h11.top rCst
  let b12 := Function.update b11 rCst 0
  have h12 : RingInputs M N K (layout M N K b12) := h11.update_layout rCst 0 (Nat.zero_le _)
  have p12 := layout_clear_update M N K b12 h12.top rCj2
  rw [evalScratchC]
  exact (p0.seq (p1.seq (p2.seq (p3.seq (p4.seq (p5.seq (p6.seq (p7.seq (p8.seq (p9.seq (p10.seq (p11.seq (p12))))))))))))).mono le_rfl le_rfl (by omega)

theorem scratchCaps_le_envelope (a : Fin 105 → ℕ)
    (ht : ∀ t, a t ≤ 2 ^ 120) (hl : EvalLengths Dc a) :
    scratchCaps (fun r ↦ a (tR r)) ≤ evaluatorEnvelope := by
  intro r
  fin_cases r <;> simp [scratchCaps, evaluatorEnvelope]
  all_goals first
    | exact ht _
    | simpa [Dc, Dims.N, Params.Kc, Params.en, Params.bc] using hl.tk.le
    | simpa [Dc, Dims.N, Params.Kc, Params.en, Params.bc] using hl.z.le
    | simpa [Dc, Dims.N, Params.Kc, Params.en, Params.bc] using hl.one.le
    | simpa [Dc, Dims.N, Params.Kc, Params.en, Params.bc] using hl.t4k.le
    | simpa [Dc, Dims.N, Params.Kc, Params.en, Params.bc] using hl.t2k.le
    | simpa [Dc, Dims.N, Params.Kc, Params.en, Params.bc] using hl.tw.le
    | simpa [Dc, Dims.N, Params.Kc, Params.en, Params.bc] using hl.tb.le
    | simpa [Dc, Dims.N, Params.Kc, Params.en, Params.bc] using hl.te.le
    | simpa [Dc, Dims.N, Params.Kc, Params.en, Params.bc] using hl.t15.le
    | simpa [Dc, Dims.N, Params.Kc, Params.en, Params.bc] using hl.bit1.le
    | simpa [Dc, Dims.N, Params.Kc, Params.en, Params.bc] using hl.tknk.le

/-- The clear routine accepts arbitrary old scratch lengths bounded by M. -/
theorem compile_evalScratchC_Dc (a : Fin 105 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) a) (hl : EvalLengths Dc a) :
    Cert (MVM.compile evalScratchC) a
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) evaluatorEnvelope) (2 ^ 130) := by
  let b := fun r ↦ a (tR r)
  have hi : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) :=
    layout_inputs _ _ _ b (fun r ↦ h.top (tR r)) h.ring h.dimension h.width
  have hin := le_layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b a h.top
    h.templateK h.templateN h.zeros.le h.ones (fun _ ↦ le_rfl)
  exact (compile_evalScratchC _ _ _ b hi).mono hin
    (layout_mono _ _ _ (scratchCaps_le_envelope a h.top hl)) (by norm_num)

set_option exponentiation.threshold 1000 in
/-- Complete actual initialization, public loading, scratch normalization and evaluation. -/
theorem compile_evalReadyC_Dc (a : Fin 105 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) a) :
    Cert (MVM.compile (evalReadyC Dc)) a
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) evaluatorEnvelope) (2 ^ 459) := by
  let ai := templateBounds (2 ^ 120) (evalInitOps Dc) (initBitsResult a)
  let af := evalFieldsResult Dc (2 ^ 120) ai
  have hi := h.evalInit Dc (by norm_num) evalInitWeight_Dc
  have hbit := evalInitBounds_bit Dc (2 ^ 120) a
  have hl := (evalInitBounds_lengths Dc (2 ^ 120) a).evalFields (2 ^ 120)
  have hsize : codecSize (mpkEnc Dc) ≤ 2 ^ 120 := keyCodec_bounds_Dc.1
  have hf := hi.evalFields Dc hsize
  have p0 := compile_evalInitC_Dc a h.top
  have p1 := compile_evalFieldsC_Dc ai hi.top hbit
  have p2 := compile_evalScratchC_Dc af hf hl
  rw [evalReadyC, evalPublicC]
  exact (p0.seq (p1.seq (p2.seq compile_evalC_envelope))).mono le_rfl le_rfl (by norm_num)

end AdvancedEncryption.ExpLUT.Prog.KeyTime
