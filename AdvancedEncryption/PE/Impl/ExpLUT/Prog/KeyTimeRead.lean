import PE.Impl.ExpLUT.Prog.KeyTimeMoveScratch
/-! Runtime certificates for actual fixed-field extraction from saved key words. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM

/-- `takeC` initializes its output length from the counter before the counted move. -/
theorem compile_takeC (d s c : Fin 64) (hd : ¬(d = s ∨ d = c ∨ s = c))
    (M : ℕ) (a : Fin 105 → ℕ) (ha : ∀ j, a j ≤ M) :
    Cert (MVM.compile (takeC d s c)) a (Function.update a (tR d) (a (tR c)))
      ((2 * M + 5) + (2 * M + 3) * (20 + 10 * a (tR c))) := by
  have hc := compile_cp_any d c a M ha
  have hm := update_top a M ha (tR d) (a (tR c)) (ha _)
  have hcd : tR c ≠ tR d := fun he ↦ hd (Or.inr (Or.inl (tR_inj he).symm))
  have hv := compile_mv_scratch d s c hd _ M hm
  have h := hc.seq hv
  simpa only [takeC, MVM.compile, Function.update_of_ne hcd, show 2 * (M + 1) + 3 = 2 * M + 5 by omega] using h

def fieldResult (src dst : Fin 64) (len M : ℕ) (a : Fin 105 → ℕ) : Fin 105 → ℕ :=
  Function.update (natResult 30 len M (Function.update a (tR 29) (a (tR src))))
    (tR dst) len

/-- Both unary counters, the skip, and the final copy are charged in the actual program. -/
theorem compile_readFieldC (src dst : Fin 64) (hd29 : dst ≠ 29) (hd30 : dst ≠ 30)
    (off len M : ℕ) (a : Fin 105 → ℕ) (ha : ∀ j, a j ≤ M)
    (hb : a (tR rB1) = 1) (ho : off ≤ M) (hl : len ≤ M) :
    Cert (MVM.compile (readFieldC src dst off len)) a (fieldResult src dst len M a)
      ((42 * (off + len) + 50) * (2 * M + 5)) := by
  let a1 := Function.update a (tR 29) (a (tR src))
  let a2 := natResult 30 off M a1
  let a3 := natResult 30 len M a2
  have h1 := compile_cp_any 29 src a M ha
  have hm1 := update_top a M ha (tR 29) (a (tR src)) (ha _)
  have hb1 : a1 (tR rB1) = 1 := by simpa [a1, rB1, tR] using hb
  have h2 := compile_natC 30 rB1 (by decide) off M a1 hm1 hb1 ho
  have hm2 := natResult_top 30 off M a1 hm1 ho
  have h3 := compile_drop_scratch 29 30 (by decide) a2 M hm2
  have hb2 : a2 (tR rB1) = 1 :=
    (natResult_other 30 rB1 (by decide) off M a1).trans hb1
  have h4 := compile_natC 30 rB1 (by decide) len M a2 hm2 hb2 hl
  have hm3 := natResult_top 30 len M a2 hm2 hl
  have h5 := compile_takeC dst 29 30 (by tauto) M a3 hm3
  have h := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  simp only [a3, a2, natResult_dest, natResult_nested] at h
  exact h.mono le_rfl le_rfl (by nlinarith)

theorem fieldResult_top (src dst : Fin 64) (len M : ℕ) (a : Fin 105 → ℕ)
    (ha : ∀ j, a j ≤ M) (hl : len ≤ M) : ∀ j, fieldResult src dst len M a j ≤ M :=
  update_top _ M (natResult_top 30 len M _ (update_top _ M ha _ _ (ha _)) hl) _ len hl

@[simp] theorem fieldResult_destination (src dst : Fin 64) (len M : ℕ)
    (a : Fin 105 → ℕ) : fieldResult src dst len M a (tR dst) = len := by
  simp [fieldResult]

theorem fieldResult_other (src dst r : Fin 64) (len M : ℕ) (a : Fin 105 → ℕ)
    (hd : r ≠ dst) (h29 : r ≠ 29) (h30 : r ≠ 30) :
    fieldResult src dst len M a (tR r) = a (tR r) := by
  rw [fieldResult, Function.update_of_ne (fun he ↦ hd (tR_inj he)),
    natResult_other 30 r h30,
    Function.update_of_ne (fun he ↦ h29 (tR_inj he))]

theorem fieldResult_low (src dst : Fin 64) (len M : ℕ) (a : Fin 105 → ℕ)
    (j : Fin 105) (hj : j.val < 39) : fieldResult src dst len M a j = a j := by
  rw [fieldResult, update_register_low _ _ _ j hj, natResult_low _ _ _ _ j hj,
    update_register_low _ _ _ j hj]

/-- Key field extraction preserves the invariant needed by subsequent ring operations. -/
theorem RingInputs.field {M N K : ℕ} {a : Fin 105 → ℕ} (h : RingInputs M N K a)
    (src dst : Fin 64) (len : ℕ) (hl : len ≤ M) :
    RingInputs M N K (fieldResult src dst len M a) := by
  refine ⟨fieldResult_top src dst len M a h.top hl, h.ring, h.dimension, h.width,
    ?_, ?_, ?_, ?_⟩
  · rw [fieldResult_low _ _ _ _ _ 35 (by decide)]; exact h.templateK
  · rw [fieldResult_low _ _ _ _ _ 36 (by decide)]; exact h.templateN
  · rw [fieldResult_low _ _ _ _ _ 37 (by decide)]; exact h.zeros
  · rw [fieldResult_low _ _ _ _ _ 38 (by decide)]; exact h.ones

noncomputable def publicReadResult (D : Dims) (dst : Fin 64) (j M : ℕ)
    (a : Fin 105 → ℕ) : Fin 105 → ℕ :=
  fieldResult 17 dst ((publicFieldLengths D).getD j 0) M a

theorem publicField_length_le (D : Dims) (j : ℕ) :
    (publicFieldLengths D).getD j 0 ≤ codecSize (mpkEnc D) := by
  have h := take_sum_add_getD_le_sum (publicFieldLengths D) j
  rw [publicFieldLengths_sum] at h
  omega

theorem compile_readPublicFieldC (D : Dims) (dst : Fin 64)
    (hd29 : dst ≠ 29) (hd30 : dst ≠ 30) (j M : ℕ) (a : Fin 105 → ℕ)
    (ha : ∀ t, a t ≤ M) (hb : a (tR rB1) = 1) (hsize : codecSize (mpkEnc D) ≤ M) :
    Cert (MVM.compile (readPublicFieldC D dst j)) a (publicReadResult D dst j M a)
      ((42 * codecSize (mpkEnc D) + 50) * (2 * M + 5)) := by
  have hl := take_sum_add_getD_le_sum (publicFieldLengths D) j
  rw [publicFieldLengths_sum] at hl
  have h := compile_readFieldC 17 dst hd29 hd30
    ((publicFieldLengths D).take j).sum ((publicFieldLengths D).getD j 0) M a ha hb
    (by omega) (by omega)
  exact h.mono le_rfl le_rfl (by gcongr)

theorem publicReadResult_top (D : Dims) (dst : Fin 64) (j M : ℕ) (a : Fin 105 → ℕ)
    (ha : ∀ t, a t ≤ M) (hsize : codecSize (mpkEnc D) ≤ M) :
    ∀ t, publicReadResult D dst j M a t ≤ M :=
  fieldResult_top _ _ _ _ _ ha ((publicField_length_le D j).trans hsize)

theorem publicReadResult_bit (D : Dims) (dst : Fin 64) (j M : ℕ) (a : Fin 105 → ℕ)
    (hd : rB1 ≠ dst) : publicReadResult D dst j M a (tR rB1) = a (tR rB1) :=
  fieldResult_other 17 dst rB1 _ M a hd (by decide) (by decide)

noncomputable def evalFieldsResult (D : Dims) (M : ℕ) (a : Fin 105 → ℕ) : Fin 105 → ℕ :=
  publicReadResult D 1 5 M (publicReadResult D 0 4 M
    (publicReadResult D 4 3 M (publicReadResult D 2 1 M a)))

/-- All four public fields are extracted by the actual program, including each repeated skip. -/
theorem compile_evalFieldsC (D : Dims) (M : ℕ) (a : Fin 105 → ℕ)
    (ha : ∀ t, a t ≤ M) (hb : a (tR rB1) = 1) (hsize : codecSize (mpkEnc D) ≤ M) :
    Cert (MVM.compile (evalFieldsC D)) a (evalFieldsResult D M a)
      (4 * ((42 * codecSize (mpkEnc D) + 50) * (2 * M + 5))) := by
  let a1 := publicReadResult D 2 1 M a
  let a2 := publicReadResult D 4 3 M a1
  let a3 := publicReadResult D 0 4 M a2
  have hm1 := publicReadResult_top D 2 1 M a ha hsize
  have hb1 : a1 (tR rB1) = 1 := (publicReadResult_bit D 2 1 M a (by decide)).trans hb
  have hm2 := publicReadResult_top D 4 3 M a1 hm1 hsize
  have hb2 : a2 (tR rB1) = 1 := (publicReadResult_bit D 4 3 M a1 (by decide)).trans hb1
  have hm3 := publicReadResult_top D 0 4 M a2 hm2 hsize
  have hb3 : a3 (tR rB1) = 1 := (publicReadResult_bit D 0 4 M a2 (by decide)).trans hb2
  have h1 := compile_readPublicFieldC D 2 (by decide) (by decide) 1 M a ha hb hsize
  have h2 := compile_readPublicFieldC D 4 (by decide) (by decide) 3 M a1 hm1 hb1 hsize
  have h3 := compile_readPublicFieldC D 0 (by decide) (by decide) 4 M a2 hm2 hb2 hsize
  have h4 := compile_readPublicFieldC D 1 (by decide) (by decide) 5 M a3 hm3 hb3 hsize
  exact (h1.seq (h2.seq (h3.seq h4))).mono le_rfl le_rfl (by omega)

theorem RingInputs.evalFields {M N K : ℕ} {a : Fin 105 → ℕ} (h : RingInputs M N K a)
    (D : Dims) (hsize : codecSize (mpkEnc D) ≤ M) :
    RingInputs M N K (evalFieldsResult D M a) :=
  (((h.field 17 2 _ ((publicField_length_le D 1).trans hsize)).field 17 4 _
      ((publicField_length_le D 3).trans hsize)).field 17 0 _
      ((publicField_length_le D 4).trans hsize)).field 17 1 _
      ((publicField_length_le D 5).trans hsize)

/-- Extraction preserves every register outside its four outputs and two counters. -/
theorem evalFieldsResult_other (D : Dims) (M : ℕ) (a : Fin 105 → ℕ) (r : Fin 64)
    (h0 : r ≠ 0) (h1 : r ≠ 1) (h2 : r ≠ 2) (h4 : r ≠ 4)
    (h29 : r ≠ 29) (h30 : r ≠ 30) : evalFieldsResult D M a (tR r) = a (tR r) := by
  simp only [evalFieldsResult, publicReadResult,
    fieldResult_other _ 1 r _ _ _ h1 h29 h30,
    fieldResult_other _ 0 r _ _ _ h0 h29 h30,
    fieldResult_other _ 4 r _ _ _ h4 h29 h30,
    fieldResult_other _ 2 r _ _ _ h2 h29 h30]

theorem evalFieldsResult_outputs (D : Dims) (M : ℕ) (a : Fin 105 → ℕ) :
    evalFieldsResult D M a (tR 2) = (publicFieldLengths D).getD 1 0 ∧
    evalFieldsResult D M a (tR 4) = (publicFieldLengths D).getD 3 0 ∧
    evalFieldsResult D M a (tR 0) = (publicFieldLengths D).getD 4 0 ∧
    evalFieldsResult D M a (tR 1) = (publicFieldLengths D).getD 5 0 := by
  simp [evalFieldsResult, publicReadResult, fieldResult, natResult, tR]

/-- Conditional scalar time bound for the actual four-field loader. -/
theorem compile_evalFieldsC_Dc (a : Fin 105 → ℕ) (ha : ∀ t, a t ≤ 2 ^ 120)
    (hb : a (tR rB1) = 1) :
    Cert (MVM.compile (evalFieldsC Dc)) a (evalFieldsResult Dc (2 ^ 120) a) (2 ^ 250) := by
  have hs := keyCodec_bounds_Dc.1
  have h := compile_evalFieldsC Dc (2 ^ 120) a ha hb hs
  apply h.mono le_rfl le_rfl
  calc
    _ ≤ 4 * ((42 * 2 ^ 120 + 50) * (2 * 2 ^ 120 + 5)) := by gcongr
    _ ≤ 2 ^ 250 := by norm_num

end AdvancedEncryption.ExpLUT.Prog.KeyTime
