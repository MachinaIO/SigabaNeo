import PE.Impl.ExpLUT.Prog.RedKeyC2Eval
import PE.Impl.ExpLUT.Prog.KeyTimePrepare
import PE.Impl.ExpLUT.Prog.RedKeyMidCode

/-!
# Cost certificate of `mid`, phase M2: `m2C = natC 6 rB1 nT ; cp 0 2 ; app 0 6 ; keyPrepareC Dc`

At the tape cap **`2^104`** (`RedKeyC2Eval`): every word of M2 is below `2^99` bits
(`|mpkEnc| ≤ 2^98`, `nT ≤ 2^98`, `c2_codec`).

**`c2_cert_m2C : Cert (compile m2C) (c2In) (layout (2^104) (2^24) (2^16) (fun _ => 2^104)) (2^389)`**,
where the input envelope `c2In = layout (2^104) (2^24) (2^16) c2InB` (`c2InB rB1 = 1`, every other
register `2^104`) holds after `midEnter ; midLdM2` (registers `2 ≤ 2^102`, `rCs ≤ predLen`,
`rB1 = 1`, every other tape a template or blank).

Phases: the msk word (`c2_cert_pre`, `≤ 2^211`), `keyInputC` (`c2_cert_keyInputC`, `≤ 2^212`),
`evalInitC ; evalFieldsC ; evalScratchC` (`≤ 2^216`), `evalC` (`c2_evalC_env`, `≤ 2^388`), the two
result copies.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 2000

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyC

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM
open AdvancedEncryption.ExpLUT.Prog
open AdvancedEncryption.ExpLUT.Prog.KeyTime
open AdvancedEncryption.ExpLUT.Params

/-! ### Sizes -/

theorem c2_codec : codecSize (mpkEnc Dc) ≤ 2 ^ 98 ∧
    codecSize (matE Dc (Wb Dc) (Fin Dc.K)) ≤ 2 ^ 98 := by
  obtain ⟨hp, ht⟩ := keyCodec_lengths Dc
  refine ⟨hp.le.trans ?_, ht.le.trans ?_⟩ <;>
    norm_num [Dc, Kc, mbar, AdvancedEncryption.PE.BranchingProgram.w8, AdvancedEncryption.PE.BranchingProgram.Width.len]

theorem c2_evalInitWeight :
    ((evalInitOps Dc).map (fun op ↦ op.2.weightBound)).sum ≤ 2 ^ 104 := by
  rw [evalInitWeight_eq]
  norm_num [Dc, Kc, gD, SigabaNeo.Lattices.gGen, tlK]

/-- The all-`2^104` layout (templates exact). -/
def c2L : Fin 105 → ℕ := layout (2 ^ 104) (2 ^ 24) (2 ^ 16) (fun _ => 2 ^ 104)

theorem c2L_inputs : RingInputs (2 ^ 104) (2 ^ 24) (2 ^ 16) c2L :=
  layout_inputs _ _ _ _ (fun _ => le_rfl) (by norm_num) (by norm_num) (by norm_num)

/-! ### `keyInputC` -/

theorem c2_cert_keyInputC (a : Fin 105 → ℕ) (ha : ∀ t, a t ≤ 2 ^ 104) :
    Cert (MVM.compile (keyInputC Dc)) a (keyInputResult Dc (2 ^ 104) a) (2 ^ 212) := by
  obtain ⟨hp, ht⟩ := c2_codec
  have hp' : codecSize (mpkEnc Dc) ≤ 2 ^ 104 := hp.trans (by norm_num)
  have ht' : codecSize (matE Dc (Wb Dc) (Fin Dc.K)) ≤ 2 ^ 104 := ht.trans (by norm_num)
  let ai := initBitsResult a
  let ap := fieldResult 0 17 (codecSize (mpkEnc Dc)) (2 ^ 104) ai
  have hi := initBits_top (2 ^ 104) (by norm_num) a ha
  have hbit := (initBits_sources a).2
  have hpt := fieldResult_top 0 17 _ (2 ^ 104) ai hi hp'
  have hpb : ap (tR rB1) = 1 :=
    (fieldResult_other 0 17 rB1 (codecSize (mpkEnc Dc)) (2 ^ 104) ai
      (by decide) (by decide) (by decide)).trans hbit
  have p0 := compile_clr_cert 6 a (2 ^ 104) ha
  have p1 := compile_bitsC 5 rB1 6 (by decide) (by decide) (by decide) (2 ^ 104)
    (by norm_num) (Function.update a (tR 6) 0)
    (update_top a (2 ^ 104) ha (tR 6) 0 (Nat.zero_le _))
  have p2 := compile_readFieldC 0 17 (by decide) (by decide) 0 (codecSize (mpkEnc Dc))
    (2 ^ 104) ai hi hbit (by omega) hp'
  have p3 := compile_readFieldC 0 16 (by decide) (by decide) (codecSize (mpkEnc Dc))
    (codecSize (matE Dc (Wb Dc) (Fin Dc.K))) (2 ^ 104) ap hpt hpb hp' ht'
  rw [keyInputC]
  apply (p0.seq (p1.seq (p2.seq p3))).mono le_rfl le_rfl
  generalize codecSize (mpkEnc Dc) = x at hp p2 p3
  generalize codecSize (matE Dc (Wb Dc) (Fin Dc.K)) = y at ht p3
  calc
    _ ≤ (2 * (2 ^ 104 + 1) + 3) +
        (4 * (2 * 2 ^ 104 + 5) +
          ((42 * (0 + 2 ^ 98) + 50) * (2 * 2 ^ 104 + 5) +
            (42 * (2 ^ 98 + 2 ^ 98) + 50) * (2 * 2 ^ 104 + 5))) := by gcongr
    _ ≤ 2 ^ 212 := by norm_num

/-! ### Initialization, fields, scratch -/

theorem c2_scratchCaps (a : Fin 105 → ℕ)
    (ht : ∀ t, a t ≤ 2 ^ 104) (hl : EvalLengths Dc a) :
    scratchCaps (fun r ↦ a (tR r)) ≤ c2Env := by
  intro r
  fin_cases r <;> simp [scratchCaps, c2Env]
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

theorem c2_cert_scratch (a : Fin 105 → ℕ)
    (h : RingInputs (2 ^ 104) (2 ^ 24) (2 ^ 16) a) (hl : EvalLengths Dc a) :
    Cert (MVM.compile evalScratchC) a
      (layout (2 ^ 104) (2 ^ 24) (2 ^ 16) c2Env) (2 ^ 110) := by
  let b := fun r ↦ a (tR r)
  have hi : RingInputs (2 ^ 104) (2 ^ 24) (2 ^ 16)
      (layout (2 ^ 104) (2 ^ 24) (2 ^ 16) b) :=
    layout_inputs _ _ _ b (fun r ↦ h.top (tR r)) h.ring h.dimension h.width
  have hin := le_layout (2 ^ 104) (2 ^ 24) (2 ^ 16) b a h.top
    h.templateK h.templateN h.zeros.le h.ones (fun _ ↦ le_rfl)
  exact (compile_evalScratchC _ _ _ b hi).mono hin
    (layout_mono _ _ _ (c2_scratchCaps a h.top hl)) (by norm_num)

theorem c2_cert_evalReadyC (a : Fin 105 → ℕ)
    (h : RingInputs (2 ^ 104) (2 ^ 24) (2 ^ 16) a) :
    Cert (MVM.compile (evalReadyC Dc)) a
      (layout (2 ^ 104) (2 ^ 24) (2 ^ 16) c2Env) (2 ^ 389) := by
  let ai := templateBounds (2 ^ 104) (evalInitOps Dc) (initBitsResult a)
  let af := evalFieldsResult Dc (2 ^ 104) ai
  have hi := h.evalInit Dc (by norm_num) c2_evalInitWeight
  have hbit := evalInitBounds_bit Dc (2 ^ 104) a
  have hl := (evalInitBounds_lengths Dc (2 ^ 104) a).evalFields (2 ^ 104)
  have hsize : codecSize (mpkEnc Dc) ≤ 2 ^ 104 := c2_codec.1.trans (by norm_num)
  have hf := hi.evalFields Dc hsize
  have p0 := compile_evalInitC Dc (2 ^ 104) (by norm_num) a h.top c2_evalInitWeight
  have p1 := compile_evalFieldsC Dc (2 ^ 104) ai hi.top hbit hsize
  have p2 := c2_cert_scratch af hf hl
  rw [evalReadyC, evalPublicC]
  apply (p0.seq (p1.seq (p2.seq c2_evalC_env))).mono le_rfl le_rfl
  have hw := (templateTimeWeight_le (evalInitOps Dc)).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 32 c2_evalInitWeight) 1)
  have hp := c2_codec.1
  generalize templateTimeWeight (evalInitOps Dc) = w at hw
  generalize codecSize (mpkEnc Dc) = x at hp
  calc
    _ ≤ (5 + (32 * 2 ^ 104 + 1)) * (2 * 2 ^ 104 + 5) +
        (4 * ((42 * 2 ^ 98 + 50) * (2 * 2 ^ 104 + 5)) + (2 ^ 110 + 2 ^ 388)) := by gcongr
    _ ≤ 2 ^ 389 := by norm_num

theorem c2_cert_keyPrepareC (a : Fin 105 → ℕ)
    (h : RingInputs (2 ^ 104) (2 ^ 24) (2 ^ 16) a) :
    Cert (MVM.compile (keyPrepareC Dc)) a c2L (2 ^ 390) := by
  obtain ⟨hp, ht⟩ := c2_codec
  have p0 := c2_cert_keyInputC a h.top
  have hi := keyInputResult_inputs Dc (2 ^ 104) (2 ^ 24) (2 ^ 16) a h (by norm_num)
    (hp.trans (by norm_num)) (ht.trans (by norm_num))
  have p1 := (c2_cert_evalReadyC _ hi).mono le_rfl (layout_mono _ _ _ c2Env_top) le_rfl
  have p2 := layout_copy (2 ^ 104) (2 ^ 24) (2 ^ 16) (fun _ ↦ 2 ^ 104) c2L_inputs.top 8 rA le_rfl
  have p3 := layout_copy (2 ^ 104) (2 ^ 24) (2 ^ 16) (fun _ ↦ 2 ^ 104) c2L_inputs.top 14 17 le_rfl
  rw [keyPrepareC, keyEvalPrepareC]
  exact (p0.seq (p1.seq (p2.seq p3))).mono le_rfl le_rfl (by norm_num)

/-! ### The msk word and the phase -/

/-- The register caps of the input of M2: `2` is the public-key word, `rB1` the bit `[false]`. -/
def c2InB : Fin 64 → ℕ := Function.update (Function.update (fun _ => 2 ^ 104) 2 (2 ^ 102)) rB1 1

/-- **The input envelope of M2.** -/
def c2In : Fin 105 → ℕ := layout (2 ^ 104) (2 ^ 24) (2 ^ 16) c2InB

theorem c2In_le : c2In ≤ c2L :=
  layout_mono _ _ _ (fun r => by simp only [c2InB, Function.update_apply]; split_ifs <;> norm_num)

theorem c2In_top : ∀ t, c2In t ≤ 2 ^ 104 := fun t => (c2In_le t).trans (c2L_inputs.top t)

theorem c2L_reg (t : Fin 105) (h : t.val = 39 ∨ t.val = 40 ∨ 41 ≤ t.val) : c2L t = 2 ^ 104 := by
  unfold c2L layout
  split_ifs with h1 h2 h3 h4 <;> first | rfl | (subst_vars; simp at h) | omega

/-- The compiler on a sequence (stated for variables, so that no `natC` is ever unfolded). -/
theorem c2_compile_seq (p q : Code) :
    MVM.compile (.seq p q) = .seq (MVM.compile p) (MVM.compile q) := rfl

theorem c2_cert_pre (k : Code) (out : Fin 105 → ℕ) (T : ℕ)
    (hk : Cert (MVM.compile k) c2L out T) :
    Cert (MVM.compile (.seq (natC 6 rB1 RedKeyMid.nT) (.seq (.cp 0 2) (.seq (.app 0 6) k))))
      c2In out (2 ^ 211 + T) := by
  rw [c2_compile_seq, c2_compile_seq, c2_compile_seq]
  have hn : RedKeyMid.nT ≤ 2 ^ 98 := c2_codec.2
  have hu : c2In (tR rB1) = 1 := by simp [c2In, c2InB]
  have p0 := compile_natC 6 rB1 (by decide) RedKeyMid.nT (2 ^ 104) c2In c2In_top hu
    (hn.trans (by norm_num))
  set a1 := natResult 6 RedKeyMid.nT (2 ^ 104) c2In with ha1d
  have ha1 : ∀ t, a1 t ≤ 2 ^ 104 := natResult_top 6 _ _ _ c2In_top (hn.trans (by norm_num))
  have ha1L : a1 ≤ c2L := by
    intro t
    simp only [a1, natResult, Function.update_apply]
    split_ifs with h1 h2 h3
    · rw [h1]; simp [c2L]; omega
    · rw [h2, c2L_reg _ (by simp)]
    · rw [h3, c2L_reg _ (by simp)]
    · exact c2In_le t
  have p1 := compile_cp_any 0 2 a1 (2 ^ 104) ha1
  set a2 := Function.update a1 (tR 0) (a1 (tR 2)) with ha2d
  have e2 : a1 (tR 2) = 2 ^ 102 := by
    rw [ha1d, natResult_register, if_neg (by decide)]
    simp only [c2In, layout_register, c2InB]
    rw [Function.update_of_ne (by decide), Function.update_self]
  have e6 : a2 (tR 6) = RedKeyMid.nT := by
    rw [ha2d, Function.update_of_ne (by decide), ha1d, natResult_dest]
  have e0 : a2 (tR 0) = 2 ^ 102 := by rw [ha2d, Function.update_self, e2]
  have ha2 : ∀ t, a2 t ≤ 2 ^ 104 := update_top a1 _ ha1 (tR 0) _ (by rw [e2]; norm_num)
  have ha2L : a2 ≤ c2L := by
    intro t
    rw [ha2d, Function.update_apply]
    split_ifs with h
    · rw [h, c2L_reg _ (Or.inr (Or.inr (by simp [tR]))), e2]; norm_num
    · exact ha1L t
  have hs : a2 (tR 0) + a2 (tR 6) ≤ 2 ^ 104 := by rw [e0, e6]; omega
  have p2 := compile_app_cert 0 6 (by decide) a2 (2 ^ 104) ha2 hs
  dsimp only at p2
  have p2' := p2.mono le_rfl (b' := c2L) ?_ le_rfl
  · have all := p0.seq (p1.seq (p2'.seq hk))
    refine all.mono le_rfl le_rfl ?_
    rw [e6]
    have h1 : (32 * RedKeyMid.nT + 4) * (2 * 2 ^ 104 + 5) ≤ (32 * 2 ^ 98 + 4) * (2 * 2 ^ 104 + 5) :=
      Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.mul_le_mul_left 32 hn) 4)
    have h2 : (4 * RedKeyMid.nT + 6) * (2 * 2 ^ 104 + 5) ≤ (4 * 2 ^ 98 + 6) * (2 * 2 ^ 104 + 5) :=
      Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hn) 6)
    have h3 : (32 * 2 ^ 98 + 4) * (2 * 2 ^ 104 + 5) + (2 * (2 ^ 104 + 1) + 3) +
        (4 * 2 ^ 98 + 6) * (2 * 2 ^ 104 + 5) ≤ 2 ^ 211 := by norm_num
    calc _ ≤ (32 * 2 ^ 98 + 4) * (2 * 2 ^ 104 + 5) + ((2 * (2 ^ 104 + 1) + 3) +
          ((4 * 2 ^ 98 + 6) * (2 * 2 ^ 104 + 5) + T)) :=
          Nat.add_le_add h1 (Nat.add_le_add_left (Nat.add_le_add_right h2 _) _)
      _ = ((32 * 2 ^ 98 + 4) * (2 * 2 ^ 104 + 5) + (2 * (2 ^ 104 + 1) + 3) +
          (4 * 2 ^ 98 + 6) * (2 * 2 ^ 104 + 5)) + T := by ring
      _ ≤ 2 ^ 211 + T := Nat.add_le_add_right h3 _
  · intro t
    rcases embedF_cases (mkE (fAp 0 6) (fAp_inj (by decide))) a2 _ t with ⟨-, h⟩ | ⟨j, hj, h⟩
    · rw [h]; exact ha2L t
    · rw [h]
      subst hj
      have hv : ∀ j : Fin 4, (fAp 0 6 j).val = 39 ∨ (fAp 0 6 j).val = 40 ∨
          41 ≤ (fAp 0 6 j).val := by decide
      rw [show mkE (fAp 0 6) (fAp_inj (by decide)) j = fAp 0 6 j from rfl, c2L_reg _ (hv j)]
      have he0 : mkE (fAp 0 6) (fAp_inj (by decide)) 0 = tR 0 := Fin.ext (by decide)
      have he1 : mkE (fAp 0 6) (fAp_inj (by decide)) 1 = tR 6 := Fin.ext (by decide)
      have h0 : (a2 ∘ mkE (fAp 0 6) (fAp_inj (by decide))) 0 = 2 ^ 102 := by
        rw [Function.comp_apply, he0, e0]
      have h1 : (a2 ∘ mkE (fAp 0 6) (fAp_inj (by decide))) 1 = RedKeyMid.nT := by
        rw [Function.comp_apply, he1, e6]
      dsimp only
      split_ifs
      · rw [h0, h1]; exact (Nat.add_le_add_left hn _).trans (by norm_num)
      · exact ha2 _
      · exact Nat.zero_le _
      · exact ha2 _

/-- **The certificate of phase M2.** -/
theorem c2_cert_m2C : Cert (MVM.compile RedKeyMid.m2C) c2In c2L (2 ^ 391) := by
  have p := c2_cert_pre _ _ _ (c2_cert_keyPrepareC c2L c2L_inputs)
  rw [RedKeyMid.m2C]
  exact p.mono le_rfl le_rfl (by norm_num)

end AdvancedEncryption.ExpLUT.Prog.RedKeyC
