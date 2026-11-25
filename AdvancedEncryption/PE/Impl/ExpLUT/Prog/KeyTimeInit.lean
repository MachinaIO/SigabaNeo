import PE.Impl.ExpLUT.Prog.KeyTimeTemplates

/-! Runtime of the actual EvalPK constant initialization. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM

theorem update_top (a : Fin 105 → ℕ) (M : ℕ) (ha : ∀ t, a t ≤ M)
    (r : Fin 105) (n : ℕ) (hn : n ≤ M) : ∀ t, Function.update a r n t ≤ M := by
  intro t; by_cases h : t = r <;> simp [h, ha, hn]

def bitsResult (t f : Fin 64) (a : Fin 105 → ℕ) : Fin 105 → ℕ :=
  Function.update (Function.update a (tR t) 1) (tR f) 1

/-- The length certificate does not need semantic equality of the input words. -/
theorem compile_bitsC (t f z : Fin 64) (htf : t ≠ f) (htz : t ≠ z) (hfz : f ≠ z)
    (M : ℕ) (hM : 1 ≤ M) (a : Fin 105 → ℕ) (ha : ∀ j, a j ≤ M) :
    Cert (MVM.compile (bitsC t f z)) a (bitsResult t f a) (4 * (2 * M + 5)) := by
  let a1 := Function.update a (tR t) 0
  let a2 := Function.update a1 (tR f) 0
  let a3 := Function.update a2 (tR t) 1
  have h1 := compile_clr_cert t a M ha
  have hm1 := update_top a M ha (tR t) 0 (Nat.zero_le _)
  have h2 := compile_clr_cert f a1 M hm1
  have hm2 := update_top a1 M hm1 (tR f) 0 (Nat.zero_le _)
  have h3 := compile_eqb_cert t f z (by tauto) a2 M hm2
  have hm3 := update_top a2 M hm2 (tR t) 1 hM
  have h4 := compile_eqb_cert f t z (by tauto) a3 M hm3
  have h := h1.seq (h2.seq (h3.seq h4))
  have he : Function.update a3 (tR f) 1 = bitsResult t f a := by
    funext j
    simp only [a3, a2, a1, bitsResult, Function.update_apply]
    split_ifs <;> rfl
  rw [he] at h
  exact h.mono le_rfl le_rfl (by omega)

def initBitsResult (a : Fin 105 → ℕ) : Fin 105 → ℕ :=
  bitsResult 5 rB1 (Function.update a (tR 6) 0)

theorem initBits_top (M : ℕ) (hM : 1 ≤ M) (a : Fin 105 → ℕ)
    (ha : ∀ j, a j ≤ M) : ∀ j, initBitsResult a j ≤ M :=
  update_top _ M (update_top _ M (update_top _ M ha _ 0 (Nat.zero_le _)) _ 1 hM) _ 1 hM

theorem initBits_sources (a : Fin 105 → ℕ) :
    initBitsResult a (tR 5) = 1 ∧ initBitsResult a (tR rB1) = 1 := by
  simp [initBitsResult, bitsResult, tR, rB1]

/-- The prefix clears its auxiliary register before constructing the two bit constants. -/
theorem compile_initBits (M : ℕ) (hM : 1 ≤ M) (a : Fin 105 → ℕ)
    (ha : ∀ j, a j ≤ M) :
    Cert (MVM.compile (.seq (.clr 6) (bitsC 5 rB1 6))) a (initBitsResult a)
      (5 * (2 * M + 5)) := by
  have h := (compile_clr_cert 6 a M ha).seq
    (compile_bitsC 5 rB1 6 (by decide) (by decide) (by decide) M hM _
      (update_top _ M ha _ 0 (Nat.zero_le _)))
  exact h.mono le_rfl le_rfl (by omega)

theorem template_length_le_weight (w : TemplateWord) : w.value.length ≤ w.weightBound := by
  cases w <;> simp [TemplateWord.value, TemplateWord.weightBound] ; omega

theorem templateTimeWeight_le (ops : List (Fin 64 × TemplateWord)) :
    templateTimeWeight ops ≤ 32 * (ops.map (fun op ↦ op.2.weightBound)).sum + 1 := by
  induction ops with
  | nil => simp [templateTimeWeight]
  | cons op ops ih =>
    rcases op with ⟨r, w⟩
    cases w <;> simp only [templateTimeWeight, TemplateWord.value, TemplateWord.weightBound,
      List.length_replicate, List.map_cons, List.sum_cons] at * <;> omega

theorem evalInitOps_valid (D : Dims) (M : ℕ)
    (hw : ((evalInitOps D).map (fun op ↦ op.2.weightBound)).sum ≤ M) :
    ∀ op ∈ evalInitOps D, op.1 ≠ 5 ∧ op.1 ≠ rB1 ∧ op.2.value.length ≤ M := by
  intro op hop
  have hlen : op.2.value.length ≤ M :=
    (template_length_le_weight op.2).trans
      ((List.single_le_sum (fun x _ ↦ Nat.zero_le x) op.2.weightBound
        (List.mem_map.mpr ⟨op, hop, rfl⟩)).trans hw)
  refine ⟨?_, ?_, hlen⟩ <;> simp only [evalInitOps, List.mem_cons, List.not_mem_nil, or_false] at hop
  all_goals rcases hop with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst op; dsimp only [Prod.fst]; decide

/-- The compiled initializer, including its bit-constant prefix and every template. -/
theorem compile_evalInitC (D : Dims) (M : ℕ) (hM : 1 ≤ M) (a : Fin 105 → ℕ)
    (ha : ∀ j, a j ≤ M)
    (hw : ((evalInitOps D).map (fun op ↦ op.2.weightBound)).sum ≤ M) :
    Cert (MVM.compile (evalInitC D)) a
      (templateBounds M (evalInitOps D) (initBitsResult a))
      ((5 + templateTimeWeight (evalInitOps D)) * (2 * M + 5)) := by
  have hclear := compile_clr_cert 6 a M ha
  have hbits := compile_bitsC 5 rB1 6 (by decide) (by decide) (by decide) M hM _
    (update_top _ M ha (tR 6) 0 (Nat.zero_le _))
  have ht := compile_templateOps (evalInitOps D) M (initBitsResult a)
    (initBits_top M hM a ha) (initBits_sources a).1 (initBits_sources a).2
    (evalInitOps_valid D M hw)
  have h := hclear.seq (hbits.seq ht)
  exact h.mono le_rfl le_rfl (by nlinarith)

theorem templateBounds_top (ops : List (Fin 64 × TemplateWord)) (M : ℕ)
    (a : Fin 105 → ℕ) (ha : ∀ j, a j ≤ M)
    (hl : ∀ op ∈ ops, op.2.value.length ≤ M) : ∀ j, templateBounds M ops a j ≤ M := by
  induction ops generalizing a with
  | nil => exact ha
  | cons op ops ih =>
    exact ih _ (natResult_top op.1 _ M a ha (hl op (by simp)))
      (fun op hop ↦ hl op (by simp [hop]))

/-- The initializer preserves a global tape bound sufficient for subsequent stages. -/
theorem evalInitBounds_top (D : Dims) (M : ℕ) (hM : 1 ≤ M)
    (a : Fin 105 → ℕ) (ha : ∀ j, a j ≤ M)
    (hw : ((evalInitOps D).map (fun op ↦ op.2.weightBound)).sum ≤ M) :
    ∀ j, templateBounds M (evalInitOps D) (initBitsResult a) j ≤ M :=
  templateBounds_top _ M _ (initBits_top M hM a ha)
    (fun op hop ↦ (evalInitOps_valid D M hw op hop).2.2)

/-- Concrete time bound for the entire constant initializer, conditional on input lengths. -/
theorem compile_evalInitC_Dc (a : Fin 105 → ℕ) (ha : ∀ j, a j ≤ 2 ^ 120) :
    Cert (MVM.compile (evalInitC Dc)) a
      (templateBounds (2 ^ 120) (evalInitOps Dc) (initBitsResult a)) (2 ^ 250) := by
  have h := compile_evalInitC Dc (2 ^ 120) (by norm_num) a ha evalInitWeight_Dc
  have hw := templateTimeWeight_le (evalInitOps Dc)
  have he := evalInitWeight_Dc
  apply h.mono le_rfl le_rfl
  calc
    _ ≤ (5 + (32 * 2 ^ 120 + 1)) * (2 * 2 ^ 120 + 5) := by
      apply Nat.mul_le_mul_right
      omega
    _ ≤ 2 ^ 250 := by norm_num

end AdvancedEncryption.ExpLUT.Prog.KeyTime
