import PE.Impl.ExpLUT.Prog.KeyTimeInit
/-! Full arithmetic certificates accepting the static scratch bounds left by initializers. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM SigabaNeo.Tape.Prog
open SigabaNeo.Tape.Sym Prog.SpecT

/-- Bounds after the first operand load clears its work and helper tapes. -/
def cleanWork (a : Fin 105 → ℕ) : Fin 105 → ℕ :=
  Function.update (Function.update (Function.update a 32 0) 39 0) 40 0

@[simp] theorem cleanWork_register (a : Fin 105 → ℕ) (r : Fin 64) :
    cleanWork a (tR r) = a (tR r) := by
  have h32 : tR r ≠ (32 : Fin 105) := by intro h; have := congrArg Fin.val h; simp [tR] at this; omega
  have h39 : tR r ≠ (39 : Fin 105) := by intro h; have := congrArg Fin.val h; simp [tR] at this; omega
  have h40 : tR r ≠ (40 : Fin 105) := by intro h; have := congrArg Fin.val h; simp [tR] at this; omega
  simp [cleanWork, h32, h39, h40]

theorem cleanWork_top (a : Fin 105 → ℕ) (M : ℕ) (hM : ∀ j, a j ≤ M) :
    ∀ j, cleanWork a j ≤ M :=
  update_top _ M (update_top _ M (update_top _ M hM _ 0 (Nat.zero_le _))
    _ 0 (Nat.zero_le _)) _ 0 (Nat.zero_le _)

/-- Normalize the actual first load to the same intermediate bounds as a clean input. -/
theorem load_scratch_normalized (N K M : ℕ) (s : Fin 64) (a : Fin 105 → ℕ)
    (hM : ∀ j, a j ≤ M) (hz : a 37 = N * K) :
    Cert (.frame (mkE (fLd 33 s) (fLd_inj 33 (Or.inl rfl) s)) (.prog ValVM.inP)) a
      (Function.update (cleanWork a) 33 (N * K))
      ((2 * M + 3) * (30 + 10 * (N * K))) := by
  let e := mkE (fLd 33 s) (fLd_inj 33 (Or.inl rfl) s)
  have h := load_scratch_cert N K M 33 (Or.inl rfl) s a hM hz
  have he : (fun j : Fin 6 ↦ if j = 0 ∨ j = 1 then N * K
      else if j = 2 then a (e 2) else 0) =
      Function.update (Function.update (Function.update (Function.update (a ∘ e) 3 0) 4 0)
        5 0) 0 (N * K) := by
    funext j; fin_cases j <;> simp [e, mkE, fLd, ofV, hz]
  change Cert _ _ (embedF e a _) _ at h
  rw [he, embed_update, embed_update, embed_update, embed_update, embed_original] at h
  exact h

theorem compile_binary_scratch (o : Op) (ho : o = .add ∨ o = .sub ∨ o = .mul)
    (d s t : Fin 64) (M N K : ℕ) (a : Fin 105 → ℕ)
    (hM : ∀ j, a j ≤ M) (hNK : N * K ≤ M) (hN : N ≤ M) (hK : K ≤ M)
    (hk : a 35 ≤ K) (hn : a 36 ≤ N) (hz : a 37 = N * K) (hones : a 38 ≤ N * K) :
    Cert (MVM.compile (.op o d s t)) a (binaryResult M N K d (cleanWork a)) (binaryTime M N K o) := by
  let a1 := Function.update (cleanWork a) (33 : Fin 105) (N * K)
  let a2 := Function.update a1 (34 : Fin 105) (N * K)
  have hM1 : ∀ j, a1 j ≤ M := by
    intro j
    simp only [a1, Function.update_apply]
    split_ifs <;> first | exact hNK | exact cleanWork_top a M hM j
  have hM2 : ∀ j, a2 j ≤ M := by
    intro j
    simp only [a2, Function.update_apply]
    split_ifs <;> first | exact hNK | exact hM1 j
  have hload1 := load_scratch_normalized N K M s a hM hz
  have hload2 := load_cert N K M 34 (Or.inr rfl) t a1 hM1
    (by simpa [a1, cleanWork] using hz) (by simp [a1, cleanWork])
    (by simp [a1, cleanWork]) (by simp [a1, cleanWork])
  have hop := binaryOp_cert o ho M N K a2 hM2 (by simp [a2, a1]) (by simp [a2])
    (by simpa [a2, a1, cleanWork] using hk) (by simpa [a2, a1, cleanWork] using hn)
  have hbM := embed_bound binaryFrame a2 (ringArea M N K (N * K)) M hM2
    (ringArea_bound M N K hNK hN hK)
  obtain ⟨hb0, hb3, hb4, hb38⟩ := binaryAfter_fields M N K a2
  have hcan := canon_cert M N K (binaryAfter M N K a2) hbM hb0.le
    (by rw [hb38]; simpa [a2, a1, cleanWork] using hones) hb3.le hb4.le
  have hcM := embed_bound canonicalFrame (binaryAfter M N K a2)
    (ringArea M N K (N * K)) M hbM (ringArea_bound M N K hNK hN hK)
  have hout := store_cert N K M d (canonicalAfter M N K (binaryAfter M N K a2)) hcM
    (canonicalAfter_result M N K _).le
  have h := hload1.seq (hload2.seq (hop.seq (hcan.seq hout)))
  have he : (2 * M + 3) * (30 + 10 * (N * K)) +
      ((2 * M + 3) * (30 + 10 * (N * K)) +
      ((2 * M + 3) * pEval [M, N, K] (binaryPoly o) +
      ((2 * M + 3) * (7 + 44 * N + 40 * (N * K)) + (2 * M + 3) * 20))) =
        binaryTime M N K o := by unfold binaryTime; ring
  rw [he] at h
  have hbin : o.bin = true := by rcases ho with rfl | rfl | rfl <;> rfl
  simpa only [MVM.compile, t2Of, hbin, ↓reduceIte, binaryResult, a1, a2,
    binaryAfter, canonicalAfter, binaryFrame, canonicalFrame] using h

theorem compile_counted_scratch (o : Op) (ho : o.bin = false)
    (d s c : Fin 64) (M N K : ℕ) (a : Fin 105 → ℕ)
    (hM : ∀ j, a j ≤ M) (hNK : N * K ≤ M) (hN : N ≤ M) (hK : K ≤ M)
    (hk : a 35 ≤ K) (hn : a 36 ≤ N) (hz : a 37 = N * K) (hones : a 38 ≤ N * K) :
    Cert (MVM.compile (.op o d s c)) a (countedResult M N K (a (tR c)) d c (cleanWork a))
      (countedTime M N K (a (tR c)) o) := by
  let a1 := Function.update (cleanWork a) (33 : Fin 105) (N * K)
  let a2 := Function.update a1 (34 : Fin 105) (N * K)
  have hM1 : ∀ j, a1 j ≤ M := by
    intro j
    simp only [a1, Function.update_apply]
    split_ifs <;> first | exact hNK | exact cleanWork_top a M hM j
  have hM2 : ∀ j, a2 j ≤ M := by
    intro j
    simp only [a2, Function.update_apply]
    split_ifs <;> first | exact hNK | exact hM1 j
  have hload1 := load_scratch_normalized N K M s a hM hz
  have hload2 := load_cert N K M 34 (Or.inr rfl) c a1 hM1
    (by simpa [a1, cleanWork] using hz) (by simp [a1, cleanWork])
    (by simp [a1, cleanWork]) (by simp [a1, cleanWork])
  have hc33 : tR c ≠ 33 := by intro he; have hv := congrArg Fin.val he; simp only [tR_val] at hv; omega
  have hc34 : tR c ≠ 34 := by intro he; have hv := congrArg Fin.val he; simp only [tR_val] at hv; omega
  have hop := countedOp_cert o ho c M N K (a (tR c)) a2 hM2 (by simp [a2, a1])
    (by simp [a2, a1, hc33, hc34]) (by simpa [a2, a1, cleanWork] using hk) (by simpa [a2, a1, cleanWork] using hn)
  have hbM := embed_bound (countedFrame c) a2 (countedArea M N K (a (tR c))) M hM2
    (countedArea_bound M N K _ hNK hN hK (hM _))
  obtain ⟨hb0, hb3, hb4, hb38⟩ := countedAfter_fields M N K (a (tR c)) c a2
  have hcan := canon_cert M N K (countedAfter M N K (a (tR c)) c a2) hbM hb0.le
    (by rw [hb38]; simpa [a2, a1, cleanWork] using hones) hb3.le hb4.le
  have hcM := embed_bound canonicalFrame (countedAfter M N K (a (tR c)) c a2)
    (ringArea M N K (N * K)) M hbM (ringArea_bound M N K hNK hN hK)
  have hout := store_cert N K M d (canonicalAfter M N K (countedAfter M N K (a (tR c)) c a2)) hcM
    (canonicalAfter_result M N K _).le
  have h := hload1.seq (hload2.seq (hop.seq (hcan.seq hout)))
  have he : (2 * M + 3) * (30 + 10 * (N * K)) +
      ((2 * M + 3) * (30 + 10 * (N * K)) +
      ((2 * M + 3) * pEval [M, N, K, a (tR c)] (countedPoly o) +
      ((2 * M + 3) * (7 + 44 * N + 40 * (N * K)) + (2 * M + 3) * 20))) =
        countedTime M N K (a (tR c)) o := by unfold countedTime; ring
  rw [he] at h
  simpa only [MVM.compile, t2Of, ho, Bool.false_eq_true, ↓reduceIte, countedResult, a1, a2,
    countedAfter, canonicalAfter, countedFrame, canonicalFrame] using h

/-- Ring-template requirements, allowing arbitrary bounded work and scratch tapes. -/
structure RingInputs (M N K : ℕ) (a : Fin 105 → ℕ) : Prop where
  top : ∀ j, a j ≤ M
  ring : N * K ≤ M
  dimension : N ≤ M
  width : K ≤ M
  templateK : a 35 ≤ K
  templateN : a 36 ≤ N
  zeros : a 37 = N * K
  ones : a 38 ≤ N * K

theorem RingInputs.clean_ready {M N K : ℕ} {a : Fin 105 → ℕ}
    (h : RingInputs M N K a) : Ready M N K (cleanWork a) := by
  refine ⟨cleanWork_top a M h.top, h.ring, h.dimension, h.width, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [cleanWork] using h.templateK
  · simpa [cleanWork] using h.templateN
  · simpa [cleanWork] using h.zeros
  · simpa [cleanWork] using h.ones
  all_goals simp [cleanWork]

/-- All eight instructions accept bounded nonblank scratch and return the same clean invariant. -/
theorem compile_op_scratch (M N K : ℕ) (o : Op) (d s c : Fin 64) (a : Fin 105 → ℕ)
    (h : RingInputs M N K a) :
    Cert (MVM.compile (.op o d s c)) a (operationResult M N K o d c (cleanWork a))
      (operationBound M N K (a (tR c))) := by
  by_cases ho : o.bin = true
  · have hb : o = .add ∨ o = .sub ∨ o = .mul := by cases o <;> simp_all [Op.bin]
    have hh := compile_binary_scratch o hb d s c M N K a h.top h.ring h.dimension h.width
      h.templateK h.templateN h.zeros h.ones
    have ht := (binaryTime_le M N K o).trans
      (operationBound_mono (le_refl M) (le_refl N) (le_refl K) (Nat.zero_le (a (tR c))))
    simpa only [operationResult, ho, ↓reduceIte] using hh.mono le_rfl le_rfl ht
  · have hf : o.bin = false := Bool.eq_false_iff.mpr ho
    have hh := compile_counted_scratch o hf d s c M N K a h.top h.ring h.dimension h.width
      h.templateK h.templateN h.zeros h.ones
    simpa only [operationResult, cleanWork_register, hf, Bool.false_eq_true, ↓reduceIte] using
      hh.mono le_rfl le_rfl (countedTime_le M N K (a (tR c)) o)

theorem compile_op_scratch_ready (M N K : ℕ) (o : Op) (d s c : Fin 64)
    (a : Fin 105 → ℕ) (h : RingInputs M N K a) :
    Cert (MVM.compile (.op o d s c)) a (operationResult M N K o d c (cleanWork a))
      (operationBound M N K (a (tR c))) ∧
      Ready M N K (operationResult M N K o d c (cleanWork a)) :=
  ⟨compile_op_scratch M N K o d s c a h,
    operationResult_ready M N K o d c (cleanWork a) h.clean_ready⟩

/-- Numeric cost, still conditional on the global input and template bounds. -/
theorem compile_op_scratch_concrete (o : Op) (d s c : Fin 64) (a : Fin 105 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) a) :
    Cert (MVM.compile (.op o d s c)) a
      (operationResult (2 ^ 120) (2 ^ 24) (2 ^ 16) o d c (cleanWork a)) (2 ^ 340) :=
  (compile_op_scratch _ _ _ o d s c a h).mono le_rfl le_rfl
    (operationBound_concrete le_rfl (h.top _))

/-- Normalized output length for the destination of any ring operation. -/
theorem operationResult_destination (M N K : ℕ) (o : Op) (d c : Fin 64)
    (a : Fin 105 → ℕ) : operationResult M N K o d c a (tR d) = N * K := by
  unfold operationResult
  split_ifs
  · exact (binaryResult_words M N K d a).1
  · exact (countedResult_words M N K d c a).1

/-- Every other register's upper bound is preserved, including the direct counter. -/
theorem operationResult_other (M N K : ℕ) (o : Op) (d c r : Fin 64)
    (hr : r ≠ d) (a : Fin 105 → ℕ) :
    operationResult M N K o d c a (tR r) = a (tR r) := by
  have hne : tR r ≠ tR d := fun he ↦ hr (tR_inj he)
  have hge : 39 ≤ (tR r).val := by simp [tR]; omega
  unfold operationResult
  split_ifs
  · exact binaryResult_high M N K d a (tR r) hge hne
  · exact countedResult_high M N K d c a (tR r) hge hne

theorem update_register_low (a : Fin 105 → ℕ) (r : Fin 64) (n : ℕ)
    (j : Fin 105) (hj : j.val < 39) : Function.update a (tR r) n j = a j := by
  apply Function.update_of_ne
  intro he
  have hv := congrArg Fin.val he
  simp only [tR_val] at hv
  omega

theorem natResult_low (r : Fin 64) (n M : ℕ) (a : Fin 105 → ℕ)
    (j : Fin 105) (hj : j.val < 39) : natResult r n M a j = a j := by
  have h39 : j ≠ 39 := by intro he; subst j; norm_num at hj
  have h40 : j ≠ 40 := by intro he; subst j; norm_num at hj
  rw [natResult, update_register_low _ _ _ j hj]
  simp [h39, h40]

theorem templateBounds_low (ops : List (Fin 64 × TemplateWord)) (M : ℕ)
    (a : Fin 105 → ℕ) (j : Fin 105) (hj : j.val < 39) :
    templateBounds M ops a j = a j := by
  induction ops generalizing a with
  | nil => rfl
  | cons op ops ih =>
    rw [templateBounds, ih, natResult_low _ _ _ _ j hj]

theorem initBitsResult_low (a : Fin 105 → ℕ) (j : Fin 105) (hj : j.val < 39) :
    initBitsResult a j = a j := by
  simp only [initBitsResult, bitsResult, update_register_low _ _ _ j hj]

/-- Initializing VM registers preserves all four fixed ring-template tapes. -/
theorem RingInputs.evalInit {M N K : ℕ} {a : Fin 105 → ℕ}
    (h : RingInputs M N K a) (D : Dims) (hM : 1 ≤ M)
    (hw : ((evalInitOps D).map (fun op ↦ op.2.weightBound)).sum ≤ M) :
    RingInputs M N K (templateBounds M (evalInitOps D) (initBitsResult a)) := by
  have he : ∀ j : Fin 105, j.val < 39 →
      templateBounds M (evalInitOps D) (initBitsResult a) j = a j := by
    intro j hj; rw [templateBounds_low _ _ _ j hj, initBitsResult_low _ j hj]
  refine ⟨evalInitBounds_top D M hM a h.top hw, h.ring, h.dimension, h.width,
    ?_, ?_, ?_, ?_⟩
  · rw [he 35 (by decide)]; exact h.templateK
  · rw [he 36 (by decide)]; exact h.templateN
  · rw [he 37 (by decide)]; exact h.zeros
  · rw [he 38 (by decide)]; exact h.ones

/-- The actual initializer returns precisely the input invariant accepted by ring instructions. -/
theorem compile_evalInitC_ringInputs (D : Dims) (M N K : ℕ) (hM : 1 ≤ M)
    (a : Fin 105 → ℕ) (h : RingInputs M N K a)
    (hw : ((evalInitOps D).map (fun op ↦ op.2.weightBound)).sum ≤ M) :
    Cert (MVM.compile (evalInitC D)) a
      (templateBounds M (evalInitOps D) (initBitsResult a))
      ((5 + templateTimeWeight (evalInitOps D)) * (2 * M + 5)) ∧
    RingInputs M N K (templateBounds M (evalInitOps D) (initBitsResult a)) :=
  ⟨compile_evalInitC D M hM a h.top hw, h.evalInit D hM hw⟩

end AdvancedEncryption.ExpLUT.Prog.KeyTime
