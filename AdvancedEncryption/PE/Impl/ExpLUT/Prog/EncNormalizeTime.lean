import PE.Impl.ExpLUT.Prog.EncInitTime
/-! # Normalization resets conservative parser/sampler bounds before the encryption core -/
namespace AdvancedEncryption.ExpLUT.Prog.EncW
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.Prog
open AdvancedEncryption.ExpLUT.Params

theorem lenBoundT_eraseP (is : List (Fin 326)) (ℓ : Fin 326 → ℕ) (i : Fin 326) :
    lenBoundT (eraseP is) ℓ i = if i ∈ is then 0 else ℓ i := by
  induction is generalizing ℓ with
  | nil => simp only [eraseP, lenBoundT_copy_self, List.not_mem_nil, ↓reduceIte]
  | cons j is ih =>
    simp only [eraseP, lenBoundT_seq_enc, ih]
    by_cases hi : i ∈ is <;> by_cases hj : i = j <;>
      simp [hi, hj, lenBoundT, Prim.lenT]

/-- Exact compiler bounds after normalization, independent of the incoming bounds. -/
theorem lenBoundT_normalizeInputsP (D : Dims) (ℓ : Fin 326 → ℕ) (i : Fin 326) :
    lenBoundT (normalizeInputsP D) ℓ i =
      if i = 321 then coinLength D else if i = 322 then publicLength D else 0 := by
  simp only [normalizeInputsP, lenBoundT_seq_enc, lenBoundT_eraseP, lenBoundT_trimP]
  by_cases h1 : i = 321 <;> by_cases h2 : i = 322 <;>
    simp [inputScratch, h1, h2]

theorem normalize_lengths (ℓ : Fin 326 → ℕ) :
    ∀ i, lenBoundT (normalizeInputsP Dc) ℓ i ≤ 2 ^ 99 := by
  intro i
  rw [lenBoundT_normalizeInputsP]
  split_ifs
  · exact (Nat.le_add_right _ _).trans EncConf.normalization_lengths
  · exact (Nat.le_add_left _ _).trans EncConf.normalization_lengths
  · exact Nat.zero_le _

theorem loopFree_trimP {k : ℕ} (src tmp : Fin k) (n : ℕ) : (trimP src tmp n).LoopFree :=
  ⟨loopFree_putW _ _, trivial, trivial, trivial⟩

theorem pcount_trimP {k : ℕ} (src tmp : Fin k) (n : ℕ) : pcount (trimP src tmp n) = n + 4 := by
  simp only [trimP, pcount, pcount_putW, List.length_replicate]

theorem loopFree_eraseP (is : List (Fin 326)) : (eraseP is).LoopFree := by
  induction is with
  | nil => trivial
  | cons i is ih => exact ⟨trivial, ih⟩

theorem pcount_eraseP (is : List (Fin 326)) : pcount (eraseP is) = is.length + 1 := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [eraseP, pcount, ih, List.length_cons]; omega

theorem pcount_normalizeInputsP : pcount (normalizeInputsP Dc) ≤ 2 ^ 100 := by
  have hl : inputScratch.length ≤ 326 := (List.length_filter_le _ _).trans (by simp)
  have hn := EncConf.normalization_lengths
  simp only [normalizeInputsP, pcount, pcount_trimP, pcount_eraseP]
  omega

set_option exponentiation.threshold 2000 in
/-- Even loose parser bounds cost only a quadratic number of steps to normalize. -/
theorem time_normalizeInputsP {ℓ : Fin 326 → ℕ} (hℓ : ∀ i, ℓ i ≤ 2 ^ 110) :
    timeBoundT (normalizeInputsP Dc) ℓ ≤ 2 ^ 212 := by
  have hf : (normalizeInputsP Dc).LoopFree := ⟨loopFree_trimP _ _ _, loopFree_trimP _ _ _, loopFree_eraseP _⟩
  have h := timeBoundT_le_pcount _ hf ℓ hℓ
  have hn := pcount_normalizeInputsP
  refine h.trans (le_trans (b := 2 ^ 100 * (2 * (2 ^ 110 + 2 ^ 100) + 5))
    (Nat.mul_le_mul hn ?_) ?_)
  · omega
  · norm_num

set_option exponentiation.threshold 2000 in
/-- The production suffix tolerates loose parser/sampler bounds and establishes the core budget. -/
theorem time_encryptionSuffix {ℓ : Fin 326 → ℕ} (hℓ : ∀ i, ℓ i ≤ 2 ^ 110) :
    timeBoundT (.seq relocateP (.seq (normalizeInputsP Dc) (cleanCoreP Dc))) ℓ ≤ 2 ^ 816 ∧
      ∀ i, lenBoundT (.seq relocateP (.seq (normalizeInputsP Dc) (cleanCoreP Dc))) ℓ i ≤ 2 ^ 99 := by
  have h1 : UBP relocateP (2 ^ 110) (2 ^ 115) (2 ^ 110) := fun a ha =>
    ⟨(time_noGrow_le relocateP (by rfl) ha).trans (by norm_num [relocateP, tbC, tbD]),
      Sym.lenBoundT_le_const relocateP (by rfl) ha⟩
  have h2 : UBP (normalizeInputsP Dc) (2 ^ 110) (2 ^ 212) (2 ^ 99) :=
    fun a ha => ⟨time_normalizeInputsP ha, normalize_lengths a⟩
  have h3 : UBP (cleanCoreP Dc) (2 ^ 99) (2 ^ 815) (2 ^ 99) := phase_cleanCoreP
  exact ((h1.seq (h2.seq h3)).mono (by norm_num) le_rfl) ℓ hℓ

end AdvancedEncryption.ExpLUT.Prog.EncW
