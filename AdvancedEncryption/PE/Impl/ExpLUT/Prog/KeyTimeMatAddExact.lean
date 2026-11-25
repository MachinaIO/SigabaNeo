import PE.Impl.ExpLUT.Prog.KeyTimeGadget

/-! Asymmetric matrix-add bounds, including initial values in the loop supremum. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM SigabaNeo.Tape.Prog

/-- Copies inside the body establish NK-sized operands even when their old caps are larger. -/
theorem compile_maBody_flexible (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hx0 : N * K ≤ b rX0) (hx1 : N * K ≤ b rX1)
    (hz : b rZ ≤ N * K) (hs : b rAccL + N * K ≤ M) :
    Cert (MVM.compile maBody) (layout M N K b)
      (layout M N K (Function.update b rAccL (b rAccL + N * K))) (matrixAddBodyTime M N K) := by
  let b0 := Function.update b rX0 (N * K)
  let b1 := Function.update b0 rX1 (N * K)
  have hi0 : RingInputs M N K (layout M N K b0) := h.update_layout rX0 _ h.ring
  have hi1 : RingInputs M N K (layout M N K b1) := hi0.update_layout rX1 _ h.ring
  have h1 := layout_copy_cap M N K b h.top rX0 rZ (N * K) hz
  have h2 := layout_moveR M N K b0 hi0 rX0 rRo0 (by decide)
  have h3 := layout_copy_cap M N K b0 hi0.top rX1 rZ (N * K) (by simpa [b0] using hz)
  have h4 := layout_moveR M N K b1 hi1 rX1 rRo1 (by decide)
  have ht : operationBound M N K M ≤ evalInstructionTime M N K := by
    unfold evalInstructionTime; omega
  have h5 := (layout_op M N K b1 hi1 .add rX0 rX0 rX1 (by simp [b1, b0])).mono le_rfl le_rfl ht
  have h6 := layout_append_uniform M N K b1 hi1.top rAccL rX0 (by simpa [b1, b0] using hs)
  have hsmall : b1 ≤ b :=
    (cap_update_le b0 rX1 (N * K) (by simpa [b0] using hx1)).trans (cap_update_le b rX0 _ hx0)
  have hout : layout M N K (Function.update b1 rAccL (b1 rAccL + b1 rX0)) ≤
      layout M N K (Function.update b rAccL (b rAccL + N * K)) := by
    apply layout_mono
    intro r
    by_cases hr : r = rAccL
    · subst r; simp [b1, b0]
    · simpa only [Function.update_of_ne hr] using hsmall r
  exact (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.mono le_rfl hout le_rfl)))))).mono
    le_rfl le_rfl (by unfold matrixAddBodyTime; omega)

theorem compile_maLoop_flexible (M N K R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hx0 : N * K ≤ b rX0) (hx1 : N * K ≤ b rX1)
    (hz : b rZ ≤ N * K) (hc : b rCi ≤ R) (hsize : R * (N * K) ≤ M) :
    Cert (MVM.compile (.rep rCi maBody))
      (layout M N K (Function.update b rAccL 0))
      (layout M N K (Function.update b rAccL (R * (N * K))))
      (R * (2 * M + matrixAddBodyTime M N K + 4) + 2) := by
  let γ := fun j ↦ layout M N K (Function.update b rAccL (j * (N * K)))
  have hi (j : ℕ) (hj : j ≤ R) : RingInputs M N K (γ j) := by
    apply h.update_layout rAccL (j * (N * K))
    exact (Nat.mul_le_mul_right _ hj).trans hsize
  apply rep_family rCi maBody γ R (matrixAddBodyTime M N K) _
    (by simp [γ]) (by simpa using hc)
  · intro j hj
    have hs : (j + 1) * (N * K) ≤ M :=
      (Nat.mul_le_mul_right _ (show j + 1 ≤ R by omega)).trans hsize
    have hb := compile_maBody_flexible M N K (Function.update b rAccL (j * (N * K)))
      (hi j (by omega)) (by simpa using hx0) (by simpa using hx1) (by simpa using hz)
      (by simpa [Nat.add_mul] using hs)
    simp only [Function.update_self, cap_reset] at hb
    have he : j * (N * K) + N * K = (j + 1) * (N * K) := by ring
    rw [he] at hb
    exact hb.mono (tailB_le (tR rCi) _) le_rfl le_rfl
  · intro j hj; exact supB_le_of (hi j (by omega)).top
  · intro j hj
    apply layout_mono
    intro r
    by_cases hr : r = rAccL
    · subst r; simp only [Function.update_self]; exact Nat.mul_le_mul_right _ hj
    · simp [Function.update_of_ne hr]

def matrixAddScratch (N K : ℕ) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (Function.update b rX0 (max (b rX0) (N * K)))
    rX1 (max (b rX1) (N * K))

def matrixAddBase (N K : ℕ) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (Function.update (Function.update (matrixAddScratch N K b)
    rRo0 (b rAccL)) rRo1 (b rMOut)) rCi (b rT4K)

def matrixAddResult (N K R : ℕ) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (matrixAddBase N K b) rAccL (R * (N * K))

theorem matrixAddScratch_inputs (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) :
    RingInputs M N K (layout M N K (matrixAddScratch N K b)) := by
  apply (h.update_layout rX0 (max (b rX0) (N * K))
    (max_le (by simpa using h.top (tR rX0)) h.ring)).update_layout rX1
  exact max_le (by simpa using h.top (tR rX1)) h.ring

theorem matrixAddBase_inputs (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) :
    RingInputs M N K (layout M N K (matrixAddBase N K b)) :=
  (((matrixAddScratch_inputs M N K b h).update_layout rRo0 (b rAccL)
    (by simpa using h.top (tR rAccL))).update_layout rRo1 (b rMOut)
    (by simpa using h.top (tR rMOut))).update_layout rCi (b rT4K)
    (by simpa using h.top (tR rT4K))

/-- The real prefix resets streams, accumulator, and counter; only operand scratch is widened. -/
theorem compile_maPre_exact (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) :
    Cert (MVM.compile maPre) (layout M N K b)
      (layout M N K (Function.update (matrixAddBase N K b) rAccL 0)) (4 * (2 * M + 5)) := by
  let c := matrixAddScratch N K b
  let b0 := Function.update c rRo0 (b rAccL)
  let b1 := Function.update b0 rRo1 (b rMOut)
  let b2 := Function.update b1 rAccL 0
  have hi := matrixAddScratch_inputs M N K b h
  have hi0 : RingInputs M N K (layout M N K b0) := hi.update_layout rRo0 _
    (by simpa using h.top (tR rAccL))
  have hi1 : RingInputs M N K (layout M N K b1) := hi0.update_layout rRo1 _
    (by simpa using h.top (tR rMOut))
  have hi2 : RingInputs M N K (layout M N K b2) := hi1.update_layout rAccL 0 (Nat.zero_le _)
  have h0 : Cert (MVM.compile (.cp rRo0 rAccL)) (layout M N K c) (layout M N K b0)
      (2 * M + 5) := by simpa [c, b0, matrixAddScratch] using layout_copy_update M N K c hi.top rRo0 rAccL
  have h1 : Cert (MVM.compile (.cp rRo1 rMOut)) (layout M N K b0) (layout M N K b1)
      (2 * M + 5) := by simpa [c, b0, b1, matrixAddScratch] using layout_copy_update M N K b0 hi0.top rRo1 rMOut
  have h2 := layout_clear_update M N K b1 hi1.top rAccL
  have h3 := layout_copy_update M N K b2 hi2.top rCi rT4K
  have he : Function.update b2 rCi (b2 rT4K) = Function.update (matrixAddBase N K b) rAccL 0 := by
    funext r
    by_cases ha : r = rAccL <;> by_cases hc : r = rCi <;>
      simp_all [b2, b1, b0, c, matrixAddBase, matrixAddScratch, Function.update_apply]
  rw [he] at h3
  apply (h0.seq (h1.seq (h2.seq h3))).mono _ le_rfl (by omega)
  apply layout_mono
  intro r
  by_cases h0 : r = rX0 <;> by_cases h1 : r = rX1 <;>
    simp_all [c, matrixAddScratch]

/-- The full adder returns exact stream/counter/output caps, with safe loop scratch suprema. -/
theorem compile_matAddC_exact (M N K R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hz : b rZ ≤ N * K)
    (ht : b rT4K ≤ R) (hsize : R * (N * K) ≤ M) :
    Cert (MVM.compile matAddC) (layout M N K b) (layout M N K (matrixAddResult N K R b))
      (4 * (2 * M + 5) + R * (2 * M + matrixAddBodyTime M N K + 4) + 2) := by
  have hi := matrixAddBase_inputs M N K b h
  have hp := compile_maPre_exact M N K b h
  have hl := compile_maLoop_flexible M N K R (matrixAddBase N K b) hi
    (by simp [matrixAddBase, matrixAddScratch]) (by simp [matrixAddBase, matrixAddScratch])
    (by simpa [matrixAddBase, matrixAddScratch] using hz)
    (by simpa [matrixAddBase] using ht) hsize
  exact (hp.seq hl).mono le_rfl le_rfl (by omega)

theorem matrixAddResult_inputs (M N K R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hsize : R * (N * K) ≤ M) :
    RingInputs M N K (layout M N K (matrixAddResult N K R b)) :=
  (matrixAddBase_inputs M N K b h).update_layout rAccL _ hsize

theorem matrixAddResult_fields (N K R : ℕ) (b : Fin 64 → ℕ) :
    matrixAddResult N K R b rX0 = max (b rX0) (N * K) ∧
    matrixAddResult N K R b rX1 = max (b rX1) (N * K) ∧
    matrixAddResult N K R b rRo0 = b rAccL ∧
    matrixAddResult N K R b rRo1 = b rMOut ∧
    matrixAddResult N K R b rCi = b rT4K ∧
    matrixAddResult N K R b rAccL = R * (N * K) := by
  simp [matrixAddResult, matrixAddBase, matrixAddScratch]

theorem matrixAddResult_other (N K R : ℕ) (b : Fin 64 → ℕ) (r : Fin 64)
    (hx0 : r ≠ rX0) (hx1 : r ≠ rX1) (h0 : r ≠ rRo0) (h1 : r ≠ rRo1)
    (hc : r ≠ rCi) (ha : r ≠ rAccL) : matrixAddResult N K R b r = b r := by
  simp [matrixAddResult, matrixAddBase, matrixAddScratch, Function.update_of_ne,
    hx0, hx1, h0, h1, hc, ha]

set_option exponentiation.threshold 1000 in
/-- The concrete bound no longer constrains the old operand, stream, counter, or output caps. -/
theorem compile_matAddC_exact_concrete (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (hz : b rZ ≤ 2 ^ 24 * 2 ^ 16) (ht : b rT4K ≤ 4 * 2 ^ 16) :
    Cert (MVM.compile matAddC) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) (matrixAddResult (2 ^ 24) (2 ^ 16) (4 * 2 ^ 16) b))
      (2 ^ 364) := by
  have hf := compile_matAddC_exact (2 ^ 120) (2 ^ 24) (2 ^ 16) (4 * 2 ^ 16) b h hz ht (by norm_num)
  have hi := evalInstructionTime_concrete
  apply hf.mono le_rfl le_rfl
  unfold matrixAddBodyTime
  calc
    _ ≤ 4 * (2 * 2 ^ 120 + 5) + (4 * 2 ^ 16) * (2 * 2 ^ 120 +
        (2 * (2 * 2 ^ 120 + 5) + 2 * moveAllowance (2 ^ 120) + 2 ^ 341 + appendAllowance (2 ^ 120))
        + 4) + 2 := by gcongr
    _ ≤ 2 ^ 364 := by norm_num [moveAllowance, appendAllowance]

end AdvancedEncryption.ExpLUT.Prog.KeyTime
