import PE.Impl.ExpLUT.Prog.KeyTimeMatrixGrowth
/-! Linear output growth in the actual entrywise matrix-adder. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM SigabaNeo.Tape.Prog

def moveAllowance (M : ℕ) : ℕ := (2 * M + 3) * (20 + 10 * M)

def matrixAddBodyTime (M N K : ℕ) : ℕ :=
  2 * (2 * M + 5) + 2 * moveAllowance M + evalInstructionTime M N K + appendAllowance M

theorem layout_moveR (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (d s : Fin 64) (hd : d ≠ s) :
    Cert (MVM.compile (.mvR d s)) (layout M N K b) (layout M N K b) (moveAllowance M) := by
  have hc := compile_mvR_scratch d s hd (layout M N K b) M h.top
  exact hc.mono le_rfl le_rfl (by unfold moveAllowance; gcongr; exact h.top 37)

theorem compile_maBody (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hx0 : b rX0 = N * K) (hx1 : b rX1 = N * K)
    (hz : b rZ ≤ N * K) (hs : b rAccL + N * K ≤ M) :
    Cert (MVM.compile maBody) (layout M N K b)
      (layout M N K (Function.update b rAccL (b rAccL + N * K))) (matrixAddBodyTime M N K) := by
  have h1 := layout_copy M N K b h.top rX0 rZ (by simpa [hx0] using hz)
  have h2 := layout_moveR M N K b h rX0 rRo0 (by decide)
  have h3 := layout_copy M N K b h.top rX1 rZ (by simpa [hx1] using hz)
  have h4 := layout_moveR M N K b h rX1 rRo1 (by decide)
  have ht : operationBound M N K M ≤ evalInstructionTime M N K := by
    unfold evalInstructionTime; omega
  have h5 := (layout_op M N K b h .add rX0 rX0 rX1 hx0.ge).mono le_rfl le_rfl ht
  have h6 := layout_append_uniform M N K b h.top rAccL rX0 (by simpa [hx0] using hs)
  rw [hx0] at h6
  exact (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))).mono le_rfl le_rfl
    (by unfold matrixAddBodyTime; omega)

theorem compile_maLoop (M N K R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hx0 : b rX0 = N * K) (hx1 : b rX1 = N * K)
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
    have hb := compile_maBody M N K (Function.update b rAccL (j * (N * K)))
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

/-- The actual matrix addition initializes both streams and rebuilds its output entry by entry. -/
theorem compile_matAddC (M N K R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hx0 : b rX0 = N * K) (hx1 : b rX1 = N * K)
    (hz : b rZ ≤ N * K) (h0 : b rAccL ≤ b rRo0) (h1 : b rMOut ≤ b rRo1)
    (ht : b rT4K ≤ b rCi) (hc : b rCi ≤ R) (hsize : R * (N * K) ≤ b rAccL) :
    Cert (MVM.compile matAddC) (layout M N K b) (layout M N K b)
      (4 * (2 * M + 5) + R * (2 * M + matrixAddBodyTime M N K + 4) + 2) := by
  let b0 := Function.update b rAccL 0
  have hi : RingInputs M N K (layout M N K b0) := h.update_layout rAccL 0 (Nat.zero_le _)
  have hcp0 := layout_copy M N K b h.top rRo0 rAccL h0
  have hcp1 := layout_copy M N K b h.top rRo1 rMOut h1
  have hclear := layout_clear_update M N K b h.top rAccL
  have hcounter := layout_copy M N K b0 hi.top rCi rT4K (by simpa [b0] using ht)
  have hpre := hcp0.seq (hcp1.seq (hclear.seq hcounter))
  have hm : R * (N * K) ≤ M := hsize.trans (by simpa using h.top (tR rAccL))
  have hl := compile_maLoop M N K R b h hx0 hx1 hz hc hm
  have hloop := hl.mono le_rfl (layout_mono M N K (cap_update_le b rAccL _ hsize)) le_rfl
  exact (hpre.seq hloop).mono le_rfl le_rfl (by omega)

set_option exponentiation.threshold 1000 in
/-- Conditional concrete cost for adding all four-K entries of the two-row matrices. -/
theorem compile_matAddC_concrete (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (hx0 : b rX0 = 2 ^ 24 * 2 ^ 16) (hx1 : b rX1 = 2 ^ 24 * 2 ^ 16)
    (hz : b rZ ≤ 2 ^ 24 * 2 ^ 16) (h0 : b rAccL ≤ b rRo0) (h1 : b rMOut ≤ b rRo1)
    (ht : b rT4K ≤ b rCi) (hc : b rCi ≤ 4 * 2 ^ 16)
    (hsize : (4 * 2 ^ 16) * (2 ^ 24 * 2 ^ 16) ≤ b rAccL) :
    Cert (MVM.compile matAddC) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) (2 ^ 364) := by
  have hfull := compile_matAddC (2 ^ 120) (2 ^ 24) (2 ^ 16) (4 * 2 ^ 16) b h
    hx0 hx1 hz h0 h1 ht hc hsize
  have hi := evalInstructionTime_concrete
  apply hfull.mono le_rfl le_rfl
  unfold matrixAddBodyTime
  calc
    _ ≤ 4 * (2 * 2 ^ 120 + 5) + (4 * 2 ^ 16) * (2 * 2 ^ 120 +
        (2 * (2 * 2 ^ 120 + 5) + 2 * moveAllowance (2 ^ 120) + 2 ^ 341 + appendAllowance (2 ^ 120))
        + 4) + 2 := by gcongr
    _ ≤ 2 ^ 364 := by norm_num [moveAllowance, appendAllowance]

end AdvancedEncryption.ExpLUT.Prog.KeyTime
