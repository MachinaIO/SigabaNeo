import PE.Impl.ExpLUT.Prog.KeyTimeMatAdd

/-! Asymmetric gadget-construction bounds: overwritten scratch caps may shrink. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM

theorem layout_copy_cap (M N K : ℕ) (b : Fin 64 → ℕ)
    (ht : ∀ t, layout M N K b t ≤ M) (d s : Fin 64) (n : ℕ) (hn : b s ≤ n) :
    Cert (MVM.compile (.cp d s)) (layout M N K b)
      (layout M N K (Function.update b d n)) (2 * M + 5) := by
  apply (layout_copy_update M N K b ht d s).mono le_rfl _ le_rfl
  apply layout_mono
  intro r
  by_cases hr : r = d
  · subst r; simpa using hn
  · simp [Function.update_of_ne hr]

/-- Assembly returns the newly computed matrix cap, independently of its old destination cap. -/
theorem compile_agPost_exact (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b))
    (hsize : 2 * b rRo0 + 2 * b rTKNK ≤ M) :
    Cert (MVM.compile agPost) (layout M N K b)
      (layout M N K (Function.update b rMA (2 * b rRo0 + 2 * b rTKNK)))
      ((2 * M + 5) + 3 * appendAllowance M) := by
  let b1 := Function.update b rMA (b rRo0)
  let b2 := Function.update b rMA (b rRo0 + b rTKNK)
  let b3 := Function.update b rMA (b rRo0 + 2 * b rTKNK)
  have ht1 := (h.update_layout rMA (b rRo0) (by omega)).top
  have ht2 := (h.update_layout rMA (b rRo0 + b rTKNK) (by omega)).top
  have ht3 := (h.update_layout rMA (b rRo0 + 2 * b rTKNK) (by omega)).top
  have h1 := layout_copy_update M N K b h.top rMA rRo0
  have h2 : Cert (MVM.compile (.app rMA rTKNK)) (layout M N K b1)
      (layout M N K b2) (appendAllowance M) := by
    simpa [b1, b2] using layout_append_uniform M N K b1 ht1 rMA rTKNK
      (by change b rRo0 + b rTKNK ≤ M; omega)
  have h3 : Cert (MVM.compile (.app rMA rTKNK)) (layout M N K b2)
      (layout M N K b3) (appendAllowance M) := by
    have he : b rRo0 + b rTKNK + b rTKNK = b rRo0 + 2 * b rTKNK := by omega
    simpa [b2, b3, he] using layout_append_uniform M N K b2 ht2 rMA rTKNK
      (by change b rRo0 + b rTKNK + b rTKNK ≤ M; omega)
  have h4 := layout_append_uniform M N K b3 ht3 rMA rRo0
    (by change b rRo0 + 2 * b rTKNK + b rRo0 ≤ M; omega)
  have he : b rRo0 + 2 * b rTKNK + b rRo0 = 2 * b rRo0 + 2 * b rTKNK := by omega
  simp only [b3, Function.update_self, Function.update_of_ne (by decide : rRo0 ≠ rMA),
    cap_reset, he] at h4
  exact (h1.seq (h2.seq (h3.seq h4))).mono le_rfl le_rfl (by omega)

def gadgetBase (N K : ℕ) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (Function.update b rX0 (N * K)) rCi (b rTK)

def gadgetResult (N K R : ℕ) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (Function.update (gadgetBase N K b) rRo0 (R * (N * K)))
    rMA (2 * (R * (N * K)) + 2 * b rTKNK)

theorem gadgetBase_inputs (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) :
    RingInputs M N K (layout M N K (gadgetBase N K b)) :=
  (h.update_layout rX0 (N * K) h.ring).update_layout rCi (b rTK)
    (by simpa using h.top (tR rTK))

/-- The actual prefix overwrites Ro0, X0, and Ci, so their old caps impose no restrictions. -/
theorem compile_agPre_exact (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hal : b rAl ≤ N * K) :
    Cert (MVM.compile agPre) (layout M N K b)
      (layout M N K (Function.update (gadgetBase N K b) rRo0 0)) (3 * (2 * M + 5)) := by
  let b0 := Function.update b rRo0 0
  let b1 := Function.update b0 rX0 (N * K)
  have hi0 : RingInputs M N K (layout M N K b0) := h.update_layout rRo0 0 (Nat.zero_le _)
  have hi1 : RingInputs M N K (layout M N K b1) := hi0.update_layout rX0 (N * K) h.ring
  have h0 := layout_clear_update M N K b h.top rRo0
  have h1 := layout_copy_cap M N K b0 hi0.top rX0 rAl (N * K) (by simpa [b0] using hal)
  have h2 := layout_copy_update M N K b1 hi1.top rCi rTK
  have he : Function.update b1 rCi (b1 rTK) = Function.update (gadgetBase N K b) rRo0 0 := by
    funext r
    by_cases h0 : r = rRo0 <;> by_cases h1 : r = rX0 <;> by_cases h2 : r = rCi <;>
      simp_all [b1, b0, gadgetBase, Function.update_apply]
  rw [he] at h2
  exact (h0.seq (h1.seq h2)).mono le_rfl le_rfl (by omega)

/-- The full gadget constructor accepts arbitrary old scratch caps and returns precise new caps. -/
theorem compile_agC_exact (M N K R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hal : b rAl ≤ N * K) (hk : b rTK ≤ R)
    (hsize : 2 * (R * (N * K)) + 2 * b rTKNK ≤ M) :
    Cert (MVM.compile agC) (layout M N K b) (layout M N K (gadgetResult N K R b))
      (4 * (2 * M + 5) + R * (2 * M + (appendAllowance M + evalInstructionTime M N K) + 4)
        + 2 + 3 * appendAllowance M) := by
  let c := gadgetBase N K b
  have hi := gadgetBase_inputs M N K b h
  have hp := compile_agPre_exact M N K b h hal
  have hl := compile_agLoop M N K R c hi (by simp [c, gadgetBase])
    (by simpa [c, gadgetBase] using hk) (by omega)
  have hlout := hi.update_layout rRo0 (R * (N * K)) (by omega)
  have hpost := compile_agPost_exact M N K (Function.update c rRo0 (R * (N * K))) hlout
    (by simpa [c, gadgetBase] using hsize)
  have he : (Function.update c rRo0 (R * (N * K))) rRo0 = R * (N * K) := by simp
  have ht : (Function.update c rRo0 (R * (N * K))) rTKNK = b rTKNK := by simp [c, gadgetBase]
  rw [he, ht] at hpost
  exact (hp.seq (hl.seq hpost)).mono le_rfl le_rfl (by omega)

theorem gadgetResult_inputs (M N K R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b))
    (hsize : 2 * (R * (N * K)) + 2 * b rTKNK ≤ M) :
    RingInputs M N K (layout M N K (gadgetResult N K R b)) :=
  ((gadgetBase_inputs M N K b h).update_layout rRo0 (R * (N * K)) (by omega)).update_layout
    rMA (2 * (R * (N * K)) + 2 * b rTKNK) hsize

/-- Only the three overwritten scratch registers and matrix destination change caps. -/
theorem gadgetResult_other (N K R : ℕ) (b : Fin 64 → ℕ) (r : Fin 64)
    (h0 : r ≠ rX0) (h1 : r ≠ rCi) (h2 : r ≠ rRo0) (h3 : r ≠ rMA) :
    gadgetResult N K R b r = b r := by
  simp [gadgetResult, gadgetBase, Function.update_of_ne, h0, h1, h2, h3]

theorem gadgetResult_fields (N K R : ℕ) (b : Fin 64 → ℕ) :
    gadgetResult N K R b rX0 = N * K ∧
    gadgetResult N K R b rCi = b rTK ∧
    gadgetResult N K R b rRo0 = R * (N * K) ∧
    gadgetResult N K R b rMA = 2 * (R * (N * K)) + 2 * b rTKNK := by
  simp [gadgetResult, gadgetBase]

set_option exponentiation.threshold 1000 in
/-- Concrete cost without any constraint on the old X0, Ci, Ro0, or MA register caps. -/
theorem compile_agC_exact_concrete (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (hal : b rAl ≤ 2 ^ 24 * 2 ^ 16) (hk : b rTK ≤ 2 ^ 16)
    (hz : b rTKNK ≤ 2 ^ 16 * (2 ^ 24 * 2 ^ 16)) :
    Cert (MVM.compile agC) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) (gadgetResult (2 ^ 24) (2 ^ 16) (2 ^ 16) b))
      (2 ^ 362) := by
  have hs : 2 * (2 ^ 16 * (2 ^ 24 * 2 ^ 16)) + 2 * b rTKNK ≤ 2 ^ 120 := by
    calc
      _ ≤ 2 * (2 ^ 16 * (2 ^ 24 * 2 ^ 16)) + 2 * (2 ^ 16 * (2 ^ 24 * 2 ^ 16)) := by gcongr
      _ ≤ 2 ^ 120 := by norm_num
  have hf := compile_agC_exact (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) b h hal hk hs
  have ht := evalInstructionTime_concrete
  apply hf.mono le_rfl le_rfl
  calc
    _ ≤ 4 * (2 * 2 ^ 120 + 5) + 2 ^ 16 *
        (2 * 2 ^ 120 + (appendAllowance (2 ^ 120) + 2 ^ 341) + 4) +
        2 + 3 * appendAllowance (2 ^ 120) := by gcongr
    _ ≤ 2 ^ 362 := by norm_num [appendAllowance]

end AdvancedEncryption.ExpLUT.Prog.KeyTime
