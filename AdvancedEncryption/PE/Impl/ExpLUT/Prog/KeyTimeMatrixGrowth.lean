import PE.Impl.ExpLUT.Prog.KeyTimeCoefA
/-! Linear queue growth for actual matrix construction loops. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM SigabaNeo.Tape.Prog

def appendAllowance (M : ℕ) : ℕ := (4 * M + 6) * (2 * M + 5)

theorem cap_update_le (b : Fin 64 → ℕ) (r : Fin 64) (n : ℕ) (hn : n ≤ b r) :
    Function.update b r n ≤ b := by
  intro s; by_cases hs : s = r
  · subst s; simpa using hn
  · simp [Function.update_of_ne hs]

@[simp] theorem cap_reset (b : Fin 64 → ℕ) (r : Fin 64) (n m : ℕ) :
    Function.update (Function.update b r n) r m = Function.update b r m := by
  funext s; simp only [Function.update_apply]; split_ifs <;> rfl

theorem layout_append_uniform (M N K : ℕ) (b : Fin 64 → ℕ)
    (ht : ∀ t, layout M N K b t ≤ M) (d s : Fin 64) (hs : b d + b s ≤ M) :
    Cert (MVM.compile (.app d s)) (layout M N K b)
      (layout M N K (Function.update b d (b d + b s))) (appendAllowance M) := by
  have hc : b s ≤ M := by simpa using ht (tR s)
  exact (layout_append M N K b ht d s hs).mono le_rfl le_rfl (by unfold appendAllowance; gcongr)

/-- One gadget row entry appends an NK-bit word and doubles that word. -/
theorem compile_agBody (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hx : b rX0 = N * K)
    (hs : b rRo0 + N * K ≤ M) :
    Cert (MVM.compile agBody) (layout M N K b)
      (layout M N K (Function.update b rRo0 (b rRo0 + N * K)))
      (appendAllowance M + evalInstructionTime M N K) := by
  have ha := layout_append_uniform M N K b h.top rRo0 rX0 (by simpa [hx] using hs)
  rw [hx] at ha
  have hi := h.update_layout rRo0 (b rRo0 + N * K) hs
  have hop := layout_op M N K _ hi .add rX0 rX0 rX0 (by simp [hx])
  have ht : operationBound M N K M ≤ evalInstructionTime M N K := by
    unfold evalInstructionTime; omega
  exact ha.seq (hop.mono le_rfl le_rfl ht)

/-- The gadget segment grows by one ring word per iteration, from zero to R*NK. -/
theorem compile_agLoop (M N K R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hx : b rX0 = N * K)
    (hc : b rCi ≤ R) (hsize : R * (N * K) ≤ M) :
    Cert (MVM.compile (.rep rCi agBody))
      (layout M N K (Function.update b rRo0 0))
      (layout M N K (Function.update b rRo0 (R * (N * K))))
      (R * (2 * M + (appendAllowance M + evalInstructionTime M N K) + 4) + 2) := by
  let γ := fun j ↦ layout M N K (Function.update b rRo0 (j * (N * K)))
  have hi (j : ℕ) (hj : j ≤ R) : RingInputs M N K (γ j) := by
    apply h.update_layout rRo0 (j * (N * K))
    exact (Nat.mul_le_mul_right _ hj).trans hsize
  apply rep_family rCi agBody γ R (appendAllowance M + evalInstructionTime M N K) _
    (by simp [γ]) (by simpa using hc)
  · intro j hj
    have hs : (j + 1) * (N * K) ≤ M :=
      (Nat.mul_le_mul_right _ (show j + 1 ≤ R by omega)).trans hsize
    have hb := compile_agBody M N K (Function.update b rRo0 (j * (N * K)))
      (hi j (by omega)) (by simpa using hx) (by simpa [Nat.add_mul] using hs)
    simp only [Function.update_self, cap_reset] at hb
    have he : j * (N * K) + N * K = (j + 1) * (N * K) := by ring
    rw [he] at hb
    exact hb.mono (tailB_le (tR rCi) _) le_rfl le_rfl
  · intro j hj; exact supB_le_of (hi j (by omega)).top
  · intro j hj
    apply layout_mono
    intro r
    by_cases hr : r = rRo0
    · subst r; simp only [Function.update_self]; exact Nat.mul_le_mul_right _ hj
    · simp [Function.update_of_ne hr]

/-- Assemble the two gadget rows from the saved segment and two zero blocks. -/
theorem compile_agPost (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b))
    (hsize : 2 * b rRo0 + 2 * b rTKNK ≤ b rMA) :
    Cert (MVM.compile agPost) (layout M N K b) (layout M N K b)
      ((2 * M + 5) + 3 * appendAllowance M) := by
  let b1 := Function.update b rMA (b rRo0)
  let b2 := Function.update b rMA (b rRo0 + b rTKNK)
  let b3 := Function.update b rMA (b rRo0 + 2 * b rTKNK)
  have hm : b rMA ≤ M := by simpa using h.top (tR rMA)
  have ht1 : ∀ t, layout M N K b1 t ≤ M :=
    fun t ↦ (layout_mono M N K (cap_update_le b rMA _ (by omega)) t).trans (h.top t)
  have ht2 : ∀ t, layout M N K b2 t ≤ M :=
    fun t ↦ (layout_mono M N K (cap_update_le b rMA _ (by omega)) t).trans (h.top t)
  have ht3 : ∀ t, layout M N K b3 t ≤ M :=
    fun t ↦ (layout_mono M N K (cap_update_le b rMA _ (by omega)) t).trans (h.top t)
  have h1 := layout_copy_update M N K b h.top rMA rRo0
  have h2 : Cert (MVM.compile (.app rMA rTKNK)) (layout M N K b1)
      (layout M N K b2) (appendAllowance M) := by
    simpa [b1, b2] using layout_append_uniform M N K b1 ht1 rMA rTKNK (by change b rRo0 + b rTKNK ≤ M; omega)
  have h3 : Cert (MVM.compile (.app rMA rTKNK)) (layout M N K b2)
      (layout M N K b3) (appendAllowance M) := by
    have he : b rRo0 + b rTKNK + b rTKNK = b rRo0 + 2 * b rTKNK := by omega
    simpa [b2, b3, he] using layout_append_uniform M N K b2 ht2 rMA rTKNK (by change b rRo0 + b rTKNK + b rTKNK ≤ M; omega)
  have h4 := layout_append_uniform M N K b3 ht3 rMA rRo0 (by change b rRo0 + 2 * b rTKNK + b rRo0 ≤ M; omega)
  have hout : layout M N K (Function.update b3 rMA (b3 rMA + b3 rRo0)) ≤ layout M N K b := by
    apply layout_mono
    simpa [b3] using cap_update_le b rMA (b rRo0 + 2 * b rTKNK + b rRo0) (by omega)
  exact (h1.seq (h2.seq (h3.seq (h4.mono le_rfl hout le_rfl)))).mono le_rfl le_rfl (by omega)

/-- The actual gadget-matrix constructor, including initialization, growth, and assembly. -/
theorem compile_agC (M N K R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hx : b rX0 = N * K)
    (hal : b rAl ≤ b rX0) (htk : b rTK ≤ b rCi) (hc : b rCi ≤ R)
    (hseg : R * (N * K) ≤ b rRo0) (hmat : 2 * b rRo0 + 2 * b rTKNK ≤ b rMA) :
    Cert (MVM.compile agC) (layout M N K b) (layout M N K b)
      (4 * (2 * M + 5) + R * (2 * M + (appendAllowance M + evalInstructionTime M N K) + 4)
        + 2 + 3 * appendAllowance M) := by
  let b0 := Function.update b rRo0 0
  have hi : RingInputs M N K (layout M N K b0) := h.update_layout rRo0 0 (Nat.zero_le _)
  have h0 := layout_clear_update M N K b h.top rRo0
  have h1 := layout_copy M N K b0 hi.top rX0 rAl (by simpa [b0] using hal)
  have h2 := layout_copy M N K b0 hi.top rCi rTK (by simpa [b0] using htk)
  have hpre := h0.seq (h1.seq h2)
  have hs : R * (N * K) ≤ M := hseg.trans (by simpa using h.top (tR rRo0))
  have hl := compile_agLoop M N K R b h hx hc hs
  have hloop := hl.mono le_rfl (layout_mono M N K (cap_update_le b rRo0 _ hseg)) le_rfl
  have hp := compile_agPost M N K b h hmat
  exact (hpre.seq (hloop.seq hp)).mono le_rfl le_rfl (by omega)

set_option exponentiation.threshold 1000 in
/-- Conditional concrete cost of constructing the four-K-word gadget matrix. -/
theorem compile_agC_concrete (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (hx : b rX0 = 2 ^ 24 * 2 ^ 16) (hal : b rAl ≤ b rX0) (htk : b rTK ≤ b rCi)
    (hc : b rCi ≤ 2 ^ 16) (hseg : 2 ^ 16 * (2 ^ 24 * 2 ^ 16) ≤ b rRo0)
    (hmat : 2 * b rRo0 + 2 * b rTKNK ≤ b rMA) :
    Cert (MVM.compile agC) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) (2 ^ 362) := by
  have hfull := compile_agC (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) b h hx hal htk hc hseg hmat
  have ht := evalInstructionTime_concrete
  apply hfull.mono le_rfl le_rfl
  calc
    _ ≤ 4 * (2 * 2 ^ 120 + 5) + 2 ^ 16 *
        (2 * 2 ^ 120 + (appendAllowance (2 ^ 120) + 2 ^ 341) + 4) +
        2 + 3 * appendAllowance (2 ^ 120) := by gcongr
    _ ≤ 2 ^ 362 := by norm_num [appendAllowance]

end AdvancedEncryption.ExpLUT.Prog.KeyTime
