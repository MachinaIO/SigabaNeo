import PE.Impl.ExpLUT.Prog.KeyTimePrepare

/-! Exact output lengths and linear coefficient growth in candidate decoding. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM SigabaNeo.Tape.Prog

theorem layout_op_update (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (o : Op) (d s c : Fin 64) :
    Cert (MVM.compile (.op o d s c)) (layout M N K b)
      (layout M N K (Function.update b d (N * K))) (operationBound M N K M) := by
  obtain ⟨hp, hr⟩ := compile_op_scratch_ready M N K o d s c _ h
  apply hp.mono le_rfl
  · apply le_layout M N K _ _ hr.top hr.templateK hr.templateN hr.zeros.le hr.ones
    intro r
    by_cases he : r = d
    · subst r; simp [operationResult_destination]
    · rw [operationResult_other _ _ _ _ _ _ _ he, cleanWork_register, layout_register,
        Function.update_of_ne he]
  · exact operationBound_mono le_rfl le_rfl le_rfl (h.top _)

def decodeBodyTime (M : ℕ) := (2 * M + 5) + moveAllowance M + 2 * appendAllowance M

/-- The copied chunk has its actual bound before appending, regardless of the old Dx cap. -/
theorem compile_decBody (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b))
    (hx : b rTBk ≤ b rDx) (hk : b rTBk + b rTKmB ≤ K) (hs : b rDw + K ≤ M) :
    Cert (MVM.compile decBody) (layout M N K b)
      (layout M N K (Function.update b rDw (b rDw + K))) (decodeBodyTime M) := by
  let c := Function.update b rDx (b rTBk)
  let d := Function.update c rDw (b rDw + b rTBk)
  have hi : RingInputs M N K (layout M N K c) :=
    h.update_layout rDx _ (by simpa using h.top (tR rTBk))
  have hd : RingInputs M N K (layout M N K d) := hi.update_layout rDw _ (by omega)
  have p0 := layout_copy_update M N K b h.top rDx rTBk
  have p1 := layout_move M N K c hi rDx rCoin rTBk (by decide)
  have p2 := layout_append_uniform M N K c hi.top rDw rDx (by change b rDw + b rTBk ≤ M; omega)
  have p3 := layout_append_uniform M N K d hd.top rDw rTKmB (by change b rDw + b rTBk + b rTKmB ≤ M; omega)
  have he : Function.update c rDw (c rDw + c rDx) = d := by simp [c, d]
  rw [he] at p2
  rw [decBody]
  apply (p0.seq (p1.seq (p2.seq p3))).mono le_rfl _ (by unfold decodeBodyTime; omega)
  apply layout_mono
  intro r
  by_cases hw : r = rDw
  · subst r
    change b rDw + b rTBk + b rTKmB ≤ b rDw + K
    omega
  · by_cases hdx : r = rDx
    · subst r; simpa [d, c] using hx
    · simp [d, c, Function.update_of_ne hw, Function.update_of_ne hdx]

/-- Exactly R coefficient slots, starting with an empty accumulator. -/
theorem compile_decLoop (M N K R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b))
    (hx : b rTBk ≤ b rDx) (hk : b rTBk + b rTKmB ≤ K)
    (hn : b AdvancedEncryption.ExpLUT.Prog.rDn ≤ R) (hs : R * K ≤ M) :
    Cert (MVM.compile (.rep AdvancedEncryption.ExpLUT.Prog.rDn decBody))
      (layout M N K (Function.update b rDw 0))
      (layout M N K (Function.update b rDw (R * K)))
      (R * (2 * M + decodeBodyTime M + 4) + 2) := by
  let γ := fun j ↦ layout M N K (Function.update b rDw (j * K))
  have hi (j : ℕ) (hj : j ≤ R) : RingInputs M N K (γ j) :=
    h.update_layout rDw _ ((Nat.mul_le_mul_right K hj).trans hs)
  apply rep_family AdvancedEncryption.ExpLUT.Prog.rDn decBody γ R (decodeBodyTime M) _
    (by simp [γ]) (by simpa using hn)
  · intro j hj
    have hjk : (j + 1) * K ≤ M := (Nat.mul_le_mul_right K (by omega : j + 1 ≤ R)).trans hs
    have hb := compile_decBody M N K (Function.update b rDw (j * K)) (hi j (by omega))
      (by simpa using hx) (by simpa using hk)
      (by simpa only [Function.update_self, Nat.add_mul, Nat.one_mul] using hjk)
    simp only [Function.update_self, cap_reset] at hb
    rw [show j * K + K = (j + 1) * K by ring] at hb
    exact hb.mono (tailB_le (tR AdvancedEncryption.ExpLUT.Prog.rDn) _) le_rfl le_rfl
  · intro j hj; exact supB_le_of (hi j (by omega)).top
  · intro j hj
    apply layout_mono
    intro r
    by_cases hr : r = rDw
    · subst r; simp only [Function.update_self]; exact Nat.mul_le_mul_right K hj
    · simp [Function.update_of_ne hr]

/-- Dx is allowed its old scratch size at iteration zero; Dn is overwritten by the real copy. -/
def decodeBase (M : ℕ) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (Function.update b rDx M) AdvancedEncryption.ExpLUT.Prog.rDn (b rTN)

def decodeResult (M N K R : ℕ) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (Function.update (decodeBase M b) rDw (R * K)) rDo (N * K)

def decodeTime (M N K R : ℕ) :=
  2 * (2 * M + 5) + R * (2 * M + decodeBodyTime M + 4) + 2 + operationBound M N K M

theorem decodeBase_inputs (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) :
    RingInputs M N K (layout M N K (decodeBase M b)) :=
  (h.update_layout rDx M le_rfl).update_layout AdvancedEncryption.ExpLUT.Prog.rDn _
    (by simpa using h.top (tR rTN))

/-- Full real decoder: clear, counter copy, coefficient loop and subtraction with exact Do=NK. -/
theorem compile_decC (M N K R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b))
    (hk : b rTBk + b rTKmB ≤ K) (hn : b rTN ≤ R) (hs : R * K ≤ M) :
    Cert (MVM.compile decC) (layout M N K b)
      (layout M N K (decodeResult M N K R b)) (decodeTime M N K R) := by
  let c := Function.update b rDx M
  let c0 := Function.update c rDw 0
  have hic : RingInputs M N K (layout M N K c) := h.update_layout rDx M le_rfl
  have hi0 : RingInputs M N K (layout M N K c0) := hic.update_layout rDw 0 (Nat.zero_le _)
  have hib := decodeBase_inputs M N K b h
  have p0 := layout_clear_update M N K c hic.top rDw
  have p1 := layout_copy_update M N K c0 hi0.top AdvancedEncryption.ExpLUT.Prog.rDn rTN
  have he : Function.update c0 AdvancedEncryption.ExpLUT.Prog.rDn (c0 rTN) =
      Function.update (decodeBase M b) rDw 0 := by
    funext r
    by_cases h0 : r = rDw <;> by_cases h1 : r = AdvancedEncryption.ExpLUT.Prog.rDn <;>
      simp_all [c0, c, decodeBase, Function.update_apply]
  rw [he] at p1
  have p2 := compile_decLoop M N K R (decodeBase M b) hib
    (by simpa [decodeBase] using h.top (tR rTBk))
    (by simpa [decodeBase] using hk) (by simpa [decodeBase] using hn) hs
  have hil := hib.update_layout rDw (R * K) hs
  have p3 := layout_op_update M N K _ hil .sub rDo rDw rC2
  rw [decC]
  apply (p0.seq (p1.seq (p2.seq p3))).mono _ le_rfl (by unfold decodeTime; omega)
  apply layout_mono
  intro r
  by_cases hr : r = rDx
  · subst r; simpa [c] using h.top (tR rDx)
  · simp [c, Function.update_of_ne hr]

theorem decodeResult_inputs (M N K R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hs : R * K ≤ M) :
    RingInputs M N K (layout M N K (decodeResult M N K R b)) :=
  ((decodeBase_inputs M N K b h).update_layout rDw _ hs).update_layout rDo _ h.ring

theorem decodeResult_fields (M N K R : ℕ) (b : Fin 64 → ℕ) :
    decodeResult M N K R b rDo = N * K ∧
    decodeResult M N K R b rDw = R * K ∧
    decodeResult M N K R b rDx = M ∧
    decodeResult M N K R b AdvancedEncryption.ExpLUT.Prog.rDn = b rTN := by
  simp [decodeResult, decodeBase]

set_option exponentiation.threshold 1000 in
theorem decodeTime_concrete : decodeTime (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 24) ≤ 2 ^ 342 := by
  have ho := operationBound_concrete (M := 2 ^ 120) (count := 2 ^ 120) le_rfl le_rfl
  unfold decodeTime
  calc
    _ ≤ 2 * (2 * 2 ^ 120 + 5) + 2 ^ 24 *
        (2 * 2 ^ 120 + decodeBodyTime (2 ^ 120) + 4) + 2 + 2 ^ 340 := by gcongr
    _ ≤ 2 ^ 342 := by norm_num [decodeBodyTime, moveAllowance, appendAllowance]

theorem compile_decC_concrete (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (hk : b rTBk + b rTKmB ≤ 2 ^ 16) (hn : b rTN ≤ 2 ^ 24) :
    Cert (MVM.compile decC) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) (decodeResult (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 24) b))
      (2 ^ 342) :=
  (compile_decC (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 24) b h hk hn (by norm_num)).mono
    le_rfl le_rfl decodeTime_concrete

end AdvancedEncryption.ExpLUT.Prog.KeyTime
