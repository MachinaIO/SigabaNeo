import PE.Impl.ExpLUT.Prog.KeyTimeDecode

/-! Linear candidate-queue growth using the actual decoder's exact ring-word output. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM SigabaNeo.Tape.Prog

theorem decodeResult_le (M N K R : ℕ) (b : Fin 64 → ℕ)
    (hx : M ≤ b rDx) (hn : b rTN ≤ b AdvancedEncryption.ExpLUT.Prog.rDn)
    (hw : R * K ≤ b rDw) (ho : N * K ≤ b rDo) : decodeResult M N K R b ≤ b := by
  intro r
  by_cases h0 : r = rDx <;> by_cases h1 : r = AdvancedEncryption.ExpLUT.Prog.rDn <;>
    by_cases h2 : r = rDw <;> by_cases h3 : r = rDo <;>
    simp_all [decodeResult, decodeBase, Function.update_apply]

def decodeQueueBodyTime (M N K R : ℕ) := decodeTime M N K R + appendAllowance M

theorem compile_decQBody (M N K R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b))
    (hk : b rTBk + b rTKmB ≤ K) (hn : b rTN ≤ R) (hr : R * K ≤ M)
    (hx : M ≤ b rDx) (hd : b rTN ≤ b AdvancedEncryption.ExpLUT.Prog.rDn)
    (hw : R * K ≤ b rDw) (ho : N * K ≤ b rDo) (hs : b rDq + N * K ≤ M) :
    Cert (MVM.compile decQBody) (layout M N K b)
      (layout M N K (Function.update b rDq (b rDq + N * K)))
      (decodeQueueBodyTime M N K R) := by
  let c := decodeResult M N K R b
  have hi := decodeResult_inputs M N K R b h hr
  have p0 := compile_decC M N K R b h hk hn hr
  have p1 := layout_append_uniform M N K c hi.top rDq rDo
    (by simpa [c, decodeResult, decodeBase] using hs)
  have hle : c ≤ b := decodeResult_le M N K R b hx hd hw ho
  rw [decQBody]
  apply (p0.seq p1).mono le_rfl _ le_rfl
  apply layout_mono
  intro r
  by_cases he : r = rDq
  · subst r; simp [c, decodeResult, decodeBase]
  · simp only [Function.update_of_ne he]; exact hle r

/-- Scratch is safely widened before the outer loop, including iteration zero. -/
def decodeQueueBase (M : ℕ) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (Function.update (Function.update (Function.update b rDx M)
    AdvancedEncryption.ExpLUT.Prog.rDn M) rDw M) rDo M

theorem decodeQueueBase_inputs (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) :
    RingInputs M N K (layout M N K (decodeQueueBase M b)) :=
  (((h.update_layout rDx M le_rfl).update_layout AdvancedEncryption.ExpLUT.Prog.rDn M le_rfl).update_layout rDw M le_rfl).update_layout rDo M le_rfl

theorem le_decodeQueueBase (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) : b ≤ decodeQueueBase M b := by
  intro r
  have ht : b r ≤ M := by simpa using h.top (tR r)
  by_cases h0 : r = rDx <;> by_cases h1 : r = AdvancedEncryption.ExpLUT.Prog.rDn <;>
    by_cases h2 : r = rDw <;> by_cases h3 : r = rDo <;>
    simp_all [decodeQueueBase]

theorem compile_decQLoop (M N K R Q : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b))
    (hk : b rTBk + b rTKmB ≤ K) (hn : b rTN ≤ R) (hr : R * K ≤ M)
    (hq : b rDqn ≤ Q) (hs : Q * (N * K) ≤ M) :
    Cert (MVM.compile (.rep rDqn decQBody))
      (layout M N K (Function.update (decodeQueueBase M b) rDq 0))
      (layout M N K (Function.update (decodeQueueBase M b) rDq (Q * (N * K))))
      (Q * (2 * M + decodeQueueBodyTime M N K R + 4) + 2) := by
  let c := decodeQueueBase M b
  let γ := fun j ↦ layout M N K (Function.update c rDq (j * (N * K)))
  have hic := decodeQueueBase_inputs M N K b h
  have hi (j : ℕ) (hj : j ≤ Q) : RingInputs M N K (γ j) :=
    hic.update_layout rDq _ ((Nat.mul_le_mul_right (N * K) hj).trans hs)
  apply rep_family rDqn decQBody γ Q (decodeQueueBodyTime M N K R) _
    (by simp [γ, c]) (by simpa [c, decodeQueueBase] using hq)
  · intro j hj
    have hsize : (j + 1) * (N * K) ≤ M :=
      (Nat.mul_le_mul_right (N * K) (by omega : j + 1 ≤ Q)).trans hs
    have hb := compile_decQBody M N K R (Function.update c rDq (j * (N * K)))
      (hi j (by omega)) (by simpa [c, decodeQueueBase] using hk)
      (by simpa [c, decodeQueueBase] using hn) hr (by simp [c, decodeQueueBase])
      (by simpa [c, decodeQueueBase] using h.top (tR rTN))
      (by simpa [c, decodeQueueBase] using hr)
      (by simpa [c, decodeQueueBase] using h.ring)
      (by simpa only [Function.update_self, Nat.add_mul, Nat.one_mul] using hsize)
    simp only [Function.update_self, cap_reset] at hb
    rw [show j * (N * K) + N * K = (j + 1) * (N * K) by ring] at hb
    exact hb.mono (tailB_le (tR rDqn) _) le_rfl le_rfl
  · intro j hj; exact supB_le_of (hi j (by omega)).top
  · intro j hj
    apply layout_mono
    intro r
    by_cases he : r = rDq
    · subst r; simp only [Function.update_self]; exact Nat.mul_le_mul_right (N * K) hj
    · simp [Function.update_of_ne he]

def decodeQueueTime (M N K R Q : ℕ) :=
  (2 * M + 5) + Q * (2 * M + decodeQueueBodyTime M N K R + 4) + 2

theorem compile_decQC (M N K R Q : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b))
    (hk : b rTBk + b rTKmB ≤ K) (hn : b rTN ≤ R) (hr : R * K ≤ M)
    (hq : b rDqn ≤ Q) (hs : Q * (N * K) ≤ M) :
    Cert (MVM.compile decQC) (layout M N K b)
      (layout M N K (Function.update (decodeQueueBase M b) rDq (Q * (N * K))))
      (decodeQueueTime M N K R Q) := by
  have hi := decodeQueueBase_inputs M N K b h
  have p0 := layout_clear_update M N K (decodeQueueBase M b) hi.top rDq
  have p1 := compile_decQLoop M N K R Q b h hk hn hr hq hs
  rw [decQC]
  exact (p0.seq p1).mono (layout_mono _ _ _ (le_decodeQueueBase M N K b h)) le_rfl le_rfl

set_option exponentiation.threshold 1000 in
theorem decodeQueueTime_concrete :
    decodeQueueTime (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 24) (2 ^ 66) ≤ 2 ^ 412 := by
  have hd := decodeTime_concrete
  unfold decodeQueueTime decodeQueueBodyTime
  calc
    _ ≤ (2 * 2 ^ 120 + 5) + 2 ^ 66 *
        (2 * 2 ^ 120 + (2 ^ 342 + appendAllowance (2 ^ 120)) + 4) + 2 := by gcongr
    _ ≤ 2 ^ 412 := by norm_num [appendAllowance]

theorem compile_decQC_concrete (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (hk : b rTBk + b rTKmB ≤ 2 ^ 16) (hn : b rTN ≤ 2 ^ 24) (hq : b rDqn ≤ 2 ^ 66) :
    Cert (MVM.compile decQC) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16)
        (Function.update (decodeQueueBase (2 ^ 120) b) rDq (2 ^ 66 * (2 ^ 24 * 2 ^ 16))))
      (2 ^ 412) :=
  (compile_decQC (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 24) (2 ^ 66) b h hk hn (by norm_num)
    hq (by norm_num)).mono le_rfl le_rfl decodeQueueTime_concrete

end AdvancedEncryption.ExpLUT.Prog.KeyTime
