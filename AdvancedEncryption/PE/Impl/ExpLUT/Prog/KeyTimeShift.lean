import PE.Impl.ExpLUT.Prog.KeyTimeGather

/-! Runtime of the actual queue automorphism and automorphic correction dot product. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM SigabaNeo.Tape.Prog

def autQueueBodyTime (M N K : ℕ) :=
  (2 * M + 5) + moveAllowance M + operationBound M N K M + appendAllowance M

theorem compile_autQBody (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b))
    (hz : b rZ ≤ b rQx) (hy : N * K ≤ b rQy) (hs : b rQa + N * K ≤ M) :
    Cert (MVM.compile autQBody) (layout M N K b)
      (layout M N K (Function.update b rQa (b rQa + N * K)))
      (autQueueBodyTime M N K) := by
  have p0 := layout_copy M N K b h.top rQx rZ hz
  have p1 := layout_moveR M N K b h rQx rQa (by decide)
  have p2 := layout_op_update M N K b h .aut rQy rQx rQk
  have hi := h.update_layout rQy (N * K) h.ring
  have p3 := layout_append_uniform M N K (Function.update b rQy (N * K)) hi.top
    rQa rQy (by simpa using hs)
  rw [autQBody]
  apply (p0.seq (p1.seq (p2.seq p3))).mono le_rfl _ (by unfold autQueueBodyTime; omega)
  apply layout_mono
  intro r
  by_cases ha : r = rQa
  · subst r; simp
  · by_cases hy' : r = rQy
    · subst r; simpa using hy
    · simp [Function.update_of_ne ha, Function.update_of_ne hy']

def autQueueTime (M N K R : ℕ) := R * (2 * M + autQueueBodyTime M N K + 4) + 2

/-- Conservative affine queue growth includes iteration zero. -/
theorem compile_autQC (M N K R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b))
    (hz : b rZ ≤ b rQx) (hy : N * K ≤ b rQy)
    (hr : b rQc ≤ R) (hs : b rQa + R * (N * K) ≤ M) :
    Cert (MVM.compile autQC) (layout M N K b)
      (layout M N K (Function.update b rQa (b rQa + R * (N * K))))
      (autQueueTime M N K R) := by
  let γ := fun j ↦ layout M N K (Function.update b rQa (b rQa + j * (N * K)))
  have hi (j : ℕ) (hj : j ≤ R) : RingInputs M N K (γ j) :=
    h.update_layout rQa _ (by
      have := Nat.mul_le_mul_right (N * K) hj
      omega)
  have hp : Cert (MVM.compile (.rep rQc autQBody)) (γ 0) (γ R)
      (R * (2 * M + autQueueBodyTime M N K + 4) + 2) := by
    apply rep_family rQc autQBody γ R (autQueueBodyTime M N K) _
      (by simp [γ]) (by simpa [γ] using hr)
    · intro j hj
      have hj' : j + 1 ≤ R := by omega
      have hsize : b rQa + (j + 1) * (N * K) ≤ M := by
        have := Nat.mul_le_mul_right (N * K) hj'; omega
      have hb := compile_autQBody M N K (Function.update b rQa (b rQa + j * (N * K)))
        (hi j (by omega)) (by simpa using hz) (by simpa using hy)
        (by simpa only [Function.update_self, Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hsize)
      simp only [Function.update_self, cap_reset] at hb
      rw [show b rQa + j * (N * K) + N * K = b rQa + (j + 1) * (N * K) by ring] at hb
      exact hb.mono (tailB_le (tR rQc) _) le_rfl le_rfl
    · intro j hj; exact supB_le_of (hi j (by omega)).top
    · intro j hj
      apply layout_mono
      intro r
      by_cases he : r = rQa
      · subst r; simp only [Function.update_self]
        exact Nat.add_le_add_left (Nat.mul_le_mul_right (N * K) hj) _
      · simp [Function.update_of_ne he]
  simpa [γ, autQC, autQueueTime] using hp

def autDotResult (N K R : ℕ) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (Function.update b 56 (b rQc)) rQa (b rQa + R * (N * K))

def autDotTime (M N K R : ℕ) :=
  2 * (2 * M + 5) + autQueueTime M N K R + innerProductTime M N K R

theorem compile_autDotC (M N K R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hc : QueueArithmeticCaps N K b)
    (hr : b rQc ≤ R) (hs : b rQa + R * (N * K) ≤ M) :
    Cert (MVM.compile autDotC) (layout M N K b)
      (layout M N K (autDotResult N K R b)) (autDotTime M N K R) := by
  let c := Function.update b 56 (b rQc)
  let d := autDotResult N K R b
  have hic : RingInputs M N K (layout M N K c) :=
    h.update_layout 56 _ (by simpa using h.top (tR rQc))
  have hid : RingInputs M N K (layout M N K d) := hic.update_layout rQa _ hs
  have p0 := layout_copy_update M N K b h.top 56 rQc
  have p1 := compile_autQC M N K R c hic (by simpa [c] using hc.zeroX)
    (by simpa [c] using hc.y) (by simpa [c] using hr) (by simpa [c] using hs)
  have p2 := layout_copy M N K d hid.top rQc 56 (by simp [d, autDotResult])
  have hcd : QueueArithmeticCaps N K d := by
    constructor
    · simpa [d, autDotResult] using hc.x
    · simpa [d, autDotResult] using hc.y
    · simpa [d, autDotResult] using hc.acc
    · simpa [d, autDotResult] using hc.zeroX
    · simpa [d, autDotResult] using hc.zeroY
  have p3 := compile_ipC M N K R d hid hcd (by simpa [d, autDotResult] using hr)
  rw [autDotC]
  exact (p0.seq (p1.seq (p2.seq p3))).mono le_rfl le_rfl (by unfold autDotTime; omega)

set_option exponentiation.threshold 1000 in
theorem autDotTime_concrete :
    autDotTime (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 66) ≤ 2 ^ 414 := by
  have ht := evalInstructionTime_concrete
  have ho := operationBound_concrete (M := 2 ^ 120) (count := 2 ^ 120) le_rfl le_rfl
  unfold autDotTime autQueueTime autQueueBodyTime innerProductTime innerProductBodyTime
  calc
    _ ≤ 2 * (2 * 2 ^ 120 + 5) +
        (2 ^ 66 * (2 * 2 ^ 120 + ((2 * 2 ^ 120 + 5) + moveAllowance (2 ^ 120) +
          2 ^ 340 + appendAllowance (2 ^ 120)) + 4) + 2) +
        (2 ^ 66 * (2 * 2 ^ 120 + (2 * (2 * 2 ^ 120 + 5) +
          2 * moveAllowance (2 ^ 120) + 2 * 2 ^ 341) + 4) + 2) := by gcongr
    _ ≤ 2 ^ 414 := by norm_num [moveAllowance, appendAllowance]

theorem compile_autDotC_concrete (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (hc : QueueArithmeticCaps (2 ^ 24) (2 ^ 16) b)
    (hr : b rQc ≤ 2 ^ 66) (hs : b rQa ≤ 2 ^ 106) :
    Cert (MVM.compile autDotC) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) (autDotResult (2 ^ 24) (2 ^ 16) (2 ^ 66) b))
      (2 ^ 414) := by
  apply (compile_autDotC (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 66) b h hc hr _).mono
    le_rfl le_rfl autDotTime_concrete
  calc
    _ ≤ 2 ^ 106 + 2 ^ 66 * (2 ^ 24 * 2 ^ 16) := Nat.add_le_add_right hs _
    _ ≤ 2 ^ 120 := by norm_num

end AdvancedEncryption.ExpLUT.Prog.KeyTime
