import PE.Impl.ExpLUT.Prog.KeyTimeCorrection

/-! Runtime and exact output lengths for actual gadget digit generation. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM SigabaNeo.Tape.Prog

def digitQueueResult (N K R : ℕ) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (Function.update b rZq (R * (N * K))) rU R

def digitQueueBodyTime (M N K : ℕ) := operationBound M N K M + 2 * appendAllowance M

theorem compile_digQBody (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hb : b rB1 = 1)
    (ht : N * K ≤ b rTd) (hs : b rZq + N * K ≤ M) (hu : b rU + 1 ≤ M) :
    Cert (MVM.compile digQBody) (layout M N K b)
      (layout M N K (Function.update (Function.update b rZq (b rZq + N * K)) rU (b rU + 1)))
      (digitQueueBodyTime M N K) := by
  let c := Function.update b rTd (N * K)
  let d := Function.update c rZq (b rZq + N * K)
  have hc := h.update_layout rTd (N * K) h.ring
  have hd := hc.update_layout rZq _ hs
  have p0 := layout_op_update M N K b h .dig rTd rY rU
  have p1 := layout_append_uniform M N K c hc.top rZq rTd (by simpa [c] using hs)
  have p2 := layout_append_uniform M N K d hd.top rU rB1 (by simpa [d, c, hb] using hu)
  rw [digQBody]
  apply (p0.seq (p1.seq p2)).mono le_rfl _ (by unfold digitQueueBodyTime; omega)
  apply layout_mono
  intro r
  by_cases h0 : r = rU
  · subst r; simp [d, c, hb]
  · by_cases h1 : r = rZq
    · subst r; simp [d, c]
    · by_cases h2 : r = rTd
      · subst r; simpa [d, c] using ht
      · simp [d, c, Function.update_of_ne h0, Function.update_of_ne h1, Function.update_of_ne h2]

theorem compile_digQLoop (M N K R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hb : b rB1 = 1)
    (ht : N * K ≤ b rTd) (hr : b rCK ≤ R) (hu : R ≤ M) (hs : R * (N * K) ≤ M) :
    Cert (MVM.compile (.rep rCK digQBody))
      (layout M N K (digitQueueResult N K 0 b))
      (layout M N K (digitQueueResult N K R b))
      (R * (2 * M + digitQueueBodyTime M N K + 4) + 2) := by
  let γ := fun j ↦ layout M N K (digitQueueResult N K j b)
  have hi (j : ℕ) (hj : j ≤ R) : RingInputs M N K (γ j) :=
    (h.update_layout rZq _ ((Nat.mul_le_mul_right _ hj).trans hs)).update_layout rU _ (hj.trans hu)
  apply rep_family rCK digQBody γ R (digitQueueBodyTime M N K) _
    (by simp [γ, digitQueueResult]) (by simpa [γ, digitQueueResult] using hr)
  · intro j hj
    have hj' : j + 1 ≤ R := by omega
    have hjm := hj'.trans hu
    have hjs := (Nat.mul_le_mul_right (N * K) hj').trans hs
    have hp := compile_digQBody M N K (digitQueueResult N K j b) (hi j (by omega))
      (by simpa [digitQueueResult] using hb) (by simpa [digitQueueResult] using ht)
      (by simpa [digitQueueResult, Nat.add_mul] using hjs)
      (by simpa [digitQueueResult] using hjm)
    have he : Function.update
        (Function.update (digitQueueResult N K j b) rZq
          (digitQueueResult N K j b rZq + N * K)) rU
          (digitQueueResult N K j b rU + 1) = digitQueueResult N K (j + 1) b := by
      funext r
      by_cases h0 : r = rU <;> by_cases h1 : r = rZq <;>
        simp_all [digitQueueResult, Function.update_apply, Nat.add_mul]
    rw [he] at hp
    exact hp.mono (tailB_le (tR rCK) _) le_rfl le_rfl
  · intro j hj; exact supB_le_of (hi j (by omega)).top
  · intro j hj
    apply layout_mono
    intro r
    by_cases h0 : r = rU
    · subst r; simpa [digitQueueResult] using hj
    · by_cases h1 : r = rZq
      · subst r; simpa [digitQueueResult] using Nat.mul_le_mul_right (N * K) hj
      · simp [digitQueueResult, Function.update_of_ne h0, Function.update_of_ne h1]

def digitQueueTime (M N K R : ℕ) :=
  2 * (2 * M + 5) + (R * (2 * M + digitQueueBodyTime M N K + 4) + 2)

theorem compile_digQC (M N K R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hb : b rB1 = 1)
    (ht : N * K ≤ b rTd) (hr : b rCK ≤ R) (hu : R ≤ M) (hs : R * (N * K) ≤ M) :
    Cert (MVM.compile digQC) (layout M N K b)
      (layout M N K (digitQueueResult N K R b)) (digitQueueTime M N K R) := by
  have p0 := layout_clear_update M N K b h.top rZq
  have p1 := layout_clear_update M N K (Function.update b rZq 0)
    (h.update_layout rZq 0 (by omega)).top rU
  have p2 := compile_digQLoop M N K R b h hb ht hr hu hs
  simp only [digitQueueResult, zero_mul] at p2
  rw [digQC]
  have ht' : (2 * M + 5) + ((2 * M + 5) +
      (R * (2 * M + digitQueueBodyTime M N K + 4) + 2)) ≤ digitQueueTime M N K R := by
    unfold digitQueueTime; omega
  exact (p0.seq (p1.seq p2)).mono le_rfl le_rfl ht'

theorem compile_decomposeC (M N K R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hb : b rB1 = 1)
    (ht : N * K ≤ b rTd) (hy : N * K ≤ b rY)
    (hr : b rCK ≤ R) (hu : R ≤ M) (hs : R * (N * K) ≤ M) :
    Cert (MVM.compile decomposeC) (layout M N K b)
      (layout M N K (digitQueueResult N K R b))
      (operationBound M N K M + digitQueueTime M N K R) := by
  have p0 := layout_op M N K b h .sub rY rQx rIa hy
  have p1 := compile_digQC M N K R b h hb ht hr hu hs
  exact p0.seq p1

theorem digitQueueResult_inputs (M N K R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hu : R ≤ M) (hs : R * (N * K) ≤ M) :
    RingInputs M N K (layout M N K (digitQueueResult N K R b)) :=
  (h.update_layout rZq _ hs).update_layout rU _ hu

theorem digitQueueResult_le (N K R : ℕ) (b : Fin 64 → ℕ)
    (hu : R ≤ b rU) (hs : R * (N * K) ≤ b rZq) : digitQueueResult N K R b ≤ b := by
  intro r
  by_cases h0 : r = rU
  · subst r; simpa [digitQueueResult] using hu
  · by_cases h1 : r = rZq
    · subst r; simpa [digitQueueResult] using hs
    · simp [digitQueueResult, Function.update_of_ne h0, Function.update_of_ne h1]

def decomposeRowTime (M N K R : ℕ) :=
  3 * (2 * M + 5) + 2 * moveAllowance M +
    (operationBound M N K M + digitQueueTime M N K R) + appendAllowance M

theorem compile_decRowBodyC (M N K R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hb : b rB1 = 1)
    (hx : b rZ ≤ b rQx) (ha : b rZ ≤ b rIa)
    (ht : N * K ≤ b rTd) (hy : N * K ≤ b rY)
    (hk : b rQk ≤ R) (hc : b rQk ≤ b rCK)
    (hu : R ≤ b rU) (hz : R * (N * K) ≤ b rZq)
    (hs : b rDq + R * (N * K) ≤ M) :
    Cert (MVM.compile decRowBodyC) (layout M N K b)
      (layout M N K (Function.update b rDq (b rDq + R * (N * K))))
      (decomposeRowTime M N K R) := by
  let c := Function.update b rCK (b rQk)
  let d := digitQueueResult N K R c
  have hc' := h.update_layout rCK _ (by simpa using h.top (tR rQk))
  have huM : R ≤ M := hu.trans (by simpa using h.top (tR rU))
  have hzM : R * (N * K) ≤ M := hz.trans (by simpa using h.top (tR rZq))
  have hd := digitQueueResult_inputs M N K R c hc' huM hzM
  have p0 := layout_copy M N K b h.top rQx rZ hx
  have p1 := layout_moveR M N K b h rQx rQa (by decide)
  have p2 := layout_copy M N K b h.top rIa rZ ha
  have p3 := layout_moveR M N K b h rIa rQb (by decide)
  have p4 := layout_copy_update M N K b h.top rCK rQk
  have pl : Cert (MVM.compile decRowLoadC) (layout M N K b) (layout M N K c)
      (3 * (2 * M + 5) + 2 * moveAllowance M) := by
    exact (p0.seq (p1.seq (p2.seq (p3.seq p4)))).mono le_rfl le_rfl (by omega)
  have pd := compile_decomposeC M N K R c hc' (by simpa [c] using hb)
    (by simpa [c] using ht) (by simpa [c] using hy) (by simpa [c] using hk) huM hzM
  have pa := layout_append_uniform M N K d hd.top rDq rZq
    (by simpa [d, c, digitQueueResult] using hs)
  have hdle : d ≤ b := (digitQueueResult_le N K R c
    (by simpa [c] using hu) (by simpa [c] using hz)).trans (cap_update_le b rCK _ hc)
  rw [decRowBodyC]
  apply (pl.seq (pd.seq pa)).mono le_rfl _ (by unfold decomposeRowTime; omega)
  apply layout_mono
  intro r
  by_cases he : r = rDq
  · subst r; simp [d, c, digitQueueResult]
  · simp only [Function.update_of_ne he]; exact hdle r

set_option exponentiation.threshold 1000 in
theorem decomposeTime_concrete :
    operationBound (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 120) +
      digitQueueTime (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) ≤ 2 ^ 360 := by
  have ho := operationBound_concrete (M := 2 ^ 120) (count := 2 ^ 120) le_rfl le_rfl
  unfold digitQueueTime digitQueueBodyTime
  calc
    _ ≤ 2 ^ 340 + (2 * (2 * 2 ^ 120 + 5) +
        (2 ^ 16 * (2 * 2 ^ 120 + (2 ^ 340 + 2 * appendAllowance (2 ^ 120)) + 4) + 2)) := by gcongr
    _ ≤ 2 ^ 360 := by norm_num [appendAllowance]

def decomposeRowsTime (M N K R Q : ℕ) :=
  (2 * M + 5) + (Q * (2 * M + decomposeRowTime M N K R + 4) + 2)

theorem compile_decRowsC (M N K R Q : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hb : b rB1 = 1)
    (hx : b rZ ≤ b rQx) (ha : b rZ ≤ b rIa)
    (ht : N * K ≤ b rTd) (hy : N * K ≤ b rY)
    (hk : b rQk ≤ R) (hc : b rQk ≤ b rCK)
    (hu : R ≤ b rU) (hz : R * (N * K) ≤ b rZq)
    (hq : b rQc ≤ Q) (hs : Q * (R * (N * K)) ≤ M) :
    Cert (MVM.compile decRowsC) (layout M N K b)
      (layout M N K (Function.update b rDq (Q * (R * (N * K)))))
      (decomposeRowsTime M N K R Q) := by
  let γ := fun j ↦ layout M N K (Function.update b rDq (j * (R * (N * K))))
  have hi (j : ℕ) (hj : j ≤ Q) : RingInputs M N K (γ j) :=
    h.update_layout rDq _ ((Nat.mul_le_mul_right _ hj).trans hs)
  have pl : Cert (MVM.compile (.rep rQc decRowBodyC)) (γ 0) (γ Q)
      (Q * (2 * M + decomposeRowTime M N K R + 4) + 2) := by
    apply rep_family rQc decRowBodyC γ Q (decomposeRowTime M N K R) _
      (by simp [γ]) (by simpa [γ] using hq)
    · intro j hj
      have hj' : j + 1 ≤ Q := by omega
      have hjs := (Nat.mul_le_mul_right (R * (N * K)) hj').trans hs
      have hp := compile_decRowBodyC M N K R
        (Function.update b rDq (j * (R * (N * K)))) (hi j (by omega))
        (by simpa using hb) (by simpa using hx) (by simpa using ha)
        (by simpa using ht) (by simpa using hy) (by simpa using hk)
        (by simpa using hc) (by simpa using hu) (by simpa using hz)
        (by simpa only [Function.update_self, Nat.add_mul, Nat.one_mul] using hjs)
      simp only [Function.update_self, cap_reset] at hp
      rw [show j * (R * (N * K)) + R * (N * K) = (j + 1) * (R * (N * K)) by ring] at hp
      exact hp.mono (tailB_le (tR rQc) _) le_rfl le_rfl
    · intro j hj; exact supB_le_of (hi j (by omega)).top
    · intro j hj
      apply layout_mono
      intro r
      by_cases he : r = rDq
      · subst r; simpa using Nat.mul_le_mul_right (R * (N * K)) hj
      · simp [Function.update_of_ne he]
  simp only [γ, zero_mul] at pl
  have p0 := layout_clear_update M N K b h.top rDq
  exact p0.seq pl

set_option exponentiation.threshold 1000 in
theorem decomposeRowsTime_concrete :
    decomposeRowsTime (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) (2 ^ 22) ≤ 2 ^ 386 := by
  have hd := decomposeTime_concrete
  have hr : decomposeRowTime (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) ≤ 2 ^ 362 := by
    unfold decomposeRowTime
    calc
      _ ≤ 3 * (2 * 2 ^ 120 + 5) + 2 * moveAllowance (2 ^ 120) +
          2 ^ 360 + appendAllowance (2 ^ 120) := by gcongr
      _ ≤ 2 ^ 362 := by norm_num [moveAllowance, appendAllowance]
  unfold decomposeRowsTime
  calc
    _ ≤ (2 * 2 ^ 120 + 5) + (2 ^ 22 * (2 * 2 ^ 120 + 2 ^ 362 + 4) + 2) := by gcongr
    _ ≤ 2 ^ 386 := by norm_num

theorem compile_decRowsC_concrete (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (hb : b rB1 = 1) (hx : b rZ ≤ b rQx) (ha : b rZ ≤ b rIa)
    (ht : 2 ^ 24 * 2 ^ 16 ≤ b rTd) (hy : 2 ^ 24 * 2 ^ 16 ≤ b rY)
    (hk : b rQk ≤ 2 ^ 16) (hc : b rQk ≤ b rCK)
    (hu : 2 ^ 16 ≤ b rU) (hz : 2 ^ 16 * (2 ^ 24 * 2 ^ 16) ≤ b rZq)
    (hq : b rQc ≤ 2 ^ 22) :
    Cert (MVM.compile decRowsC) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16)
        (Function.update b rDq (2 ^ 22 * (2 ^ 16 * (2 ^ 24 * 2 ^ 16))))) (2 ^ 386) :=
  (compile_decRowsC (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) (2 ^ 22) b h hb hx ha ht hy
    hk hc hu hz hq (by norm_num)).mono le_rfl le_rfl decomposeRowsTime_concrete

end AdvancedEncryption.ExpLUT.Prog.KeyTime
