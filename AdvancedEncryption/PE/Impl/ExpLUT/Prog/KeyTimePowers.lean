import PE.Impl.ExpLUT.Prog.KeyTimeDigitsTail
/-! Actual gadget-power generation and repeated coefficient-row concatenation. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM SigabaNeo.Tape.Prog

def repeatAppendTime (M R : ℕ) := R * (2 * M + appendAllowance M + 4) + 2

theorem compile_repAppC (M N K R : ℕ) (b : Fin 64 → ℕ) (c d s : Fin 64)
    (hcd : c ≠ d) (hsd : s ≠ d)
    (h : RingInputs M N K (layout M N K b)) (hr : b c ≤ R)
    (hs : b d + R * b s ≤ M) :
    Cert (MVM.compile (repAppC c d s)) (layout M N K b)
      (layout M N K (Function.update b d (b d + R * b s))) (repeatAppendTime M R) := by
  let γ := fun j ↦ layout M N K (Function.update b d (b d + j * b s))
  have hi (j : ℕ) (hj : j ≤ R) : RingInputs M N K (γ j) :=
    h.update_layout d _ (by have := Nat.mul_le_mul_right (b s) hj; omega)
  have hp : Cert (MVM.compile (.rep c (.app d s))) (γ 0) (γ R)
      (R * (2 * M + appendAllowance M + 4) + 2) := by
    apply rep_family c (.app d s) γ R (appendAllowance M) _
      (by simp [γ]) (by simpa [γ, Function.update_of_ne hcd] using hr)
    · intro j hj
      have hjs : b d + (j + 1) * b s ≤ M := by
        have := Nat.mul_le_mul_right (b s) (by omega : j + 1 ≤ R); omega
      have ha := layout_append_uniform M N K (Function.update b d (b d + j * b s))
        (hi j (by omega)).top d s
        (by simpa [Function.update_of_ne hsd, Nat.add_mul, Nat.add_assoc] using hjs)
      simp only [Function.update_self, Function.update_of_ne hsd, cap_reset] at ha
      rw [show b d + j * b s + b s = b d + (j + 1) * b s by ring] at ha
      exact ha.mono (tailB_le (tR c) _) le_rfl le_rfl
    · intro j hj; exact supB_le_of (hi j (by omega)).top
    · intro j hj
      apply layout_mono
      intro r
      by_cases he : r = d
      · subst r; simp only [Function.update_self]
        exact Nat.add_le_add_left (Nat.mul_le_mul_right (b s) hj) _
      · simp [Function.update_of_ne he]
  simpa only [γ, zero_mul, add_zero, Function.update_eq_self, repAppC, repeatAppendTime] using hp

def powersBodyTime (M N K : ℕ) := appendAllowance M + operationBound M N K M

theorem compile_powersBody (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (h7 : b 7 = N * K)
    (hs : b 4 + N * K ≤ M) :
    Cert (MVM.compile powersBody) (layout M N K b)
      (layout M N K (Function.update b 4 (b 4 + N * K))) (powersBodyTime M N K) := by
  have p0 := layout_append_uniform M N K b h.top 4 7 (by simpa [h7] using hs)
  rw [h7] at p0
  have hi := h.update_layout 4 _ hs
  have p1 := layout_op M N K (Function.update b 4 (b 4 + N * K)) hi .add 7 7 7
    (by simpa using h7.ge)
  exact p0.seq p1

def powersTime (M N K R : ℕ) :=
  (2 * M + 5) + (R * (2 * M + powersBodyTime M N K + 4) + 2)

theorem compile_powersC (M N K R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (h7 : b 7 = N * K)
    (hr : b 2 ≤ R) (hs : R * (N * K) ≤ M) :
    Cert (MVM.compile powersC) (layout M N K b)
      (layout M N K (Function.update b 4 (R * (N * K)))) (powersTime M N K R) := by
  let γ := fun j ↦ layout M N K (Function.update b 4 (j * (N * K)))
  have hi (j : ℕ) (hj : j ≤ R) : RingInputs M N K (γ j) :=
    h.update_layout 4 _ ((Nat.mul_le_mul_right _ hj).trans hs)
  have pl : Cert (MVM.compile (.rep 2 powersBody)) (γ 0) (γ R)
      (R * (2 * M + powersBodyTime M N K + 4) + 2) := by
    apply rep_family 2 powersBody γ R (powersBodyTime M N K) _
      (by simp [γ]) (by simpa [γ] using hr)
    · intro j hj
      have hjs := (Nat.mul_le_mul_right (N * K) (by omega : j + 1 ≤ R)).trans hs
      have hp := compile_powersBody M N K (Function.update b 4 (j * (N * K)))
        (hi j (by omega)) (by simpa using h7)
        (by simpa only [Function.update_self, Nat.add_mul, Nat.one_mul] using hjs)
      simp only [Function.update_self, cap_reset] at hp
      rw [show j * (N * K) + N * K = (j + 1) * (N * K) by ring] at hp
      exact hp.mono (tailB_le (tR 2) _) le_rfl le_rfl
    · intro j hj; exact supB_le_of (hi j (by omega)).top
    · intro j hj
      apply layout_mono
      intro r
      by_cases he : r = 4
      · subst r; simpa using Nat.mul_le_mul_right (N * K) hj
      · simp [Function.update_of_ne he]
  simp only [γ, zero_mul] at pl
  exact (layout_clear_update M N K b h.top 4).seq pl

def negativeCoeffResult (N K H : ℕ) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (Function.update (Function.update (Function.update b 2 H) 6 (K * (N * K)))
    7 (K * (N * K) + K * (N * K))) 4 (H * (K * (N * K) + K * (N * K)))

def negativeCoeffTime (M N K H : ℕ) :=
  (32 * K + 4) * (2 * M + 5) + powersTime M N K K +
    (32 * (K * (N * K)) + 4) * (2 * M + 5) + appendAllowance M +
    2 * (2 * M + 5) + (32 * H + 4) * (2 * M + 5) + repeatAppendTime M H

theorem compile_negativeCoeffC (M N K H : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hb : b rB1 = 1) (h7 : b 7 = N * K)
    (hh : H ≤ M) (hr : K * (N * K) + K * (N * K) ≤ M)
    (hs : H * (K * (N * K) + K * (N * K)) ≤ M) :
    Cert (MVM.compile (negativeCoeffC N K H)) (layout M N K b)
      (layout M N K (negativeCoeffResult N K H b)) (negativeCoeffTime M N K H) := by
  let c := Function.update b 2 K
  let d := Function.update c 4 (K * (N * K))
  let e := Function.update d 6 (K * (N * K))
  let f := Function.update e 4 (K * (N * K) + K * (N * K))
  let g := Function.update f 7 (K * (N * K) + K * (N * K))
  let v := Function.update g 4 0
  let w := Function.update v 2 H
  have hrow : K * (N * K) ≤ M := by omega
  have hc := h.update_layout 2 K h.width
  have hd := hc.update_layout 4 _ hrow
  have he := hd.update_layout 6 _ hrow
  have hf := he.update_layout 4 _ hr
  have hg := hf.update_layout 7 _ hr
  have hv := hg.update_layout 4 0 (by omega)
  have hw := hv.update_layout 2 H hh
  have p0 := layout_nat_update M N K b h 2 rB1 (by decide) K hb h.width
  have p1 := compile_powersC M N K K c hc (by simpa [c] using h7) (by simp [c]) hrow
  have p2 := layout_nat_update M N K d hd 6 rB1 (by decide) (K * (N * K))
    (by simpa [d, c] using hb) hrow
  have p3 := layout_append_uniform M N K e he.top 4 6 (by simpa [e, d] using hr)
  have p4 := layout_copy_update M N K f hf.top 7 4
  have p5 := layout_clear_update M N K g hg.top 4
  have p6 := layout_nat_update M N K v hv 2 rB1 (by decide) H
    (by simpa [v, g, f, e, d, c] using hb) hh
  have p7 := compile_repAppC M N K H w 2 4 7 (by decide) (by decide) hw
    (by simp [w]) (by simpa [w, v, g] using hs)
  have out : Function.update w 4 (w 4 + H * w 7) = negativeCoeffResult N K H b := by
    funext r
    by_cases h0 : r = 2 <;> by_cases h1 : r = 4 <;>
      by_cases h2 : r = 6 <;> by_cases h3 : r = 7 <;>
        simp_all [w, v, g, f, e, d, c, negativeCoeffResult]
  rw [out] at p7
  have ht : (32 * K + 4) * (2 * M + 5) + (powersTime M N K K +
      ((32 * (K * (N * K)) + 4) * (2 * M + 5) + (appendAllowance M +
      ((2 * M + 5) + ((2 * M + 5) + ((32 * H + 4) * (2 * M + 5) + repeatAppendTime M H)))))) ≤
      negativeCoeffTime M N K H := by unfold negativeCoeffTime; omega
  rw [negativeCoeffC]
  exact (p0.seq (p1.seq (p2.seq (p3.seq (p4.seq (p5.seq (p6.seq p7))))))).mono le_rfl le_rfl ht

set_option exponentiation.threshold 1000 in
theorem negativeCoeffTime_concrete :
    negativeCoeffTime (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 6) ≤ 2 ^ 364 := by
  have ho := operationBound_concrete (M := 2 ^ 120) (count := 2 ^ 120) le_rfl le_rfl
  unfold negativeCoeffTime powersTime powersBodyTime
  calc
    _ ≤ (32 * 2 ^ 16 + 4) * (2 * 2 ^ 120 + 5) +
      ((2 * 2 ^ 120 + 5) + (2 ^ 16 * (2 * 2 ^ 120 +
        (appendAllowance (2 ^ 120) + 2 ^ 340) + 4) + 2)) +
      (32 * (2 ^ 16 * (2 ^ 24 * 2 ^ 16)) + 4) * (2 * 2 ^ 120 + 5) +
      appendAllowance (2 ^ 120) + 2 * (2 * 2 ^ 120 + 5) +
      (32 * 2 ^ 6 + 4) * (2 * 2 ^ 120 + 5) + repeatAppendTime (2 ^ 120) (2 ^ 6) := by gcongr
    _ ≤ 2 ^ 364 := by norm_num [appendAllowance, repeatAppendTime]

theorem compile_negativeCoeffC_concrete (H : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (hb : b rB1 = 1) (h7 : b 7 = 2 ^ 24 * 2 ^ 16) (hh : H ≤ 2 ^ 6) :
    Cert (MVM.compile (negativeCoeffC (2 ^ 24) (2 ^ 16) H))
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) (negativeCoeffResult (2 ^ 24) (2 ^ 16) H b))
      (2 ^ 364) := by
  have hs : H * (2 ^ 16 * (2 ^ 24 * 2 ^ 16) + 2 ^ 16 * (2 ^ 24 * 2 ^ 16)) ≤ 2 ^ 120 := by
    calc
      _ ≤ 2 ^ 6 * (2 ^ 16 * (2 ^ 24 * 2 ^ 16) + 2 ^ 16 * (2 ^ 24 * 2 ^ 16)) :=
        Nat.mul_le_mul_right _ hh
      _ ≤ 2 ^ 120 := by norm_num
  apply (compile_negativeCoeffC (2 ^ 120) (2 ^ 24) (2 ^ 16) H b h hb h7
    (hh.trans (by norm_num)) (by norm_num) hs).mono le_rfl le_rfl
  apply le_trans _ negativeCoeffTime_concrete
  unfold negativeCoeffTime repeatAppendTime
  gcongr

theorem negativeCoeffResult_inputs (M N K H : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hh : H ≤ M)
    (hr : K * (N * K) + K * (N * K) ≤ M)
    (hs : H * (K * (N * K) + K * (N * K)) ≤ M) :
    RingInputs M N K (layout M N K (negativeCoeffResult N K H b)) :=
  (((h.update_layout 2 H hh).update_layout 6 _ (by omega)).update_layout 7 _ hr).update_layout 4 _ hs

theorem negativeCoeffResult_other (N K H : ℕ) (b : Fin 64 → ℕ) (r : Fin 64)
    (h2 : r ≠ 2) (h4 : r ≠ 4) (h6 : r ≠ 6) (h7 : r ≠ 7) :
    negativeCoeffResult N K H b r = b r := by
  simp [negativeCoeffResult, Function.update_of_ne h2, Function.update_of_ne h4,
    Function.update_of_ne h6, Function.update_of_ne h7]

end AdvancedEncryption.ExpLUT.Prog.KeyTime
