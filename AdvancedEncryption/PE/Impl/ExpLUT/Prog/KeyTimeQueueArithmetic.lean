import PE.Impl.ExpLUT.Prog.KeyTimeCoins

/-! Actual inner-product and gadget-recomposition kernels used by key proposals. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM

structure QueueArithmeticCaps (N K : ℕ) (b : Fin 64 → ℕ) : Prop where
  x : N * K ≤ b rQx
  y : N * K ≤ b rQy
  acc : N * K ≤ b rIa
  zeroX : b rZ ≤ b rQx
  zeroY : b rZ ≤ b rQy

def innerProductBodyTime (M N K : ℕ) :=
  2 * (2 * M + 5) + 2 * moveAllowance M + 2 * evalInstructionTime M N K

def innerProductTime (M N K R : ℕ) := R * (2 * M + innerProductBodyTime M N K + 4) + 2

theorem compile_ipBody (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hc : QueueArithmeticCaps N K b) :
    Cert (MVM.compile ipBody) (layout M N K b) (layout M N K b)
      (innerProductBodyTime M N K) := by
  have hop : operationBound M N K M ≤ evalInstructionTime M N K := by
    unfold evalInstructionTime; omega
  have p0 := layout_copy M N K b h.top rQx rZ hc.zeroX
  have p1 := layout_moveR M N K b h rQx rQa (by decide)
  have p2 := layout_copy M N K b h.top rQy rZ hc.zeroY
  have p3 := layout_moveR M N K b h rQy rQb (by decide)
  have p4 := (layout_op M N K b h .mul rQx rQx rQy hc.x).mono le_rfl le_rfl hop
  have p5 := (layout_op M N K b h .add rIa rIa rQx hc.acc).mono le_rfl le_rfl hop
  rw [ipBody]
  exact (p0.seq (p1.seq (p2.seq (p3.seq (p4.seq p5))))).mono le_rfl le_rfl
    (by unfold innerProductBodyTime; omega)

theorem compile_ipC (M N K R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hc : QueueArithmeticCaps N K b)
    (hr : b rQc ≤ R) :
    Cert (MVM.compile ipC) (layout M N K b) (layout M N K b) (innerProductTime M N K R) :=
  rep_fixed rQc ipBody (layout M N K b) M R (innerProductBodyTime M N K)
    h.top (by simpa using hr) (compile_ipBody M N K b h hc)

def recomposeBodyTime (M N K : ℕ) :=
  (2 * M + 5) + moveAllowance M + 3 * evalInstructionTime M N K

def recomposeTime (M N K R : ℕ) :=
  (2 * M + 5) + R * (2 * M + recomposeBodyTime M N K + 4) + 2

theorem compile_grBody (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hc : QueueArithmeticCaps N K b) :
    Cert (MVM.compile grBody) (layout M N K b) (layout M N K b) (recomposeBodyTime M N K) := by
  have hop : operationBound M N K M ≤ evalInstructionTime M N K := by
    unfold evalInstructionTime; omega
  have p0 := layout_copy M N K b h.top rQx rZ hc.zeroX
  have p1 := layout_moveR M N K b h rQx rQa (by decide)
  have p2 := (layout_op M N K b h .mul rQx rQx rQy hc.x).mono le_rfl le_rfl hop
  have p3 := (layout_op M N K b h .add rIa rIa rQx hc.acc).mono le_rfl le_rfl hop
  have p4 := (layout_op M N K b h .add rQy rQy rQy hc.y).mono le_rfl le_rfl hop
  rw [grBody]
  exact (p0.seq (p1.seq (p2.seq (p3.seq p4)))).mono le_rfl le_rfl
    (by unfold recomposeBodyTime; omega)

theorem compile_gadRecC (M N K R : ℕ) (b : Fin 64 → ℕ) (rOneW : Fin 64)
    (h : RingInputs M N K (layout M N K b)) (hc : QueueArithmeticCaps N K b)
    (hr : b rQc ≤ R) (ho : b rOneW ≤ b rQy) :
    Cert (MVM.compile (gadRecC rOneW)) (layout M N K b) (layout M N K b)
      (recomposeTime M N K R) := by
  have p0 := layout_copy M N K b h.top rQy rOneW ho
  have p1 := rep_fixed rQc grBody (layout M N K b) M R (recomposeBodyTime M N K)
    h.top (by simpa using hr) (compile_grBody M N K b h hc)
  rw [gadRecC]
  exact (p0.seq p1).mono le_rfl le_rfl (by unfold recomposeTime; omega)

def signedProductTime (M N K R : ℕ) :=
  6 * (2 * M + 5) + 2 * innerProductTime M N K R + operationBound M N K M

/-- Both signed dot products and the final subtraction, with exact output length NK. -/
theorem compile_signedDotC (M N K R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hc : QueueArithmeticCaps N K b)
    (hr : b rQc ≤ R) (hz : b rZ ≤ b rIa) (hs : b rIa ≤ b 13)
    (ha : b 10 ≤ b rQa) (hb : b 11 ≤ b rQb) (hn : b 12 ≤ b rQc) :
    Cert (MVM.compile signedDotC) (layout M N K b)
      (layout M N K (Function.update b rIa (N * K))) (signedProductTime M N K R) := by
  have p0 := layout_copy M N K b h.top rIa rZ hz
  have pi := compile_ipC M N K R b h hc hr
  have p2 := layout_copy M N K b h.top 13 rIa hs
  have p3 := layout_copy M N K b h.top rQa 10 ha
  have p4 := layout_copy M N K b h.top rQb 11 hb
  have p5 := layout_copy M N K b h.top rQc 12 hn
  have p8 := layout_op_update M N K b h .sub rIa 13 rIa
  rw [signedDotC]
  exact (p0.seq (pi.seq (p2.seq (p3.seq (p4.seq (p5.seq (p0.seq (pi.seq p8)))))))).mono
    le_rfl le_rfl (by unfold signedProductTime; omega)

set_option exponentiation.threshold 1000 in
theorem innerProductTime_concrete :
    innerProductTime (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 120) ≤ 2 ^ 466 := by
  have ht := evalInstructionTime_concrete
  unfold innerProductTime innerProductBodyTime
  calc
    _ ≤ 2 ^ 120 * (2 * 2 ^ 120 +
        (2 * (2 * 2 ^ 120 + 5) + 2 * moveAllowance (2 ^ 120) + 2 * 2 ^ 341) + 4) + 2 := by gcongr
    _ ≤ 2 ^ 466 := by norm_num [moveAllowance]

set_option exponentiation.threshold 1000 in
theorem recomposeTime_concrete :
    recomposeTime (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 120) ≤ 2 ^ 466 := by
  have ht := evalInstructionTime_concrete
  unfold recomposeTime recomposeBodyTime
  calc
    _ ≤ (2 * 2 ^ 120 + 5) + 2 ^ 120 * (2 * 2 ^ 120 +
        ((2 * 2 ^ 120 + 5) + moveAllowance (2 ^ 120) + 3 * 2 ^ 341) + 4) + 2 := by gcongr
    _ ≤ 2 ^ 466 := by norm_num [moveAllowance]

set_option exponentiation.threshold 1000 in
theorem signedProductTime_concrete :
    signedProductTime (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 120) ≤ 2 ^ 468 := by
  have hi := innerProductTime_concrete
  have ho := operationBound_concrete (M := 2 ^ 120) (count := 2 ^ 120) le_rfl le_rfl
  unfold signedProductTime
  calc
    _ ≤ 6 * (2 * 2 ^ 120 + 5) + 2 * 2 ^ 466 + 2 ^ 340 := by gcongr
    _ ≤ 2 ^ 468 := by norm_num

theorem prepared_queueArithmeticCaps : QueueArithmeticCaps (2 ^ 24) (2 ^ 16) (fun _ ↦ 2 ^ 120) := by
  constructor <;> norm_num

theorem cert_ipC_prepared : Cert (MVM.compile ipC) preparedBounds preparedBounds (2 ^ 466) :=
  (compile_ipC (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 120) (fun _ ↦ 2 ^ 120)
    preparedBounds_inputs prepared_queueArithmeticCaps le_rfl).mono le_rfl le_rfl
      innerProductTime_concrete

theorem cert_gadRecC_prepared (rOneW : Fin 64) :
    Cert (MVM.compile (gadRecC rOneW)) preparedBounds preparedBounds (2 ^ 466) :=
  (compile_gadRecC (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 120) (fun _ ↦ 2 ^ 120) rOneW
    preparedBounds_inputs prepared_queueArithmeticCaps le_rfl le_rfl).mono le_rfl le_rfl
      recomposeTime_concrete

theorem cert_signedDotC_prepared :
    Cert (MVM.compile signedDotC) preparedBounds
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) (Function.update (fun _ ↦ 2 ^ 120) rIa (2 ^ 24 * 2 ^ 16)))
      (2 ^ 468) :=
  (compile_signedDotC (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 120) (fun _ ↦ 2 ^ 120)
    preparedBounds_inputs prepared_queueArithmeticCaps le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl).mono
      le_rfl le_rfl signedProductTime_concrete

end AdvancedEncryption.ExpLUT.Prog.KeyTime
