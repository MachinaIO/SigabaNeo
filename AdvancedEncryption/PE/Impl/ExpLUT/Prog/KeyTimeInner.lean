import PE.Impl.ExpLUT.Prog.KeyTimeDigitAcc
/-! Four digit accumulations inside the actual matrix-product inner body. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM

def digitTime (M N K R : ℕ) : ℕ :=
  6 * (2 * M + 5) + R * (2 * M + digitBodyTime M N K + 4) + 2

theorem digitResult_le (M N K : ℕ) (b : Fin 64 → ℕ)
    (ha : N * K ≤ b rDA) (hn : b rTK ≤ b MVM.rDn) : digitResult M N K b ≤ b := by
  intro r
  by_cases h0 : r = rDA <;> by_cases h1 : r = MVM.rDn <;> by_cases h2 : r = rUp <;>
    by_cases h3 : r = rEl <;> by_cases h4 : r = rDg <;> by_cases h5 : r = rPr <;>
    simp_all [digitResult, digitClean, digitBase, digitWide, Function.update_apply]

theorem layout_digAcc (M N K R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (ha : b rDA = N * K)
    (hz : b rZ ≤ N * K) (hk : b rTK ≤ R) (hn : b rTK ≤ b MVM.rDn) :
    Cert (MVM.compile digAccC) (layout M N K b) (layout M N K b) (digitTime M N K R) :=
  (compile_digAccC M N K R b h ha.le hz hk).mono le_rfl
    (layout_mono M N K (digitResult_le M N K b ha.ge hn)) le_rfl

/-- Register relations used by the four digit calls and their stream/accumulator copies. -/
structure InnerCaps (N K : ℕ) (b : Fin 64 → ℕ) : Prop where
  x0 : b rX0 = N * K
  x1 : b rX1 = N * K
  ac0 : b rAc0 = N * K
  ac1 : b rAc1 = N * K
  da : b rDA = N * K
  dx : N * K ≤ b rDX
  zero : b rZ ≤ N * K
  stream : b rDE = b rMAd
  counter : b rTK ≤ b MVM.rDn

def innerTime (M N K R : ℕ) : ℕ :=
  12 * (2 * M + 5) + 2 * moveAllowance M + 4 * digitTime M N K R

/-- Every copy and all four digit accumulations of the actual iBody are charged. -/
theorem compile_iBody (M N K R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hc : InnerCaps N K b) (hk : b rTK ≤ R) :
    Cert (MVM.compile iBody) (layout M N K b) (layout M N K b) (innerTime M N K R) := by
  have hd := layout_digAcc M N K R b h hc.da hc.zero hk hc.counter
  have h0 := layout_copy M N K b h.top rX0 rZ (by rw [hc.x0]; exact hc.zero)
  have h1 := layout_moveR M N K b h rX0 rCo0 (by decide)
  have h2 := layout_copy M N K b h.top rX1 rZ (by rw [hc.x1]; exact hc.zero)
  have h3 := layout_moveR M N K b h rX1 rCo1 (by decide)
  have h4 := layout_copy M N K b h.top rDE rMAd hc.stream.ge
  have h5 := layout_copy M N K b h.top rDA rAc0 (by rw [hc.da, hc.ac0])
  have h6 := layout_copy M N K b h.top rDX rX0 (by rw [hc.x0]; exact hc.dx)
  have h8 := layout_copy M N K b h.top rDX rX1 (by rw [hc.x1]; exact hc.dx)
  have h10 := layout_copy M N K b h.top rAc0 rDA (by rw [hc.da, hc.ac0])
  have h11 := layout_copy M N K b h.top rDA rAc1 (by rw [hc.da, hc.ac1])
  have h16 := layout_copy M N K b h.top rAc1 rDA (by rw [hc.da, hc.ac1])
  have h17 := layout_copy M N K b h.top rMAd rDE hc.stream.le
  rw [iBody]
  exact (h0.seq (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (hd.seq
    (h8.seq (hd.seq (h10.seq (h11.seq (h6.seq (hd.seq (h8.seq (hd.seq
    (h16.seq h17))))))))))))))))).mono le_rfl le_rfl (by unfold innerTime; omega)

set_option exponentiation.threshold 1000 in
theorem digitTime_concrete : digitTime (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) ≤ 2 ^ 363 := by
  have ht := evalInstructionTime_concrete
  unfold digitTime digitBodyTime
  calc
    _ ≤ 6 * (2 * 2 ^ 120 + 5) + 2 ^ 16 * (2 * 2 ^ 120 +
        ((2 * 2 ^ 120 + 5) + 2 * moveAllowance (2 ^ 120) + 3 * 2 ^ 341) + 4) + 2 := by gcongr
    _ ≤ 2 ^ 363 := by norm_num [moveAllowance]

set_option exponentiation.threshold 1000 in
theorem innerTime_concrete : innerTime (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) ≤ 2 ^ 366 := by
  have ht := digitTime_concrete
  unfold innerTime
  calc
    _ ≤ 12 * (2 * 2 ^ 120 + 5) + 2 * moveAllowance (2 ^ 120) + 4 * 2 ^ 363 := by gcongr
    _ ≤ 2 ^ 366 := by norm_num [moveAllowance]

/-- Conditional concrete bound for a real matrix-product inner step. -/
theorem compile_iBody_concrete (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (hc : InnerCaps (2 ^ 24) (2 ^ 16) b) (hk : b rTK ≤ 2 ^ 16) :
    Cert (MVM.compile iBody) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) (2 ^ 366) :=
  (compile_iBody (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) b h hc hk).mono le_rfl le_rfl innerTime_concrete

end AdvancedEncryption.ExpLUT.Prog.KeyTime
