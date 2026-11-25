import PE.Impl.ExpLUT.Prog.KeyTimeBoxDigits
/-! Complete streaming range test and rejection latch, on the actual family program. -/
set_option exponentiation.threshold 1000
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM

structure BoxCaps (N K : ℕ) (b : Fin 64 → ℕ) : Prop where
  digit : N * K ≤ b rTd
  acc : N * K ≤ b rFa
  positive : N * K ≤ b rTa
  negative : N * K ≤ b rTnb
  span : b rTBk + b rTKB ≤ b rDi
  counter : b rTKB ≤ b rDc
  high : b rTKB ≤ 2 ^ 16
  zeroInput : b rZ ≤ b rTx
  zeroAcc : b rZ ≤ b rFa
  flag : 1 ≤ b rTx
  latch : b rB1 ≤ b rDq

theorem compile_boxBodyC_Dc (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hb : b rB1 = 1) (hc : BoxCaps Dc.N Dc.K b) :
    Cert (MVM.compile boxBodyC) (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K b) (2 ^ 362) := by
  have p0 := layout_copy (2 ^ 120) Dc.N Dc.K b h.top rTx rZ hc.zeroInput
  have p1 := layout_moveR (2 ^ 120) Dc.N Dc.K b h rTx rQa (by decide)
  have p2 := layout_copy (2 ^ 120) Dc.N Dc.K b h.top rFa rZ hc.zeroAcc
  have p3 := (compile_ballTestC_Dc b h hb hc.digit hc.acc hc.positive hc.negative
    hc.span hc.counter hc.high).mono le_rfl
      (layout_mono _ _ _ (cap_update_le b rTx 1 hc.flag)) le_rfl
  have pn := (compile_nop _ (2 ^ 120) h.top).mono le_rfl le_rfl
    (show 2 * (2 ^ 120 + 1) + 3 ≤ 2 * 2 ^ 120 + 5 by omega)
  have pc := layout_copy (2 ^ 120) Dc.N Dc.K b h.top rDq rB1 hc.latch
  have p4 := Cert.ifBit (tR rTx) pn pc
  exact ((p0.seq (p1.seq p2)).seq (p3.seq p4)).mono le_rfl le_rfl
    (by norm_num [moveAllowance])

theorem compile_boxQueueC_Dc (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hb : b rB1 = 1) (hc : BoxCaps Dc.N Dc.K b) (hr : b rQc ≤ 2 ^ 66) :
    Cert (MVM.compile boxQueueC) (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K b) (2 ^ 430) := by
  have p0 := (layout_clear_update (2 ^ 120) Dc.N Dc.K b h.top rDq).mono le_rfl
    (layout_mono _ _ _ (cap_update_le b rDq 0 (Nat.zero_le _))) le_rfl
  have p1 := rep_fixed rQc boxBodyC (layout (2 ^ 120) Dc.N Dc.K b) (2 ^ 120) (2 ^ 66)
    (2 ^ 362) h.top (by simpa using hr) (compile_boxBodyC_Dc b h hb hc)
  exact (p0.seq p1).mono le_rfl le_rfl (by norm_num)

theorem compile_boxFamilyC_Dc (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hb : b rB1 = 1) (hc : BoxCaps Dc.N Dc.K b) (hr : b rQc ≤ 2 ^ 66) :
    Cert (MVM.compile boxFamilyC) (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K (Function.update b rTx 1)) (2 ^ 432) := by
  have p0 := compile_boxQueueC_Dc b h hb hc hr
  have p1 := (layout_clear_update (2 ^ 120) Dc.N Dc.K b h.top rQb).mono le_rfl
    (layout_mono _ _ _ (cap_update_le b rQb 0 (Nat.zero_le _))) le_rfl
  have p2 := layout_eqb_update (2 ^ 120) Dc.N Dc.K b h rTx rDq rQb (by decide)
  exact (p0.seq (p1.seq p2)).mono le_rfl le_rfl (by norm_num)

end AdvancedEncryption.ExpLUT.Prog.KeyTime
