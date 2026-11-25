import PE.Impl.ExpLUT.Prog.KeyTimeInner
/-! Actual column routines that call the four-accumulation inner kernel. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM

def columnTime (M N K D R : ℕ) : ℕ :=
  5 * (2 * M + 5) + 4 * moveAllowance M + R * (2 * M + innerTime M N K D + 4) + 2

/-- The real jBody includes both stream resets, the i-loop, and both output moves. -/
theorem compile_jBody (M N K D R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hi : InnerCaps N K b)
    (h0 : b rRo0 ≤ b rCo0) (h1 : b rRo1 ≤ b rCo1)
    (hk : b rTK ≤ D) (hci : b rTK ≤ b rCi) (hr : b rCi ≤ R) :
    Cert (MVM.compile jBody) (layout M N K b) (layout M N K b) (columnTime M N K D R) := by
  have p0 := layout_copy M N K b h.top rAc0 rZ (by rw [hi.ac0]; exact hi.zero)
  have p1 := layout_moveR M N K b h rAc0 rS (by decide)
  have p2 := layout_copy M N K b h.top rAc1 rZ (by rw [hi.ac1]; exact hi.zero)
  have p3 := layout_moveR M N K b h rAc1 rS (by decide)
  have p4 := layout_copy M N K b h.top rCo0 rRo0 h0
  have p5 := layout_copy M N K b h.top rCo1 rRo1 h1
  have p6 := layout_copy M N K b h.top rCi rTK hci
  have pre := p0.seq (p1.seq (p2.seq (p3.seq (p4.seq (p5.seq p6)))))
  have hb := compile_iBody M N K D b h hi hk
  have hl := rep_fixed rCi iBody (layout M N K b) M R (innerTime M N K D)
    h.top (by simpa using hr) hb
  have q0 := layout_moveR M N K b h rS2 rAc0 (by decide)
  have q1 := layout_moveR M N K b h rS2 rAc1 (by decide)
  rw [jBody, jPre, jPost]
  exact (pre.seq (hl.seq (q0.seq q1))).mono le_rfl le_rfl (by unfold columnTime; omega)

def inverseColumnTime (M N K D : ℕ) : ℕ :=
  3 * (2 * M + 5) + innerTime M N K D + 2 * moveAllowance M

/-- The actual inverse-gadget column resets two accumulators and reads the supplied X matrix. -/
theorem compile_gBody (M N K D : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hi : InnerCaps N K b)
    (hx : b rGX ≤ b rMAd) (hk : b rTK ≤ D) :
    Cert (MVM.compile gBody) (layout M N K b) (layout M N K b) (inverseColumnTime M N K D) := by
  have p0 := layout_copy M N K b h.top rAc0 rZ (by rw [hi.ac0]; exact hi.zero)
  have p1 := layout_copy M N K b h.top rAc1 rZ (by rw [hi.ac1]; exact hi.zero)
  have p2 := layout_copy M N K b h.top rMAd rGX hx
  have hb := compile_iBody M N K D b h hi hk
  have q0 := layout_moveR M N K b h rS2 rAc0 (by decide)
  have q1 := layout_moveR M N K b h rS2 rAc1 (by decide)
  rw [gBody]
  exact (p0.seq (p1.seq (p2.seq (hb.seq (q0.seq q1))))).mono le_rfl le_rfl
    (by unfold inverseColumnTime; omega)

set_option exponentiation.threshold 1000 in
theorem columnTime_concrete :
    columnTime (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) (4 * 2 ^ 16) ≤ 2 ^ 388 := by
  have hi := innerTime_concrete
  unfold columnTime
  calc
    _ ≤ 5 * (2 * 2 ^ 120 + 5) + 4 * moveAllowance (2 ^ 120) +
        (4 * 2 ^ 16) * (2 * 2 ^ 120 + 2 ^ 366 + 4) + 2 := by gcongr
    _ ≤ 2 ^ 388 := by norm_num [moveAllowance]

set_option exponentiation.threshold 1000 in
theorem inverseColumnTime_concrete :
    inverseColumnTime (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) ≤ 2 ^ 368 := by
  have hi := innerTime_concrete
  unfold inverseColumnTime
  calc
    _ ≤ 3 * (2 * 2 ^ 120 + 5) + 2 ^ 366 + 2 * moveAllowance (2 ^ 120) := by gcongr
    _ ≤ 2 ^ 368 := by norm_num [moveAllowance]

/-- The allowance permits a Ci cap of four-K, including caps left by matrix addition. -/
theorem compile_jBody_concrete (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (hi : InnerCaps (2 ^ 24) (2 ^ 16) b) (h0 : b rRo0 ≤ b rCo0) (h1 : b rRo1 ≤ b rCo1)
    (hk : b rTK ≤ 2 ^ 16) (hci : b rTK ≤ b rCi) (hr : b rCi ≤ 4 * 2 ^ 16) :
    Cert (MVM.compile jBody) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) (2 ^ 388) :=
  (compile_jBody (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) (4 * 2 ^ 16) b h hi h0 h1 hk hci hr).mono le_rfl le_rfl columnTime_concrete

theorem compile_gBody_concrete (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (hi : InnerCaps (2 ^ 24) (2 ^ 16) b) (hx : b rGX ≤ b rMAd) (hk : b rTK ≤ 2 ^ 16) :
    Cert (MVM.compile gBody) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) (2 ^ 368) :=
  (compile_gBody (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) b h hi hx hk).mono le_rfl le_rfl inverseColumnTime_concrete

end AdvancedEncryption.ExpLUT.Prog.KeyTime
