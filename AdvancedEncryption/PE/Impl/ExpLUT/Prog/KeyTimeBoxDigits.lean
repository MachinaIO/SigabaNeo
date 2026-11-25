import PE.Impl.ExpLUT.Prog.KeyTimeAcceptInit
/-! The actual high-digit range test, with its increasing digit-position counter. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM

def testDigitTime (M N K : ℕ) := 4 * operationBound M N K M + appendAllowance M

theorem compile_tstBody (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hb : b rB1 = 1)
    (hd : N * K ≤ b rTd) (hf : N * K ≤ b rFa) (hs : b rDi + 1 ≤ M) :
    Cert (MVM.compile tstBody) (layout M N K b)
      (layout M N K (Function.update b rDi (b rDi + 1))) (testDigitTime M N K) := by
  have p0 := layout_op M N K b h .dig rTd rTa rDi hd
  have p1 := layout_op M N K b h .add rFa rFa rTd hf
  have p2 := layout_op M N K b h .dig rTd rTnb rDi hd
  have p3 := layout_append_uniform M N K b h.top rDi rB1 (by simpa [hb] using hs)
  rw [hb] at p3
  exact (p0.seq (p1.seq (p2.seq (p1.seq p3)))).mono le_rfl le_rfl
    (by unfold testDigitTime; omega)

def testLoopTime (M N K R : ℕ) := R * (2 * M + testDigitTime M N K + 4) + 2

theorem compile_tstLoop (M N K R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hb : b rB1 = 1)
    (hd : N * K ≤ b rTd) (hf : N * K ≤ b rFa)
    (hr : b rDc ≤ R) (hs : b rDi + R ≤ M) :
    Cert (MVM.compile (.rep rDc tstBody)) (layout M N K b)
      (layout M N K (Function.update b rDi (b rDi + R))) (testLoopTime M N K R) := by
  let γ := fun j ↦ layout M N K (Function.update b rDi (b rDi + j))
  have hi (j : ℕ) (hj : j ≤ R) : RingInputs M N K (γ j) :=
    h.update_layout rDi _ (by omega)
  apply rep_family rDc tstBody γ R (testDigitTime M N K) _
    (by simp [γ]) (by simpa using hr)
  · intro j hj
    have hp := compile_tstBody M N K (Function.update b rDi (b rDi + j))
      (hi j (by omega)) (by simpa using hb) (by simpa using hd) (by simpa using hf)
      (by simp only [Function.update_self]; omega)
    simp only [Function.update_self, cap_reset] at hp
    have he : b rDi + j + 1 = b rDi + (j + 1) := by omega
    rw [he] at hp
    exact hp.mono (tailB_le (tR rDc) _) le_rfl le_rfl
  · intro j hj; exact SigabaNeo.Tape.Prog.supB_le_of (hi j (by omega)).top
  · intro j hj
    apply layout_mono
    intro r
    by_cases he : r = rDi
    · subst r; simp only [Function.update_self]; omega
    · simp [Function.update_of_ne he]

def testTime (M N K R : ℕ) :=
  2 * operationBound M N K M + 2 * (2 * M + 5) + testLoopTime M N K R

/-- The two counter copies install the actual starting position and iteration bound. -/
theorem compile_tstC (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hb : b rB1 = 1)
    (hd : N * K ≤ b rTd) (hf : N * K ≤ b rFa)
    (ha : N * K ≤ b rTa) (hn : N * K ≤ b rTnb)
    (hs : b rTBk + b rTKB ≤ b rDi) (hc : b rTKB ≤ b rDc) :
    Cert (MVM.compile tstC) (layout M N K b) (layout M N K b)
      (testTime M N K (b rTKB)) := by
  let c := Function.update b rDi (b rTBk)
  let d := Function.update c rDc (b rTKB)
  have hi := h.update_layout rDi (b rTBk) (by simpa using h.top (tR rTBk))
  have hj := hi.update_layout rDc (b rTKB) (by simpa using h.top (tR rTKB))
  have p0 := layout_op M N K b h .add rTa rTx rRR ha
  have p1 := layout_op M N K b h .sub rTnb rRR rTx hn
  have p2 := layout_copy_update M N K b h.top rDi rTBk
  have p3 := layout_copy_update M N K c hi.top rDc rTKB
  have he : c rTKB = b rTKB := by simp [c]
  rw [he] at p3
  have p4 := compile_tstLoop M N K (b rTKB) d hj
    (by simpa [d, c] using hb) (by simpa [d, c] using hd) (by simpa [d, c] using hf)
    (by simp [d]) (by simpa [d, c] using hs.trans (show b rDi ≤ M by simpa using h.top (tR rDi)))
  have ho : Function.update d rDi (d rDi + b rTKB) ≤ b := by
    intro r
    by_cases hdi : r = rDi
    · subst r; simpa [d, c] using hs
    · by_cases hdc : r = rDc
      · subst r; simpa [d, c] using hc
      · simp [Function.update_of_ne hdi, Function.update_of_ne hdc, d, c]
  exact (p0.seq (p1.seq (p2.seq (p3.seq p4)))).mono le_rfl (layout_mono _ _ _ ho)
    (by unfold testTime; omega)

theorem layout_eqb_update (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (f s t : Fin 64)
    (hd : ¬(f = s ∨ f = t ∨ s = t)) :
    Cert (MVM.compile (.eqb f s t)) (layout M N K b)
      (layout M N K (Function.update b f 1)) (2 * M + 5) := by
  rw [layout_update]
  exact compile_eqb_cert f s t hd _ M h.top

theorem compile_ballTestC (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hb : b rB1 = 1)
    (hd : N * K ≤ b rTd) (hf : N * K ≤ b rFa)
    (ha : N * K ≤ b rTa) (hn : N * K ≤ b rTnb)
    (hs : b rTBk + b rTKB ≤ b rDi) (hc : b rTKB ≤ b rDc) :
    Cert (MVM.compile ballTestC) (layout M N K b)
      (layout M N K (Function.update b rTx 1))
      (testTime M N K (b rTKB) + (2 * M + 5)) :=
  (compile_tstC M N K b h hb hd hf ha hn hs hc).seq
    (layout_eqb_update M N K b h rTx rFa rZ (by decide))

set_option exponentiation.threshold 1000 in
theorem testTime_concrete (R : ℕ) (hr : R ≤ 2 ^ 16) :
    testTime (2 ^ 120) (2 ^ 24) (2 ^ 16) R + (2 * 2 ^ 120 + 5) ≤ 2 ^ 360 := by
  have hop := operationBound_concrete (M := 2 ^ 120) (count := 2 ^ 120) le_rfl le_rfl
  unfold testTime testLoopTime testDigitTime
  calc
    _ ≤ 2 * 2 ^ 340 + 2 * (2 * 2 ^ 120 + 5) +
        (2 ^ 16 * (2 * 2 ^ 120 + (4 * 2 ^ 340 + appendAllowance (2 ^ 120)) + 4) + 2) +
        (2 * 2 ^ 120 + 5) := by gcongr
    _ ≤ 2 ^ 360 := by norm_num [appendAllowance]

theorem compile_ballTestC_Dc (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b))
    (hb : b rB1 = 1) (hd : Dc.N * Dc.K ≤ b rTd) (hf : Dc.N * Dc.K ≤ b rFa)
    (ha : Dc.N * Dc.K ≤ b rTa) (hn : Dc.N * Dc.K ≤ b rTnb)
    (hs : b rTBk + b rTKB ≤ b rDi) (hc : b rTKB ≤ b rDc) (hr : b rTKB ≤ 2 ^ 16) :
    Cert (MVM.compile ballTestC) (layout (2 ^ 120) Dc.N Dc.K b)
      (layout (2 ^ 120) Dc.N Dc.K (Function.update b rTx 1)) (2 ^ 360) := by
  apply (compile_ballTestC _ _ _ b h hb hd hf ha hn hs hc).mono le_rfl le_rfl
  have hn : Dc.N = 2 ^ 24 := by norm_num [Dc, Dims.N, Params.en]
  have hk : Dc.K = 2 ^ 16 := by norm_num [Dc, Params.Kc]
  rw [hn, hk]; exact testTime_concrete _ hr

end AdvancedEncryption.ExpLUT.Prog.KeyTime
