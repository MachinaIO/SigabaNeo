import PE.Impl.ExpLUT.Prog.EncPrepareTime

/-! # The actual ciphertext framing program and its compiler clock -/
namespace AdvancedEncryption.ExpLUT.Prog.EncW
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.Prog

/-- The deterministic body of the frame emitter. -/
def outFrameBody : SigabaNeo.Tape.Prog 326 :=
  .seq (.prim (.snoc 0 true)) (.seq (.prim (.snocHead 0 2)) (.prim (.tail 2)))

/-- The same instructions as `frameCiphertextP`, viewed as a deterministic program. -/
def outFrameP : SigabaNeo.Tape.Prog 326 :=
  .seq (.seq (cp 1 0) (clr 0))
    (.seq (.seq (cp 2 1) (.seq (forN 3 1 outFrameBody)
      (.seq (.prim (.snoc 0 false)) (clr 2)))) (clr 1))

theorem time_frameCiphertextP (ℓ : Fin 326 → ℕ) :
    XProg.timeBoundT frameCiphertextP ℓ = timeBoundT outFrameP ℓ := by rfl

theorem len_frameCiphertextP (ℓ : Fin 326 → ℕ) :
    XProg.lenBoundT frameCiphertextP ℓ = lenBoundT outFrameP ℓ := by rfl

theorem ubp_outFrameBody (M : ℕ) : UBP outFrameBody M (10 * (M + 3)) (M + 2) := by
  have h := (ubp_prim (.snoc (0 : Fin 326) true) M).seq
    ((ubp_prim (.snocHead 0 2) (M + 1)).seq (ubp_prim0 (.tail 2) rfl (M + 1 + 1)))
  exact h.mono (by omega) (by omega)

set_option exponentiation.threshold 2000 in
theorem bounds_outFrameP : UBP outFrameP (2 ^ 99) (2 ^ 205) (2 ^ 101) := by
  have hp := (ubp_prim0 (.copy (1 : Fin 326) 0) rfl (2 ^ 99)).seq
    (ubp_prim0 (.clear 0) rfl (2 ^ 99))
  have hc := ubp_prim0 (.copy (2 : Fin 326) 1) rfl (2 ^ 99)
  have hcounter := ubp_prim0 (.copy (3 : Fin 326) 1) rfl (2 ^ 99)
  have hl := ubp_loop (3 : Fin 326) outFrameBody 2 _ ubp_outFrameBody (2 ^ 99)
  have he := (ubp_prim (.snoc (0 : Fin 326) false) (2 ^ 99 + 2 * 2 ^ 99)).seq
    (ubp_prim0 (.clear 2) rfl (2 ^ 99 + 2 * 2 ^ 99 + 1))
  have hlast := ubp_prim0 (.clear (1 : Fin 326)) rfl (2 ^ 99 + 2 * 2 ^ 99 + 1)
  have h := hp.seq ((hc.seq ((hcounter.seq hl).seq he)).seq hlast)
  have hb := h.mono (by norm_num : _ ≤ 2 ^ 205) (by norm_num : _ ≤ 2 ^ 101)
  intro ℓ hℓ
  exact hb ℓ hℓ

/-- Bounds for the emitter used by the compiled encryption machine. -/
theorem bounds_frameCiphertextP : XBound frameCiphertextP (2 ^ 99) (2 ^ 205) (2 ^ 101) := by
  intro ℓ hℓ
  rw [time_frameCiphertextP, len_frameCiphertextP]
  exact bounds_outFrameP ℓ hℓ

end AdvancedEncryption.ExpLUT.Prog.EncW
