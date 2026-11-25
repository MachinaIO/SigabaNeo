import PE.Impl.ExpLUT.Prog.KeyTimeGrowth
/-! Growing counter bounds for the actual complement-bit loop in alpha coefficients. -/
set_option exponentiation.threshold 1000
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM SigabaNeo.Tape.Prog

def bitBodyTime (M N K : ℕ) : ℕ :=
  2 * evalInstructionTime M N K + 1 + (4 * M + 6) * (2 * M + 5)

theorem compile_bitBody (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hE : N * K ≤ b rE)
    (hc : b rCnt + b rCnt ≤ M) :
    Cert (MVM.compile bitBody) (layout M N K b)
      (layout M N K (Function.update b rCnt (b rCnt + b rCnt))) (bitBodyTime M N K) := by
  let T := evalInstructionTime M N K
  have hop : operationBound M N K M ≤ T := by dsimp [T, evalInstructionTime]; omega
  have hs : 2 * M + 5 ≤ T := by dsimp [T, evalInstructionTime]; omega
  have hrho := (layout_op M N K b h .rho rE rE rCnt hE).mono le_rfl le_rfl hop
  have hnop := (compile_nop (layout M N K b) M h.top).mono le_rfl le_rfl
    (show 2 * (M + 1) + 3 ≤ T by omega)
  have hif := Cert.ifBit (tR rCp) hnop hrho
  have htl := (layout_tail M N K b h.top rCp).mono le_rfl le_rfl hs
  have happ := layout_append M N K b h.top rCnt rCnt hc
  apply (hif.seq (htl.seq happ)).mono le_rfl le_rfl
  have hcnt : b rCnt ≤ M := by simpa using h.top (tR rCnt)
  simp only [max_self]
  dsimp [bitBodyTime, T]
  nlinarith

/-- The counter cap doubles each iteration; the entire loop keeps all other register caps. -/
theorem compile_bitLoop (M N K e : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hE : N * K ≤ b rE)
    (hcb : b rCb ≤ e) (hpow : 2 ^ e ≤ M) :
    Cert (MVM.compile (.rep rCb bitBody))
      (layout M N K (Function.update b rCnt 1))
      (layout M N K (Function.update b rCnt (2 ^ e)))
      (e * (2 * M + bitBodyTime M N K + 4) + 2) := by
  let γ := fun j ↦ layout M N K (Function.update b rCnt (2 ^ j))
  have hi (j : ℕ) (hj : j ≤ e) : RingInputs M N K (γ j) := by
    apply h.update_layout rCnt (2 ^ j)
    apply le_trans _ hpow
    gcongr
  apply rep_family rCb bitBody γ e (bitBodyTime M N K) _ (by simp [γ])
    (by simpa [layout_register] using hcb)
  · intro j hj
    have hp : 2 ^ (j + 1) ≤ M := by
      apply le_trans _ hpow
      gcongr
      omega
    have hb := compile_bitBody M N K (Function.update b rCnt (2 ^ j)) (hi j (by omega))
      (by simpa using hE) (by simp only [Function.update_self]; simpa [pow_succ, Nat.mul_two] using hp)
    have he : Function.update (Function.update b rCnt (2 ^ j)) rCnt
        ((Function.update b rCnt (2 ^ j)) rCnt + (Function.update b rCnt (2 ^ j)) rCnt) =
        Function.update b rCnt (2 ^ (j + 1)) := by
      funext r
      simp only [Function.update_apply]
      split_ifs <;> simp_all [pow_succ, Nat.mul_two]
    rw [he] at hb
    exact hb.mono (tailB_le (tR rCb) _) le_rfl le_rfl
  · intro j hj; exact supB_le_of (hi j (by omega)).top
  · intro j hj
    apply layout_mono
    intro r
    by_cases hr : r = rCnt
    · subst r; simp only [Function.update_self]; gcongr
    · simp [Function.update_of_ne hr]

/-- The inner loop in the concrete alpha coefficient consumes fourteen bits. -/
theorem compile_bitLoop_concrete (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (hE : 2 ^ 24 * 2 ^ 16 ≤ b rE) (hcb : b rCb ≤ 14) :
    Cert (MVM.compile (.rep rCb bitBody))
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) (Function.update b rCnt 1))
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) (Function.update b rCnt (2 ^ 14))) (2 ^ 348) := by
  have hb := compile_bitLoop (2 ^ 120) (2 ^ 24) (2 ^ 16) 14 b h hE hcb (by norm_num)
  have hi := evalInstructionTime_concrete
  apply hb.mono le_rfl le_rfl
  unfold bitBodyTime
  calc
    _ ≤ 14 * (2 * 2 ^ 120 + (2 * 2 ^ 341 + 1 + (4 * 2 ^ 120 + 6) * (2 * 2 ^ 120 + 5)) + 4) + 2 := by
      gcongr
    _ ≤ 2 ^ 348 := by norm_num

end AdvancedEncryption.ExpLUT.Prog.KeyTime
