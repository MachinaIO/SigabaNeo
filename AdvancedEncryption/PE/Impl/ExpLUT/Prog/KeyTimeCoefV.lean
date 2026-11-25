import PE.Impl.ExpLUT.Prog.KeyTimeLayout
/-! Runtime of the actual final-table coefficient loop. -/
set_option exponentiation.threshold 1000

namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM

/-- Uniform instruction allowance includes ring arithmetic and the simpler control instructions. -/
def evalInstructionTime (M N K : ℕ) : ℕ := operationBound M N K M + (2 * M + 5)

theorem compile_vBody (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (ha : N * K ≤ b rAl) (hp : N * K ≤ b rPw) :
    Cert (MVM.compile vBody) (layout M N K b) (layout M N K b)
      (3 * evalInstructionTime M N K + 1) := by
  let T := evalInstructionTime M N K
  have hop : operationBound M N K M ≤ T := by dsimp [T, evalInstructionTime]; omega
  have hs : 2 * M + 5 ≤ T := by dsimp [T, evalInstructionTime]; omega
  have hadd := (layout_op M N K b h .add rAl rAl rPw ha).mono le_rfl le_rfl hop
  have hnop := (compile_nop (layout M N K b) M h.top).mono le_rfl le_rfl
    (show 2 * (M + 1) + 3 ≤ T by omega)
  have hif := Cert.ifBit (tR rCp) hadd hnop
  have htl := (layout_tail M N K b h.top rCp).mono le_rfl le_rfl hs
  have hmul := (layout_op M N K b h .mul rPw rPw rMu hp).mono le_rfl le_rfl hop
  exact (hif.seq (htl.seq hmul)).mono le_rfl le_rfl (by simp; omega)

/-- Initialization, all iterations, and the final rotation of the real coefficient program. -/
theorem compile_coefVC (M N K R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (ha : N * K ≤ b rAl) (hp : N * K ≤ b rPw)
    (hz : b rZ ≤ b rAl) (hone : b rOne ≤ b rPw) (hw : b rTW ≤ b rCu)
    (hc : b rCu ≤ R) :
    Cert (MVM.compile coefVC) (layout M N K b) (layout M N K b)
      (4 * evalInstructionTime M N K + R * (2 * M + 3 * evalInstructionTime M N K + 5) + 2) := by
  let T := evalInstructionTime M N K
  have hs : 2 * M + 5 ≤ T := by dsimp [T, evalInstructionTime]; omega
  have h1 := (layout_copy M N K b h.top rAl rZ hz).mono le_rfl le_rfl hs
  have h2 := (layout_copy M N K b h.top rPw rOne hone).mono le_rfl le_rfl hs
  have h3 := (layout_copy M N K b h.top rCu rTW hw).mono le_rfl le_rfl hs
  have hpre := h1.seq (h2.seq h3)
  have hbody := compile_vBody M N K b h ha hp
  have hloop := rep_fixed rCu vBody (layout M N K b) M R
    (3 * evalInstructionTime M N K + 1) h.top (by simpa using hc) hbody
  have hrot := (layout_op M N K b h .rot rAl rAl rTb ha).mono le_rfl le_rfl
    (show operationBound M N K M ≤ T by dsimp [T, evalInstructionTime]; omega)
  exact (hpre.seq (hloop.seq hrot)).mono le_rfl le_rfl (by dsimp [T]; ring_nf; omega)

theorem evalInstructionTime_concrete :
    evalInstructionTime (2 ^ 120) (2 ^ 24) (2 ^ 16) ≤ 2 ^ 341 := by
  have h := operationBound_concrete (M := 2 ^ 120) (count := 2 ^ 120) le_rfl le_rfl
  unfold evalInstructionTime
  calc
    _ ≤ 2 ^ 340 + (2 * 2 ^ 120 + 5) := Nat.add_le_add_right h _
    _ ≤ 2 ^ 341 := by norm_num

/-- The final-table coefficient has at most W=2^22 iterations at the concrete parameters. -/
theorem compile_coefVC_concrete (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (ha : 2 ^ 24 * 2 ^ 16 ≤ b rAl) (hp : 2 ^ 24 * 2 ^ 16 ≤ b rPw)
    (hz : b rZ ≤ b rAl) (hone : b rOne ≤ b rPw) (hw : b rTW ≤ b rCu)
    (hc : b rCu ≤ 2 ^ 22) :
    Cert (MVM.compile coefVC) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) (2 ^ 368) := by
  have ht := compile_coefVC (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 22) b h ha hp hz hone hw hc
  have hi := evalInstructionTime_concrete
  apply ht.mono le_rfl le_rfl
  calc
    _ ≤ 4 * 2 ^ 341 + 2 ^ 22 * (2 * 2 ^ 120 + 3 * 2 ^ 341 + 5) + 2 := by gcongr
    _ ≤ 2 ^ 368 := by norm_num

/-- The real caller also copies the predicate stream into the coefficient scratch register. -/
theorem compile_cfV (M N K R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (ha : N * K ≤ b rAl) (hp : N * K ≤ b rPw)
    (hz : b rZ ≤ b rAl) (hone : b rOne ≤ b rPw) (hw : b rTW ≤ b rCu)
    (hc : b rCu ≤ R) (hstream : b rCs ≤ b rCp) :
    Cert (MVM.compile cfV) (layout M N K b) (layout M N K b)
      ((2 * M + 5) +
        (4 * evalInstructionTime M N K + R * (2 * M + 3 * evalInstructionTime M N K + 5) + 2)) :=
  (layout_copy M N K b h.top rCp rCs hstream).seq
    (compile_coefVC M N K R b h ha hp hz hone hw hc)

end AdvancedEncryption.ExpLUT.Prog.KeyTime
