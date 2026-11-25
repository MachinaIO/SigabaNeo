import PE.Impl.ExpLUT.Prog.KeyTimeBitLoop
/-! Runtime of the actual nested alpha-table coefficient loops. -/
set_option exponentiation.threshold 1000
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM

def alphaEntryTime (M N K e : ℕ) : ℕ :=
  5 * evalInstructionTime M N K + e * (2 * M + bitBodyTime M N K + 4) + 2

/-- One table entry resets its doubling counter, processes e bits, then updates two ring words. -/
theorem compile_uBody (M N K e : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b))
    (ha : N * K ≤ b rAl) (hp : N * K ≤ b rPw) (he : b rPw ≤ b rE)
    (hbit : b rBit1 = 1) (hte : b rTe ≤ b rCb) (hcb : b rCb ≤ e)
    (hcnt : 2 ^ e ≤ b rCnt) :
    Cert (MVM.compile uBody) (layout M N K b) (layout M N K b) (alphaEntryTime M N K e) := by
  let T := evalInstructionTime M N K
  let b1 := Function.update b rCnt 1
  have hop : operationBound M N K M ≤ T := by dsimp [T, evalInstructionTime]; omega
  have hs : 2 * M + 5 ≤ T := by dsimp [T, evalInstructionTime]; omega
  have hpow : 2 ^ e ≤ M := hcnt.trans (by simpa using h.top (tR rCnt))
  have hone : 1 ≤ M := by have := pow_pos (by decide : 0 < (2 : ℕ)) e; omega
  have hi : RingInputs M N K (layout M N K b1) := h.update_layout rCnt 1 hone
  have h1 := (layout_copy M N K b h.top rE rPw he).mono le_rfl le_rfl hs
  have h2 := layout_copy_update M N K b h.top rCnt rBit1
  rw [hbit] at h2
  have h3 := (layout_copy M N K b1 hi.top rCb rTe (by simpa [b1] using hte)).mono le_rfl le_rfl hs
  have hb := compile_bitLoop M N K e b h (hp.trans he) hcb hpow
  have hout : layout M N K (Function.update b rCnt (2 ^ e)) ≤ layout M N K b := by
    apply layout_mono
    intro r
    by_cases hr : r = rCnt
    · subst r; simpa using hcnt
    · simp [Function.update_of_ne hr]
  have hloop := hb.mono le_rfl hout le_rfl
  have hadd := (layout_op M N K b h .add rAl rAl rE ha).mono le_rfl le_rfl hop
  have hmul := (layout_op M N K b h .mul rPw rPw rMu hp).mono le_rfl le_rfl hop
  exact (h1.seq (h2.seq (h3.seq (hloop.seq (hadd.seq hmul))))).mono le_rfl le_rfl
    (by dsimp [alphaEntryTime, T] at *; omega)

/-- Both nested loops and the final multiplication/rotation of the real alpha coefficient. -/
theorem compile_coefAC (M N K e R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b))
    (ha : N * K ≤ b rAl) (hp : N * K ≤ b rPw) (he : b rPw ≤ b rE)
    (hbit : b rBit1 = 1) (hte : b rTe ≤ b rCb) (hcb : b rCb ≤ e)
    (hcnt : 2 ^ e ≤ b rCnt) (hz : b rZ ≤ b rAl) (hone : b rOne ≤ b rPw)
    (hw : b rTW ≤ b rCu) (hc : b rCu ≤ R) :
    Cert (MVM.compile coefAC) (layout M N K b) (layout M N K b)
      (5 * evalInstructionTime M N K + R * (2 * M + alphaEntryTime M N K e + 4) + 2) := by
  let T := evalInstructionTime M N K
  have hs : 2 * M + 5 ≤ T := by dsimp [T, evalInstructionTime]; omega
  have hop : operationBound M N K M ≤ T := by dsimp [T, evalInstructionTime]; omega
  have h1 := (layout_copy M N K b h.top rAl rZ hz).mono le_rfl le_rfl hs
  have h2 := (layout_copy M N K b h.top rPw rOne hone).mono le_rfl le_rfl hs
  have h3 := (layout_copy M N K b h.top rCu rTW hw).mono le_rfl le_rfl hs
  have hpre := h1.seq (h2.seq h3)
  have hbody := compile_uBody M N K e b h ha hp he hbit hte hcb hcnt
  have hloop := rep_fixed rCu uBody (layout M N K b) M R (alphaEntryTime M N K e)
    h.top (by simpa using hc) hbody
  have hmul := (layout_op M N K b h .mul rAl rAl rXc ha).mono le_rfl le_rfl hop
  have hrot := (layout_op M N K b h .rot rAl rAl rTb ha).mono le_rfl le_rfl hop
  exact (hpre.seq (hloop.seq (hmul.seq hrot))).mono le_rfl le_rfl (by omega)

theorem alphaEntryTime_concrete :
    alphaEntryTime (2 ^ 120) (2 ^ 24) (2 ^ 16) 14 ≤ 2 ^ 349 := by
  have h := evalInstructionTime_concrete
  unfold alphaEntryTime bitBodyTime
  calc
    _ ≤ 5 * 2 ^ 341 + 14 * (2 * 2 ^ 120 +
        (2 * 2 ^ 341 + 1 + (4 * 2 ^ 120 + 6) * (2 * 2 ^ 120 + 5)) + 4) + 2 := by gcongr
    _ ≤ 2 ^ 349 := by norm_num

/-- Conditional bound for all W alpha-table entries, including their fourteen-bit inner loops. -/
theorem compile_coefAC_concrete (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (ha : 2 ^ 24 * 2 ^ 16 ≤ b rAl) (hp : 2 ^ 24 * 2 ^ 16 ≤ b rPw) (he : b rPw ≤ b rE)
    (hbit : b rBit1 = 1) (hte : b rTe ≤ b rCb) (hcb : b rCb ≤ 14)
    (hcnt : 2 ^ 14 ≤ b rCnt) (hz : b rZ ≤ b rAl) (hone : b rOne ≤ b rPw)
    (hw : b rTW ≤ b rCu) (hc : b rCu ≤ 2 ^ 22) :
    Cert (MVM.compile coefAC) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) (2 ^ 375) := by
  have ht := compile_coefAC (2 ^ 120) (2 ^ 24) (2 ^ 16) 14 (2 ^ 22) b h
    ha hp he hbit hte hcb hcnt hz hone hw hc
  have hi := evalInstructionTime_concrete
  have hu := alphaEntryTime_concrete
  apply ht.mono le_rfl le_rfl
  calc
    _ ≤ 5 * 2 ^ 341 + 2 ^ 22 * (2 * 2 ^ 120 + 2 ^ 349 + 4) + 2 := by gcongr
    _ ≤ 2 ^ 375 := by norm_num

/-- The alpha coefficient caller first copies the actual predicate stream. -/
theorem compile_cfA (M N K e R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b))
    (ha : N * K ≤ b rAl) (hp : N * K ≤ b rPw) (he : b rPw ≤ b rE)
    (hbit : b rBit1 = 1) (hte : b rTe ≤ b rCb) (hcb : b rCb ≤ e)
    (hcnt : 2 ^ e ≤ b rCnt) (hz : b rZ ≤ b rAl) (hone : b rOne ≤ b rPw)
    (hw : b rTW ≤ b rCu) (hc : b rCu ≤ R) (hstream : b rCs ≤ b rCp) :
    Cert (MVM.compile cfA) (layout M N K b) (layout M N K b)
      ((2 * M + 5) +
        (5 * evalInstructionTime M N K + R * (2 * M + alphaEntryTime M N K e + 4) + 2)) :=
  (layout_copy M N K b h.top rCp rCs hstream).seq
    (compile_coefAC M N K e R b h ha hp he hbit hte hcb hcnt hz hone hw hc)

end AdvancedEncryption.ExpLUT.Prog.KeyTime
