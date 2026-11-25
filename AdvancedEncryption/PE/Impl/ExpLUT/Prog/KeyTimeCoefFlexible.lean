import PE.Impl.ExpLUT.Prog.KeyTimeChain
/-! Coefficient certificates that use actual resets of shared matrix scratch registers. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM

/-- Cb is overwritten before the bit loop; its old cap need not be at most e. -/
theorem compile_uBody_flexible (M N K e : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b))
    (ha : N * K ≤ b rAl) (hp : N * K ≤ b rPw) (he : b rPw ≤ b rE)
    (hbit : b rBit1 = 1) (hte : b rTe ≤ b rCb) (ht : b rTe ≤ e)
    (hcnt : 2 ^ e ≤ b rCnt) :
    Cert (MVM.compile uBody) (layout M N K b) (layout M N K b)
      (alphaEntryTime M N K e) := by
  let b1 := Function.update b rCnt 1
  let bc := Function.update b rCb (b rTe)
  have hpow : 2 ^ e ≤ M := hcnt.trans (by simpa using h.top (tR rCnt))
  have hone : 1 ≤ M := by
    have := pow_pos (by decide : 0 < (2 : ℕ)) e
    omega
  have hi1 : RingInputs M N K (layout M N K b1) := h.update_layout rCnt 1 hone
  have hic : RingInputs M N K (layout M N K bc) :=
    h.update_layout rCb (b rTe) (by simpa using h.top (tR rTe))
  have p0 := layout_copy M N K b h.top rE rPw he
  have p1 := layout_copy_update M N K b h.top rCnt rBit1
  rw [hbit] at p1
  have p2 := layout_copy_update M N K b1 hi1.top rCb rTe
  have heq : Function.update b1 rCb (b1 rTe) = Function.update bc rCnt 1 := by
    funext r
    by_cases h0 : r = rCnt <;> by_cases h1 : r = rCb <;>
      simp_all [b1, bc]
  rw [heq] at p2
  have hb := compile_bitLoop M N K e bc hic (by simpa [bc] using hp.trans he)
    (by simpa [bc] using ht) hpow
  have hout : Function.update bc rCnt (2 ^ e) ≤ b :=
    (cap_update_le bc rCnt (2 ^ e) (by simpa [bc] using hcnt)).trans
      (cap_update_le b rCb (b rTe) hte)
  have hl := hb.mono le_rfl (layout_mono M N K hout) le_rfl
  have hop : operationBound M N K M ≤ evalInstructionTime M N K := by
    unfold evalInstructionTime; omega
  have pa := (layout_op M N K b h .add rAl rAl rE ha).mono le_rfl le_rfl hop
  have pm := (layout_op M N K b h .mul rPw rPw rMu hp).mono le_rfl le_rfl hop
  have hs : 2 * M + 5 ≤ evalInstructionTime M N K := by unfold evalInstructionTime; omega
  rw [uBody]
  exact (p0.seq (p1.seq (p2.seq (hl.seq (pa.seq pm))))).mono le_rfl le_rfl
    (by unfold alphaEntryTime; omega)

/-- The prefix overwrites Pw and Cu with an actual ring word and the table length. -/
def coefficientBase (N K : ℕ) (b : Fin 64 → ℕ) : Fin 64 → ℕ :=
  Function.update (Function.update b rPw (N * K)) rCu (b rTW)

theorem coefficientBase_inputs (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) :
    RingInputs M N K (layout M N K (coefficientBase N K b)) :=
  (h.update_layout rPw (N * K) h.ring).update_layout rCu (b rTW)
    (by simpa using h.top (tR rTW))

theorem coefficientBase_le (N K : ℕ) (b : Fin 64 → ℕ)
    (hp : N * K ≤ b rPw) (hw : b rTW ≤ b rCu) : coefficientBase N K b ≤ b :=
  (cap_update_le (Function.update b rPw (N * K)) rCu (b rTW)
    (by simpa using hw)).trans (cap_update_le b rPw (N * K) hp)

theorem compile_coefPre_exact (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hz : b rZ ≤ b rAl) (hone : b rOne ≤ N * K) :
    Cert (MVM.compile coefPre) (layout M N K b) (layout M N K (coefficientBase N K b))
      (3 * (2 * M + 5)) := by
  have p0 := layout_copy M N K b h.top rAl rZ hz
  have p1 := layout_copy_cap M N K b h.top rPw rOne (N * K) hone
  have p2 := layout_copy_update M N K (Function.update b rPw (N * K))
    (h.update_layout rPw (N * K) h.ring).top rCu rTW
  simp only [Function.update_of_ne (by decide : rTW ≠ rPw)] at p2
  rw [coefPre]
  exact (p0.seq (p1.seq p2)).mono le_rfl le_rfl (by omega)

def alphaCoefficientTime (M N K e R : ℕ) :=
  5 * evalInstructionTime M N K + R * (2 * M + alphaEntryTime M N K e + 4) + 2

/-- Shared Pw/Cu/Cb caps may be large on entry; the real copies set the loop bounds. -/
theorem compile_coefAC_flexible (M N K e R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b))
    (ha : N * K ≤ b rAl) (hp : N * K ≤ b rPw) (he : N * K ≤ b rE)
    (hbit : b rBit1 = 1) (hte : b rTe ≤ b rCb) (ht : b rTe ≤ e)
    (hcnt : 2 ^ e ≤ b rCnt) (hz : b rZ ≤ b rAl) (hone : b rOne ≤ N * K)
    (hw : b rTW ≤ b rCu) (hc : b rTW ≤ R) :
    Cert (MVM.compile coefAC) (layout M N K b) (layout M N K b)
      (alphaCoefficientTime M N K e R) := by
  let c := coefficientBase N K b
  have hi := coefficientBase_inputs M N K b h
  have hb := compile_uBody_flexible M N K e c hi
    (by simpa [c, coefficientBase] using ha) (by simp [c, coefficientBase])
    (by simpa [c, coefficientBase] using he) (by simpa [c, coefficientBase] using hbit)
    (by simpa [c, coefficientBase] using hte) (by simpa [c, coefficientBase] using ht)
    (by simpa [c, coefficientBase] using hcnt)
  have hl := rep_fixed rCu uBody (layout M N K c) M R (alphaEntryTime M N K e)
    hi.top (by simpa [c, coefficientBase] using hc) hb
  have hop : operationBound M N K M ≤ evalInstructionTime M N K := by
    unfold evalInstructionTime; omega
  have pm := (layout_op M N K c hi .mul rAl rAl rXc
    (by simpa [c, coefficientBase] using ha)).mono le_rfl le_rfl hop
  have pr := (layout_op M N K c hi .rot rAl rAl rTb
    (by simpa [c, coefficientBase] using ha)).mono le_rfl le_rfl hop
  have pre := compile_coefPre_exact M N K b h hz hone
  have hs : 2 * M + 5 ≤ evalInstructionTime M N K := by unfold evalInstructionTime; omega
  rw [coefAC]
  exact (pre.seq (hl.seq (pm.seq pr))).mono le_rfl
    (layout_mono M N K (coefficientBase_le N K b hp hw))
    (by unfold alphaCoefficientTime; omega)

def valueCoefficientTime (M N K R : ℕ) :=
  4 * evalInstructionTime M N K + R * (2 * M + 3 * evalInstructionTime M N K + 5) + 2

/-- The final-table coefficient also resets its formerly large matrix-loop counter. -/
theorem compile_coefVC_flexible (M N K R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b))
    (ha : N * K ≤ b rAl) (hp : N * K ≤ b rPw)
    (hz : b rZ ≤ b rAl) (hone : b rOne ≤ N * K)
    (hw : b rTW ≤ b rCu) (hc : b rTW ≤ R) :
    Cert (MVM.compile coefVC) (layout M N K b) (layout M N K b)
      (valueCoefficientTime M N K R) := by
  let c := coefficientBase N K b
  have hi := coefficientBase_inputs M N K b h
  have hb := compile_vBody M N K c hi (by simpa [c, coefficientBase] using ha)
    (by simp [c, coefficientBase])
  have hl := rep_fixed rCu vBody (layout M N K c) M R
    (3 * evalInstructionTime M N K + 1) hi.top (by simpa [c, coefficientBase] using hc) hb
  have hop : operationBound M N K M ≤ evalInstructionTime M N K := by
    unfold evalInstructionTime; omega
  have pr := (layout_op M N K c hi .rot rAl rAl rTb
    (by simpa [c, coefficientBase] using ha)).mono le_rfl le_rfl hop
  have pre := compile_coefPre_exact M N K b h hz hone
  have hs : 2 * M + 5 ≤ evalInstructionTime M N K := by unfold evalInstructionTime; omega
  rw [coefVC]
  exact (pre.seq (hl.seq pr)).mono le_rfl
    (layout_mono M N K (coefficientBase_le N K b hp hw))
    (by unfold valueCoefficientTime; ring_nf; omega)

/-- Compatible entry bounds for coefficient evaluation after a matrix routine. -/
structure CoefficientCaps (N K e R : ℕ) (b : Fin 64 → ℕ) : Prop where
  accumulator : N * K ≤ b rAl
  power : N * K ≤ b rPw
  entry : N * K ≤ b rE
  bit : b rBit1 = 1
  bitCopy : b rTe ≤ b rCb
  bits : b rTe ≤ e
  doubling : 2 ^ e ≤ b rCnt
  zero : b rZ ≤ b rAl
  one : b rOne ≤ N * K
  tableCopy : b rTW ≤ b rCu
  table : b rTW ≤ R
  predicate : b rCs ≤ b rCp

theorem compile_cfA_flexible (M N K e R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hc : CoefficientCaps N K e R b) :
    Cert (MVM.compile cfA) (layout M N K b) (layout M N K b)
      ((2 * M + 5) + alphaCoefficientTime M N K e R) :=
  (layout_copy M N K b h.top rCp rCs hc.predicate).seq
    (compile_coefAC_flexible M N K e R b h hc.accumulator hc.power hc.entry hc.bit
      hc.bitCopy hc.bits hc.doubling hc.zero hc.one hc.tableCopy hc.table)

theorem compile_cfV_flexible (M N K e R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hc : CoefficientCaps N K e R b) :
    Cert (MVM.compile cfV) (layout M N K b) (layout M N K b)
      ((2 * M + 5) + valueCoefficientTime M N K R) :=
  (layout_copy M N K b h.top rCp rCs hc.predicate).seq
    (compile_coefVC_flexible M N K R b h hc.accumulator hc.power hc.zero hc.one
      hc.tableCopy hc.table)

set_option exponentiation.threshold 1000 in
theorem alphaCoefficientTime_concrete :
    (2 * 2 ^ 120 + 5) + alphaCoefficientTime (2 ^ 120) (2 ^ 24) (2 ^ 16) 14 (2 ^ 22)
      ≤ 2 ^ 376 := by
  have ht := evalInstructionTime_concrete
  have hu := alphaEntryTime_concrete
  unfold alphaCoefficientTime
  calc
    _ ≤ (2 * 2 ^ 120 + 5) +
        (5 * 2 ^ 341 + 2 ^ 22 * (2 * 2 ^ 120 + 2 ^ 349 + 4) + 2) := by gcongr
    _ ≤ 2 ^ 376 := by norm_num

set_option exponentiation.threshold 1000 in
theorem valueCoefficientTime_concrete :
    (2 * 2 ^ 120 + 5) + valueCoefficientTime (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 22)
      ≤ 2 ^ 369 := by
  have ht := evalInstructionTime_concrete
  unfold valueCoefficientTime
  calc
    _ ≤ (2 * 2 ^ 120 + 5) +
        (4 * 2 ^ 341 + 2 ^ 22 * (2 * 2 ^ 120 + 3 * 2 ^ 341 + 5) + 2) := by gcongr
    _ ≤ 2 ^ 369 := by norm_num

theorem compile_cfA_flexible_concrete (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (hc : CoefficientCaps (2 ^ 24) (2 ^ 16) 14 (2 ^ 22) b) :
    Cert (MVM.compile cfA) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) (2 ^ 376) :=
  (compile_cfA_flexible (2 ^ 120) (2 ^ 24) (2 ^ 16) 14 (2 ^ 22) b h hc).mono
    le_rfl le_rfl alphaCoefficientTime_concrete

theorem compile_cfV_flexible_concrete (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (hc : CoefficientCaps (2 ^ 24) (2 ^ 16) 14 (2 ^ 22) b) :
    Cert (MVM.compile cfV) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) (2 ^ 369) :=
  (compile_cfV_flexible (2 ^ 120) (2 ^ 24) (2 ^ 16) 14 (2 ^ 22) b h hc).mono
    le_rfl le_rfl valueCoefficientTime_concrete

end AdvancedEncryption.ExpLUT.Prog.KeyTime
