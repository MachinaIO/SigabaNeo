import PE.Impl.ExpLUT.Prog.KeyTimeColumns
/-! Runtime certificates for the complete compiled matrix multiplication routines. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM

/-- Explicit stable bounds used by matrix prefixes, columns and transposition. -/
structure MatrixCaps (N K : ℕ) (b : Fin 64 → ℕ) extends InnerCaps N K b where
  tmp : b rMA ≤ b rTmp
  row0 : b rTKNK ≤ b rRo0
  row1 : b rTKNK ≤ b rRo1
  col0 : b rRo0 ≤ b rCo0
  col1 : b rRo1 ≤ b rCo1
  trans0 : b rT2KNK ≤ b rCo0
  trans1 : b rT2KNK ≤ b rCo1
  sums : b rT4KNK ≤ b rS2
  streamOut : b rS2 ≤ b rS
  output : b rT4KNK ≤ b rMOut
  columns : b rT2K ≤ b rCj
  rows : b rTK ≤ b rCi

theorem layout_move (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (d s c : Fin 64)
    (hd : ¬(d = s ∨ d = c ∨ s = c)) :
    Cert (MVM.compile (.mv d s c)) (layout M N K b) (layout M N K b)
      (moveAllowance M) := by
  have ht := compile_mv_scratch d s c hd (layout M N K b) M h.top
  exact ht.mono le_rfl le_rfl (by unfold moveAllowance; gcongr; exact h.top (tR c))

def transposeBodyTime (M : ℕ) := 2 * (2 * M + 5) + 4 * moveAllowance M
def transposeTime (M C : ℕ) :=
  3 * (2 * M + 5) + C * (2 * M + transposeBodyTime M + 4) + 2
def matrixOutTime (M : ℕ) := (2 * M + 5) + 2 * moveAllowance M

theorem compile_tBody (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hi : InnerCaps N K b) :
    Cert (MVM.compile tBody) (layout M N K b) (layout M N K b)
      (transposeBodyTime M) := by
  have p0 := layout_copy M N K b h.top rAc0 rZ (by rw [hi.ac0]; exact hi.zero)
  have p1 := layout_moveR M N K b h rAc0 rS (by decide)
  have p2 := layout_moveR M N K b h rCo0 rAc0 (by decide)
  have p3 := layout_copy M N K b h.top rAc1 rZ (by rw [hi.ac1]; exact hi.zero)
  have p4 := layout_moveR M N K b h rAc1 rS (by decide)
  have p5 := layout_moveR M N K b h rCo1 rAc1 (by decide)
  rw [tBody]
  exact (p0.seq (p1.seq (p2.seq (p3.seq (p4.seq p5))))).mono le_rfl le_rfl
    (by unfold transposeBodyTime; omega)

theorem compile_tLoop (M N K C : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hc : MatrixCaps N K b) (hj : b rCj ≤ C) :
    Cert (MVM.compile tLoop) (layout M N K b) (layout M N K b) (transposeTime M C) := by
  have p0 := layout_copy M N K b h.top rCo0 rT2KNK hc.trans0
  have p1 := layout_copy M N K b h.top rCo1 rT2KNK hc.trans1
  have p2 := layout_copy M N K b h.top rCj rT2K hc.columns
  have hl := rep_fixed rCj tBody (layout M N K b) M C (transposeBodyTime M)
    h.top (by simpa using hj) (compile_tBody M N K b h hc.toInnerCaps)
  rw [tLoop, tPre]
  exact ((p0.seq (p1.seq p2)).seq hl).mono le_rfl le_rfl (by unfold transposeTime; omega)

theorem compile_tOut (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hc : MatrixCaps N K b) :
    Cert (MVM.compile tOut) (layout M N K b) (layout M N K b) (matrixOutTime M) := by
  have p0 := layout_copy M N K b h.top rMOut rT4KNK hc.output
  have p1 := layout_move M N K b h rMOut rCo0 rT2KNK (by decide)
  have p2 := layout_move M N K b h rMOut rCo1 rT2KNK (by decide)
  rw [tOut]
  exact (p0.seq (p1.seq p2)).mono le_rfl le_rfl (by unfold matrixOutTime; omega)

def rowPrefixTime (M : ℕ) := 6 * (2 * M + 5) + 4 * moveAllowance M
def rowTime (M N K D R C : ℕ) :=
  rowPrefixTime M + C * (2 * M + columnTime M N K D R + 4) + 2 + (2 * M + 5)

theorem compile_rPre (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hc : MatrixCaps N K b) (r : Fin 2) :
    Cert (MVM.compile (rPre r)) (layout M N K b) (layout M N K b) (rowPrefixTime M) := by
  have p0 := layout_copy M N K b h.top rTmp rMA hc.tmp
  have pd := layout_drop M N K b h rTmp rTKNK (by decide)
  have pi : Cert (MVM.compile (if r = 1 then .drop rTmp rTKNK else .nop))
      (layout M N K b) (layout M N K b) ((2 * M + 5) + moveAllowance M) := by
    split
    · exact pd.mono le_rfl le_rfl (by omega)
    · exact (compile_nop (layout M N K b) M h.top).mono le_rfl le_rfl (by omega)
  have p2 := layout_copy M N K b h.top rRo0 rTKNK hc.row0
  have p3 := layout_move M N K b h rRo0 rTmp rTKNK (by decide)
  have p5 := layout_copy M N K b h.top rRo1 rTKNK hc.row1
  have p6 := layout_move M N K b h rRo1 rTmp rTKNK (by decide)
  have p7 := layout_copy M N K b h.top rS2 rT4KNK hc.sums
  have p8 := layout_copy M N K b h.top rCj rT2K hc.columns
  rw [rPre]
  exact (p0.seq (pi.seq (p2.seq (p3.seq (pd.seq (p5.seq (p6.seq (p7.seq p8)))))))).mono
    le_rfl le_rfl (by unfold rowPrefixTime; omega)

theorem compile_rPart (M N K D R C : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hc : MatrixCaps N K b)
    (hk : b rTK ≤ D) (hi : b rCi ≤ R) (hj : b rCj ≤ C) (r : Fin 2) :
    Cert (MVM.compile (rPart r)) (layout M N K b) (layout M N K b) (rowTime M N K D R C) := by
  have hp := compile_rPre M N K b h hc r
  have hb := compile_jBody M N K D R b h hc.toInnerCaps hc.col0 hc.col1 hk hc.rows hi
  have hl := rep_fixed rCj jBody (layout M N K b) M C (columnTime M N K D R)
    h.top (by simpa using hj) hb
  have ho := layout_copy M N K b h.top rS rS2 hc.streamOut
  rw [rPart]
  exact (hp.seq (hl.seq ho)).mono le_rfl le_rfl (by unfold rowTime; omega)

def matrixTime (M N K D R C : ℕ) :=
  (2 * M + 5) + 2 * rowTime M N K D R C + transposeTime M C + matrixOutTime M

theorem compile_mulPKC (M N K D R C : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hc : MatrixCaps N K b)
    (hk : b rTK ≤ D) (hi : b rCi ≤ R) (hj : b rCj ≤ C) :
    Cert (MVM.compile mulPKC) (layout M N K b) (layout M N K b) (matrixTime M N K D R C) := by
  have p0 := layout_copy M N K b h.top rS rT4KNK (hc.sums.trans hc.streamOut)
  have p1 := compile_rPart M N K D R C b h hc hk hi hj 0
  have p2 := compile_rPart M N K D R C b h hc hk hi hj 1
  have p3 := compile_tLoop M N K C b h hc hj
  have p4 := compile_tOut M N K b h hc
  rw [mulPKC]
  exact (p0.seq (p1.seq (p2.seq (p3.seq p4)))).mono le_rfl le_rfl
    (by unfold matrixTime; omega)

def inversePrefixTime (M : ℕ) := 5 * (2 * M + 5) + 2 * moveAllowance M

theorem compile_gPre (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hc : MatrixCaps N K b) :
    Cert (MVM.compile gPre) (layout M N K b) (layout M N K b) (inversePrefixTime M) := by
  have p0 := layout_copy M N K b h.top rTmp rMA hc.tmp
  have p1 := layout_copy M N K b h.top rCo0 rT2KNK hc.trans0
  have p2 := layout_move M N K b h rCo0 rTmp rT2KNK (by decide)
  have p3 := layout_copy M N K b h.top rCo1 rT2KNK hc.trans1
  have p4 := layout_move M N K b h rCo1 rTmp rT2KNK (by decide)
  have p5 := layout_copy M N K b h.top rS2 rT4KNK hc.sums
  have p6 := layout_copy M N K b h.top rCj rT2K hc.columns
  rw [gPre]
  exact (p0.seq (p1.seq (p2.seq (p3.seq (p4.seq (p5.seq p6)))))).mono le_rfl le_rfl
    (by unfold inversePrefixTime; omega)

def inverseMatrixTime (M N K D C : ℕ) :=
  inversePrefixTime M + C * (2 * M + inverseColumnTime M N K D + 4) + 2 +
    (2 * M + 5) + transposeTime M C + matrixOutTime M

theorem compile_ginvMulC (M N K D C : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hc : MatrixCaps N K b)
    (hk : b rTK ≤ D) (hj : b rCj ≤ C) (hx : b rGX ≤ b rMAd) :
    Cert (MVM.compile ginvMulC) (layout M N K b) (layout M N K b) (inverseMatrixTime M N K D C) := by
  have p0 := compile_gPre M N K b h hc
  have hb := compile_gBody M N K D b h hc.toInnerCaps hx hk
  have p1 := rep_fixed rCj gBody (layout M N K b) M C (inverseColumnTime M N K D)
    h.top (by simpa using hj) hb
  have p2 := layout_copy M N K b h.top rS rS2 hc.streamOut
  have p3 := compile_tLoop M N K C b h hc hj
  have p4 := compile_tOut M N K b h hc
  rw [ginvMulC]
  exact (p0.seq (p1.seq (p2.seq (p3.seq p4)))).mono le_rfl le_rfl
    (by unfold inverseMatrixTime; omega)

set_option exponentiation.threshold 1000 in
set_option maxRecDepth 10000 in
theorem matrixTime_concrete :
    matrixTime (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) (4 * 2 ^ 16) (2 * 2 ^ 16) ≤ 2 ^ 412 := by
  have hc := columnTime_concrete
  unfold matrixTime rowTime
  calc
    _ ≤ (2 * 2 ^ 120 + 5) +
        2 * (rowPrefixTime (2 ^ 120) + (2 * 2 ^ 16) *
          (2 * 2 ^ 120 + 2 ^ 388 + 4) + 2 + (2 * 2 ^ 120 + 5)) +
        transposeTime (2 ^ 120) (2 * 2 ^ 16) + matrixOutTime (2 ^ 120) := by gcongr
    _ ≤ 2 ^ 412 := by
      norm_num [rowPrefixTime, transposeTime, transposeBodyTime, matrixOutTime, moveAllowance]

set_option exponentiation.threshold 1000 in
set_option maxRecDepth 10000 in
theorem inverseMatrixTime_concrete :
    inverseMatrixTime (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) (2 * 2 ^ 16) ≤ 2 ^ 390 := by
  have hc := inverseColumnTime_concrete
  unfold inverseMatrixTime
  calc
    _ ≤ inversePrefixTime (2 ^ 120) + (2 * 2 ^ 16) *
        (2 * 2 ^ 120 + 2 ^ 368 + 4) + 2 + (2 * 2 ^ 120 + 5) +
        transposeTime (2 ^ 120) (2 * 2 ^ 16) + matrixOutTime (2 ^ 120) := by gcongr
    _ ≤ 2 ^ 390 := by
      norm_num [inversePrefixTime, transposeTime, transposeBodyTime, matrixOutTime, moveAllowance]

theorem compile_mulPKC_concrete (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (hc : MatrixCaps (2 ^ 24) (2 ^ 16) b)
    (hk : b rTK ≤ 2 ^ 16) (hi : b rCi ≤ 4 * 2 ^ 16) (hj : b rCj ≤ 2 * 2 ^ 16) :
    Cert (MVM.compile mulPKC) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) (2 ^ 412) :=
  (compile_mulPKC (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) (4 * 2 ^ 16) (2 * 2 ^ 16)
    b h hc hk hi hj).mono le_rfl le_rfl matrixTime_concrete

theorem compile_ginvMulC_concrete (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (hc : MatrixCaps (2 ^ 24) (2 ^ 16) b)
    (hk : b rTK ≤ 2 ^ 16) (hj : b rCj ≤ 2 * 2 ^ 16) (hx : b rGX ≤ b rMAd) :
    Cert (MVM.compile ginvMulC) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) (2 ^ 390) :=
  (compile_ginvMulC (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) (2 * 2 ^ 16)
    b h hc hk hj hx).mono le_rfl le_rfl inverseMatrixTime_concrete

end AdvancedEncryption.ExpLUT.Prog.KeyTime
