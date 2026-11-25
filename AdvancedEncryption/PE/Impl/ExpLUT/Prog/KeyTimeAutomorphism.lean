import PE.Impl.ExpLUT.Prog.KeyTimeMatrix
/-! Actual automorphism matrix evaluation, including both matrix multiplications. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM

def automorphismBodyTime (M N K : ℕ) :=
  2 * (2 * M + 5) + 4 * moveAllowance M + 2 * evalInstructionTime M N K

theorem compile_aBody (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hi : InnerCaps N K b) :
    Cert (MVM.compile aBody) (layout M N K b) (layout M N K b)
      (automorphismBodyTime M N K) := by
  have p0 := layout_copy M N K b h.top rX0 rZ (by rw [hi.x0]; exact hi.zero)
  have p1 := layout_moveR M N K b h rX0 rTmp (by decide)
  have p2 := (layout_op M N K b h .aut rX1 rX0 rKc hi.x1.ge).mono le_rfl le_rfl
    (show operationBound M N K M ≤ evalInstructionTime M N K by
      unfold evalInstructionTime; omega)
  have p3 := layout_moveR M N K b h rS2 rX1 (by decide)
  rw [aBody]
  exact (p0.seq (p1.seq (p2.seq (p3.seq (p0.seq (p1.seq (p2.seq p3))))))).mono
    le_rfl le_rfl (by unfold automorphismBodyTime; omega)

def automorphismMatrixTime (M N K C : ℕ) :=
  4 * (2 * M + 5) + C * (2 * M + automorphismBodyTime M N K + 4) + 2

theorem compile_autMatC (M N K C : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hc : MatrixCaps N K b)
    (hj : b rCj ≤ C) (ho : b rS2 ≤ b rMOut) :
    Cert (MVM.compile autMatC) (layout M N K b) (layout M N K b)
      (automorphismMatrixTime M N K C) := by
  have p0 := layout_copy M N K b h.top rTmp rMA hc.tmp
  have p1 := layout_copy M N K b h.top rS2 rT4KNK hc.sums
  have p2 := layout_copy M N K b h.top rCj rT2K hc.columns
  have hl := rep_fixed rCj aBody (layout M N K b) M C (automorphismBodyTime M N K)
    h.top (by simpa using hj) (compile_aBody M N K b h hc.toInnerCaps)
  have po := layout_copy M N K b h.top rMOut rS2 ho
  rw [autMatC, aPre]
  exact ((p0.seq (p1.seq p2)).seq (hl.seq po)).mono le_rfl le_rfl
    (by unfold automorphismMatrixTime; omega)

def automorphismStepTime (M N K C : ℕ) := automorphismMatrixTime M N K C + (2 * M + 5)

theorem compile_aStep (M N K C : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hc : MatrixCaps N K b)
    (hj : b rCj ≤ C) (ho : b rS2 ≤ b rMOut) (ha : b rMOut ≤ b rMA) :
    Cert (MVM.compile aStep) (layout M N K b) (layout M N K b)
      (automorphismStepTime M N K C) := by
  have hp := compile_autMatC M N K C b h hc hj ho
  have hq := layout_copy M N K b h.top rMA rMOut ha
  rw [aStep]
  exact hp.seq hq

def automorphismTime (M N K D R C P : ℕ) :=
  P * (2 * M + automorphismStepTime M N K C + 4) + 2 +
    matrixTime M N K D R C + 3 * (2 * M + 5) + inverseMatrixTime M N K D C

/-- The actual repeated automorphism, multiplication, saved digit stream and inverse product. -/
theorem compile_autPKC (M N K D R C P : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hc : MatrixCaps N K b)
    (hk : b rTK ≤ D) (hi : b rCi ≤ R) (hj : b rCj ≤ C) (hp : b rP ≤ P)
    (ho : b rS2 ≤ b rMOut) (ha : b rMOut ≤ b rMA)
    (hx : b rGX ≤ b rMAd) (hs : b rSv = b rMAd) :
    Cert (MVM.compile autPKC) (layout M N K b) (layout M N K b)
      (automorphismTime M N K D R C P) := by
  have hb := compile_aStep M N K C b h hc hj ho ha
  have p0 := rep_fixed rP aStep (layout M N K b) M P (automorphismStepTime M N K C)
    h.top (by simpa using hp) hb
  have p1 := compile_mulPKC M N K D R C b h hc hk hi hj
  have p2 := layout_copy M N K b h.top rSv rMAd hs.ge
  have p3 := layout_copy M N K b h.top rMA rMOut ha
  have p4 := compile_ginvMulC M N K D C b h hc hk hj hx
  have p5 := layout_copy M N K b h.top rMAd rSv hs.le
  rw [autPKC]
  exact (p0.seq (p1.seq (p2.seq (p3.seq (p4.seq p5))))).mono le_rfl le_rfl
    (by unfold automorphismTime; omega)

set_option exponentiation.threshold 1000 in
theorem automorphismStepTime_concrete :
    automorphismStepTime (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 * 2 ^ 16) ≤ 2 ^ 364 := by
  have ht := evalInstructionTime_concrete
  unfold automorphismStepTime automorphismMatrixTime automorphismBodyTime
  calc
    _ ≤ 4 * (2 * 2 ^ 120 + 5) + (2 * 2 ^ 16) *
        (2 * 2 ^ 120 + (2 * (2 * 2 ^ 120 + 5) + 4 * moveAllowance (2 ^ 120) +
          2 * 2 ^ 341) + 4) + 2 + (2 * 2 ^ 120 + 5) := by gcongr
    _ ≤ 2 ^ 364 := by norm_num [moveAllowance]

set_option exponentiation.threshold 1000 in
theorem automorphismTime_concrete :
    automorphismTime (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) (4 * 2 ^ 16)
      (2 * 2 ^ 16) (2 ^ 22) ≤ 2 ^ 414 := by
  have ht := automorphismStepTime_concrete
  have hm := matrixTime_concrete
  have hg := inverseMatrixTime_concrete
  unfold automorphismTime
  calc
    _ ≤ 2 ^ 22 * (2 * 2 ^ 120 + 2 ^ 364 + 4) + 2 + 2 ^ 412 +
        3 * (2 * 2 ^ 120 + 5) + 2 ^ 390 := by gcongr
    _ ≤ 2 ^ 414 := by norm_num

theorem compile_autPKC_concrete (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (hc : MatrixCaps (2 ^ 24) (2 ^ 16) b)
    (hk : b rTK ≤ 2 ^ 16) (hi : b rCi ≤ 4 * 2 ^ 16) (hj : b rCj ≤ 2 * 2 ^ 16)
    (hp : b rP ≤ 2 ^ 22) (ho : b rS2 ≤ b rMOut) (ha : b rMOut ≤ b rMA)
    (hx : b rGX ≤ b rMAd) (hs : b rSv = b rMAd) :
    Cert (MVM.compile autPKC) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b) (2 ^ 414) :=
  (compile_autPKC (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) (4 * 2 ^ 16)
    (2 * 2 ^ 16) (2 ^ 22) b h hc hk hi hj hp ho ha hx hs).mono le_rfl le_rfl
      automorphismTime_concrete

end AdvancedEncryption.ExpLUT.Prog.KeyTime
