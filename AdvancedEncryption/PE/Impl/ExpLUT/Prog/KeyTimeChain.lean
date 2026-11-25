import PE.Impl.ExpLUT.Prog.KeyTimeAutomorphism

/-! The actual chain evaluator with a doubling exponent counter. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM SigabaNeo.Tape.Prog

/-- Additional stream and template bounds for the real chain prefixes. -/
structure ChainCaps (N K : ℕ) (b : Fin 64 → ℕ) extends MatrixCaps N K b where
  out : b rS2 ≤ b rMOut
  again : b rMOut ≤ b rMA
  inverse : b rGX ≤ b rMAd
  saved : b rSv = b rMAd
  source : b rSs = b rMAd
  autWords : b rAautW ≤ b rSs
  hWords : b rHW ≤ b rHs
  bit : b rBit1 = 1
  count : b rTb ≤ b rCt
  read : b rTb ≤ b rS
  bitOutput : N * K ≤ b rS2
  gadget : b rT4KNK ≤ b rGX

theorem ChainCaps.update_pw2 {N K : ℕ} {b : Fin 64 → ℕ}
    (h : ChainCaps N K b) (n : ℕ) : ChainCaps N K (Function.update b rPw2 n) := by
  exact {
    toMatrixCaps := {
      toInnerCaps := {
        x0 := by simpa using h.x0
        x1 := by simpa using h.x1
        ac0 := by simpa using h.ac0
        ac1 := by simpa using h.ac1
        da := by simpa using h.da
        dx := by simpa using h.dx
        zero := by simpa using h.zero
        stream := by simpa using h.stream
        counter := by simpa using h.counter
      }
      tmp := by simpa using h.tmp
      row0 := by simpa using h.row0
      row1 := by simpa using h.row1
      col0 := by simpa using h.col0
      col1 := by simpa using h.col1
      trans0 := by simpa using h.trans0
      trans1 := by simpa using h.trans1
      sums := by simpa using h.sums
      streamOut := by simpa using h.streamOut
      output := by simpa using h.output
      columns := by simpa using h.columns
      rows := by simpa using h.rows
    }
    out := by simpa using h.out
    again := by simpa using h.again
    inverse := by simpa using h.inverse
    saved := by simpa using h.saved
    source := by simpa using h.source
    autWords := by simpa using h.autWords
    hWords := by simpa using h.hWords
    bit := by simpa using h.bit
    count := by simpa using h.count
    read := by simpa using h.read
    bitOutput := by simpa using h.bitOutput
    gadget := by simpa using h.gadget
  }

def chainPreTime (M N K : ℕ) :=
  3 * (2 * M + 5) + 3 * moveAllowance M + evalInstructionTime M N K

theorem compile_chPre (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hc : ChainCaps N K b) :
    Cert (MVM.compile chPre) (layout M N K b) (layout M N K b) (chainPreTime M N K) := by
  have p0 := layout_copy M N K b h.top rS rTb hc.read
  have p1 := layout_tail M N K b h.top rS
  have p2 := layout_drop M N K b h rS rCt (by decide)
  have p3 := (layout_op M N K b h .dig rS2 rJ rS hc.bitOutput).mono le_rfl le_rfl
    (show operationBound M N K M ≤ evalInstructionTime M N K by
      unfold evalInstructionTime; omega)
  have p4 := layout_copy M N K b h.top rGX rT4KNK hc.gadget
  have p5 := layout_move M N K b h rGX rHs rT4KNK (by decide)
  have p6 := layout_drop M N K b h rHs rT4KNK (by decide)
  rw [chPre]
  exact (p0.seq (p1.seq (p2.seq (p3.seq (p4.seq (p5.seq p6)))))).mono le_rfl le_rfl
    (by unfold chainPreTime; omega)

def chainAutTime (M N K D R C P : ℕ) :=
  4 * (2 * M + 5) + automorphismTime M N K D R C P

theorem compile_chainAut (M N K D R C P : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hc : ChainCaps N K b)
    (hk : b rTK ≤ D) (hi : b rCi ≤ R) (hj : b rCj ≤ C) (hp : b rP ≤ P)
    (he : b rPw2 ≤ b rP) :
    Cert (MVM.compile autStep) (layout M N K b) (layout M N K b)
      (chainAutTime M N K D R C P) := by
  have p0 := layout_copy M N K b h.top rMAd rSs hc.source.le
  have p1 := layout_copy M N K b h.top rP rPw2 he
  have p2 := compile_autPKC M N K D R C P b h hc.toMatrixCaps hk hi hj hp
    hc.out hc.again hc.inverse hc.saved
  have p3 := layout_copy M N K b h.top rMA rMOut hc.again
  have p4 := layout_copy M N K b h.top rSs rMAd hc.source.ge
  rw [autStep]
  exact (p0.seq (p1.seq (p2.seq (p3.seq p4)))).mono le_rfl le_rfl
    (by unfold chainAutTime; omega)

def chainBodyTime (M N K D R C P : ℕ) :=
  chainPreTime M N K + (max (chainAutTime M N K D R C P) (moveAllowance M) + 1) +
    appendAllowance M

theorem compile_chBody (M N K D R C P : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hc : ChainCaps N K b)
    (hk : b rTK ≤ D) (hi : b rCi ≤ R) (hj : b rCj ≤ C) (hp : b rP ≤ P)
    (he : b rPw2 ≤ b rP) (hs : b rPw2 + b rPw2 ≤ M) :
    Cert (MVM.compile chBody) (layout M N K b)
      (layout M N K (Function.update b rPw2 (b rPw2 + b rPw2)))
      (chainBodyTime M N K D R C P) := by
  have p0 := compile_chPre M N K b h hc
  have pt := compile_chainAut M N K D R C P b h hc hk hi hj hp he
  have pf := layout_drop M N K b h rSs rTBlk (by decide)
  have p1 := Cert.ifBit (tR rS2) pt pf
  have p2 := layout_append_uniform M N K b h.top rPw2 rPw2 hs
  rw [chBody]
  exact (p0.seq (p1.seq p2)).mono le_rfl le_rfl (by unfold chainBodyTime; omega)

/-- The actual loop doubles only its exponent cap; all other register caps are retained. -/
theorem compile_chainLoop (M N K D R C P B : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hc : ChainCaps N K b)
    (hk : b rTK ≤ D) (hi : b rCi ≤ R) (hj : b rCj ≤ C) (hp : b rP ≤ P)
    (hct : b rCt ≤ B) (hpow : 2 ^ B ≤ M) (he : 2 ^ B ≤ b rP) :
    Cert (MVM.compile (.rep rCt chBody))
      (layout M N K (Function.update b rPw2 1))
      (layout M N K (Function.update b rPw2 (2 ^ B)))
      (B * (2 * M + chainBodyTime M N K D R C P + 4) + 2) := by
  have hcol := hj
  let γ := fun j ↦ layout M N K (Function.update b rPw2 (2 ^ j))
  have hin (j : ℕ) (hj : j ≤ B) : RingInputs M N K (γ j) := by
    apply h.update_layout rPw2 (2 ^ j)
    apply le_trans _ hpow
    gcongr
  apply rep_family rCt chBody γ B (chainBodyTime M N K D R C P) _
    (by simp [γ]) (by simpa using hct)
  · intro j hj
    have hs : 2 ^ (j + 1) ≤ M := by
      apply le_trans _ hpow
      gcongr
      omega
    have he' : 2 ^ j ≤ b rP := by
      apply le_trans _ he
      gcongr
    have hb := compile_chBody M N K D R C P (Function.update b rPw2 (2 ^ j))
      (hin j (by omega)) (hc.update_pw2 _) (by simpa using hk) (by simpa using hi)
      (by simpa using hcol) (by simpa using hp)
      (by simpa using he') (by simpa [pow_succ, Nat.mul_two] using hs)
    simp only [Function.update_self, cap_reset] at hb
    rw [show 2 ^ j + 2 ^ j = 2 ^ (j + 1) by simp [pow_succ, Nat.mul_two]] at hb
    exact hb.mono (tailB_le (tR rCt) _) le_rfl le_rfl
  · intro j hj; exact supB_le_of (hin j (by omega)).top
  · intro j hj
    apply layout_mono
    intro r
    by_cases hr : r = rPw2
    · subst r; simp only [Function.update_self]; gcongr
    · simp [Function.update_of_ne hr]

def chainTime (M N K D R C P B : ℕ) :=
  4 * (2 * M + 5) + B * (2 * M + chainBodyTime M N K D R C P + 4) + 2

/-- Includes the four actual initialization copies, including resetting the exponent to one. -/
theorem compile_chainC (M N K D R C P B : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hc : ChainCaps N K b)
    (hk : b rTK ≤ D) (hi : b rCi ≤ R) (hj : b rCj ≤ C) (hp : b rP ≤ P)
    (hct : b rCt ≤ B) (hpow : 2 ^ B ≤ M) (he : 2 ^ B ≤ b rP) :
    Cert (MVM.compile chainC) (layout M N K b)
      (layout M N K (Function.update b rPw2 (2 ^ B))) (chainTime M N K D R C P B) := by
  have p0 := layout_copy M N K b h.top rSs rAautW hc.autWords
  have p1 := layout_copy M N K b h.top rHs rHW hc.hWords
  have p2 := layout_copy_update M N K b h.top rPw2 rBit1
  rw [hc.bit] at p2
  have hone : 1 ≤ M := by
    have := pow_pos (by decide : 0 < (2 : ℕ)) B
    omega
  have h1 : RingInputs M N K (layout M N K (Function.update b rPw2 1)) :=
    h.update_layout rPw2 1 hone
  have p3 := layout_copy M N K (Function.update b rPw2 1) h1.top rCt rTb
    (by simpa using hc.count)
  have pl := compile_chainLoop M N K D R C P B b h hc hk hi hj hp hct hpow he
  rw [chainC]
  exact (p0.seq (p1.seq (p2.seq (p3.seq pl)))).mono le_rfl le_rfl
    (by unfold chainTime; omega)

set_option exponentiation.threshold 1000 in
theorem chainBodyTime_concrete :
    chainBodyTime (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) (4 * 2 ^ 16)
      (2 * 2 ^ 16) (2 ^ 22) ≤ 2 ^ 416 := by
  have ha := automorphismTime_concrete
  have ht := evalInstructionTime_concrete
  have hp : chainPreTime (2 ^ 120) (2 ^ 24) (2 ^ 16) ≤ 2 ^ 343 := by
    unfold chainPreTime
    calc
      _ ≤ 3 * (2 * 2 ^ 120 + 5) + 3 * moveAllowance (2 ^ 120) + 2 ^ 341 := by gcongr
      _ ≤ 2 ^ 343 := by norm_num [moveAllowance]
  have hb : chainAutTime (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) (4 * 2 ^ 16)
      (2 * 2 ^ 16) (2 ^ 22) ≤ 2 ^ 415 := by
    unfold chainAutTime
    calc
      _ ≤ 4 * (2 * 2 ^ 120 + 5) + 2 ^ 414 := by gcongr
      _ ≤ 2 ^ 415 := by norm_num
  have hm : moveAllowance (2 ^ 120) ≤ 2 ^ 415 := by norm_num [moveAllowance]
  have hmax := max_le hb hm
  unfold chainBodyTime
  calc
    _ ≤ 2 ^ 343 + (2 ^ 415 + 1) + appendAllowance (2 ^ 120) := by gcongr
    _ ≤ 2 ^ 416 := by norm_num [appendAllowance]

set_option exponentiation.threshold 1000 in
theorem chainTime_concrete :
    chainTime (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) (4 * 2 ^ 16)
      (2 * 2 ^ 16) (2 ^ 22) 22 ≤ 2 ^ 422 := by
  have hb := chainBodyTime_concrete
  unfold chainTime
  calc
    _ ≤ 4 * (2 * 2 ^ 120 + 5) + 22 * (2 * 2 ^ 120 + 2 ^ 416 + 4) + 2 := by gcongr
    _ ≤ 2 ^ 422 := by norm_num

theorem compile_chainC_concrete (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b))
    (hc : ChainCaps (2 ^ 24) (2 ^ 16) b)
    (hk : b rTK ≤ 2 ^ 16) (hi : b rCi ≤ 4 * 2 ^ 16) (hj : b rCj ≤ 2 * 2 ^ 16)
    (hp : b rP = 2 ^ 22) (hct : b rCt ≤ 22) :
    Cert (MVM.compile chainC) (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) b)
      (layout (2 ^ 120) (2 ^ 24) (2 ^ 16) (Function.update b rPw2 (2 ^ 22))) (2 ^ 422) :=
  (compile_chainC (2 ^ 120) (2 ^ 24) (2 ^ 16) (2 ^ 16) (4 * 2 ^ 16)
    (2 * 2 ^ 16) (2 ^ 22) 22 b h hc hk hi hj hp.le hct (by norm_num) hp.ge).mono
      le_rfl le_rfl chainTime_concrete

end AdvancedEncryption.ExpLUT.Prog.KeyTime
