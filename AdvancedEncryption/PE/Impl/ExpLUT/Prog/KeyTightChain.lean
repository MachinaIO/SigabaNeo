import PE.Impl.ExpLUT.Prog.KeyTimeEval
/-!
# KeyGen evaluator: tight matrix and chain kernels (generic in `M N K`)

F3's evaluator kernels (`KeyTimeDigitAcc` … `KeyTimeChain`) charge every ring instruction with
`operationBound M N K M` (the counter at the tape cap) and every single-word move with
`moveAllowance M = (2M+3)(20+10M)`. Here:

* binary ring instructions cost `operationBound M N K 0` (`tOpBin`, from F3's
  `compile_binary_scratch`/`binaryTime_le`), counted ones `operationBound M N K C` for a counter
  bound `C` (`RedKeyT.rktOp`); single-word moves cost `RedKeyT.mvT`, drops `(2M+3)(20+10C)`;
* in `digAccBody` the digit counter `MVM.rUp` is a fresh copy of `rTK1`: the copy is certified with
  `layout_copy_update`, so the digit instruction sees `MVM.rUp ≤ b rTK1 ≤ C` although the loop
  envelope keeps `MVM.rUp` at the cap;
* the automorphism instructions are charged with the exponent bound `b rKc ≤ G`.

Kernels: `tDigAccBody`, `tDigAccC`, `tIBody`, `tJBody`, `tGBody`, `tRPart`, `tMulPKC`,
`tGinvMulC`, `tABody`, `tAutMatC`, `tAStep`, `tAutPKC`, `tChainAut`, `tChBody`, `tChainLoop`,
**`tChainC`** (F3's `rPre`, `tLoop`, `tOut`, `gPre`, `chPre` are reused as they are).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.KeyTight

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM
open AdvancedEncryption.ExpLUT.Prog
open AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo.Tape.Prog (supB_le_of)

/-! ### Leaves -/

/-- A ring instruction, charging the counter register `c` with its layout bound
(as `RedKeyT.rktOp`). -/
theorem tOpC (M N K C : ℕ) (b : Fin 64 → ℕ) (h : RingInputs M N K (layout M N K b))
    (o : Op) (d s c : Fin 64) (hd : N * K ≤ b d) (hc : b c ≤ C) :
    Cert (MVM.compile (.op o d s c)) (layout M N K b) (layout M N K b)
      (operationBound M N K C) := by
  obtain ⟨hp, hr⟩ := compile_op_scratch_ready M N K o d s c _ h
  apply hp.mono le_rfl
  · apply le_layout M N K b _ hr.top hr.templateK hr.templateN hr.zeros.le hr.ones
    intro r
    by_cases he : r = d
    · subst r; rw [operationResult_destination]; exact hd
    · rw [operationResult_other _ _ _ _ _ _ _ he, cleanWork_register, layout_register]
  · exact operationBound_mono le_rfl le_rfl le_rfl (by simpa using hc)

/-- The exact cost of a single-word register move (as `RedKeyT.mvT`). -/
def tMvT (M N K : ℕ) : ℕ := (2 * M + 3) * (20 + 10 * (N * K))

theorem tMvR (M N K : ℕ) (b : Fin 64 → ℕ) (h : RingInputs M N K (layout M N K b))
    (d s : Fin 64) (hd : d ≠ s) :
    Cert (MVM.compile (.mvR d s)) (layout M N K b) (layout M N K b) (tMvT M N K) := by
  have hc := compile_mvR_scratch d s hd (layout M N K b) M h.top
  have h37 : layout M N K b 37 = N * K := by simp [layout]
  rw [h37] at hc
  exact hc

/-- A binary ring instruction, independent of its third register. -/
theorem tOpBin (M N K : ℕ) (b : Fin 64 → ℕ) (h : RingInputs M N K (layout M N K b))
    (o : Op) (ho : o.bin = true) (d s c : Fin 64) (hd : N * K ≤ b d) :
    Cert (MVM.compile (.op o d s c)) (layout M N K b) (layout M N K b)
      (operationBound M N K 0) := by
  obtain ⟨_, hr⟩ := compile_op_scratch_ready M N K o d s c _ h
  have ho' : o = .add ∨ o = .sub ∨ o = .mul := by cases o <;> simp_all [Op.bin]
  have hh := compile_binary_scratch o ho' d s c M N K _ h.top h.ring h.dimension h.width
    h.templateK h.templateN h.zeros h.ones
  have hp : Cert (MVM.compile (.op o d s c)) (layout M N K b)
      (operationResult M N K o d c (cleanWork (layout M N K b))) (operationBound M N K 0) := by
    simpa only [operationResult, ho, ↓reduceIte] using
      hh.mono le_rfl le_rfl (binaryTime_le M N K o)
  apply hp.mono le_rfl _ le_rfl
  apply le_layout M N K b _ hr.top hr.templateK hr.templateN hr.zeros.le hr.ones
  intro r
  by_cases he : r = d
  · subst r; rw [operationResult_destination]; exact hd
  · rw [operationResult_other _ _ _ _ _ _ _ he, cleanWork_register, layout_register]

def tDropT (M C : ℕ) : ℕ := (2 * M + 3) * (20 + 10 * C)

theorem tDrop (M N K C : ℕ) (b : Fin 64 → ℕ) (h : RingInputs M N K (layout M N K b))
    (d c : Fin 64) (hdc : d ≠ c) (hc : b c ≤ C) :
    Cert (MVM.compile (.drop d c)) (layout M N K b) (layout M N K b) (tDropT M C) := by
  have ht := compile_drop_scratch d c hdc (layout M N K b) M h.top
  exact ht.mono le_rfl le_rfl (by unfold tDropT; gcongr; simpa using hc)

/-! ### Digit accumulation -/

def tDigBT (M N K C D : ℕ) : ℕ :=
  (2 * M + 5) + tDropT M D + tMvT M N K + operationBound M N K C + 2 * operationBound M N K 0

theorem tDigAccBody (M N K C D : ℕ) (b : Fin 64 → ℕ) (h : RingInputs M N K (layout M N K b))
    (hu : b rTK1 ≤ b MVM.rUp) (hC : b rTK1 ≤ C) (hn : b MVM.rDn ≤ D)
    (hd : N * K ≤ b rDg) (hp : N * K ≤ b rPr) (ha : N * K ≤ b rDA) :
    Cert (MVM.compile digAccBody) (layout M N K b) (layout M N K b) (tDigBT M N K C D) := by
  let b1 := Function.update b MVM.rUp (b rTK1)
  have h1 : RingInputs M N K (layout M N K b1) :=
    h.update_layout _ _ (by simpa using h.top (tR rTK1))
  have p0 := layout_copy_update M N K b h.top MVM.rUp rTK1
  have p1 := tDrop M N K D b1 h1 MVM.rUp MVM.rDn (by decide) (by simpa [b1] using hn)
  have p2 := tMvR M N K b1 h1 rEl rDE (by decide)
  have p3 := tOpC M N K C b1 h1 .dig rDg rDX MVM.rUp (by simpa [b1] using hd) (by simpa [b1] using hC)
  have p4 := tOpBin M N K b1 h1 .mul rfl rPr rEl rDg (by simpa [b1] using hp)
  have p5 := tOpBin M N K b1 h1 .add rfl rDA rDA rPr (by simpa [b1] using ha)
  rw [digAccBody]
  have all := p0.seq (p1.seq (p2.seq (p3.seq (p4.seq p5))))
  exact all.mono le_rfl
    (layout_mono _ _ _ (cap_update_le b MVM.rUp _ hu)) (by unfold tDigBT; omega)

def tDigitT (M N K C R : ℕ) : ℕ :=
  6 * (2 * M + 5) + R * (2 * M + tDigBT M N K C R + 4) + 2

theorem tDigAccC (M N K C R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (ha : b rDA ≤ N * K) (hz : b rZ ≤ N * K)
    (hk : b rTK ≤ R) (hC : b rTK1 ≤ C) :
    Cert (MVM.compile digAccC) (layout M N K b) (layout M N K (digitResult M N K b))
      (tDigitT M N K C R) := by
  let c := digitWide M N K b
  let c1 := Function.update c MVM.rDn (b rTK)
  let c2 := digitBase M N K b
  have hi := digitWide_inputs M N K b h
  have hi1 : RingInputs M N K (layout M N K c1) := hi.update_layout MVM.rDn (b rTK)
    (by simpa using h.top (tR rTK))
  have hi2 := digitBase_inputs M N K b h
  have h0 : Cert (MVM.compile (.cp MVM.rDn rTK)) (layout M N K c) (layout M N K c1)
      (2 * M + 5) := by
    simpa [c, c1, digitWide] using layout_copy_update M N K c hi.top MVM.rDn rTK
  have h1 := layout_copy_cap M N K c1 hi1.top rEl rZ (N * K)
    (by simpa [c1, c, digitWide] using hz)
  have hb := tDigAccBody M N K C R c2 hi2
    (by simpa [c2, digitBase, digitWide] using h.top (tR rTK1))
    (by simpa [c2, digitBase, digitWide] using hC)
    (by simpa [c2, digitBase, digitWide] using hk)
    (by simpa [c2, digitBase, digitWide] using h.ring)
    (by simpa [c2, digitBase, digitWide] using h.ring) (by simp [c2, digitBase, digitWide])
  have hl := rep_fixed MVM.rDn digAccBody (layout M N K c2) M R (tDigBT M N K C R)
    hi2.top (by simpa [c2, digitBase, digitWide] using hk) hb
  have hc := compile_digAccClean M N K c2 hi2
  rw [digAccC]
  refine (h0.seq (h1.seq (hl.seq hc))).mono ?_ le_rfl ?_
  swap; · unfold tDigitT; omega
  apply layout_mono
  have hb : ∀ r, b r ≤ M := fun r ↦ by simpa using h.top (tR r)
  intro r
  by_cases h0 : r = rDA <;> by_cases h1 : r = MVM.rUp <;>
    by_cases h2 : r = rDg <;> by_cases h3 : r = rPr <;>
    simp_all [c, digitWide]

theorem tLayoutDigAcc (M N K C R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (ha : b rDA = N * K)
    (hz : b rZ ≤ N * K) (hk : b rTK ≤ R) (hn : b rTK ≤ b MVM.rDn) (hC : b rTK1 ≤ C) :
    Cert (MVM.compile digAccC) (layout M N K b) (layout M N K b) (tDigitT M N K C R) :=
  (tDigAccC M N K C R b h ha.le hz hk hC).mono le_rfl
    (layout_mono M N K (digitResult_le M N K b ha.ge hn)) le_rfl

/-! ### Inner step, columns -/

def tInnerT (M N K C R : ℕ) : ℕ :=
  12 * (2 * M + 5) + 2 * tMvT M N K + 4 * tDigitT M N K C R

theorem tIBody (M N K C R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hc : InnerCaps N K b) (hk : b rTK ≤ R)
    (hC : b rTK1 ≤ C) :
    Cert (MVM.compile MVM.iBody) (layout M N K b) (layout M N K b) (tInnerT M N K C R) := by
  have hd := tLayoutDigAcc M N K C R b h hc.da hc.zero hk hc.counter hC
  have h0 := layout_copy M N K b h.top rX0 rZ (by rw [hc.x0]; exact hc.zero)
  have h1 := tMvR M N K b h rX0 rCo0 (by decide)
  have h2 := layout_copy M N K b h.top rX1 rZ (by rw [hc.x1]; exact hc.zero)
  have h3 := tMvR M N K b h rX1 rCo1 (by decide)
  have h4 := layout_copy M N K b h.top rDE rMAd hc.stream.ge
  have h5 := layout_copy M N K b h.top rDA rAc0 (by rw [hc.da, hc.ac0])
  have h6 := layout_copy M N K b h.top rDX rX0 (by rw [hc.x0]; exact hc.dx)
  have h8 := layout_copy M N K b h.top rDX rX1 (by rw [hc.x1]; exact hc.dx)
  have h10 := layout_copy M N K b h.top rAc0 rDA (by rw [hc.da, hc.ac0])
  have h11 := layout_copy M N K b h.top rDA rAc1 (by rw [hc.da, hc.ac1])
  have h16 := layout_copy M N K b h.top rAc1 rDA (by rw [hc.da, hc.ac1])
  have h17 := layout_copy M N K b h.top rMAd rDE hc.stream.le
  rw [MVM.iBody]
  have all := h0.seq (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (hd.seq
    (h8.seq (hd.seq (h10.seq (h11.seq (h6.seq (hd.seq (h8.seq (hd.seq
    (h16.seq h17))))))))))))))))
  exact all.mono le_rfl le_rfl (by unfold tInnerT; omega)

def tColT (M N K C D R : ℕ) : ℕ :=
  5 * (2 * M + 5) + 4 * tMvT M N K + R * (2 * M + tInnerT M N K C D + 4) + 2

theorem tJBody (M N K C D R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hi : InnerCaps N K b)
    (h0 : b rRo0 ≤ b rCo0) (h1 : b rRo1 ≤ b rCo1)
    (hk : b rTK ≤ D) (hci : b rTK ≤ b rCi) (hr : b rCi ≤ R) (hC : b rTK1 ≤ C) :
    Cert (MVM.compile MVM.jBody) (layout M N K b) (layout M N K b) (tColT M N K C D R) := by
  have p0 := layout_copy M N K b h.top rAc0 rZ (by rw [hi.ac0]; exact hi.zero)
  have p1 := tMvR M N K b h rAc0 rS (by decide)
  have p2 := layout_copy M N K b h.top rAc1 rZ (by rw [hi.ac1]; exact hi.zero)
  have p3 := tMvR M N K b h rAc1 rS (by decide)
  have p4 := layout_copy M N K b h.top rCo0 rRo0 h0
  have p5 := layout_copy M N K b h.top rCo1 rRo1 h1
  have p6 := layout_copy M N K b h.top rCi rTK hci
  have pre := p0.seq (p1.seq (p2.seq (p3.seq (p4.seq (p5.seq p6)))))
  have hb := tIBody M N K C D b h hi hk hC
  have hl := rep_fixed rCi MVM.iBody (layout M N K b) M R (tInnerT M N K C D)
    h.top (by simpa using hr) hb
  have q0 := tMvR M N K b h rS2 rAc0 (by decide)
  have q1 := tMvR M N K b h rS2 rAc1 (by decide)
  rw [MVM.jBody, MVM.jPre, MVM.jPost]
  have all := pre.seq (hl.seq (q0.seq q1))
  exact all.mono le_rfl le_rfl (by unfold tColT; omega)

def tGT (M N K C D : ℕ) : ℕ := 3 * (2 * M + 5) + tInnerT M N K C D + 2 * tMvT M N K

theorem tGBody (M N K C D : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hi : InnerCaps N K b)
    (hx : b rGX ≤ b rMAd) (hk : b rTK ≤ D) (hC : b rTK1 ≤ C) :
    Cert (MVM.compile gBody) (layout M N K b) (layout M N K b) (tGT M N K C D) := by
  have p0 := layout_copy M N K b h.top rAc0 rZ (by rw [hi.ac0]; exact hi.zero)
  have p1 := layout_copy M N K b h.top rAc1 rZ (by rw [hi.ac1]; exact hi.zero)
  have p2 := layout_copy M N K b h.top rMAd rGX hx
  have hb := tIBody M N K C D b h hi hk hC
  have q0 := tMvR M N K b h rS2 rAc0 (by decide)
  have q1 := tMvR M N K b h rS2 rAc1 (by decide)
  rw [gBody]
  have all := p0.seq (p1.seq (p2.seq (hb.seq (q0.seq q1))))
  exact all.mono le_rfl le_rfl
    (by unfold tGT; omega)

/-! ### Matrix products -/

def tRowT (M N K C D R J : ℕ) : ℕ :=
  rowPrefixTime M + J * (2 * M + tColT M N K C D R + 4) + 2 + (2 * M + 5)

theorem tRPart (M N K C D R J : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hc : MatrixCaps N K b)
    (hk : b rTK ≤ D) (hi : b rCi ≤ R) (hj : b rCj ≤ J) (hC : b rTK1 ≤ C) (r : Fin 2) :
    Cert (MVM.compile (rPart r)) (layout M N K b) (layout M N K b) (tRowT M N K C D R J) := by
  have hp := compile_rPre M N K b h hc r
  have hb := tJBody M N K C D R b h hc.toInnerCaps hc.col0 hc.col1 hk hc.rows hi hC
  have hl := rep_fixed rCj MVM.jBody (layout M N K b) M J (tColT M N K C D R)
    h.top (by simpa using hj) hb
  have ho := layout_copy M N K b h.top rS rS2 hc.streamOut
  rw [rPart]
  have all := hp.seq (hl.seq ho)
  exact all.mono le_rfl le_rfl (by unfold tRowT; omega)

def tMatT (M N K C D R J : ℕ) : ℕ :=
  (2 * M + 5) + 2 * tRowT M N K C D R J + transposeTime M J + matrixOutTime M

theorem tMulPKC (M N K C D R J : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hc : MatrixCaps N K b)
    (hk : b rTK ≤ D) (hi : b rCi ≤ R) (hj : b rCj ≤ J) (hC : b rTK1 ≤ C) :
    Cert (MVM.compile mulPKC) (layout M N K b) (layout M N K b) (tMatT M N K C D R J) := by
  have p0 := layout_copy M N K b h.top rS rT4KNK (hc.sums.trans hc.streamOut)
  have p1 := tRPart M N K C D R J b h hc hk hi hj hC 0
  have p2 := tRPart M N K C D R J b h hc hk hi hj hC 1
  have p3 := compile_tLoop M N K J b h hc hj
  have p4 := compile_tOut M N K b h hc
  rw [mulPKC]
  have all := p0.seq (p1.seq (p2.seq (p3.seq p4)))
  exact all.mono le_rfl le_rfl (by unfold tMatT; omega)

def tInvT (M N K C D J : ℕ) : ℕ :=
  inversePrefixTime M + J * (2 * M + tGT M N K C D + 4) + 2 +
    (2 * M + 5) + transposeTime M J + matrixOutTime M

theorem tGinvMulC (M N K C D J : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hc : MatrixCaps N K b)
    (hk : b rTK ≤ D) (hj : b rCj ≤ J) (hx : b rGX ≤ b rMAd) (hC : b rTK1 ≤ C) :
    Cert (MVM.compile ginvMulC) (layout M N K b) (layout M N K b) (tInvT M N K C D J) := by
  have p0 := compile_gPre M N K b h hc
  have hb := tGBody M N K C D b h hc.toInnerCaps hx hk hC
  have p1 := rep_fixed rCj gBody (layout M N K b) M J (tGT M N K C D) h.top (by simpa using hj) hb
  have p2 := layout_copy M N K b h.top rS rS2 hc.streamOut
  have p3 := compile_tLoop M N K J b h hc hj
  have p4 := compile_tOut M N K b h hc
  rw [ginvMulC]
  have all := p0.seq (p1.seq (p2.seq (p3.seq p4)))
  exact all.mono le_rfl le_rfl (by unfold tInvT; omega)

/-! ### Automorphisms -/

def tABT (M N K G : ℕ) : ℕ := 2 * (2 * M + 5) + 4 * tMvT M N K + 2 * operationBound M N K G

theorem tABody (M N K G : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hi : InnerCaps N K b) (hG : b rKc ≤ G) :
    Cert (MVM.compile aBody) (layout M N K b) (layout M N K b) (tABT M N K G) := by
  have p0 := layout_copy M N K b h.top rX0 rZ (by rw [hi.x0]; exact hi.zero)
  have p1 := tMvR M N K b h rX0 rTmp (by decide)
  have p2 := tOpC M N K G b h .aut rX1 rX0 rKc hi.x1.ge hG
  have p3 := tMvR M N K b h rS2 rX1 (by decide)
  rw [aBody]
  have all := p0.seq (p1.seq (p2.seq (p3.seq (p0.seq (p1.seq (p2.seq p3))))))
  exact all.mono
    le_rfl le_rfl (by unfold tABT; omega)

def tAMT (M N K G J : ℕ) : ℕ := 4 * (2 * M + 5) + J * (2 * M + tABT M N K G + 4) + 2

theorem tAutMatC (M N K G J : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hc : MatrixCaps N K b)
    (hj : b rCj ≤ J) (ho : b rS2 ≤ b rMOut) (hG : b rKc ≤ G) :
    Cert (MVM.compile autMatC) (layout M N K b) (layout M N K b) (tAMT M N K G J) := by
  have p0 := layout_copy M N K b h.top rTmp rMA hc.tmp
  have p1 := layout_copy M N K b h.top rS2 rT4KNK hc.sums
  have p2 := layout_copy M N K b h.top rCj rT2K hc.columns
  have hl := rep_fixed rCj aBody (layout M N K b) M J (tABT M N K G)
    h.top (by simpa using hj) (tABody M N K G b h hc.toInnerCaps hG)
  have po := layout_copy M N K b h.top rMOut rS2 ho
  rw [autMatC, aPre]
  exact ((p0.seq (p1.seq p2)).seq (hl.seq po)).mono le_rfl le_rfl (by unfold tAMT; omega)

def tAutT (M N K C G D R J P : ℕ) : ℕ :=
  P * (2 * M + (tAMT M N K G J + (2 * M + 5)) + 4) + 2 +
    tMatT M N K C D R J + 3 * (2 * M + 5) + tInvT M N K C D J

theorem tAutPKC (M N K C G D R J P : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hc : MatrixCaps N K b)
    (hk : b rTK ≤ D) (hi : b rCi ≤ R) (hj : b rCj ≤ J) (hp : b rP ≤ P)
    (ho : b rS2 ≤ b rMOut) (ha : b rMOut ≤ b rMA)
    (hx : b rGX ≤ b rMAd) (hs : b rSv = b rMAd) (hC : b rTK1 ≤ C) (hG : b rKc ≤ G) :
    Cert (MVM.compile autPKC) (layout M N K b) (layout M N K b) (tAutT M N K C G D R J P) := by
  have hb : Cert (MVM.compile aStep) (layout M N K b) (layout M N K b)
      (tAMT M N K G J + (2 * M + 5)) := by
    have hp := tAutMatC M N K G J b h hc hj ho hG
    have hq := layout_copy M N K b h.top rMA rMOut ha
    rw [aStep]
    exact hp.seq hq
  have p0 := rep_fixed rP aStep (layout M N K b) M P (tAMT M N K G J + (2 * M + 5))
    h.top (by simpa using hp) hb
  have p1 := tMulPKC M N K C D R J b h hc hk hi hj hC
  have p2 := layout_copy M N K b h.top rSv rMAd hs.ge
  have p3 := layout_copy M N K b h.top rMA rMOut ha
  have p4 := tGinvMulC M N K C D J b h hc hk hj hx hC
  have p5 := layout_copy M N K b h.top rMAd rSv hs.le
  rw [autPKC]
  have all := p0.seq (p1.seq (p2.seq (p3.seq (p4.seq p5))))
  exact all.mono le_rfl le_rfl
    (by unfold tAutT; omega)

/-! ### The chain -/

def tChainAutT (M N K C G D R J P : ℕ) : ℕ := 4 * (2 * M + 5) + tAutT M N K C G D R J P

theorem tChainAut (M N K C G D R J P : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hc : ChainCaps N K b)
    (hk : b rTK ≤ D) (hi : b rCi ≤ R) (hj : b rCj ≤ J) (hp : b rP ≤ P)
    (he : b rPw2 ≤ b rP) (hC : b rTK1 ≤ C) (hG : b rKc ≤ G) :
    Cert (MVM.compile autStep) (layout M N K b) (layout M N K b)
      (tChainAutT M N K C G D R J P) := by
  have p0 := layout_copy M N K b h.top rMAd rSs hc.source.le
  have p1 := layout_copy M N K b h.top rP rPw2 he
  have p2 := tAutPKC M N K C G D R J P b h hc.toMatrixCaps hk hi hj hp
    hc.out hc.again hc.inverse hc.saved hC hG
  have p3 := layout_copy M N K b h.top rMA rMOut hc.again
  have p4 := layout_copy M N K b h.top rSs rMAd hc.source.ge
  rw [autStep]
  have all := p0.seq (p1.seq (p2.seq (p3.seq p4)))
  exact all.mono le_rfl le_rfl
    (by unfold tChainAutT; omega)

def tChBodyT (M N K C G D R J P : ℕ) : ℕ :=
  chainPreTime M N K + (max (tChainAutT M N K C G D R J P) (moveAllowance M) + 1) +
    appendAllowance M

theorem tChBody (M N K C G D R J P : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hc : ChainCaps N K b)
    (hk : b rTK ≤ D) (hi : b rCi ≤ R) (hj : b rCj ≤ J) (hp : b rP ≤ P)
    (he : b rPw2 ≤ b rP) (hs : b rPw2 + b rPw2 ≤ M) (hC : b rTK1 ≤ C) (hG : b rKc ≤ G) :
    Cert (MVM.compile chBody) (layout M N K b)
      (layout M N K (Function.update b rPw2 (b rPw2 + b rPw2)))
      (tChBodyT M N K C G D R J P) := by
  have p0 := compile_chPre M N K b h hc
  have pt := tChainAut M N K C G D R J P b h hc hk hi hj hp he hC hG
  have pf := layout_drop M N K b h rSs rTBlk (by decide)
  have p1 := Cert.ifBit (tR rS2) pt pf
  have p2 := layout_append_uniform M N K b h.top rPw2 rPw2 hs
  rw [chBody]
  have all := p0.seq (p1.seq p2)
  exact all.mono le_rfl le_rfl (by unfold tChBodyT; omega)

theorem tChainLoop (M N K C G D R J P B : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hc : ChainCaps N K b)
    (hk : b rTK ≤ D) (hi : b rCi ≤ R) (hj : b rCj ≤ J) (hp : b rP ≤ P)
    (hct : b rCt ≤ B) (hpow : 2 ^ B ≤ M) (he : 2 ^ B ≤ b rP) (hC : b rTK1 ≤ C)
    (hG : b rKc ≤ G) :
    Cert (MVM.compile (.rep rCt chBody))
      (layout M N K (Function.update b rPw2 1))
      (layout M N K (Function.update b rPw2 (2 ^ B)))
      (B * (2 * M + tChBodyT M N K C G D R J P + 4) + 2) := by
  have hcol := hj
  let γ := fun j ↦ layout M N K (Function.update b rPw2 (2 ^ j))
  have hin (j : ℕ) (hj : j ≤ B) : RingInputs M N K (γ j) := by
    apply h.update_layout rPw2 (2 ^ j)
    apply le_trans _ hpow
    gcongr
  apply rep_family rCt chBody γ B (tChBodyT M N K C G D R J P) _
    (by simp [γ]) (by simpa using hct)
  · intro j hj
    have hs : 2 ^ (j + 1) ≤ M := by
      apply le_trans _ hpow
      gcongr
      omega
    have he' : 2 ^ j ≤ b rP := by
      apply le_trans _ he
      gcongr
    have hb := tChBody M N K C G D R J P (Function.update b rPw2 (2 ^ j))
      (hin j (by omega)) (hc.update_pw2 _) (by simpa using hk) (by simpa using hi)
      (by simpa using hcol) (by simpa using hp)
      (by simpa using he') (by simpa [pow_succ, Nat.mul_two] using hs)
      (by simpa using hC) (by simpa using hG)
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

def tChainT (M N K C G D R J P B : ℕ) : ℕ :=
  4 * (2 * M + 5) + B * (2 * M + tChBodyT M N K C G D R J P + 4) + 2

/-- **The chain** (tight). -/
theorem tChainC (M N K C G D R J P B : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hc : ChainCaps N K b)
    (hk : b rTK ≤ D) (hi : b rCi ≤ R) (hj : b rCj ≤ J) (hp : b rP ≤ P)
    (hct : b rCt ≤ B) (hpow : 2 ^ B ≤ M) (he : 2 ^ B ≤ b rP) (hC : b rTK1 ≤ C)
    (hG : b rKc ≤ G) :
    Cert (MVM.compile chainC) (layout M N K b)
      (layout M N K (Function.update b rPw2 (2 ^ B))) (tChainT M N K C G D R J P B) := by
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
  have pl := tChainLoop M N K C G D R J P B b h hc hk hi hj hp hct hpow he hC hG
  rw [chainC]
  have all := p0.seq (p1.seq (p2.seq (p3.seq pl)))
  exact all.mono le_rfl le_rfl
    (by unfold tChainT; omega)

end AdvancedEncryption.ExpLUT.Prog.KeyTight
