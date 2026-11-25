import PE.Impl.ExpLUT.Prog.RedKeyPktRows
/-!
# The packet stream, part 4: the slab codes of an `Ā` slab `inl w₀` (generic `N K`)

The six slab codes of `ptSkelC` for the slab `inl w₀` read the column `w₀` of four blocks of rows
through cursors (`RedKeyPktRows`): `R^aut` (`ptCurA`, `nD · nC` rows per bit), `R₀` (`ptCurR0`),
`Z` (`ptCurZ`, `nC` rows per step), `R^in` (`ptCurRin`, `nD · nC` rows per step); `cr`, `hr` are the
zero row `ptZ2`, `l0` ends with `ptZL`.

**`ptSubOk_inl`**: the contract `PtSubOk` with the phase invariants `ptIadL …` (cursors advanced by
the number of rounds done) — hence (**`exec_ptSkelC_inl`**) one packet of the slab.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyPkt

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo.NegaG
open SigabaNeo.Lattices.Algo (encRM)
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

/-! ### The codes -/

/-- `ad_t` of an `Ā` slab. -/
def ptAdInlC : Code := ptDigRowsC ptCurA
/-- A zero row (`cr_t`, `hr_t` of an `Ā` slab). -/
def ptZRowC : Code := .app rAinS ptZ2
/-- `l0` of an `Ā` slab. -/
def ptL0InlC : Code := .seq (ptBitRowC ptCurR0 rAinS) (.app rAinS ptZL)
/-- `z_i` of an `Ā` slab. -/
def ptZInlC : Code := ptBitRowC ptCurZ rAinS
/-- `rd_i` of an `Ā` slab. -/
def ptRdInlC : Code := ptDigRowsC ptCurRin

/-- **One packet of an `Ā` slab.** -/
def ptSlabInlC : Code := ptSkelC ptAdInlC ptZRowC ptZRowC ptL0InlC ptZInlC ptRdInlC

theorem ptFree_ptAdInlC : PtFree ptAdInlC := by unfold PtFree; decide
theorem ptFree_ptZRowC : PtFree ptZRowC := by unfold PtFree; decide
theorem ptFree_ptL0InlC : PtFree ptL0InlC := by unfold PtFree; decide
theorem ptFree_ptZInlC : PtFree ptZInlC := by unfold PtFree; decide
theorem ptFree_ptRdInlC : PtFree ptRdInlC := by unfold PtFree; decide

/-! ### The constants of the slab codes -/

/-- The constants of the slab codes: widths and words. -/
structure PtRowConst (m nC nD : ℕ) (O Z Z2 ZL : List Bool) (w : St) : Prop where
  tm : (w ptTm).length = m
  tc : (w ptTC).length = nC
  td : (w ptTD).length = nD
  one : w ptOne = O
  zero : w ptZero = Z
  z2 : w ptZ2 = Z2
  zl : w ptZL = ZL

/-- The registers of the constants. -/
def ptRowConstR (r : Fin 64) : Bool :=
  r == ptTm || r == ptTC || r == ptTD || r == ptOne || r == ptZero || r == ptZ2 || r == ptZL

theorem PtRowConst.of_frame {m nC nD : ℕ} {O Z Z2 ZL : List Bool} {w w' : St}
    (h : PtRowConst m nC nD O Z Z2 ZL w) (hw : ∀ r, ptRowConstR r = true → w' r = w r) :
    PtRowConst m nC nD O Z Z2 ZL w' :=
  ⟨by rw [hw _ rfl]; exact h.tm, by rw [hw _ rfl]; exact h.tc, by rw [hw _ rfl]; exact h.td,
   by rw [hw _ rfl]; exact h.one, by rw [hw _ rfl]; exact h.zero, by rw [hw _ rfl]; exact h.z2,
   by rw [hw _ rfl]; exact h.zl⟩

theorem PtRowConst.update {m nC nD : ℕ} {O Z Z2 ZL : List Bool} {w : St}
    (h : PtRowConst m nC nD O Z Z2 ZL w) (r : Fin 64) (hr : ptRowConstR r = false) (v : List Bool) :
    PtRowConst m nC nD O Z Z2 ZL (Function.update w r v) :=
  h.of_frame fun q hq => Function.update_of_ne (fun e => by subst e; rw [hq] at hr; cases hr) _ _

/-- A cursor register at the rows. -/
def PtCurAt (w0 : ℕ) (q : Fin 64) (rows : List (List Bool)) (w : St) : Prop :=
  ∃ T, w q = (rows.flatten ++ T).drop w0

theorem PtCurAt.update {w0 : ℕ} {q : Fin 64} {rows : List (List Bool)} {w : St}
    (h : PtCurAt w0 q rows w) (r : Fin 64) (hr : r ≠ q) (v : List Bool) :
    PtCurAt w0 q rows (Function.update w r v) := by
  obtain ⟨T, hT⟩ := h
  exact ⟨T, by rw [Function.update_of_ne (Ne.symm hr)]; exact hT⟩

theorem PtCurAt.of_eq {w0 : ℕ} {q : Fin 64} {rows : List (List Bool)} {w w' : St}
    (h : PtCurAt w0 q rows w) (e : w' q = w q) : PtCurAt w0 q rows w' := by
  obtain ⟨T, hT⟩ := h
  exact ⟨T, by rw [e]; exact hT⟩

/-! ### The phase invariants -/

section Inv

variable (m w0 nC nD b : ℕ) (O Z Z2 ZL : List Bool) (rA rR0 rZ rRin : List (List Bool))

/-- Before `ad_t`. -/
def ptIadL (t : ℕ) (w : St) : Prop :=
  PtRowConst m nC nD O Z Z2 ZL w ∧ PtCurAt w0 ptCurA (rA.drop (t * (nD * nC))) w ∧
    PtCurAt w0 ptCurR0 rR0 w ∧ PtCurAt w0 ptCurZ rZ w ∧ PtCurAt w0 ptCurRin rRin w

/-- Before `cr_t` and `hr_t`. -/
def ptIcrL (t : ℕ) (w : St) : Prop := ptIadL m w0 nC nD O Z Z2 ZL rA rR0 rZ rRin (t + 1) w

/-- Before `z_i`. -/
def ptIzL (i : ℕ) (w : St) : Prop :=
  PtRowConst m nC nD O Z Z2 ZL w ∧ PtCurAt w0 ptCurZ (rZ.drop (i * nC)) w ∧
    PtCurAt w0 ptCurRin (rRin.drop (i * (nD * nC))) w

/-- Before `rd_i`. -/
def ptIrdL (i : ℕ) (w : St) : Prop :=
  PtRowConst m nC nD O Z Z2 ZL w ∧ PtCurAt w0 ptCurZ (rZ.drop ((i + 1) * nC)) w ∧
    PtCurAt w0 ptCurRin (rRin.drop (i * (nD * nC))) w

/-- The words of the slab segments. -/
def ptAdLW (t : ℕ) : List Bool := ptDigW O Z w0 nC nD ((rA.drop (t * (nD * nC))).take (nD * nC))
def ptL0LW : List Bool := ptEmit O Z (ptCol w0 (rR0.take nC)) ++ ZL
def ptZLW (i : ℕ) : List Bool := ptEmit O Z (ptCol w0 ((rZ.drop (i * nC)).take nC))
def ptRdLW (i : ℕ) : List Bool := ptDigW O Z w0 nC nD ((rRin.drop (i * (nD * nC))).take (nD * nC))

end Inv

theorem ptSkW_rowConst (r : Fin 64) (h : ptSkW r = true ∨ r = rAinS) : ptRowConstR r = false := by
  revert h; revert r; decide

theorem ptSkW_ne (r q : Fin 64) (hq : ptSkW q = false) (hq0 : q ≠ rAinS) (h : ptSkW r = true ∨ r = rAinS) :
    r ≠ q := by
  rintro rfl
  rcases h with h | h
  · rw [h] at hq; cases hq
  · exact hq0 h

theorem curAt_split {w0 : ℕ} {q : Fin 64} {rows : List (List Bool)} {w : St}
    (h : PtCurAt w0 q rows w) (n : ℕ) :
    ∃ T, w q = (((rows.take n) ++ rows.drop n).flatten ++ T).drop w0 := by
  obtain ⟨T, hT⟩ := h
  exact ⟨T, by rw [List.take_append_drop]; exact hT⟩

/-- **The contract of the slab codes of an `Ā` slab.** -/
theorem ptSubOk_inl {N K : ℕ} (m w0 nC nD b : ℕ) (hw0 : w0 < m) (O Z Z2 ZL : List Bool)
    (rA rR0 rZ rRin : List (List Bool))
    (hA : ∀ r ∈ rA, r.length = m) (hR0 : ∀ r ∈ rR0, r.length = m) (hZ : ∀ r ∈ rZ, r.length = m)
    (hRin : ∀ r ∈ rRin, r.length = m)
    (lA : b * (nD * nC) ≤ rA.length) (lR0 : nC ≤ rR0.length) (lZ : 16 * nC ≤ rZ.length)
    (lRin : 16 * (nD * nC) ≤ rRin.length) :
    PtSubOk N K b ptAdInlC ptZRowC ptZRowC ptL0InlC ptZInlC ptRdInlC
      (ptIadL m w0 nC nD O Z Z2 ZL rA rR0 rZ rRin) (ptIcrL m w0 nC nD O Z Z2 ZL rA rR0 rZ rRin)
      (ptIcrL m w0 nC nD O Z Z2 ZL rA rR0 rZ rRin) (ptIzL m w0 nC nD O Z Z2 ZL rZ rRin)
      (ptIrdL m w0 nC nD O Z Z2 ZL rZ rRin) (ptAdLW w0 nC nD O Z rA) (fun _ => Z2) (fun _ => Z2)
      (ptL0LW w0 nC O Z ZL rR0) (ptZLW w0 nC O Z rZ) (ptRdLW w0 nC nD O Z rRin) where
  fad := ptFree_ptAdInlC
  fcr := ptFree_ptZRowC
  fhr := ptFree_ptZRowC
  fl0 := ptFree_ptL0InlC
  fz := ptFree_ptZInlC
  frd := ptFree_ptRdInlC
  sad t := fun w r v hr ⟨h1, h2, h3, h4, h5⟩ =>
    ⟨h1.update r (ptSkW_rowConst r hr) v, h2.update r (ptSkW_ne r _ rfl (by decide) hr) v,
     h3.update r (ptSkW_ne r _ rfl (by decide) hr) v, h4.update r (ptSkW_ne r _ rfl (by decide) hr) v,
     h5.update r (ptSkW_ne r _ rfl (by decide) hr) v⟩
  scr t := fun w r v hr ⟨h1, h2, h3, h4, h5⟩ =>
    ⟨h1.update r (ptSkW_rowConst r hr) v, h2.update r (ptSkW_ne r _ rfl (by decide) hr) v,
     h3.update r (ptSkW_ne r _ rfl (by decide) hr) v, h4.update r (ptSkW_ne r _ rfl (by decide) hr) v,
     h5.update r (ptSkW_ne r _ rfl (by decide) hr) v⟩
  shr t := fun w r v hr ⟨h1, h2, h3, h4, h5⟩ =>
    ⟨h1.update r (ptSkW_rowConst r hr) v, h2.update r (ptSkW_ne r _ rfl (by decide) hr) v,
     h3.update r (ptSkW_ne r _ rfl (by decide) hr) v, h4.update r (ptSkW_ne r _ rfl (by decide) hr) v,
     h5.update r (ptSkW_ne r _ rfl (by decide) hr) v⟩
  sz i := fun w r v hr ⟨h1, h2, h3⟩ =>
    ⟨h1.update r (ptSkW_rowConst r hr) v, h2.update r (ptSkW_ne r _ rfl (by decide) hr) v,
     h3.update r (ptSkW_ne r _ rfl (by decide) hr) v⟩
  srd i := fun w r v hr ⟨h1, h2, h3⟩ =>
    ⟨h1.update r (ptSkW_rowConst r hr) v, h2.update r (ptSkW_ne r _ rfl (by decide) hr) v,
     h3.update r (ptSkW_ne r _ rfl (by decide) hr) v⟩
  had t ht := by
    intro w ⟨h1, h2, h3, h4, h5⟩
    unfold ptAdInlC
    obtain ⟨T, hT⟩ := curAt_split h2 (nD * nC)
    have hlen : ((rA.drop (t * (nD * nC))).take (nD * nC)).length = nD * nC := by
      rw [List.length_take, List.length_drop]
      have := Nat.mul_le_mul_right (nD * nC) (Nat.succ_le_of_lt ht)
      rw [Nat.succ_mul] at this
      omega
    obtain ⟨e1, e2, e3⟩ := exec_ptDigRowsC (N := N) (K := K) ptCurA (by unfold ptDigQ; decide) w
      h1.tm hw0 h1.tc h1.td _ _
      (fun r hr => hA r (List.mem_of_mem_drop (List.mem_of_mem_take hr))) hlen T hT
    refine ⟨by rw [e1, h1.one, h1.zero]; rfl, ?_, ?_, ?_, ?_, ?_⟩
    · exact h1.of_frame fun r hr => e3 r (by revert hr; revert r; decide)
        (by revert hr; revert r; decide) (by revert hr; revert r; decide)
        (by revert hr; revert r; decide) (by revert hr; revert r; decide)
    · refine ⟨T, ?_⟩
      rw [e2, List.drop_drop, show t * (nD * nC) + nD * nC = (t + 1) * (nD * nC) by ring]
    · exact h3.of_eq (e3 _ (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact h4.of_eq (e3 _ (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact h5.of_eq (e3 _ (by decide) (by decide) (by decide) (by decide) (by decide))
  hcr t ht := by
    intro w ⟨h1, h2, h3, h4, h5⟩
    refine ⟨by simp [ptZRowC, h1.z2], ?_⟩
    simp only [ptZRowC, exec_app]
    exact ⟨h1.update _ rfl _, h2.update _ (by decide) _, h3.update _ (by decide) _,
      h4.update _ (by decide) _, h5.update _ (by decide) _⟩
  hhr t ht := by
    intro w ⟨h1, h2, h3, h4, h5⟩
    refine ⟨by simp [ptZRowC, h1.z2], ?_⟩
    simp only [ptZRowC, exec_app]
    exact ⟨h1.update _ rfl _, h2.update _ (by decide) _, h3.update _ (by decide) _,
      h4.update _ (by decide) _, h5.update _ (by decide) _⟩
  hl0 := by
    intro w ⟨h1, h2, h3, h4, h5⟩
    obtain ⟨T, hT⟩ := curAt_split h3 nC
    obtain ⟨e1, e2, e3⟩ := exec_ptBitRowC (N := N) (K := K) ptCurR0 rAinS (by decide) (by decide) w
      h1.tm hw0 _ _ (fun r hr => hR0 r (List.mem_of_mem_take hr))
      (by rw [List.length_take, h1.tc]; omega) T hT
    set w1 := exec N K (ptBitRowC ptCurR0 rAinS) w with hw1
    have c1 : PtRowConst m nC nD O Z Z2 ZL w1 :=
      h1.of_frame fun r hr => e3 r (by revert hr; revert r; decide)
        (by revert hr; revert r; decide) (by revert hr; revert r; decide)
    have hE : exec N K ptL0InlC w = exec N K (.app rAinS ptZL) w1 := rfl
    rw [hE]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [exec_app, Function.update_self]
      rw [e1, h1.one, h1.zero, c1.zl]; simp [ptL0LW, List.append_assoc]
    · simp only [exec_app]; exact c1.update _ rfl _
    · simp only [exec_app, Nat.zero_mul, List.drop_zero]
      exact (h4.of_eq (e3 _ (by decide) (by decide) (by decide))).update _ (by decide) _
    · simp only [exec_app, Nat.zero_mul, List.drop_zero]
      exact (h5.of_eq (e3 _ (by decide) (by decide) (by decide))).update _ (by decide) _
  hz i hi := by
    intro w ⟨h1, h2, h3⟩
    unfold ptZInlC
    have := Nat.mul_le_mul_right nC (Nat.succ_le_of_lt hi)
    rw [Nat.succ_mul] at this
    obtain ⟨T, hT⟩ := curAt_split h2 nC
    obtain ⟨e1, e2, e3⟩ := exec_ptBitRowC (N := N) (K := K) ptCurZ rAinS (by decide) (by decide) w
      h1.tm hw0 _ _ (fun r hr => hZ r (List.mem_of_mem_drop (List.mem_of_mem_take hr)))
      (by rw [List.length_take, List.length_drop, h1.tc]; omega) T hT
    refine ⟨by rw [e1, h1.one, h1.zero]; rfl, ?_, ?_, ?_⟩
    · exact h1.of_frame fun r hr => e3 r (by revert hr; revert r; decide)
        (by revert hr; revert r; decide) (by revert hr; revert r; decide)
    · refine ⟨T, ?_⟩
      rw [e2, List.drop_drop, show i * nC + nC = (i + 1) * nC by ring]
    · exact h3.of_eq (e3 _ (by decide) (by decide) (by decide))
  hrd i hi := by
    intro w ⟨h1, h2, h3⟩
    unfold ptRdInlC
    obtain ⟨T, hT⟩ := curAt_split h3 (nD * nC)
    have hlen : ((rRin.drop (i * (nD * nC))).take (nD * nC)).length = nD * nC := by
      rw [List.length_take, List.length_drop]
      have := Nat.mul_le_mul_right (nD * nC) (Nat.succ_le_of_lt hi)
      rw [Nat.succ_mul] at this
      omega
    obtain ⟨e1, e2, e3⟩ := exec_ptDigRowsC (N := N) (K := K) ptCurRin (by unfold ptDigQ; decide) w
      h1.tm hw0 h1.tc h1.td _ _
      (fun r hr => hRin r (List.mem_of_mem_drop (List.mem_of_mem_take hr))) hlen T hT
    refine ⟨by rw [e1, h1.one, h1.zero]; rfl, ?_, ?_, ?_⟩
    · exact h1.of_frame fun r hr => e3 r (by revert hr; revert r; decide)
        (by revert hr; revert r; decide) (by revert hr; revert r; decide)
        (by revert hr; revert r; decide) (by revert hr; revert r; decide)
    · exact h2.of_eq (e3 _ (by decide) (by decide) (by decide) (by decide) (by decide))
    · refine ⟨T, ?_⟩
      rw [e2, List.drop_drop, show i * (nD * nC) + nD * nC = (i + 1) * (nD * nC) by ring]

/-- **One packet of an `Ā` slab.** -/
theorem exec_ptSlabInlC {N K : ℕ} (m w0 nC nD b : ℕ) (hw0 : w0 < m) (O Z Z2 ZL : List Bool)
    (rA rR0 rZ rRin : List (List Bool))
    (hA : ∀ r ∈ rA, r.length = m) (hR0 : ∀ r ∈ rR0, r.length = m) (hZ : ∀ r ∈ rZ, r.length = m)
    (hRin : ∀ r ∈ rRin, r.length = m)
    (lA : b * (nD * nC) ≤ rA.length) (lR0 : nC ≤ rR0.length) (lZ : 16 * nC ≤ rZ.length)
    (lRin : 16 * (nD * nC) ≤ rRin.length)
    {G Aa Hf SP PU : ℕ → List Bool} {A0 : List Bool} (w : St)
    (hin : PtSkIn b G Aa Hf SP PU A0 w) (hc : PtRowConst m nC nD O Z Z2 ZL w)
    (cA : PtCurAt w0 ptCurA rA w) (cR0 : PtCurAt w0 ptCurR0 rR0 w) (cZ : PtCurAt w0 ptCurZ rZ w)
    (cRin : PtCurAt w0 ptCurRin rRin w) :
    exec N K ptSlabInlC w rAinS = w rAinS ++ ptPacket b G (ptAdLW w0 nC nD O Z rA) (fun _ => Z2) Aa
        (fun _ => Z2) Hf (ptL0LW w0 nC O Z ZL rR0) A0 SP (ptZLW w0 nC O Z rZ)
        (ptRdLW w0 nC nD O Z rRin) PU ∧
      (∀ r, ptSkR r = true → exec N K ptSlabInlC w r = w r) := by
  obtain ⟨h1, -, h3⟩ := exec_ptSkelC (ptSubOk_inl (N := N) (K := K) m w0 nC nD b hw0 O Z Z2 ZL
    rA rR0 rZ rRin hA hR0 hZ hRin lA lR0 lZ lRin) w hin
    ⟨hc, by simpa using cA, cR0, cZ, cRin⟩
  exact ⟨h1, h3⟩

end AdvancedEncryption.ExpLUT.Prog.RedKeyPkt
