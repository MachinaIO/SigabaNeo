import PE.Impl.ExpLUT.Prog.RedKeyPktInr
/-!
# The packet stream, part 6: the loops over the slabs (generic `N K`)

* **`ptInlLoopC`**: for `w₀ < m` (the counter `ptCW` holds `w₀` bits): the four cursors from the
  word of the programming rows `ptZR = (rZ ++ rR0 ++ rRin ++ rA).flatten` (drop `w₀`, then the
  widths of the blocks before), then one packet (`ptSlabInlC`) — **`exec_ptInlLoopC`**;
* **`ptInrLoopC`**: for `t₀ < b`, `s ∈ {0, 1}`, `j < nC`: the selector of `k = (t₀, s)` (`ptSelW`) and
  the unit row `e_j` (`ptUnitW`), then one packet (`ptSlabInrC`) — **`exec_ptInrLoopC`**.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyPkt

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo.NegaG
open SigabaNeo.Lattices.Algo (encRM)
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

/-! ### Registers of the loops -/

/-- The word of the programming rows. -/
@[simp, vmreg] abbrev ptZR : Fin 64 := 49
/-- Unary width of the `Z` block. -/
@[simp, vmreg] abbrev ptTZb : Fin 64 := 50
/-- Unary width of the `R₀` block. -/
@[simp, vmreg] abbrev ptTR0b : Fin 64 := 51
/-- Unary width of the `R^in` block. -/
@[simp, vmreg] abbrev ptTRinb : Fin 64 := 52
/-- The column counter `w₀`. -/
@[simp, vmreg] abbrev ptCW : Fin 64 := 53
/-- The outer loop counter. -/
@[simp, vmreg] abbrev ptLA : Fin 64 := 54
/-- `[false]`. -/
@[simp, vmreg] abbrev ptB1 : Fin 64 := 55
/-- The inner loop counter. -/
@[simp, vmreg] abbrev ptLB : Fin 64 := 56
/-- `[true]` (in the `η` loop). -/
@[simp, vmreg] abbrev ptBT : Fin 64 := 49
/-- `j` zero words (in the `η` loop). -/
@[simp, vmreg] abbrev ptCj : Fin 64 := 50
/-- `2 t₀` zero bits (in the `η` loop). -/
@[simp, vmreg] abbrev ptT0 : Fin 64 := 51
/-- `2 b` zero bits (in the `η` loop). -/
@[simp, vmreg] abbrev ptZS : Fin 64 := 52
/-- Scratch (in the `η` loop). -/
@[simp, vmreg] abbrev ptR : Fin 64 := 53

theorem drop_append_drop (A B : List Bool) (w0 : ℕ) : ((A ++ B).drop w0).drop A.length = B.drop w0 := by
  rw [List.drop_drop, show w0 + A.length = A.length + w0 by ring, ← List.drop_drop, List.drop_left]

theorem length_flatten_rows {m : ℕ} (rows : List (List Bool)) (h : ∀ r ∈ rows, r.length = m) :
    rows.flatten.length = rows.length * m := by
  induction rows with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    rw [h a (by simp), ih (fun r hr => h r (by simp [hr]))]; ring

/-! ### The `Ā` slabs -/

/-- The four cursors of the column `w₀`. -/
def ptCursC : Code :=
  .seq (.cp ptCurZ ptZR) <| .seq (.drop ptCurZ ptCW) <| .seq (.cp ptCurR0 ptCurZ) <|
  .seq (.drop ptCurR0 ptTZb) <| .seq (.cp ptCurRin ptCurR0) <| .seq (.drop ptCurRin ptTR0b) <|
  .seq (.cp ptCurA ptCurRin) (.drop ptCurA ptTRinb)

/-- One `Ā` slab. -/
def ptInlBody : Code := .seq ptCursC (.seq ptSlabInlC (.app ptCW ptB1))

/-- **The `Ā` slabs**, `|ptTm|` of them. -/
def ptInlLoopC : Code := .seq (.clr ptCW) (.seq (.cp ptLA ptTm) (.rep ptLA ptInlBody))

theorem ptInlBody_writes : ∀ r : Fin 64, ptRowConstR r = true ∨ ptSkR r = true ∨ r = ptLA ∨
    r = ptZR ∨ r = ptTZb ∨ r = ptTR0b ∨ r = ptTRinb ∨ r = ptB1 → ptInlBody.writes r = false := by
  decide

theorem exec_ptCursC {N K : ℕ} (w : St) (w0 m : ℕ) (rZ rR0 rRin rA : List (List Bool))
    (hZr : ∀ r ∈ rZ, r.length = m) (hR0r : ∀ r ∈ rR0, r.length = m)
    (hRinr : ∀ r ∈ rRin, r.length = m)
    (hZR : w ptZR = (rZ ++ (rR0 ++ (rRin ++ rA))).flatten) (hCW : (w ptCW).length = w0)
    (hTZ : (w ptTZb).length = rZ.length * m) (hTR0 : (w ptTR0b).length = rR0.length * m)
    (hTRin : (w ptTRinb).length = rRin.length * m) :
    let v := exec N K ptCursC w
    PtCurAt w0 ptCurZ rZ v ∧ PtCurAt w0 ptCurR0 rR0 v ∧ PtCurAt w0 ptCurRin rRin v ∧
      PtCurAt w0 ptCurA rA v ∧
      ∀ r, r ≠ ptCurZ → r ≠ ptCurR0 → r ≠ ptCurRin → r ≠ ptCurA → v r = w r := by
  intro v
  have hv : v = exec N K ptCursC w := rfl
  simp only [ptCursC, exec_seq, exec_cp, exec_drop] at hv
  simp only [show (ptCurZ : Fin 64) ≠ ptCW by decide, show (ptCurR0 : Fin 64) ≠ ptTZb by decide,
    show (ptCurRin : Fin 64) ≠ ptTR0b by decide, show (ptCurA : Fin 64) ≠ ptTRinb by decide,
    if_false] at hv
  have eZ : v ptCurZ = ((rZ ++ (rR0 ++ (rRin ++ rA))).flatten).drop w0 := by
    rw [hv]; simp [Function.update_apply, hZR, hCW]
  have eR0 : v ptCurR0 = ((rR0 ++ (rRin ++ rA)).flatten).drop w0 := by
    rw [hv]; simp only [Function.update_apply]
    simp only [show (ptCurR0 : Fin 64) ≠ ptCurA by decide, show (ptCurR0 : Fin 64) ≠ ptCurRin by decide,
      show (ptCurR0 : Fin 64) = ptCurR0 from rfl, show (ptTZb : Fin 64) ≠ ptCurR0 by decide,
      show (ptTZb : Fin 64) ≠ ptCurZ by decide, show (ptCW : Fin 64) ≠ ptCurZ by decide,
      show (ptZR : Fin 64) ≠ ptCurZ by decide, if_true, if_false]
    rw [hZR, hCW, hTZ, ← length_flatten_rows rZ hZr, List.flatten_append, drop_append_drop]
  have eRin : v ptCurRin = ((rRin ++ rA).flatten).drop w0 := by
    rw [hv]; simp only [Function.update_apply]
    simp only [show (ptCurRin : Fin 64) ≠ ptCurA by decide, show (ptTR0b : Fin 64) ≠ ptCurRin by decide,
      show (ptTR0b : Fin 64) ≠ ptCurR0 by decide, show (ptTR0b : Fin 64) ≠ ptCurZ by decide,
      show (ptCurR0 : Fin 64) ≠ ptCurZ by decide,
      show (ptTZb : Fin 64) ≠ ptCurR0 by decide,
      show (ptTZb : Fin 64) ≠ ptCurZ by decide, show (ptCW : Fin 64) ≠ ptCurZ by decide,
      show (ptZR : Fin 64) ≠ ptCurZ by decide, if_true, if_false]
    rw [hZR, hCW, hTZ, hTR0, ← length_flatten_rows rZ hZr, ← length_flatten_rows rR0 hR0r,
      List.flatten_append, drop_append_drop, List.flatten_append, drop_append_drop]
  have eA : v ptCurA = rA.flatten.drop w0 := by
    rw [hv]; simp only [Function.update_apply]
    simp only [show (ptTRinb : Fin 64) ≠ ptCurA by decide, show (ptTRinb : Fin 64) ≠ ptCurRin by decide,
      show (ptTRinb : Fin 64) ≠ ptCurR0 by decide, show (ptTRinb : Fin 64) ≠ ptCurZ by decide,
      show (ptCurRin : Fin 64) ≠ ptCurR0 by decide, show (ptCurRin : Fin 64) ≠ ptCurZ by decide,
      show (ptTR0b : Fin 64) ≠ ptCurRin by decide,
      show (ptTR0b : Fin 64) ≠ ptCurR0 by decide, show (ptTR0b : Fin 64) ≠ ptCurZ by decide,
      show (ptCurR0 : Fin 64) ≠ ptCurZ by decide,
      show (ptTZb : Fin 64) ≠ ptCurR0 by decide,
      show (ptTZb : Fin 64) ≠ ptCurZ by decide, show (ptCW : Fin 64) ≠ ptCurZ by decide,
      show (ptZR : Fin 64) ≠ ptCurZ by decide, if_true, if_false]
    rw [hZR, hCW, hTZ, hTR0, hTRin, ← length_flatten_rows rZ hZr, ← length_flatten_rows rR0 hR0r,
      ← length_flatten_rows rRin hRinr, List.flatten_append, drop_append_drop, List.flatten_append,
      drop_append_drop, List.flatten_append, drop_append_drop]
  refine ⟨⟨(rR0 ++ (rRin ++ rA)).flatten, by rw [eZ, List.flatten_append]⟩,
    ⟨(rRin ++ rA).flatten, by rw [eR0, List.flatten_append]⟩,
    ⟨rA.flatten, by rw [eRin, List.flatten_append]⟩, ⟨[], by rw [eA, List.append_nil]⟩, ?_⟩
  intro r h1 h2 h3 h4
  rw [hv]; simp [Function.update_apply, h1, h2, h3, h4]

/-- The packet of the `Ā` slab `w₀`. -/
def ptInlPk (b nC nD : ℕ) (O Z Z2 ZL : List Bool) (rA rR0 rZ rRin : List (List Bool))
    (G Aa Hf SP PU : ℕ → List Bool) (A0 : List Bool) (w0 : ℕ) : List Bool :=
  ptPacket b G (ptAdLW w0 nC nD O Z rA) (fun _ => Z2) Aa (fun _ => Z2) Hf
    (ptL0LW w0 nC O Z ZL rR0) A0 SP (ptZLW w0 nC O Z rZ) (ptRdLW w0 nC nD O Z rRin) PU

/-- **The `Ā` slabs.** -/
theorem exec_ptInlLoopC {N K : ℕ} (m nC nD b : ℕ) (O Z Z2 ZL : List Bool)
    (rA rR0 rZ rRin : List (List Bool))
    (hA : ∀ r ∈ rA, r.length = m) (hR0 : ∀ r ∈ rR0, r.length = m) (hZ : ∀ r ∈ rZ, r.length = m)
    (hRin : ∀ r ∈ rRin, r.length = m)
    (lA : b * (nD * nC) ≤ rA.length) (lR0 : nC ≤ rR0.length) (lZ : 16 * nC ≤ rZ.length)
    (lRin : 16 * (nD * nC) ≤ rRin.length)
    {G Aa Hf SP PU : ℕ → List Bool} {A0 : List Bool} (w : St)
    (hin : PtSkIn b G Aa Hf SP PU A0 w) (hc : PtRowConst m nC nD O Z Z2 ZL w)
    (hZR : w ptZR = (rZ ++ (rR0 ++ (rRin ++ rA))).flatten) (hB1 : w ptB1 = [false])
    (hTZ : (w ptTZb).length = rZ.length * m) (hTR0 : (w ptTR0b).length = rR0.length * m)
    (hTRin : (w ptTRinb).length = rRin.length * m) :
    exec N K ptInlLoopC w rAinS = w rAinS ++
        (List.range m).flatMap (ptInlPk b nC nD O Z Z2 ZL rA rR0 rZ rRin G Aa Hf SP PU A0) ∧
      ∀ r, ptRowConstR r = true ∨ ptSkR r = true ∨ r = ptZR ∨ r = ptTZb ∨ r = ptTR0b ∨
        r = ptTRinb ∨ r = ptB1 → exec N K ptInlLoopC w r = w r := by
  set w1 := exec N K (.cp ptLA ptTm) (exec N K (.clr ptCW) w) with hw1
  have hfr1 : ∀ r, r ≠ ptLA → r ≠ ptCW → w1 r = w r := fun r h1 h2 => by
    simp [hw1, Function.update_apply, h1, h2]
  have hcnt : (w1 ptLA).length = m := by simp [hw1, hc.tm]
  have key := exec_rep_inv2 (N := N) (K := K) ptLA ptInlBody (ptInlBody_writes _ (by simp))
    (fun j v => v rAinS = w rAinS ++ (List.range j).flatMap
      (ptInlPk b nC nD O Z Z2 ZL rA rR0 rZ rRin G Aa Hf SP PU A0) ∧
      v ptCW = List.replicate j false) w1
    ⟨by rw [hfr1 _ (by decide) (by decide)]; simp,
     by simp [hw1, Function.update_apply]⟩
    (by
      intro j v hj hP _ hfr
      rw [hcnt] at hj
      obtain ⟨h1, h2⟩ := hP
      set v1 := Function.update v ptLA (v ptLA).tail with hv1
      have fr : ∀ r, ptRowConstR r = true ∨ ptSkR r = true ∨ r = ptZR ∨ r = ptTZb ∨
          r = ptTR0b ∨ r = ptTRinb ∨ r = ptB1 → v1 r = w r := by
        intro r hr
        have hrA : r ≠ ptLA := by
          rintro rfl; revert hr; decide
        have hrW : r ≠ ptCW := by
          rintro rfl; revert hr; decide
        rw [hv1, Function.update_of_ne hrA, hfr r (ptInlBody_writes r (by tauto)) hrA,
          hfr1 r hrA hrW]
      obtain ⟨c1, c2, c3, c4, c5⟩ := exec_ptCursC (N := N) (K := K) v1 j m rZ rR0 rRin rA hZ hR0
        hRin (by rw [fr _ (by simp)]; exact hZR)
        (by rw [hv1, Function.update_of_ne (by decide), h2, List.length_replicate])
        (by rw [fr _ (by simp)]; exact hTZ) (by rw [fr _ (by simp)]; exact hTR0)
        (by rw [fr _ (by simp)]; exact hTRin)
      set v2 := exec N K ptCursC v1 with hv2
      have fr2 : ∀ r, ptRowConstR r = true ∨ ptSkR r = true ∨ r = ptZR ∨ r = ptTZb ∨
          r = ptTR0b ∨ r = ptTRinb ∨ r = ptB1 → v2 r = w r := by
        intro r hr
        rw [c5 r (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide)
          (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide), fr r hr]
      obtain ⟨s1, s2⟩ := exec_ptSlabInlC (N := N) (K := K) m j nC nD b hj O Z Z2 ZL rA rR0 rZ rRin
        hA hR0 hZ hRin lA lR0 lZ lRin v2 (hin.of_frame fun r hr => fr2 r (by tauto))
        (hc.of_frame fun r hr => fr2 r (by tauto)) c4 c2 c1 c3
      have hE : exec N K ptInlBody v1 = exec N K (.app ptCW ptB1) (exec N K ptSlabInlC v2) := rfl
      rw [hE]
      have hw2 : ∀ r, r = ptCW ∨ r = ptB1 ∨ r = rAinS → exec N K ptSlabInlC v2 r = v2 r ∨ r = rAinS := by
        intro r hr
        rcases hr with rfl | rfl | rfl
        · exact Or.inl (exec_writes _ _ _ (by decide))
        · exact Or.inl (exec_writes _ _ _ (by decide))
        · exact Or.inr rfl
      refine ⟨?_, ?_⟩
      · rw [exec_app, Function.update_of_ne (by decide), s1]
        have e0 : v2 rAinS = v rAinS := by
          rw [c5 _ (by decide) (by decide) (by decide) (by decide), hv1,
            Function.update_of_ne (by decide)]
        rw [e0, h1, List.range_succ, List.flatMap_append]
        simp [List.append_assoc, ptInlPk]
      · rw [exec_app, Function.update_self]
        rw [exec_writes _ _ ptCW (by decide), exec_writes _ _ ptB1 (by decide),
          c5 _ (by decide) (by decide) (by decide) (by decide),
          c5 _ (by decide) (by decide) (by decide) (by decide), hv1,
          Function.update_of_ne (by decide), Function.update_of_ne (by decide), h2,
          hfr _ (ptInlBody_writes _ (by simp)) (by decide), hfr1 _ (by decide) (by decide), hB1,
          List.replicate_succ'])
  rw [hcnt] at key
  refine ⟨key.1, fun r hr => ?_⟩
  have hrA : r ≠ ptLA := by rintro rfl; revert hr; decide
  have hrW : r ≠ ptCW := by rintro rfl; revert hr; decide
  have hw : (Code.rep ptLA ptInlBody).writes r = false := by
    simp only [Code.writes, ptInlBody_writes r (by tauto), Bool.or_false, beq_eq_false_iff_ne]
    exact fun h => hrA h.symm
  show exec N K (.rep ptLA ptInlBody) w1 r = w r
  rw [exec_writes _ _ r hw, hfr1 r hrA hrW]

end AdvancedEncryption.ExpLUT.Prog.RedKeyPkt
