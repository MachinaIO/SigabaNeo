import PE.Impl.ExpLUT.Prog.RedKeyPktInl

/-!
# The packet stream, part 5: the slab codes of an `η` slab `inr (k, c')` (generic `N K`)

All slab segments of an `η` slab are zero rows except `cr_t` (`k = (t, 1)`) and `hr_t`
(`k = (t, 0)`), which are the unit row `e_{c'}` (register `ptU`). A *selector* word `ptSel`
holds the bits `[k = (t, 1), k = (t, 0)]_{t < b}`; `cr` and `hr` pop one bit each.

**`ptSubOk_inr`**, **`exec_ptSlabInrC`**: one packet of the slab.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyPkt

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo.NegaG
open SigabaNeo.Lattices.Algo (encRM)
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

/-- The selector bits. -/
@[simp, vmreg] abbrev ptSel : Fin 64 := 47
/-- The unit row. -/
@[simp, vmreg] abbrev ptU : Fin 64 := 48

/-! ### The codes -/

/-- `nD` times two zero rows (`ad_t`, `rd_i` of an `η` slab). -/
def ptAdInrC : Code := .seq (.cp ptCD ptTD) (.rep ptCD (.seq (.app rAinS ptZ2) (.app rAinS ptZ2)))
/-- `cr_t`/`hr_t` of an `η` slab: the unit row or a zero row by the next selector bit. -/
def ptSelC : Code := .seq (.ifb ptSel (.app rAinS ptU) (.app rAinS ptZ2)) (.tl ptSel)
/-- `l0` of an `η` slab. -/
def ptL0InrC : Code := .seq (.app rAinS ptZ2) (.app rAinS ptZL)

/-- **One packet of an `η` slab.** -/
def ptSlabInrC : Code := ptSkelC ptAdInrC ptSelC ptSelC ptL0InrC ptZRowC ptAdInrC

theorem ptFree_ptAdInrC : PtFree ptAdInrC := by unfold PtFree; decide
theorem ptFree_ptSelC : PtFree ptSelC := by unfold PtFree; decide
theorem ptFree_ptL0InrC : PtFree ptL0InrC := by unfold PtFree; decide

/-! ### Invariants and words -/

section Inv

variable (m nC nD : ℕ) (O Z Z2 ZL : List Bool) (sel U : List Bool)

/-- Before `ad_t`, `cr_t`. -/
def ptIadR (t : ℕ) (w : St) : Prop :=
  PtRowConst m nC nD O Z Z2 ZL w ∧ w ptSel = sel.drop (2 * t) ∧ w ptU = U

/-- Before `hr_t`. -/
def ptIhrR (t : ℕ) (w : St) : Prop :=
  PtRowConst m nC nD O Z Z2 ZL w ∧ w ptSel = sel.drop (2 * t + 1) ∧ w ptU = U

/-- In the steps. -/
def ptIzR (_ : ℕ) (w : St) : Prop := PtRowConst m nC nD O Z Z2 ZL w

/-- `nD` pairs of zero rows. -/
def ptAdRW : List Bool := (List.replicate nD (Z2 ++ Z2)).flatten

/-- `cr_t`. -/
def ptCrRW (t : ℕ) : List Bool := if sel.getD (2 * t) false then U else Z2

/-- `hr_t`. -/
def ptHrRW (t : ℕ) : List Bool := if sel.getD (2 * t + 1) false then U else Z2

end Inv

theorem hd_drop (l : List Bool) (n : ℕ) : hd (l.drop n) = l.getD n false := by
  rw [hd, List.headD_eq_head?_getD, List.head?_drop, List.getD_eq_getElem?_getD]

theorem exec_ptAdInrC {N K : ℕ} (w : St) {nD : ℕ} (hD : (w ptTD).length = nD) :
    exec N K ptAdInrC w rAinS = w rAinS ++ (List.replicate nD (w ptZ2 ++ w ptZ2)).flatten ∧
      ∀ r, r ≠ rAinS → r ≠ ptCD → exec N K ptAdInrC w r = w r := by
  set w1 := exec N K (.cp ptCD ptTD) w with hw1
  have hc : (w1 ptCD).length = nD := by simp [hw1, hD]
  have key := exec_rep_inv (N := N) (K := K) ptCD (.seq (.app rAinS ptZ2) (.app rAinS ptZ2))
    (by decide) (fun j v => v rAinS = w rAinS ++ (List.replicate j (w ptZ2 ++ w ptZ2)).flatten ∧
      ∀ r, r ≠ rAinS → r ≠ ptCD → v r = w r) w1
    ⟨by simp [hw1, Function.update_apply], fun r h1 h2 => by simp [hw1, Function.update_apply, h2]⟩
    (by
      intro j v _ hP _
      obtain ⟨h1, h2⟩ := hP
      have e2 : v ptZ2 = w ptZ2 := h2 _ (by decide) (by decide)
      refine ⟨?_, ?_⟩
      · simp only [exec_seq, exec_app, Function.update_self, Function.update_apply,
          show (ptZ2 : Fin 64) ≠ rAinS by decide, show (ptZ2 : Fin 64) ≠ ptCD by decide,
          show (rAinS : Fin 64) ≠ ptCD by decide, if_false, if_true, h1, e2, List.replicate_succ',
          List.flatten_append, List.flatten_singleton, List.append_assoc]
      · intro r r1 r2
        simp only [exec_seq, exec_app, Function.update_apply, if_neg r1, if_neg r2]
        exact h2 r r1 r2)
  rw [hc] at key
  exact key

/-- **The contract of the slab codes of an `η` slab.** -/
theorem ptSubOk_inr {N K : ℕ} (m nC nD b : ℕ) (O Z Z2 ZL sel U : List Bool) :
    PtSubOk N K b ptAdInrC ptSelC ptSelC ptL0InrC ptZRowC ptAdInrC
      (ptIadR m nC nD O Z Z2 ZL sel U) (ptIadR m nC nD O Z Z2 ZL sel U)
      (ptIhrR m nC nD O Z Z2 ZL sel U) (ptIzR m nC nD O Z Z2 ZL) (ptIzR m nC nD O Z Z2 ZL)
      (fun _ => ptAdRW nD Z2) (ptCrRW Z2 sel U) (ptHrRW Z2 sel U) (Z2 ++ ZL) (fun _ => Z2)
      (fun _ => ptAdRW nD Z2) where
  fad := ptFree_ptAdInrC
  fcr := ptFree_ptSelC
  fhr := ptFree_ptSelC
  fl0 := ptFree_ptL0InrC
  fz := ptFree_ptZRowC
  frd := ptFree_ptAdInrC
  sad t := fun w r v hr ⟨h1, h2, h3⟩ =>
    ⟨h1.update r (ptSkW_rowConst r hr) v,
     by rw [Function.update_of_ne (Ne.symm (ptSkW_ne r ptSel rfl (by decide) hr))]; exact h2,
     by rw [Function.update_of_ne (Ne.symm (ptSkW_ne r ptU rfl (by decide) hr))]; exact h3⟩
  scr t := fun w r v hr ⟨h1, h2, h3⟩ =>
    ⟨h1.update r (ptSkW_rowConst r hr) v,
     by rw [Function.update_of_ne (Ne.symm (ptSkW_ne r ptSel rfl (by decide) hr))]; exact h2,
     by rw [Function.update_of_ne (Ne.symm (ptSkW_ne r ptU rfl (by decide) hr))]; exact h3⟩
  shr t := fun w r v hr ⟨h1, h2, h3⟩ =>
    ⟨h1.update r (ptSkW_rowConst r hr) v,
     by rw [Function.update_of_ne (Ne.symm (ptSkW_ne r ptSel rfl (by decide) hr))]; exact h2,
     by rw [Function.update_of_ne (Ne.symm (ptSkW_ne r ptU rfl (by decide) hr))]; exact h3⟩
  sz i := fun w r v hr h1 => h1.update r (ptSkW_rowConst r hr) v
  srd i := fun w r v hr h1 => h1.update r (ptSkW_rowConst r hr) v
  had t _ := by
    intro w ⟨h1, h2, h3⟩
    obtain ⟨e1, e2⟩ := exec_ptAdInrC (N := N) (K := K) w h1.td
    refine ⟨by rw [e1, h1.z2]; rfl, h1.of_frame fun r hr => e2 r (by revert hr; revert r; decide)
      (by revert hr; revert r; decide), by rw [e2 _ (by decide) (by decide)]; exact h2,
      by rw [e2 _ (by decide) (by decide)]; exact h3⟩
  hcr t _ := by
    intro w ⟨h1, h2, h3⟩
    have hh : hd (w ptSel) = sel.getD (2 * t) false := by rw [h2, hd_drop]
    simp only [ptSelC, exec_seq, exec_ifb, hh]
    split_ifs with hb
    · refine ⟨by rw [ptCrRW, if_pos hb]; simp [Function.update_apply, h3], ?_, ?_, ?_⟩
      · exact (h1.update _ rfl _).update _ rfl _
      · simp [Function.update_apply, h2, List.tail_drop]
      · simp [Function.update_apply, h3]
    · refine ⟨by rw [ptCrRW, if_neg hb]; simp [Function.update_apply, h1.z2], ?_, ?_, ?_⟩
      · exact (h1.update _ rfl _).update _ rfl _
      · simp [Function.update_apply, h2, List.tail_drop]
      · simp [Function.update_apply, h3]
  hhr t _ := by
    intro w ⟨h1, h2, h3⟩
    have hh : hd (w ptSel) = sel.getD (2 * t + 1) false := by rw [h2, hd_drop]
    simp only [ptSelC, exec_seq, exec_ifb, hh]
    split_ifs with hb
    · refine ⟨by rw [ptHrRW, if_pos hb]; simp [Function.update_apply, h3], ?_, ?_, ?_⟩
      · exact (h1.update _ rfl _).update _ rfl _
      · simp [Function.update_apply, h2, List.tail_drop]; congr 1
      · simp [Function.update_apply, h3]
    · refine ⟨by rw [ptHrRW, if_neg hb]; simp [Function.update_apply, h1.z2], ?_, ?_, ?_⟩
      · exact (h1.update _ rfl _).update _ rfl _
      · simp [Function.update_apply, h2, List.tail_drop]; congr 1
      · simp [Function.update_apply, h3]
  hl0 := by
    intro w ⟨h1, _, _⟩
    refine ⟨?_, ?_⟩
    · simp only [ptL0InrC, exec_seq, exec_app, Function.update_self, Function.update_apply,
        show (ptZL : Fin 64) ≠ rAinS by decide, if_false, h1.z2, h1.zl, List.append_assoc]
    · simp only [ptL0InrC, exec_seq, exec_app]
      exact (h1.update _ rfl _).update _ rfl _
  hz i _ := by
    intro w h1
    exact ⟨by simp [ptZRowC, h1.z2], by simp only [ptZRowC, exec_app]; exact h1.update _ rfl _⟩
  hrd i _ := by
    intro w h1
    obtain ⟨e1, e2⟩ := exec_ptAdInrC (N := N) (K := K) w h1.td
    exact ⟨by rw [e1, h1.z2]; rfl, h1.of_frame fun r hr => e2 r (by revert hr; revert r; decide)
      (by revert hr; revert r; decide)⟩

/-- **One packet of an `η` slab.** -/
theorem exec_ptSlabInrC {N K : ℕ} (m nC nD b : ℕ) (O Z Z2 ZL sel U : List Bool)
    {G Aa Hf SP PU : ℕ → List Bool} {A0 : List Bool} (w : St)
    (hin : PtSkIn b G Aa Hf SP PU A0 w) (hc : PtRowConst m nC nD O Z Z2 ZL w)
    (hs : w ptSel = sel) (hu : w ptU = U) :
    exec N K ptSlabInrC w rAinS = w rAinS ++ ptPacket b G (fun _ => ptAdRW nD Z2) (ptCrRW Z2 sel U)
        Aa (ptHrRW Z2 sel U) Hf (Z2 ++ ZL) A0 SP (fun _ => Z2) (fun _ => ptAdRW nD Z2) PU ∧
      (∀ r, ptSkR r = true → exec N K ptSlabInrC w r = w r) := by
  obtain ⟨h1, -, h3⟩ := exec_ptSkelC (ptSubOk_inr (N := N) (K := K) m nC nD b O Z Z2 ZL sel U) w
    hin ⟨hc, by simpa using hs, hu⟩
  exact ⟨h1, h3⟩

end AdvancedEncryption.ExpLUT.Prog.RedKeyPkt
