import PE.Impl.ExpLUT.Prog.DecTightLutF
import PE.Impl.ExpLUT.Prog.DecTightLutT
import PE.Impl.ExpLUT.Prog.DecTightPre

/-!
# Tight clock of the `Dec` code: the whole code (part 4)

The block certificates are glued along the structure of `decCode` with the generic lemmas
`codeOK_seqT`/`codeOK_monoT` (no block is unfolded):

* a step `stepC i last = mulC i ; tblC i ; lutC last ; copies` keeps the invariant `dtBs`
  (`dt_stepF`, `dt_stepT`), so the sixteen steps do too (`dt_stepsN`);
* **`dt_decCode`**: from `dtB0`, the compiled code ends below `dtBend` within `dtTvm ≤ 2^224`
  steps (operation area `2^40`).
-/

namespace AdvancedEncryption.ExpLUT.Prog.DecTight

set_option autoImplicit false

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.RingVM
open AdvancedEncryption.ExpLUT.Prog.DecT

/-- The clock of a non-final step. -/
def dtTstepF : ℕ := dtTmul + (dtTtbl + (dtTlutF + dtTtailF))
/-- The clock of the final step. -/
def dtTstepT : ℕ := dtTmul + (dtTtbl + (dtTlutT + dtTtailT))

/-- The ring-word machine clock at the concrete parameters. -/
abbrev DOK (c : Code) (B B' : ℕ) (T : ℕ) : Prop :=
  CodeOK (2 ^ 40) (2 ^ 24) (2 ^ 16) c (toB B) (toB B') T

theorem dt_stepF (i : ℕ) (hi : i < 16) : DOK (stepC i false) dtBs dtBs dtTstepF := by
  show DOK (.seq (mulC i) (.seq (tblC i) (.seq (lutC false) (.seq (.cp 177 162)
    (.seq (.cp 176 163) .nop))))) dtBs dtBs dtTstepF
  exact codeOK_seqT (dtChk_ok (dtChk_mul i hi)) (codeOK_seqT (dtChk_ok (dtChk_tbl i hi))
    (codeOK_seqT (dtChk_ok dtChk_lutF) (dtChk_ok dtChk_tailF)))

theorem dt_stepT : DOK (stepC 15 true) dtBs dtBs dtTstepT := by
  show DOK (.seq (mulC 15) (.seq (tblC 15) (.seq (lutC true) (.seq (.cp 177 162)
    (.seq (.cp 176 163) .nop))))) dtBs dtBs dtTstepT
  exact codeOK_seqT (dtChk_ok (dtChk_mul 15 (by decide))) (codeOK_seqT
    (dtChk_ok (dtChk_tbl 15 (by decide))) (codeOK_seqT (dtChk_ok dtChk_lutT)
      (dtChk_ok dtChk_tailT)))

/-- **The first `n ≤ 15` steps keep the invariant.** -/
theorem dt_stepsN : ∀ n, n ≤ 15 → DOK (stepsN n) dtBs dtBs (3 + n * dtTstepF)
  | 0, _ => codeOK_monoT (codeOK_nopT _ _ _ _) le_rfl le_rfl (by simp)
  | n + 1, h => by
    have hd : decide (n = 15) = false := decide_eq_false (by omega)
    show DOK (.seq (stepsN n) (stepC n (decide (n = 15)))) dtBs dtBs _
    rw [hd]
    exact codeOK_monoT (codeOK_seqT (dt_stepsN n (by omega)) (dt_stepF n (by omega))) le_rfl
      le_rfl (by rw [Nat.succ_mul]; omega)

theorem dt_steps16 : DOK (stepsN 16) dtBs dtBs (3 + 15 * dtTstepF + dtTstepT) :=
  codeOK_seqT (dt_stepsN 15 le_rfl) dt_stepT

/-- The clock of the compiled `Dec` code. -/
def dtTvm : ℕ := dtTS1 + (dtTS2 + (dtTF + ((dtTc1 + (dtTc2 + ((3 + 15 * dtTstepF + dtTstepT) + 3))) +
  dtTfin)))

/-- **The compiled `Dec` code**: from `dtB0` it ends below `dtBend` within `dtTvm` steps. -/
theorem dt_decCode : DOK decCode dtB0 dtBend dtTvm := by
  have hdev : DOK devalC dtB3 dtBs (dtTc1 + (dtTc2 + ((3 + 15 * dtTstepF + dtTstepT) + 3))) := by
    show DOK (.seq (.cp 177 61) (.seq (.cp 176 71) (.seq (stepsN 16) .nop))) dtB3 dtBs _
    exact codeOK_seqT (dtChk_ok dtChk_c1) (codeOK_seqT (dtChk_ok dtChk_c2)
      (codeOK_seqT dt_steps16 (codeOK_nopT _ _ _ _)))
  show DOK (.seq splitSkC (.seq splitCtC (.seq fixC (.seq devalC finC)))) dtB0 dtBend dtTvm
  exact codeOK_seqT (dtChk_ok dtChk_S1) (codeOK_seqT (dtChk_ok dtChk_S2)
    (codeOK_seqT (dtChk_ok dtChk_F) (codeOK_seqT hdev (dtChk_ok dtChk_fin))))

set_option exponentiation.threshold 2000 in
theorem dtTvm_le : dtTvm ≤ 2 ^ 224 := by
  unfold dtTvm dtTstepF dtTstepT dtTS1 dtTS2 dtTF dtTc1 dtTc2 dtTmul dtTtbl dtTlutF dtTlutT
    dtTtailF dtTtailT dtTfin
  norm_num

end AdvancedEncryption.ExpLUT.Prog.DecTight
