import PE.Impl.ExpLUT.Prog.RedKeyTNeg
/-!
# Module 9: the key component with its scratch tapes cleared (`rkKeyPT`)

`RedKeyTNeg` shows that the static length bound of `rkKeyP mid` (`RedKeyMFront`) is nonzero on
tape `2` (and on the guard's scratch tape `5`), so `Sub.KeyComp.len` fails. The fix only appends
`clr`s on tapes that are blank at run time, so the law is unchanged:

* `rkLeChkT`, `rkEqChkT`: the two tests followed by `clr 4 ⨾ clr 5` (local scratch; global `5`, `6`);
* `rkInvPT`: `rkInvP` with `⨾ clr 2` at the end (the counter of `natP`/`appT`);
* `rkKeyOfT vP`, **`rkKeyPT mid := rkKeyOfT (rkValidP mid)`**; **`wf_rkKeyPT`**, **`law_rkKeyPT`**
  (from `RkMidOk mid`, exactly as `law_rkKeyP`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyT

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.Prog SigabaNeo.Tape.XProg
  Cslib Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open AdvancedEncryption.ExpLUT.Prog.RedKeyM
open AdvancedEncryption.ExpLUT.Params
open scoped SigabaNeo.Tape.Prog

theorem io2_upd2_clr56 (a C x : List Bool) :
    Function.update (Function.update (Function.update (io2 (R := 245) a C []) 2 x) 5 []) 6 [] =
      Function.update (io2 (R := 245) a C []) 2 x := by
  funext t
  by_cases h6 : t = 6
  · subst h6; simp [io2, Function.update_apply]
  by_cases h5 : t = 5
  · subst h5; simp [io2, Function.update_apply]
  simp [Function.update_of_ne h5, Function.update_of_ne h6]

/-- `tape 2 := [decide (|C| ≤ predLen)]`, the scratch tapes `5`, `6` cleared. -/
def rkLeChkT : SigabaNeo.Tape.Prog 247 := rkLeChk ⨾ clr 5 ⨾ clr 6

/-- `tape 2 := [decide (ValidC C)]`, the scratch tapes `5`, `6` cleared. -/
def rkEqChkT : SigabaNeo.Tape.Prog 247 := rkEqChk ⨾ clr 5 ⨾ clr 6

theorem run_rkLeChkT (a C : List Bool) :
    rkLeChkT.run (io2 (R := 245) a C []) =
      Function.update (io2 (R := 245) a C []) 2 [decide (C.length ≤ predLen)] := by
  rw [rkLeChkT, run_seq, run_seq, run_rkLeChk, run_clear, run_clear, io2_upd2_clr56]

theorem run_rkEqChkT (a C : List Bool) :
    rkEqChkT.run (io2 (R := 245) a C []) =
      Function.update (io2 (R := 245) a C []) 2 [decide (C.length = predLen)] := by
  rw [rkEqChkT, run_seq, run_seq, run_rkEqChk, run_clear, run_clear, io2_upd2_clr56]

theorem coinFree_rkLeChkT : rkLeChkT.CoinFree :=
  coinFree_rkLeChk.seq' ((CoinFree.prim' _).seq' (CoinFree.prim' _))

theorem coinFree_rkEqChkT : rkEqChkT.CoinFree :=
  coinFree_rkEqChk.seq' ((CoinFree.prim' _).seq' (CoinFree.prim' _))

theorem wf_rkLeChkT : rkLeChkT.WF := ⟨wf_rkLeChk, trivial, trivial⟩

theorem wf_rkEqChkT : rkEqChkT.WF := ⟨wf_rkEqChk, trivial, trivial⟩

/-- **Invalid predicate word**, the counter tape `2` cleared at the end. -/
noncomputable def rkInvPT : XProg 247 := .seq rkInvP (.prog (clr 2))

theorem wf_rkInvPT : rkInvPT.WF := ⟨wf_rkInvP, trivial⟩

theorem law_rkInvPT (σ : RawSec Dc) (C x : List Bool) :
    rkInvPT.law (Function.update (io2 (R := 245) ((rawEnc Dc).enc σ) C []) 2 x) =
      PMF.pure (io2 (R := 245) ((skEnc Dc).enc ((redView Dc (rawF Dc σ)).1, 0)) [] []) := by
  rw [rkInvPT, XProg.law_seq, law_rkInvP, PMF.pure_bind, lawP _ (CoinFree.prim' _), run_clear]
  congr 1
  funext t
  by_cases h : t = 2
  · subst h; simp [io2]
  · simp [Function.update_of_ne h]

/-- **The key component from its valid branch**, scratch tapes cleared. -/
noncomputable def rkKeyOfT (vP : XProg 247) : XProg 247 :=
  .seq (.prog rkLeChkT) <|
  .ifBit 2 (.seq (.prog (clr 2 ⨾ rkEqChkT)) (.ifBit 2 (.seq (.prog (clr 2)) vP) rkInvPT))
    (.prog rkLongP)

theorem wf_rkKeyOfT {vP : XProg 247} (hv : vP.WF) : (rkKeyOfT vP).WF :=
  ⟨wf_rkLeChkT, ⟨⟨trivial, wf_rkEqChkT⟩, ⟨trivial, hv⟩, wf_rkInvPT⟩, ⟨trivial, trivial, trivial⟩⟩

theorem law_rkKeyOfT {vP : XProg 247} (hv : RkValidOk vP) (σ : RawSec Dc) (C : List Bool) :
    (rkKeyOfT vP).law (io2 (R := 245) ((rawEnc Dc).enc σ) C []) =
      (KGsim Dc kbDc predLen (rawF Dc σ) C).map fun sk => io2 (R := 245) sk [] [] := by
  rw [rkKeyOfT, XProg.law_seq, lawP _ coinFree_rkLeChkT, run_rkLeChkT, PMF.pure_bind,
    law_ifBit247]
  simp only [Function.update_self, List.head?_cons, Option.some.injEq, decide_eq_true_eq]
  unfold KGsim
  by_cases hL : C.length ≤ predLen
  · rw [if_pos hL, if_pos hL, XProg.law_seq,
      lawP _ ((CoinFree.prim' _).seq' coinFree_rkEqChkT), run_seq, run_clear, io2_upd2_clr,
      run_rkEqChkT, PMF.pure_bind, law_ifBit247]
    simp only [Function.update_self, List.head?_cons, Option.some.injEq, decide_eq_true_eq]
    by_cases hV : ValidC C
    · rw [if_pos hV, if_pos hV, XProg.law_seq, lawP _ (CoinFree.prim' _), run_clear, io2_upd2_clr,
        PMF.pure_bind, hv σ C hV, PMF.map_comp]
      rfl
    · rw [if_neg hV, if_neg hV, law_rkInvPT, PMF.pure_map]
  · rw [if_neg hL, if_neg hL, lawP rkLongP ((CoinFree.prim' _).seq' ((CoinFree.prim' _).seq'
      (CoinFree.prim' _))), rkLongP, run_seq, run_seq, run_clear, run_clear, run_clear,
      io2_upd2_clr012, PMF.pure_map]

/-- **The reduction's key component** (scratch tapes cleared) from its middle phases. -/
noncomputable def rkKeyPT (mid : XProg 247) : XProg 247 := rkKeyOfT (rkValidP mid)

theorem wf_rkKeyPT {mid : XProg 247} (hm : mid.WF) : (rkKeyPT mid).WF :=
  wf_rkKeyOfT (wf_rkValidP hm)

/-- **`law_key`** of the fixed component, from the contract of the middle phases. -/
theorem law_rkKeyPT {mid : XProg 247} (hm : RkMidOk mid) (σ : RawSec Dc) (C : List Bool) :
    (rkKeyPT mid).law (io2 (R := 245) ((rawEnc Dc).enc σ) C []) =
      (KGsim Dc kbDc predLen (rawF Dc σ) C).map fun sk => io2 (R := 245) sk [] [] :=
  law_rkKeyOfT (rkValidOk_of_mid hm) σ C

end AdvancedEncryption.ExpLUT.Prog.RedKeyT
