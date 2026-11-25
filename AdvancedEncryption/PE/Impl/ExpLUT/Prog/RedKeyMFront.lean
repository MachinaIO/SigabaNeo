import PE.Impl.ExpLUT.Prog.RedKeyMTail
import PE.Impl.ExpLUT.Prog.RedPubPDc
import SigabaNeo.Lib.Machines.Prog.LenEq

/-!
# `KGsim` on the VM (module 8, top level): the reduction's key component on `247` tapes

`rkKeyP mid : XProg 247` from input `io2 ((rawEnc Dc).enc σ) C []`:

1. `rkLeChk`: tape `2 := [decide (|C| ≤ predLen)]` (`rkLenLeP`, a copy of `lenEqP`);
   too long → `rkLongP` (all blank: `KGsim = pure []`);
2. `rkEqChk`: tape `2 := [decide (ValidC C)]`; invalid → `rkInvP`: `pubP` (the public-key
   component, `law_pubP_Dc`) then `++ 0^{|keyEnc|}` (`natP`, `appT`): `skEnc (mpk, 0)`;
3. valid → `rkValidP mid = mid ; frame (tapes 0 … 104) rkTailP` (`RedKeyMTail`).

**`law_rkKeyP`**: under the contract **`RkMidOk mid`** — for every raw secret `σ` and valid `C`,
`mid` deterministically reaches the MVM state `enc w` on tapes `0 … 104` (all other tapes blank)
with `RkMidReady (redView σ').1 (bpOf (progOf C)) R̂ w` (`R̂ = simKey …`, `σ' = rawF Dc σ`) —
`XProg.law (rkKeyP mid) (io2 (rawEnc σ) C []) = (KGsim Dc kbDc predLen (rawF Dc σ) C).map
(io2 · [] [])`, i.e. the `law` field of `Sub.KeyComp`. **`wf_rkKeyP`** from `mid.WF`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyM

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.Prog
  SigabaNeo.Tape.XProg Cslib Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open AdvancedEncryption.ExpLUT.Params
open scoped SigabaNeo.Tape.Prog

/-! ### The length test `|C| ≤ n` -/

/-- **`|C| ≤ n`**: tapes as `lenEqP` (`0` input, kept; `1` flag; `2 … 5` scratch). -/
def rkLenLeP (n : ℕ) : SigabaNeo.Tape.Prog 6 :=
  natU 2 4 5 n ⨾ cp 3 0 ⨾ dropT 3 2 4 ⨾ ifBlank 3 (setB 1 true) (setB 1 false) ⨾ clr 2 ⨾ clr 3

theorem run_rkLenLeP (n : ℕ) (C : List Bool) :
    run (rkLenLeP n) (in0 C) = Function.update (in0 C) 1 [decide (C.length ≤ n)] := by
  simp only [rkLenLeP, run_seq]
  have e1 : run (dropT 3 2 4) (run (cp 3 0) (run (natU 2 4 5 n) (in0 C))) =
      Function.update (Function.update (in0 C) 2 (List.replicate n true)) 3 (C.drop n) := by
    rw [run_natU (by decide) (by decide) (by decide) n _ rfl rfl, run_copy,
      run_dropT_blank (by decide) _ (by simp [in0, Function.update_apply])]
    funext t; simp +decide [in0, Function.update_apply]; split_ifs <;> simp_all
  rw [e1, run_ifBlank]
  simp only [Function.update_self]
  by_cases hc : C.length ≤ n
  · rw [ite_t (List.drop_eq_nil_iff.mpr hc), run_setB, run_clear, run_clear]
    funext t; simp +decide [in0, Function.update_apply, hc]
    split_ifs <;> simp_all
  · rw [ite_f (by rw [List.drop_eq_nil_iff]; omega), run_setB, run_clear, run_clear]
    funext t; simp +decide [in0, Function.update_apply, hc]
    split_ifs <;> simp_all

theorem coinFree_rkLenLeP (n : ℕ) : (rkLenLeP n).CoinFree := by
  simp only [rkLenLeP]
  exact (coinFree_natU _ _ _ n).seq' ((CoinFree.prim' _).seq' ((coinFree_dropT _ _ _).seq'
    ((CoinFree.ifBlank' (coinFree_setB _ _) (coinFree_setB _ _)).seq'
    ((CoinFree.prim' _).seq' (CoinFree.prim' _)))))

theorem wf_rkLenLeP (n : ℕ) : (rkLenLeP n).WF :=
  ⟨wf_natU (by decide) (by decide) n, trivial, wf_dropT (by decide),
    ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩, trivial, trivial⟩

/-! ### The two tests on `247` tapes -/

/-- The test tapes: `C` on tape `1`, the flag on tape `2`, scratch `3 … 6`. -/
def rkChkMap : Fin 6 → Fin 247 := ![1, 2, 3, 4, 5, 6]

theorem rkChkMap_inj : Function.Injective rkChkMap := by decide

/-- `tape 2 := [decide (|C| ≤ predLen)]`. -/
def rkLeChk : SigabaNeo.Tape.Prog 247 := Prog.map rkChkMap (rkLenLeP predLen)

/-- `tape 2 := [decide (ValidC C)]`. -/
def rkEqChk : SigabaNeo.Tape.Prog 247 := Prog.map rkChkMap (lenEqP predLen)

theorem rk_comp (a C : List Bool) : (io2 (R := 245) a C []) ∘ rkChkMap = in0 C := by
  funext j
  fin_cases j <;> simp [rkChkMap, io2, in0]

theorem run_rkLeChk (a C : List Bool) :
    rkLeChk.run (io2 (R := 245) a C []) =
      Function.update (io2 (R := 245) a C []) 2 [decide (C.length ≤ predLen)] := by
  rw [rkLeChk, Prog.run_map rkChkMap_inj, rk_comp, run_rkLenLeP, ← rk_comp a C,
    extend_update rkChkMap_inj, extend_comp_self]
  rfl

theorem run_rkEqChk (a C : List Bool) :
    rkEqChk.run (io2 (R := 245) a C []) =
      Function.update (io2 (R := 245) a C []) 2 [decide (C.length = predLen)] := by
  rw [rkEqChk, Prog.run_map rkChkMap_inj, rk_comp, run_lenEqP, ← rk_comp a C,
    extend_update rkChkMap_inj, extend_comp_self]
  rfl

theorem coinFree_rkLeChk : rkLeChk.CoinFree := coinFree_mapP _ (coinFree_rkLenLeP _)

theorem coinFree_rkEqChk : rkEqChk.CoinFree := coinFree_mapP _ (coinFree_lenEqP _)

theorem wf_rkLeChk : rkLeChk.WF := (wf_rkLenLeP _).map rkChkMap_inj

theorem wf_rkEqChk : rkEqChk.WF := (wf_lenEqP _).map rkChkMap_inj

/-! ### Store identities -/

theorem io2_upd2_clr (a C x : List Bool) :
    Function.update (Function.update (io2 (R := 245) a C []) 2 x) 2 [] = io2 (R := 245) a C [] := by
  funext t
  by_cases h : t = 2
  · subst h; simp [io2]
  · simp [Function.update_of_ne h]

theorem io2_upd2_clr12 (a C x : List Bool) :
    Function.update (Function.update (Function.update (io2 (R := 245) a C []) 2 x) 1 []) 2 [] =
      io2 (R := 245) a [] [] := by
  funext t
  by_cases h2 : t = 2
  · subst h2; simp [io2]
  by_cases h1 : t = 1
  · subst h1; simp [io2]
  have v1 : t.val ≠ 1 := fun e => h1 (Fin.ext e)
  simp only [Function.update_of_ne h2, Function.update_of_ne h1, io2, v1, if_false]

theorem io2_upd2_clr012 (a C x : List Bool) :
    Function.update (Function.update (Function.update (Function.update (io2 (R := 245) a C []) 2 x)
      0 []) 1 []) 2 [] = io2 (R := 245) [] [] [] := by
  funext t
  by_cases h2 : t = 2
  · subst h2; simp [io2]
  by_cases h1 : t = 1
  · subst h1; simp [io2]
  by_cases h0 : t = 0
  · subst h0; simp [io2]
  have v1 : t.val ≠ 1 := fun e => h1 (Fin.ext e)
  have v0 : t.val ≠ 0 := fun e => h0 (Fin.ext e)
  simp only [Function.update_of_ne h2, Function.update_of_ne h1, Function.update_of_ne h0, io2, v1,
    v0, if_false]

theorem lawP (p : SigabaNeo.Tape.Prog 247) (hp : p.CoinFree) (s : Store 247) :
    (XProg.prog p).law s = PMF.pure (p.run s) := by
  rw [XProg.law_prog, Prog.law_eq_run_of_coinFree _ hp]

theorem law_ifBit247 (i : Fin 247) (p q : XProg 247) (s : Store 247) :
    (XProg.ifBit i p q).law s = if (s i).head? = some true then p.law s else q.law s := by
  change (if (s i).head? = some true then p.denote s else q.denote s).eval = _
  split_ifs <;> rfl

/-! ### The branches -/

/-- Too long: the blank output. -/
def rkLongP : SigabaNeo.Tape.Prog 247 := clr 0 ⨾ clr 1 ⨾ clr 2

/-- **Invalid predicate word**: `skEnc (mpk, 0)` — `pubP`, then `0^{|keyEnc|}` appended. -/
noncomputable def rkInvP : XProg 247 :=
  .seq (.prog (clr 1 ⨾ clr 2)) <| .seq (RedPubP.pubP Dc) <|
  .seq (natP 1 2 (codecSize (keyEnc Dc))) (.prog (appT 0 1 2 3 ⨾ clr 1))

theorem wf_rkInvP : rkInvP.WF :=
  ⟨⟨trivial, trivial⟩, RedPubP.wf_pubP_Dc, wf_natP (by decide) _, wf_appT (by decide) (by decide),
    trivial⟩

theorem law_rkInvP (σ : RawSec Dc) (C x : List Bool) :
    rkInvP.law (Function.update (io2 (R := 245) ((rawEnc Dc).enc σ) C []) 2 x) =
      PMF.pure (io2 (R := 245) ((skEnc Dc).enc ((redView Dc (rawF Dc σ)).1, 0)) [] []) := by
  rw [rkInvP, XProg.law_seq, lawP _ ((CoinFree.prim' _).seq' (CoinFree.prim' _)), run_seq,
    run_clear, run_clear, io2_upd2_clr12, PMF.pure_bind, XProg.law_seq, RedPubP.law_pubP_Dc,
    PMF.pure_bind, XProg.law_seq, law_natP (by decide) _ _ (by simp [io2]), PMF.pure_bind,
    lawP _ ((coinFree_appT _ _ _ _).seq' (CoinFree.prim' _)), run_seq,
    run_appT (by decide) (by decide) (by decide), run_clear]
  congr 1
  have hk : (skEnc Dc).enc ((redView Dc (rawF Dc σ)).1, 0) =
      (mpkEnc Dc).enc (redView Dc (rawF Dc σ)).1 ++ (keyEnc Dc).enc 0 := rfl
  rw [hk, keyEnc_zero]
  funext t
  by_cases h1 : t = 1
  · subst h1; simp [io2]
  by_cases h3 : t = 3
  · subst h3; simp [io2]
  by_cases h2 : t = 2
  · subst h2; simp [io2]
  by_cases h0 : t = 0
  · subst h0; simp [io2]
  have v1 : t.val ≠ 1 := fun e => h1 (Fin.ext e)
  have v0 : t.val ≠ 0 := fun e => h0 (Fin.ext e)
  simp only [Function.update_of_ne h1, Function.update_of_ne h3, Function.update_of_ne h2,
    Function.update_of_ne h0, io2, v1, v0, if_false]

/-- **The contract of the valid branch.** -/
def RkValidOk (vP : XProg 247) : Prop :=
  ∀ (σ : RawSec Dc) (C : List Bool), ValidC C →
    vP.law (io2 (R := 245) ((rawEnc Dc).enc σ) C []) =
      (redKeyLaw (S := setting Dc) kbDc.Big kbDc.Small kbDc.hBig gadDec (helperMap Dc) wSt
        (rawF Dc σ).2.1 (rawF Dc σ).1 (rawF Dc σ).2.2.1 (rawF Dc σ).2.2.2.1 (rawF Dc σ).2.2.2.2
        (bpOf (progOf C))).map
        fun o => io2 (R := 245) ((skEnc Dc).enc ((redView Dc (rawF Dc σ)).1, keyOfOutput o)) [] []

/-- **The key component from its valid branch.** -/
noncomputable def rkKeyOf (vP : XProg 247) : XProg 247 :=
  .seq (.prog rkLeChk) <|
  .ifBit 2 (.seq (.prog (clr 2 ⨾ rkEqChk)) (.ifBit 2 (.seq (.prog (clr 2)) vP) rkInvP))
    (.prog rkLongP)

theorem wf_rkKeyOf {vP : XProg 247} (hv : vP.WF) : (rkKeyOf vP).WF :=
  ⟨wf_rkLeChk, ⟨⟨trivial, wf_rkEqChk⟩, ⟨trivial, hv⟩, wf_rkInvP⟩, ⟨trivial, trivial, trivial⟩⟩

/-- **The law of the key component**, from the contract of its valid branch. -/
theorem law_rkKeyOf {vP : XProg 247} (hv : RkValidOk vP) (σ : RawSec Dc) (C : List Bool) :
    (rkKeyOf vP).law (io2 (R := 245) ((rawEnc Dc).enc σ) C []) =
      (KGsim Dc kbDc predLen (rawF Dc σ) C).map fun sk => io2 (R := 245) sk [] [] := by
  rw [rkKeyOf, XProg.law_seq, lawP _ coinFree_rkLeChk, run_rkLeChk, PMF.pure_bind, law_ifBit247]
  simp only [Function.update_self, List.head?_cons, Option.some.injEq, decide_eq_true_eq]
  unfold KGsim
  by_cases hL : C.length ≤ predLen
  · rw [if_pos hL, if_pos hL, XProg.law_seq,
      lawP _ ((CoinFree.prim' _).seq' coinFree_rkEqChk), run_seq, run_clear, io2_upd2_clr,
      run_rkEqChk, PMF.pure_bind, law_ifBit247]
    simp only [Function.update_self, List.head?_cons, Option.some.injEq, decide_eq_true_eq]
    by_cases hV : ValidC C
    · rw [if_pos hV, if_pos hV, XProg.law_seq, lawP _ (CoinFree.prim' _), run_clear, io2_upd2_clr,
        PMF.pure_bind, hv σ C hV, PMF.map_comp]
      rfl
    · rw [if_neg hV, if_neg hV, law_rkInvP, PMF.pure_map]
  · rw [if_neg hL, if_neg hL, lawP rkLongP ((CoinFree.prim' _).seq' ((CoinFree.prim' _).seq'
      (CoinFree.prim' _))), rkLongP, run_seq, run_seq, run_clear, run_clear, run_clear, io2_upd2_clr012,
      PMF.pure_map]

/-! ### The valid branch: the middle phases, then the back end on tapes `0 … 104` -/

/-- The MVM's tapes inside the `247`. -/
def rkE : Fin 105 ↪ Fin 247 := Fin.castLEEmb (by norm_num)

/-- A `105`-tape store on tapes `0 … 104`, the others blank. -/
def rkLift (a : Store 105) : Store 247 := embedF rkE (fun _ => []) a

theorem rkLift_rkE (a : Store 105) : (fun j => rkLift a (rkE j)) = a := by
  funext j
  simp [rkLift]

theorem embedF_rkLift_inputStore (a : Store 105) (sk : List Bool) :
    embedF rkE (rkLift a) (inputStore (0 : Fin 105) sk) = io2 (R := 245) sk [] [] := by
  funext l
  rcases embedF_cases rkE (rkLift a) (inputStore (0 : Fin 105) sk) l with ⟨hl, h⟩ | ⟨j, hj, h⟩
  · rw [h, rkLift, embedF, hl]
    have hv : l.val ≠ 0 := by
      intro h0
      have : rkE ⟨0, by norm_num⟩ = l := Fin.ext (by simp [rkE, h0])
      rw [← this, partialInv_self] at hl
      exact absurd hl (by simp)
    simp [io2, hv]
  · rw [h, ← hj]
    by_cases h0 : j = 0
    · subst h0; simp [inputStore, io2, rkE]
    · have hv : (rkE j).val ≠ 0 := by
        simp only [rkE, Fin.castLEEmb_apply, Fin.coe_castLE]
        exact fun e => h0 (Fin.ext e)
      simp [inputStore, Function.update_of_ne h0, io2, hv]

theorem rk_map3 {α β γ δ : Type} (p : PMF α) (f : α → β) (g : β → γ) (h : γ → δ) (k : α → δ)
    (hk : ∀ a, h (g (f a)) = k a) : ((p.map f).map g).map h = p.map k := by
  rw [PMF.map_comp, PMF.map_comp]
  exact congrArg (fun m => PMF.map m p) (funext hk)

/-- **The contract of the middle phases**: from the input, the MVM state `enc w` on tapes
`0 … 104` (the others blank) with the public key, `A_F` and the rows of `X` in place. -/
def RkMidOk (mid : XProg 247) : Prop :=
  ∀ (σ : RawSec Dc) (C : List Bool), ValidC C → ∃ w : MVM.St,
    mid.law (io2 (R := 245) ((rawEnc Dc).enc σ) C []) = PMF.pure (rkLift (MVM.enc Dc.N Dc.K w)) ∧
    RkMidReady (redView Dc (rawF Dc σ)).1 (bpOf (progOf C))
      (simKey (helperMap Dc) (redView Dc (rawF Dc σ)).1 (bpOf (progOf C)) (redView Dc (rawF Dc σ)).2
        (rawF Dc σ).1 (ExpLUT.progOf (rawF Dc σ).2.2.1)) w

/-- **The valid branch**: the middle phases, then the back end on tapes `0 … 104`. -/
noncomputable def rkValidP (mid : XProg 247) : XProg 247 :=
  .seq mid (.frame rkE (rkTailP Dc Bk rSmall))

theorem wf_rkValidP {mid : XProg 247} (hm : mid.WF) : (rkValidP mid).WF :=
  ⟨hm, wf_rkTailP_Dc⟩

theorem rkValidOk_of_mid {mid : XProg 247} (hm : RkMidOk mid) : RkValidOk (rkValidP mid) := by
  intro σ C hC
  obtain ⟨w, hlaw, hw⟩ := hm σ C hC
  rw [rkValidP, XProg.law_seq, hlaw, PMF.pure_bind, XProg.law_frame, rkLift_rkE,
    law_rkTailP_Dc _ _ _ w hw]
  exact rk_map3 _ _ _ _ _ fun o => embedF_rkLift_inputStore _ _

/-! ### The key component -/

/-- **The reduction's key component** from its middle phases. -/
noncomputable def rkKeyP (mid : XProg 247) : XProg 247 := rkKeyOf (rkValidP mid)

theorem wf_rkKeyP {mid : XProg 247} (hm : mid.WF) : (rkKeyP mid).WF :=
  wf_rkKeyOf (wf_rkValidP hm)

/-- **`law_key` of the reduction's key component**, from the contract of the middle phases. -/
theorem law_rkKeyP {mid : XProg 247} (hm : RkMidOk mid) (σ : RawSec Dc) (C : List Bool) :
    (rkKeyP mid).law (io2 (R := 245) ((rawEnc Dc).enc σ) C []) =
      (KGsim Dc kbDc predLen (rawF Dc σ) C).map fun sk => io2 (R := 245) sk [] [] :=
  law_rkKeyOf (rkValidOk_of_mid hm) σ C

end AdvancedEncryption.ExpLUT.Prog.RedKeyM
