import PE.Impl.ExpLUT.Prog.RedKeyMidCode
import PE.Impl.ExpLUT.Prog.RedKeyMFront
open SigabaNeo.Tape.RingVM.Handler
/-!
# `mid` of the key component: the tape-level assembly

The middle phases of `RedKeyM.rkKeyP` (`247` tapes): the MVM phases run framed on the tapes
`0 … 104` (`RedKeyM.rkE`), words survive between phases on the **storage tapes** `242 … 246`
(`tA` = `matL A_F`, `tCt`, `tMpk`, `tSig`, `tC` of `RedKeyMidPub`). A `247`-store is written
`mS a g` (`a` on `0 … 104`, `g` elsewhere).

`mid pk` (phases, in order; each a separate `XProg` for the cost certificate):

| phase | program | effect |
|---|---|---|
| M1 | `m1P` | `RingVM`: `mpkW`, `ctW`; storage `tCt tMpk tSig tC` |
| enter | `midEnter` | fresh MVM state `enc wB` on `0 … 104` |
| load | `midLdM2` | `2 := mpkW`, `rCs := C`, `rB1 := [false]` (`m2Init`) |
| M2 | `frame rkE (compile m2C)` | `8` = `matL A_F` |
| stash | `midStA` | `tA := reg 8` |
| enter | `midEnter` | fresh MVM state |
| load | `midLdPk` | `pkInit σ C` |
| M3 | `frame rkE (compile pk)` | `SimKeyIn` (contract `PkOk pk`) |
| M4a | `frame rkE (compile simKeyC)` | `rxRh` = `R̂_F` |
| load | `midLd14` | `14 := mpkW` |
| M4b | `frame rkE (compile (setXC Dc))` | module 5's inputs |
| M4c | `frame rkE (compile simXC)` | `16` = rows of `X` |
| exit | `midFin` | `8 := tA`, `14 := tMpk`, storage cleared |

**`rkMidOk_mid`**: `PkOk pk → RkMidOk (mid pk)`; **`wf_mid`**: `pk.WFc → (mid pk).WF`. With
`RedKeyMComp.keyCompOf (mid pk) …` this closes the law of the key component once the packet code
`pk` (phase M3) is provided.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyMid

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape Cslib
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open AdvancedEncryption.ExpLUT.Prog.RedKeyM
open scoped SigabaNeo.Tape.Prog

/-! ### Stores with storage tapes -/

/-- The `105`-store `a` on the tapes `0 … 104`, the storage `g` elsewhere. -/
def mS (a : Store 105) (g : Store 247) : Store 247 := embedF rkE g a

theorem rkE_val (j : Fin 105) : (rkE j).val = j.val := rfl

theorem mS_rkE (a : Store 105) (g : Store 247) (j : Fin 105) : mS a g (rkE j) = a j := by
  simp [mS]

theorem mS_hi (a : Store 105) (g : Store 247) (t : Fin 247) (ht : 105 ≤ t.val) : mS a g t = g t := by
  rcases embedF_cases rkE g a t with ⟨-, h⟩ | ⟨j, hj, -⟩
  · exact h
  · have := j.isLt; rw [← hj, rkE_val] at ht; omega

theorem mS_restrict (a : Store 105) (g : Store 247) : (fun j => mS a g (rkE j)) = a := by
  funext j; exact mS_rkE a g j

theorem embedF_mS (a a' : Store 105) (g : Store 247) : embedF rkE (mS a g) a' = mS a' g := by
  funext t
  rcases embedF_cases rkE (mS a g) a' t with ⟨hn, h⟩ | ⟨j, hj, h⟩
  · rw [h, mS, mS]
    rcases embedF_cases rkE g a t with ⟨-, h1⟩ | ⟨j, hj, -⟩
    · rcases embedF_cases rkE g a' t with ⟨-, h2⟩ | ⟨j', hj', -⟩
      · rw [h1, h2]
      · rw [← hj', partialInv_self] at hn; cases hn
    · rw [← hj, partialInv_self] at hn; cases hn
  · rw [h, ← hj, mS_rkE]

theorem law_frame_mS (p : XProg 105) (a : Store 105) (g : Store 247) :
    (XProg.frame rkE p).law (mS a g) = (p.law a).map (fun a' => mS a' g) := by
  rw [XProg.law_frame, mS_restrict]
  congr 1
  funext a'
  exact embedF_mS a a' g

theorem update_mS_lo (a : Store 105) (g : Store 247) (j : Fin 105) (v : List Bool) :
    Function.update (mS a g) (rkE j) v = mS (Function.update a j v) g := by
  funext t
  by_cases ht : t = rkE j
  · subst ht; simp [mS_rkE]
  rw [Function.update_of_ne ht]
  by_cases hlo : t.val < 105
  · have e : t = rkE ⟨t.val, hlo⟩ := Fin.ext rfl
    have hne : (⟨t.val, hlo⟩ : Fin 105) ≠ j := fun h => ht (by rw [e, h])
    rw [e, mS_rkE, mS_rkE, Function.update_of_ne hne]
  · rw [mS_hi _ _ _ (by omega), mS_hi _ _ _ (by omega)]

theorem update_mS_hi (a : Store 105) (g : Store 247) (t : Fin 247) (ht : 105 ≤ t.val)
    (v : List Bool) : Function.update (mS a g) t v = mS a (Function.update g t v) := by
  funext l
  by_cases hl : l = t
  · subst hl; rw [Function.update_self, mS_hi _ _ _ ht, Function.update_self]
  rw [Function.update_of_ne hl]
  by_cases hlo : l.val < 105
  · have e : l = rkE ⟨l.val, hlo⟩ := Fin.ext rfl
    rw [e, mS_rkE, mS_rkE]
  · rw [mS_hi _ _ _ (by omega), mS_hi _ _ _ (by omega), Function.update_of_ne hl]

/-- The tape of the register `r` among the `247`. -/
def tRg (r : Fin 64) : Fin 247 := rkE (MVM.tR r)

theorem enc_update (w : MVM.St) (r : Fin 64) (v : List Bool) :
    Function.update (MVM.enc Dc.N Dc.K w) (MVM.tR r) v = MVM.enc Dc.N Dc.K (Function.update w r v) :=
  MVM.update_tR r v

/-- Load the storage tape `t` into the register `r`. -/
theorem run_ld (w : MVM.St) (g : Store 247) (r : Fin 64) (t : Fin 247) (ht : 105 ≤ t.val) :
    (Prog.cp (tRg r) t).run (mS (MVM.enc Dc.N Dc.K w) g) =
      mS (MVM.enc Dc.N Dc.K (Function.update w r (g t))) g := by
  rw [Prog.run_copy, mS_hi _ _ _ ht, tRg, update_mS_lo, enc_update]

/-- Stash the register `r` on the storage tape `t`. -/
theorem run_st (w : MVM.St) (g : Store 247) (r : Fin 64) (t : Fin 247) (ht : 105 ≤ t.val) :
    (Prog.cp t (tRg r)).run (mS (MVM.enc Dc.N Dc.K w) g) =
      mS (MVM.enc Dc.N Dc.K w) (Function.update g t (w r)) := by
  have e : MVM.enc Dc.N Dc.K w (MVM.tR r) = w r := MVM.encX_tR r
  rw [Prog.run_copy, tRg, mS_rkE, e, update_mS_hi _ _ _ ht]

/-- Clear the storage tape `t`. -/
theorem run_clrS (a : Store 105) (g : Store 247) (t : Fin 247) (ht : 105 ≤ t.val) :
    (Prog.clr t).run (mS a g) = mS a (Function.update g t []) := by
  rw [Prog.run_clear, update_mS_hi _ _ _ ht]

/-- Put a bit in front of the register `r`. -/
theorem run_consR (w : MVM.St) (g : Store 247) (r : Fin 64) (b : Bool) :
    (Prog.prim (.cons (tRg r) b)).run (mS (MVM.enc Dc.N Dc.K w) g) =
      mS (MVM.enc Dc.N Dc.K (Function.update w r (b :: w r))) g := by
  have e : MVM.enc Dc.N Dc.K w (MVM.tR r) = w r := MVM.encX_tR r
  rw [Prog.run_prim]
  show Function.update (mS (MVM.enc Dc.N Dc.K w) g) (tRg r)
    (b :: mS (MVM.enc Dc.N Dc.K w) g (tRg r)) = _
  rw [tRg, mS_rkE, e, update_mS_lo, enc_update]

/-! ### The phases -/

def tAF : Fin 247 := 242

/-- A fresh MVM state on the tapes `0 … 104`. -/
noncomputable def midEnter : XProg 247 :=
  .frame rkE (.prog (MVM.IO.pre Dc.N Dc.K (fun _ => 0)))

/-- The input of M2. -/
def midLdM2 : Tape.Prog 247 :=
  Prog.cp (tRg 2) tMpk ⨾ Prog.cp (tRg rCs) tC ⨾ .prim (.cons (tRg rB1) false)

/-- Stash `matL A_F`. -/
def midStA : Tape.Prog 247 := Prog.cp tAF (tRg 8)

/-- The input of M3. -/
def midLdPk : Tape.Prog 247 :=
  Prog.cp (tRg 0) tSig ⨾ Prog.cp (tRg 1) tCt ⨾ Prog.cp (tRg 2) tMpk ⨾ Prog.cp (tRg rCs) tC

/-- The public-key word for `setXC`. -/
def midLd14 : Tape.Prog 247 := Prog.cp (tRg 14) tMpk

/-- The exit: `8`, `14` reloaded, the storage cleared. -/
def midFin : Tape.Prog 247 :=
  Prog.cp (tRg 8) tAF ⨾ Prog.cp (tRg 14) tMpk ⨾ Prog.clr tAF ⨾ Prog.clr tCt ⨾ Prog.clr tMpk ⨾
    Prog.clr tSig ⨾ Prog.clr tC

/-- An MVM code on the tapes `0 … 104`. -/
noncomputable def onM (c : MVM.Code) : XProg 247 := .frame rkE (MVM.compile c)

/-- **The middle phases** of the key component, for a packet code `pk` (phase M3). -/
noncomputable def mid (pk : MVM.Code) : XProg 247 :=
  .seq m1P <| .seq midEnter <| .seq (.prog midLdM2) <| .seq (onM m2C) <| .seq (.prog midStA) <|
  .seq midEnter <| .seq (.prog midLdPk) <| .seq (onM pk) <| .seq (onM (simKeyC Dc)) <|
  .seq (.prog midLd14) <| .seq (onM (setXC Dc)) <| .seq (onM simXC) <| .prog midFin

theorem wf_midEnter : midEnter.WF := ⟨trivial, trivial, MVM.IO.wf_setList _ _⟩

theorem wf_mid {pk : MVM.Code} (hpk : pk.WFc) : (mid pk).WF :=
  ⟨wf_m1P, wf_midEnter, ⟨trivial, trivial, trivial⟩, MVM.wf_compile _ wf_m2C, trivial,
    wf_midEnter, ⟨trivial, trivial, trivial, trivial⟩, MVM.wf_compile _ hpk,
    MVM.wf_compile _ (wf_simKeyC Dc), trivial, MVM.wf_compile _ (wf_setXC Dc),
    MVM.wf_compile _ wf_simXC, ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩⟩

/-! ### Laws of the phases -/

theorem law_onM (c : MVM.Code) (w : MVM.St) (g : Store 247) :
    (onM c).law (mS (MVM.enc Dc.N Dc.K w) g) =
      PMF.pure (mS (MVM.enc Dc.N Dc.K (MVM.exec Dc.N Dc.K c w)) g) := by
  rw [onM, law_frame_mS, MVM.law_compile Dc.N_pos Dc.K_pos, PMF.pure_map]

theorem init_blank : MVM.IO.init [] [] (fun _ => 0) = wB := by
  funext r; simp [MVM.IO.init, wB]

theorem law_midEnter (a : Store 105) (g : Store 247) (h0 : a 0 = []) (h1 : a 1 = []) :
    midEnter.law (mS a g) = PMF.pure (mS (MVM.enc Dc.N Dc.K wB) g) := by
  rw [midEnter, law_frame_mS, XProg.law_prog,
    Prog.law_eq_run_of_coinFree _ (MVM.IO.coinFree_pre _ _ _), KeyCore.run_pre_any, h0, h1,
    init_blank, PMF.pure_map]

theorem enc_blank0 (w : MVM.St) : MVM.enc Dc.N Dc.K w 0 = [] := rfl
theorem enc_blank1 (w : MVM.St) : MVM.enc Dc.N Dc.K w 1 = [] := rfl

theorem m1Store_lo (σ : RawSec Dc) (C : List Bool) (t : Fin 247) (h : t.val < 105) :
    m1Store σ C t = [] := by
  have n1 : t ≠ tCt := fun e => by rw [e] at h; exact absurd h (by decide)
  have n2 : t ≠ tMpk := fun e => by rw [e] at h; exact absurd h (by decide)
  have n3 : t ≠ tSig := fun e => by rw [e] at h; exact absurd h (by decide)
  have n4 : t ≠ tC := fun e => by rw [e] at h; exact absurd h (by decide)
  rw [m1Store, put3, Function.update_of_ne n1, Function.update_of_ne n4, Function.update_of_ne n3,
    Function.update_of_ne n2]

theorem m1Store_eq (σ : RawSec Dc) (C : List Bool) :
    m1Store σ C = mS (fun _ => []) (m1Store σ C) := by
  funext t
  by_cases hlo : t.val < 105
  · have e : t = rkE ⟨t.val, hlo⟩ := Fin.ext rfl
    have h := mS_rkE (fun _ => []) (m1Store σ C) ⟨t.val, hlo⟩
    rw [← e] at h
    rw [h, m1Store_lo σ C t hlo]
  · rw [mS_hi _ _ _ (by omega)]

/-- **The middle phases are a valid `mid`.** -/
theorem rkMidOk_mid {pk : MVM.Code} (hpk : PkOk pk) : RkMidOk (mid pk) := by
  intro σ C hC
  set A := MVM.encL Dc.N Dc.K
    (MVM.matL (keyPK (helperMap Dc) (redView Dc (rawF Dc σ)).1 (bpOf (progOf C))))
  refine ⟨wFin pk σ C A, ?_, ready_of_pk hpk σ C hC⟩
  have g1M : m1Store σ C tMpk = mpkW σ := by
    rw [m1Store, Function.update_of_ne (by decide), put3, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_self]
  have g1C : m1Store σ C tC = C := by
    rw [m1Store, Function.update_of_ne (by decide), put3, Function.update_self]
  have g1S : m1Store σ C tSig = (rawEnc Dc).enc σ := by
    rw [m1Store, Function.update_of_ne (by decide), put3, Function.update_of_ne (by decide),
      Function.update_self]
  have g1T : m1Store σ C tCt = ctW σ := by rw [m1Store, Function.update_self]
  -- M1 and the first entry
  rw [mid, XProg.law_seq, law_m1P, PMF.pure_bind, m1Store_eq, XProg.law_seq,
    law_midEnter _ _ rfl rfl, PMF.pure_bind]
  -- M2
  rw [XProg.law_seq, XProg.law_prog, Prog.law_eq_run_of_coinFree _ (by rfl)]
  have hM2 : midLdM2.run (mS (MVM.enc Dc.N Dc.K wB) (m1Store σ C)) =
      mS (MVM.enc Dc.N Dc.K (m2Init σ C)) (m1Store σ C) := by
    simp only [midLdM2, Prog.run_seq]
    rw [run_ld _ _ _ _ (by decide), run_ld _ _ _ _ (by decide), run_consR, g1M, g1C]
    congr 3
  rw [hM2, PMF.pure_bind, XProg.law_seq, law_onM, PMF.pure_bind, XProg.law_seq, XProg.law_prog,
    Prog.law_eq_run_of_coinFree _ (by rfl), midStA, run_st _ _ _ _ (by decide), PMF.pure_bind,
    (exec_m2C σ C).2]
  set g2 := Function.update (m1Store σ C) tAF A with hg2
  -- M3, M4
  rw [XProg.law_seq, law_midEnter _ _ rfl rfl, PMF.pure_bind, XProg.law_seq, XProg.law_prog,
    Prog.law_eq_run_of_coinFree _ (by rfl)]
  have g2M : g2 tMpk = mpkW σ := by rw [hg2, Function.update_of_ne (by decide)]; exact g1M
  have g2C : g2 tC = C := by rw [hg2, Function.update_of_ne (by decide)]; exact g1C
  have g2S : g2 tSig = (rawEnc Dc).enc σ := by rw [hg2, Function.update_of_ne (by decide)]; exact g1S
  have g2T : g2 tCt = ctW σ := by rw [hg2, Function.update_of_ne (by decide)]; exact g1T
  have hPk : midLdPk.run (mS (MVM.enc Dc.N Dc.K wB) g2) = mS (MVM.enc Dc.N Dc.K (pkInit σ C)) g2 := by
    simp only [midLdPk, Prog.run_seq]
    rw [run_ld _ _ _ _ (by decide), run_ld _ _ _ _ (by decide), run_ld _ _ _ _ (by decide),
      run_ld _ _ _ _ (by decide), g2M, g2C, g2S, g2T]
    rfl
  rw [hPk, PMF.pure_bind, XProg.law_seq, law_onM, PMF.pure_bind, XProg.law_seq, law_onM,
    PMF.pure_bind, XProg.law_seq, XProg.law_prog, Prog.law_eq_run_of_coinFree _ (by rfl), midLd14,
    run_ld _ _ _ _ (by decide), g2M, PMF.pure_bind, XProg.law_seq, law_onM, PMF.pure_bind,
    XProg.law_seq, law_onM, PMF.pure_bind, XProg.law_prog, Prog.law_eq_run_of_coinFree _ (by rfl)]
  -- the exit
  congr 1
  simp only [midFin, Prog.run_seq]
  rw [run_ld _ _ _ _ (by decide), run_ld _ _ _ _ (by decide), run_clrS _ _ _ (by decide),
    run_clrS _ _ _ (by decide), run_clrS _ _ _ (by decide), run_clrS _ _ _ (by decide),
    run_clrS _ _ _ (by decide), g2M]
  have hgA : g2 tAF = A := by rw [hg2, Function.update_self]
  rw [hgA]
  show mS _ _ = mS _ (fun _ => [])
  congr 1
  funext t
  simp only [hg2, m1Store, put3, Function.update_apply]
  split_ifs <;> rfl

end AdvancedEncryption.ExpLUT.Prog.RedKeyMid
