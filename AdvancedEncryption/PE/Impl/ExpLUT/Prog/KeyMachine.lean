import PE.Impl.ExpLUT.Prog.KeyFront
import SigabaNeoStd.Machines.Prog.FrameOut

/-! A fully framed finite-clock KeyGen machine. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyCore
open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape
  SigabaNeo.Tape.Prog SigabaNeo.Tape.XProg SigabaNeo.Tape.MVM Cslib Cslib.Probability

/-- Frame the complete public-key/key pair as one primitive output field. -/
def frameKeyP : XProg 105 :=
  .seq (.prog (.seq (cp 1 0) (clr 0)))
    (.seq (XProg.frameApP 0 1 2 3) (.prog (clr 1)))

theorem wf_frameKeyP : frameKeyP.WF :=
  ⟨⟨trivial, trivial⟩, XProg.wf_frameApP (by decide) (by decide), trivial⟩

theorem law_frameKeyP (w : List Bool) :
    frameKeyP.law (inputStore 0 w) = PMF.pure (inputStore 0 (encodeTuple [w])) := by
  rw [frameKeyP, XProg.law_seq, XProg.law_prog,
    Prog.law_eq_run_of_coinFree _ (by rfl), Prog.run_seq, run_copy, run_clear,
    PMF.pure_bind, XProg.law_seq]
  rw [XProg.law_frameApP (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ (by simp [inputStore]) (by simp [inputStore])]
  rw [PMF.pure_bind, XProg.law_prog, Prog.law_eq_run_of_coinFree _ (by rfl), run_clear]
  congr 1
  funext i
  by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;>
    simp [inputStore, h0, h1, encodeTuple_cons, encodeTuple_nil]

/-- Parse, validate, generate one key, and frame the output. -/
noncomputable def keyProgram (D : Dims) (B r : ℕ) : XProg 105 :=
  .seq (.prog parse) <| .seq (chooseP D B r) frameKeyP

theorem wf_keyProgram (D : Dims) (B r : ℕ) : (keyProgram D B r).WF :=
  ⟨wf_parse, wf_chooseP D B r, wf_frameKeyP⟩

theorem law_keyProgram (D : Dims) (hb : D.b = 22) (hn : 2 ^ D.b ≤ D.q)
    (B r : ℕ) (hB : 2 ^ B ≤ D.q) (hBK : B ≤ D.K)
    (hr : 2 * r < 2 ^ B) (hq : 2 ^ (B + 1) ≤ D.q) (hcount : 2 * (D.K - B) < D.q)
    (pw : List Bool) (msk : MSKt D) (C : List Bool) :
    (keyProgram D B r).law (inputStore 0 (encodeTuple [pw, (mskEnc D).enc msk, C])) =
      (keyLawW D (kbOf D B hB r) msk C).map
        (fun sk ↦ inputStore (0 : Fin 105) (encodeTuple [(skEnc D).enc sk])) := by
  rw [keyProgram, XProg.law_seq, XProg.law_prog,
    Prog.law_eq_run_of_coinFree _ coinFree_parse, run_parse, PMF.pure_bind,
    XProg.law_seq, law_chooseP D hb hn B r hB hBK hr hq hcount, PMF.bind_map]
  have hh := congrArg (PMF.bind (keyLawW D (kbOf D B hB r) msk C))
    (funext fun sk ↦ law_frameKeyP ((skEnc D).enc sk))
  exact hh.trans (PMF.bind_pure_comp _ _)

/-- Framed input length bound for predicates of at most L bits. -/
noncomputable def keyInputBound (D : Dims) (L : ℕ) : ℕ :=
  (2 * pwW.length + 1) + (2 * codecSize (mskEnc D) + 1) + (2 * L + 1)

theorem length_keyInput_le (D : Dims) (L : ℕ) (msk : MSKt D) (C : List Bool)
    (hC : C.length ≤ L) :
    (encodeTuple [pwW, (mskEnc D).enc msk, C]).length ≤ keyInputBound D L := by
  have hm : ((mskEnc D).enc msk).length = codecSize (mskEnc D) := (mskEnc D).length msk
  simp only [encodeTuple_cons, encodeTuple_nil, List.length_append, length_frame,
    List.length_nil, hm, keyInputBound]
  omega

/-- KeyGen with the compiler's explicit input-length-dependent finite clock. -/
noncomputable def keyMP (D : Dims) (B r L : ℕ) : Machine :=
  (keyProgram D B r).toMachineT 0 0 (keyInputBound D L)

/-- Full primitive specification, including invalid predicate words and framed output. -/
theorem keySpec_keyMP (D : Dims) (hb : D.b = 22) (hn : 2 ^ D.b ≤ D.q)
    (B r L : ℕ) (hB : 2 ^ B ≤ D.q) (hBK : B ≤ D.K)
    (hr : 2 * r < 2 ^ B) (hq : 2 ^ (B + 1) ≤ D.q) (hcount : 2 * (D.K - B) < D.q) :
    KeySpec D (kbOf D B hB r) L (keyMP D B r L) := by
  intro msk C hC
  rw [keyMP, XProg.run_toMachineT _ (wf_keyProgram D B r) 0 0 (keyInputBound D L) _
    (length_keyInput_le D L msk C hC), law_keyProgram D hb hn B r hB hBK hr hq hcount,
    PMF.map_comp]
  congr 1

/-- The machine clock is the compiler's explicit bound for the full interface program. -/
theorem time_keyMP (D : Dims) (B r L : ℕ) :
    (keyMP D B r L).time = XProg.totalTimeT (keyProgram D B r) 0 0 (keyInputBound D L) := rfl

open Params

/-- The configured KeyGen machine satisfies KeySpec with all arithmetic side conditions closed. -/
theorem keySpec_keyMP_Dc (L : ℕ) :
    KeySpec Dc kbDc L (keyMP Dc Bk rSmall L) := by
  have hb : Dc.b = 22 := rfl
  have hn : 2 ^ Dc.b ≤ Dc.q := by
    calc 2 ^ Dc.b ≤ 2 ^ Bk := Nat.pow_le_pow_right (by decide) (by rw [hb, Bk_def]; omega)
      _ ≤ Dc.q := hBk_Dc
  have h := keySpec_keyMP Dc hb hn Bk rSmall L hBk_Dc Bk_lt_Kc.le
    small_test_conditions_Dc.1 small_test_conditions_Dc.2.1 small_test_conditions_Dc.2.2
  rw [← kbDc_def] at h
  exact h

end AdvancedEncryption.ExpLUT.Prog.KeyCore
