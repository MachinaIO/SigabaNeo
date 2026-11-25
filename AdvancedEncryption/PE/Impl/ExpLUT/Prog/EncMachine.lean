import PE.Impl.ExpLUT.Prog.EncPipeline
import SigabaNeo.Lib.Machines.Prog.FrameOut

/-! # A compiled encryption machine satisfying EncSpec -/
namespace AdvancedEncryption.ExpLUT.Prog.EncW
open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo
  SigabaNeo.Lattices.Algo.NegaG SigabaNeo.Tape SigabaNeo.Tape.Prog Matrix
open PE.BranchingProgram Cslib Cslib.Probability

/-- Wrap the ciphertext in the single-field tuple required by the primitive interface. -/
def frameCiphertextP : XProg 326 :=
  .seq (.prog (.seq (cp 1 0) (clr 0)))
    (.seq (XProg.frameApP 0 1 2 3) (.prog (clr 1)))

theorem law_frameCiphertextP (w : List Bool) :
    frameCiphertextP.law (inputStore 0 w) = PMF.pure (inputStore 0 (encodeTuple [w])) := by
  rw [frameCiphertextP, XProg.law_seq, XProg.law_prog,
    Prog.law_eq_run_of_coinFree _ (by rfl), Prog.run_seq, run_copy, run_clear,
    PMF.pure_bind, XProg.law_seq]
  rw [XProg.law_frameApP (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ (by simp [inputStore]) (by simp [inputStore])]
  rw [PMF.pure_bind, XProg.law_prog, Prog.law_eq_run_of_coinFree _ (by rfl), run_clear]
  congr 1
  funext i
  by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;>
    simp [inputStore, h0, h1, encodeTuple_cons, encodeTuple_nil]

theorem wf_frameCiphertextP : frameCiphertextP.WF :=
  ⟨⟨trivial, trivial⟩, XProg.wf_frameApP (by decide) (by decide), trivial⟩

variable (D : Dims)

noncomputable def encProgram (η L e : ℕ) : XProg 326 :=
  .seq (encryptionP D η L e) frameCiphertextP

theorem wf_encProgram (η L e : ℕ) : (encProgram D η L e).WF :=
  ⟨wf_encryptionP D η L e, wf_frameCiphertextP⟩

theorem law_encProgram {η L e : ℕ} (hL : 1 ≤ L) (hLK : L ≤ D.K)
    (hη : η + 1 ≤ 2 ^ (L - 1)) (he : e < D.K)
    (hb : 0 < D.b) (hN : 2 ≤ D.N) (hw : wSt * 128 ≤ 2 * D.N)
    (pw : List Bool) (mpk : MPKt D) (x : Attribute w8) (μ : Bool) :
    (encProgram D η L e).law (inputStore 0
      (encodeTuple [pw, (mpkEnc D).enc mpk, encAttribute w8 x, [μ]])) =
      (encLawW D (cbdR D η) (cbdR D η) (floodR D e) mpk x μ).map
        (fun ct ↦ inputStore 0 (encodeTuple [(ctEnc D).enc ct])) := by
  rw [encProgram, XProg.law_seq, law_encryptionP D hL hLK hη he hb hN hw,
    PMF.bind_map]
  have hh := congrArg (PMF.bind (encCoinsLaw (setting D) (Wb D) (Jh D) Pos
    (cbdR D η) (cbdR D η) (floodR D e)))
      (funext fun r ↦ law_frameCiphertextP ((ctEnc D).enc
        (encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r)))
  rw [encLawW, encLaw, PMF.map_comp]
  exact hh.trans (PMF.bind_pure_comp _ _)

/-- Exact framed input length, independent of key and attribute values. -/
def encInputLength : ℕ := (2 * pwW.length + 1) + (2 * fixedSize (mpkEnc D) + 1) + 257 + 3

theorem length_encInput (mpk : MPKt D) (x : Attribute w8) (μ : Bool) :
    (encodeTuple [pwW, (mpkEnc D).enc mpk, encAttribute w8 x, [μ]]).length = encInputLength D := by
  simp only [encodeTuple_cons, encodeTuple_nil, List.length_append, length_frame,
    List.length_nil, List.length_cons, (mpkEnc D).length mpk, length_encAttribute]
  simp only [encInputLength, fixedSize]
  omega

/-- Concrete finite-clock machine compiled from the full encryption program. -/
noncomputable def encMP (η L e : ℕ) : Machine :=
  (encProgram D η L e).toMachineT 0 0 (encInputLength D)

/-- The compiled machine meets the primitive's exact encryption specification. -/
theorem encSpec_encMP {η L e : ℕ} (hL : 1 ≤ L) (hLK : L ≤ D.K)
    (hη : η + 1 ≤ 2 ^ (L - 1)) (he : e < D.K)
    (hb : 0 < D.b) (hN : 2 ≤ D.N) (hw : wSt * 128 ≤ 2 * D.N) :
    EncSpec D (cbdR D η) (cbdR D η) (floodR D e) (encMP D η L e) := by
  intro mpk x μ
  rw [encMP, XProg.run_toMachineT _ (wf_encProgram D η L e) 0 0 (encInputLength D) _
    (by rw [length_encInput]), law_encProgram D hL hLK hη he hb hN hw, PMF.map_comp]
  congr 1

/-- The machine uses the compiler's explicit finite clock for this concrete program. -/
theorem time_encMP (η L e : ℕ) : (encMP D η L e).time =
    XProg.totalTimeT (encProgram D η L e) 0 0 (encInputLength D) := rfl

end AdvancedEncryption.ExpLUT.Prog.EncW
