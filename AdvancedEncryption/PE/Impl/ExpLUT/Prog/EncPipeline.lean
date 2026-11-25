import PE.Impl.ExpLUT.Prog.EncComplete
import PE.Impl.ExpLUT.Prog.EncFront
import PE.Impl.ExpLUT.Prog.EncNormalize

/-! # Input parsing, sampling, concrete encryption, and output cleanup -/
namespace AdvancedEncryption.ExpLUT.Prog.EncW
open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo
  SigabaNeo.Lattices.Algo.NegaG SigabaNeo.Tape SigabaNeo.Tape.Prog Matrix
open PE.BranchingProgram AdvancedEncryption.DualUse.Prog Cslib Cslib.Probability

/-- Erase a finite list of tapes using concrete clear instructions. -/
def eraseP : List (Fin 326) → SigabaNeo.Tape.Prog 326
  | [] => cp 0 0
  | i :: is => .seq (clr i) (eraseP is)

theorem run_eraseP (is : List (Fin 326)) (S : Store 326) (j : Fin 326) :
    (eraseP is).run S j = if j ∈ is then [] else S j := by
  induction is generalizing S with
  | nil => simp [eraseP, run_copy]
  | cons i is ih =>
    rw [eraseP, Prog.run_seq, run_clear, ih]
    by_cases hj : j ∈ is <;> by_cases hi : j = i <;> simp [hj, hi]

def eraseNonoutput : SigabaNeo.Tape.Prog 326 := eraseP ((List.finRange 325).map Fin.succ)

theorem run_eraseNonoutput (S : Store 326) :
    eraseNonoutput.run S = inputStore 0 (S 0) := by
  funext j
  cases j using Fin.cases with
  | zero => simp [eraseNonoutput, run_eraseP, inputStore]
  | succ j => simp [eraseNonoutput, run_eraseP, inputStore]

theorem wf_eraseP (is : List (Fin 326)) : (eraseP is).WF := by
  induction is with
  | nil => trivial
  | cons i is ih => exact ⟨trivial, ih⟩

theorem coinFree_eraseP (is : List (Fin 326)) : (eraseP is).CoinFree := by
  induction is with
  | nil => rfl
  | cons i is ih => exact ih

variable (D : Dims)

/-- Deterministic encryption returns only the ciphertext on tape zero. -/
noncomputable def cleanCoreP : SigabaNeo.Tape.Prog 326 :=
  .seq (initializedCoreP D) eraseNonoutput

theorem run_cleanCoreP (mpk : MPKt D) (x : Attribute w8) (μ : Bool)
    (r : EncCoins (setting D) (Wb D) (Jh D) Pos) (hb : 0 < D.b) (hN : 2 ≤ D.N)
    (hw : wSt * 128 ≤ 2 * D.N) :
    (cleanCoreP D).run (encStart (encCoinWord D r)
      ((mpkEnc D).enc mpk ++ (encAttribute w8 x ++ [μ]))) =
      inputStore 0 ((ctEnc D).enc (encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r)) := by
  rw [cleanCoreP, Prog.run_seq, run_eraseNonoutput, run_initializedCoreP_ciphertext D mpk x μ r hb hN hw]

theorem wf_cleanCoreP : (cleanCoreP D).WF := ⟨wf_initializedCoreP D, wf_eraseP _⟩
theorem coinFree_cleanCoreP : (cleanCoreP D).CoinFree := by
  simp only [cleanCoreP, Prog.CoinFree, Prog.coinFreeB, Bool.and_eq_true]
  exact ⟨coinFree_initializedCoreP D, coinFree_eraseP _⟩

/-- Move the parser/sampler outputs to the input streams of the concrete core. -/
def relocateP : SigabaNeo.Tape.Prog 326 :=
  .seq (cp 321 0) (.seq (cp 322 1) (.seq (clr 0) (clr 1)))

theorem run_relocateP (coins pub : List Bool) :
    relocateP.run (io2 (R := 324) coins pub []) = encStart coins pub := by
  funext i
  simp only [relocateP, Prog.run_seq, run_copy, run_clear]
  have hz : i.val = 0 ↔ i = 0 := by simp
  have ho : i.val = 1 ↔ i = 1 := by
    constructor
    · intro h; exact Fin.ext h
    · intro h; subst i; rfl
  by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;>
    by_cases h321 : i = 321 <;> by_cases h322 : i = 322 <;>
      simp_all [io2, encStart, sourceTape]

def prepareFrame : Fin 105 ↪ Fin 326 := Fin.castLEEmb (by decide)

theorem restrict_inputStore (w : List Bool) :
    (fun j ↦ inputStore (0 : Fin 326) w (prepareFrame j)) = inputStore (0 : Fin 105) w := by
  funext j
  by_cases hj : j = 0
  · subst j; simp [inputStore, prepareFrame]
  · have hj' : prepareFrame j ≠ 0 := prepareFrame.injective.ne hj
    simp [inputStore, hj, hj']

theorem embed_prepare_output (w coins pub : List Bool) :
    embedF prepareFrame (inputStore 0 w) (io2 (R := 103) coins pub []) =
      io2 (R := 324) coins pub [] := by
  funext i
  rcases embedF_cases prepareFrame (inputStore 0 w) (io2 (R := 103) coins pub []) i with
    ⟨hn, he⟩ | ⟨j, hj, he⟩
  · have h0 : i ≠ 0 := by
      intro hi; subst i
      rw [show (0 : Fin 326) = prepareFrame 0 from rfl, partialInv_self] at hn
      contradiction
    have h1 : i ≠ 1 := by
      intro hi; subst i
      rw [show (1 : Fin 326) = prepareFrame 1 from rfl, partialInv_self] at hn
      contradiction
    rw [he]
    have hz : i.val ≠ 0 := fun h ↦ h0 (Fin.ext h)
    have ho : i.val ≠ 1 := fun h ↦ h1 (Fin.ext h)
    simp [inputStore, io2, h0, hz, ho]
  · subst i
    rw [he]
    rfl

noncomputable def widePrepare (η L e : ℕ) : XProg 326 :=
  .frame prepareFrame (EncIO.prepare D η L e)

theorem law_widePrepare {η L e : ℕ} (hL : 1 ≤ L) (hLK : L ≤ D.K)
    (hη : η + 1 ≤ 2 ^ (L - 1)) (he : e < D.K) (pw mpk x μ : List Bool) :
    (widePrepare D η L e).law (inputStore 0 (encodeTuple [pw, mpk, x, μ])) =
      (encCoinsLaw (setting D) (Wb D) (Jh D) Pos (cbdR D η) (cbdR D η) (floodR D e)).map
        (fun r ↦ io2 (R := 324) (encCoinWord D r) (mpk ++ (x ++ μ)) []) := by
  rw [widePrepare, XProg.law_frame, restrict_inputStore,
    EncIO.law_prepare D hL hLK hη he pw mpk x μ, PMF.map_comp]
  congr 1
  funext r
  exact embed_prepare_output _ _ _

/-- Keep only the two input queues; all compiler scratch bounds are reset explicitly. -/
def inputScratch : List (Fin 326) := (List.finRange 326).filter fun i => i ≠ 321 ∧ i ≠ 322

noncomputable def normalizeInputsP : SigabaNeo.Tape.Prog 326 :=
  .seq (trimP 321 323 (coinLength D))
    (.seq (trimP 322 323 (publicLength D)) (eraseP inputScratch))

theorem run_normalizeInputsP (S : Store 326) :
    (normalizeInputsP D).run S = encStart (takeD (coinLength D) (S 321))
      (takeD (publicLength D) (S 322)) := by
  funext i
  simp only [normalizeInputsP, Prog.run_seq, run_eraseP,
    run_trimP (321 : Fin 326) 323 (by decide),
    run_trimP (322 : Fin 326) 323 (by decide), encStart]
  by_cases h1 : i = 321 <;> by_cases h2 : i = 322 <;>
    simp [inputScratch, sourceTape, h1, h2]

theorem run_normalizeInputsP_start (mpk : MPKt D) (x : Attribute w8) (μ : Bool)
    (r : EncCoins (setting D) (Wb D) (Jh D) Pos) :
    (normalizeInputsP D).run (encStart (encCoinWord D r)
      ((mpkEnc D).enc mpk ++ (encAttribute w8 x ++ [μ]))) =
    encStart (encCoinWord D r) ((mpkEnc D).enc mpk ++ (encAttribute w8 x ++ [μ])) := by
  rw [run_normalizeInputsP]
  simp [encStart, sourceTape, takeD_of_length' (length_encCoinWord D r),
    takeD_of_length' (length_publicWord D mpk x μ)]

theorem wf_normalizeInputsP : (normalizeInputsP D).WF :=
  ⟨wf_trimP _ _ _, wf_trimP _ _ _, wf_eraseP _⟩

theorem coinFree_normalizeInputsP : (normalizeInputsP D).CoinFree := by
  simp only [normalizeInputsP, CoinFree, coinFreeB, Bool.and_eq_true]
  exact ⟨coinFree_trimP _ _ _, coinFree_trimP _ _ _, coinFree_eraseP _⟩

/-- The complete randomized encryption program, with no abstract core parameter. -/
noncomputable def encryptionP (η L e : ℕ) : XProg 326 :=
  .seq (widePrepare D η L e) (.prog (.seq relocateP (.seq (normalizeInputsP D) (cleanCoreP D))))

theorem wf_encryptionP (η L e : ℕ) : (encryptionP D η L e).WF :=
  ⟨EncIO.wf_prepare D η L e, ⟨⟨trivial, trivial, trivial, trivial⟩,
    wf_normalizeInputsP D, wf_cleanCoreP D⟩⟩

/-- Exact randomized encryption law, including parsing, sampling, execution, and cleanup. -/
theorem law_encryptionP {η L e : ℕ} (hL : 1 ≤ L) (hLK : L ≤ D.K)
    (hη : η + 1 ≤ 2 ^ (L - 1)) (he : e < D.K)
    (hb : 0 < D.b) (hN : 2 ≤ D.N) (hw : wSt * 128 ≤ 2 * D.N)
    (pw : List Bool) (mpk : MPKt D) (x : Attribute w8) (μ : Bool) :
    (encryptionP D η L e).law (inputStore 0
      (encodeTuple [pw, (mpkEnc D).enc mpk, encAttribute w8 x, [μ]])) =
      (encCoinsLaw (setting D) (Wb D) (Jh D) Pos (cbdR D η) (cbdR D η) (floodR D e)).map
        (fun r ↦ inputStore 0 ((ctEnc D).enc
          (encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r))) := by
  have hc : (Prog.seq relocateP (.seq (normalizeInputsP D) (cleanCoreP D))).CoinFree := by
    simp only [Prog.CoinFree, Prog.coinFreeB, Bool.and_eq_true]
    exact ⟨rfl, coinFree_normalizeInputsP D, coinFree_cleanCoreP D⟩
  rw [encryptionP, XProg.law_seq, law_widePrepare D hL hLK hη he, PMF.bind_map]
  have hrun : ∀ r : EncCoins (setting D) (Wb D) (Jh D) Pos,
      (XProg.prog (.seq relocateP (.seq (normalizeInputsP D) (cleanCoreP D)))).law
        (io2 (R := 324) (encCoinWord D r) ((mpkEnc D).enc mpk ++ (encAttribute w8 x ++ [μ])) []) =
      PMF.pure (inputStore 0 ((ctEnc D).enc
        (encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r))) := by
    intro r
    rw [XProg.law_prog, Prog.law_eq_run_of_coinFree _ hc, Prog.run_seq,
      run_relocateP, Prog.run_seq, run_normalizeInputsP_start D mpk x μ r,
      run_cleanCoreP D mpk x μ r hb hN hw]
  exact (congrArg (PMF.bind (encCoinsLaw (setting D) (Wb D) (Jh D) Pos
    (cbdR D η) (cbdR D η) (floodR D e))) (funext hrun)).trans (PMF.bind_pure_comp _ _)

end AdvancedEncryption.ExpLUT.Prog.EncW
