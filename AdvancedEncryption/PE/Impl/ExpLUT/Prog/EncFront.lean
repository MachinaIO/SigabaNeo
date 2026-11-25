import PE.Impl.ExpLUT.Prog.EncCoins
import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.VMIO
import SigabaNeoStd.Machines.Prog.FrameIO

/-! # Encryption input parsing, random tape generation, and VM execution -/

namespace AdvancedEncryption.ExpLUT.Prog.EncIO

open SigabaNeo SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.Prog SigabaNeo.Tape.XProg
  Cslib Cslib.Probability AdvancedEncryption.RingBTVW.Prog
open AdvancedEncryption.PE.BranchingProgram

/-- Frame parser tapes: input, destination, and two scratch tapes. -/
def parseMap (d : Fin 105) : Fin 4 → Fin 105 := ![0, d, 2, 3]

theorem run_unfr (d : Fin 105) (hd : Function.Injective (parseMap d))
    (s : Store 105) (u r : List Bool) (h0 : s 0 = Turing.MultiTapeTM.frame u ++ r)
    (h3 : s 3 = []) :
    (Prog.map (parseMap d) unfrP).run s =
      Function.update (Function.update (Function.update s 0 r) d (s d ++ u)) 2 [] := by
  rw [run_map hd, run_unfrP (s ∘ parseMap d) u r h0 h3,
    extend_update hd, extend_update hd, extend_update hd, extend_comp_self]
  rfl

/-- Discard the parameter word; concatenate public key, attribute, and message on tape 1. -/
def parse : SigabaNeo.Tape.Prog 105 :=
  Prog.map (parseMap 4) unfrP ⨾ Prog.map (parseMap 1) unfrP ⨾
    Prog.map (parseMap 1) unfrP ⨾ Prog.map (parseMap 1) unfrP ⨾ clr 4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem run_parse (pw mpk x μ : List Bool) :
    parse.run (inputStore 0 (encodeTuple [pw, mpk, x, μ])) =
      io2 (R := 103) [] (mpk ++ (x ++ μ)) [] := by
  have he : encodeTuple [pw, mpk, x, μ] = Turing.MultiTapeTM.frame pw ++
      (Turing.MultiTapeTM.frame mpk ++ (Turing.MultiTapeTM.frame x ++
        (Turing.MultiTapeTM.frame μ ++ []))) := by simp [encodeTuple_cons, encodeTuple_nil]
  let S0 := inputStore (0 : Fin 105) (encodeTuple [pw, mpk, x, μ])
  let S1 := Function.update (Function.update (Function.update S0 0
    (Turing.MultiTapeTM.frame mpk ++ (Turing.MultiTapeTM.frame x ++
      (Turing.MultiTapeTM.frame μ ++ [])))) 4 (S0 4 ++ pw)) 2 []
  let S2 := Function.update (Function.update (Function.update S1 0
    (Turing.MultiTapeTM.frame x ++ (Turing.MultiTapeTM.frame μ ++ []))) 1 (S1 1 ++ mpk)) 2 []
  let S3 := Function.update (Function.update (Function.update S2 0
    (Turing.MultiTapeTM.frame μ ++ [])) 1 (S2 1 ++ x)) 2 []
  have h1 : (Prog.map (parseMap 4) unfrP).run S0 = S1 :=
    run_unfr 4 (by decide) S0 pw _ (by simp [S0, inputStore, he]) (by simp [S0, inputStore])
  have h2 : (Prog.map (parseMap 1) unfrP).run S1 = S2 :=
    run_unfr 1 (by decide) S1 mpk _ (by simp [S1]) (by simp [S1, S0, inputStore])
  have h3 : (Prog.map (parseMap 1) unfrP).run S2 = S3 :=
    run_unfr 1 (by decide) S2 x _ (by simp [S2]) (by simp [S2, S1, S0, inputStore])
  have h4 := run_unfr 1 (by decide) S3 μ [] (by simp [S3])
    (by simp [S3, S2, S1, S0, inputStore])
  change parse.run S0 = _
  simp only [parse, run_seq, run_clear]
  rw [h1, h2, h3, h4]
  funext t
  fin_cases t <;> simp [S3, S2, S1, S0, inputStore, io2, List.append_assoc]

theorem coinFree_parse : parse.CoinFree := rfl

theorem wf_parse : parse.WF :=
  ⟨wf_unfrP.map (by decide), wf_unfrP.map (by decide),
    wf_unfrP.map (by decide), wf_unfrP.map (by decide), trivial⟩

/-- Embed the seven sampler tapes in the VM's 105 tapes. -/
def sampleFrame : Fin 7 ↪ Fin 105 := Fin.castLEEmb (by decide)

variable (D : Dims)

/-- Parse the public input and sample the complete encryption coin queue. -/
noncomputable def prepare (η L e : ℕ) : XProg 105 :=
  seq (prog parse) (frame sampleFrame (encCoinsP D η L e))

/-- The exact distribution at the entrance to the deterministic encryption VM. -/
theorem law_prepare {η L e : ℕ} (hL : 1 ≤ L) (hLK : L ≤ D.K)
    (hη : η + 1 ≤ 2 ^ (L - 1)) (he : e < D.K) (pw mpk x μ : List Bool) :
    (prepare D η L e).law (inputStore 0 (encodeTuple [pw, mpk, x, μ])) =
      (encCoinsLaw (setting D) (Wb D) (Jh D) Pos
        (cbdR D η) (cbdR D η) (floodR D e)).map
          (fun r ↦ io2 (R := 103) (encCoinWord D r) (mpk ++ (x ++ μ)) []) := by
  rw [prepare, XProg.law_seq, XProg.law_prog, Prog.law_eq_run_of_coinFree _ coinFree_parse, run_parse, PMF.pure_bind]
  have ha := appendLaw_frame sampleFrame (appendLaw_encCoinsP D hL hLK hη he)
  rw [ha _ (by simp [P5, P3, io2, sampleFrame]), PMF.map_comp]
  congr 1
  funext r t
  by_cases ht : t = 0
  · subst ht; simp [io2, sampleFrame]
  · simp [io2, sampleFrame, ht]

/-- The randomized encryption pipeline with the deterministic VM core supplied explicitly. -/
noncomputable def program (η L e : ℕ) (tm : Fin 64 → ℕ) (code : MVM.Code) : XProg 105 :=
  seq (prepare D η L e) (MVM.frontIO D.N D.K tm code)

theorem law_program {η L e : ℕ} (hL : 1 ≤ L) (hLK : L ≤ D.K)
    (hη : η + 1 ≤ 2 ^ (L - 1)) (he : e < D.K) (tm : Fin 64 → ℕ) (code : MVM.Code)
    (pw mpk x μ : List Bool) :
    (program D η L e tm code).law (inputStore 0 (encodeTuple [pw, mpk, x, μ])) =
      (encCoinsLaw (setting D) (Wb D) (Jh D) Pos
        (cbdR D η) (cbdR D η) (floodR D e)).map
          (fun r ↦ io2 (R := 103)
            (MVM.exec D.N D.K code (MVM.IO.init (encCoinWord D r) (mpk ++ (x ++ μ)) tm) 0) [] []) := by
  rw [program, XProg.law_seq, law_prepare D hL hLK hη he, PMF.bind_map]
  have hh : ∀ r : EncCoins (setting D) (Wb D) (Jh D) Pos,
      (MVM.frontIO D.N D.K tm code).law
        (io2 (R := 103) (encCoinWord D r) (mpk ++ (x ++ μ)) []) =
      PMF.pure (io2 (R := 103)
        (MVM.exec D.N D.K code (MVM.IO.init (encCoinWord D r) (mpk ++ (x ++ μ)) tm) 0) [] []) :=
    fun _ ↦ MVM.law_frontIO D.N_pos D.K_pos tm code _ _
  exact (congrArg (PMF.bind (encCoinsLaw (setting D) (Wb D) (Jh D) Pos
    (cbdR D η) (cbdR D η) (floodR D e))) (funext hh)).trans (PMF.bind_pure_comp _ _)


theorem wf_prepare (η L e : ℕ) : (prepare D η L e).WF :=
  ⟨wf_parse, wf_encCoinsP D η L e⟩

theorem wf_program (η L e : ℕ) (tm : Fin 64 → ℕ) (code : MVM.Code) (hc : code.WFc) :
    (program D η L e tm code).WF :=
  ⟨wf_prepare D η L e, MVM.wf_frontIO D.N D.K tm code hc⟩


/-- Once the explicit core computes the ciphertext word, the pipeline has the scheme's law.
The core premise is an outstanding implementation obligation, not a cryptographic assumption. -/
theorem law_program_of_core {η L e : ℕ} (hL : 1 ≤ L) (hLK : L ≤ D.K)
    (hη : η + 1 ≤ 2 ^ (L - 1)) (he : e < D.K) (tm : Fin 64 → ℕ) (code : MVM.Code)
    (mpk : MPKt D) (x : Attribute w8) (μ : Bool)
    (hc : ∀ r : EncCoins (setting D) (Wb D) (Jh D) Pos,
      MVM.exec D.N D.K code (MVM.IO.init (encCoinWord D r)
        ((mpkEnc D).enc mpk ++ (encAttribute w8 x ++ [μ])) tm) 0 =
      encodeTuple [(ctEnc D).enc (encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r)]) :
    (program D η L e tm code).law (inputStore 0 (encodeTuple [pwW, (mpkEnc D).enc mpk,
      encAttribute w8 x,
      [μ]])) =
      (encLawW D (cbdR D η) (cbdR D η) (floodR D e) mpk x μ).map
        (fun ct ↦ io2 (R := 103) (encodeTuple [(ctEnc D).enc ct]) [] []) := by
  rw [law_program D hL hLK hη he]
  unfold encLawW encLaw
  rw [PMF.map_comp]
  apply congrArg (PMF.map · (encCoinsLaw (setting D) (Wb D) (Jh D) Pos
    (cbdR D η) (cbdR D η) (floodR D e)))
  funext r
  exact congrArg (fun out ↦ io2 (R := 103) out [] []) (hc r)

end AdvancedEncryption.ExpLUT.Prog.EncIO
