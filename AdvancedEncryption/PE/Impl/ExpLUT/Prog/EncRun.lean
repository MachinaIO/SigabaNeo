import PE.Impl.ExpLUT.Prog.EncReady
import PE.Impl.ExpLUT.Prog.EncOutputState

/-! # Scheme outputs of the initialized encryption phases -/
namespace AdvancedEncryption.ExpLUT.Prog.EncW
open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo
  SigabaNeo.Lattices.Algo.NegaG SigabaNeo.Tape SigabaNeo.Tape.Prog Matrix
open PE.BranchingProgram
variable (D : Dims) (mpk : MPKt D) (x : Attribute w8) (μ : Bool)
  (r : EncCoins (setting D) (Wb D) (Jh D) Pos)

noncomputable def bWord (ct : CTt D) : List Bool :=
  (vecE D (BCol (Wb D) D.K)).enc ct.b
noncomputable def hWord (ct : CTt D) : List Bool :=
  (FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).enc ct.h
noncomputable def aWord (ct : CTt D) : List Bool :=
  (FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc ct.caut

theorem length_bWord (ct : CTt D) : (bWord D ct).length =
    (Enum.list (α := BCol (Wb D) D.K)).length * (D.N * D.K) :=
  (vecE D (BCol (Wb D) D.K)).length ct.b

theorem length_hWord (ct : CTt D) : (hWord D ct).length =
    D.b * (2 * ((D.K + D.K) * (D.N * D.K))) := by
  rw [hWord, (FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).length ct.h]
  simp only [Jh, Enum.length_prod, len_fin]
  ring

theorem length_aWord (ct : CTt D) : (aWord D ct).length =
    D.b * ((D.K + D.K + (D.K + D.K)) * (D.K * ((D.K + D.K) * (D.N * D.K)))) := by
  rw [aWord, (FixedEnc.fun (α := Fin D.b)
    (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).length ct.caut]
  simp only [Dig, Enum.length_prod, len_fin]
  ring

theorem run_ready_b (o : List Bool) :
    mrowP.run (Function.update (readyCore D mpk x μ r ∘ bSlot) 0 o) 0 =
      shiftAppend o (bWord D (encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r)) := by
  obtain ⟨hs, hy, hz, hB, hE⟩ := ready_bData D mpk x μ r
  have hr := run_bPhase_ciphertext D _ ((ready_bOK D mpk x μ r).output o) mpk x μ r [] []
    (by simpa using hs) (by simpa using hy) (by simpa using hz)
    (by simpa using hB) (by simpa using hE)
  rw [hr]
  simp only [Function.update_self, Function.update_of_ne (by decide : (0 : Fin 66) ≠ 4), Function.update_of_ne (by decide : (0 : Fin 66) ≠ 5), shiftAppend, length_bWord]
  rfl

theorem run_ready_helper (hb : 0 < D.b) (o : List Bool)
    (ho : (hWord D (encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r)).length ≤ o.length) :
    (helperPairsP D 0 D.b).run (Function.update (readyCore D mpk x μ r ∘ helperSlot) 0 o) 0 =
      shiftAppend o (hWord D (encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r)) := by
  obtain ⟨hs, h1, hg, h5, h6, hH, hE⟩ := ready_helperData D mpk x μ r
  have hr := run_helperPairsP_ciphertext D _ ((ready_helperOK D mpk x μ r).output o) hb mpk x μ r
    (by simpa using hs) (by simpa using h1) (by simpa using hg) (by simpa using h5)
    (by simpa using h6) (by simpa using hH) (by simpa using hE)
    (by simpa only [Function.update_self, length_hWord] using ho)
  rw [hr]
  simp only [helperState, Function.update_self, Function.update_of_ne (by decide : (0 : Fin 69) ≠ 2), Function.update_of_ne (by decide : (0 : Fin 69) ≠ 3), shiftAppend, length_hWord]
  rfl

theorem run_ready_aut (hb : 0 < D.b) (o : List Bool)
    (ho : (aWord D (encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r)).length ≤ o.length) :
    (autBlocksP D 0 D.b).run (Function.update (readyCore D mpk x μ r ∘ autSlot) 0 o) 0 =
      shiftAppend o (aWord D (encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r)) := by
  obtain ⟨hs, h1, hg, h7, h8, hH, hEh, hA, hE⟩ := ready_autData D mpk x μ r
  have hr := run_autBlocksP_ciphertext D _ ((ready_autOK D mpk x μ r).output o) hb mpk x μ r
    (by simpa using hs) (by simpa using h1) (by simpa using hg) (by simpa using h7)
    (by simpa using h8) (by simpa using hH) (by simpa using hEh)
    (by simpa using hA) (by simpa using hE)
    (by simpa only [Function.update_self, length_aWord] using ho)
  rw [hr]
  simp only [autState, Function.update_self, Function.update_of_ne (by decide : (0 : Fin 85) ≠ 2), Function.update_of_ne (by decide : (0 : Fin 85) ≠ 3), Function.update_of_ne (by decide : (0 : Fin 85) ≠ 4), Function.update_of_ne (by decide : (0 : Fin 85) ≠ 5), shiftAppend, length_aWord]
  rfl

end AdvancedEncryption.ExpLUT.Prog.EncW
