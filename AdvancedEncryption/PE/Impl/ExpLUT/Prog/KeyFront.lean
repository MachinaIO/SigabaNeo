import PE.Impl.ExpLUT.Prog.KeyBranch
import PE.Impl.ExpLUT.Prog.EncFront
import SigabaNeo.Lib.Machines.Prog.LenEq

/-! Framed input parsing and exact predicate validation for KeyGen. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyCore
open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape
  SigabaNeo.Tape.Prog SigabaNeo.Tape.XProg SigabaNeo.Tape.MVM Cslib Cslib.Probability

/-- Decode the parameter word, master secret key, and predicate; retain the last two. -/
def parse : SigabaNeo.Tape.Prog 105 :=
  Prog.map (EncIO.parseMap 4) unfrP ⨾ Prog.map (EncIO.parseMap 1) unfrP ⨾
    Prog.map (EncIO.parseMap 5) unfrP ⨾ cp 0 1 ⨾ cp 1 5 ⨾ clr 4 ⨾ clr 5

theorem wf_parse : parse.WF :=
  ⟨wf_unfrP.map (by decide), wf_unfrP.map (by decide), wf_unfrP.map (by decide),
    trivial, trivial, trivial, trivial⟩

theorem coinFree_parse : parse.CoinFree := rfl

set_option maxHeartbeats 800000 in
theorem run_parse (pw msk C : List Bool) :
    parse.run (inputStore 0 (encodeTuple [pw, msk, C])) = io2 (R := 103) msk C [] := by
  have he : encodeTuple [pw, msk, C] = Turing.MultiTapeTM.frame pw ++
      (Turing.MultiTapeTM.frame msk ++ (Turing.MultiTapeTM.frame C ++ [])) := by
    simp [encodeTuple_cons, encodeTuple_nil]
  let S0 := inputStore (0 : Fin 105) (encodeTuple [pw, msk, C])
  let S1 := Function.update (Function.update (Function.update S0 0
    (Turing.MultiTapeTM.frame msk ++ (Turing.MultiTapeTM.frame C ++ []))) 4 (S0 4 ++ pw)) 2 []
  let S2 := Function.update (Function.update (Function.update S1 0
    (Turing.MultiTapeTM.frame C ++ [])) 1 (S1 1 ++ msk)) 2 []
  have h1 : (Prog.map (EncIO.parseMap 4) unfrP).run S0 = S1 :=
    EncIO.run_unfr 4 (by decide) S0 pw _ (by simp [S0, inputStore, he])
      (by simp [S0, inputStore])
  have h2 : (Prog.map (EncIO.parseMap 1) unfrP).run S1 = S2 :=
    EncIO.run_unfr 1 (by decide) S1 msk _ (by simp [S1]) (by simp [S1, S0, inputStore])
  have h3 := EncIO.run_unfr 5 (by decide) S2 C [] (by simp [S2])
    (by simp [S2, S1, S0, inputStore])
  change parse.run S0 = _
  simp only [parse, Prog.run_seq, run_copy, run_clear]
  rw [h1, h2, h3]
  funext t
  fin_cases t <;> simp [S2, S1, S0, inputStore, io2]

/-- Length-check input is predicate1; result2; scratch3..6. -/
def checkMap : Fin 6 → Fin 105 := ![1, 2, 3, 4, 5, 6]

def checkP : SigabaNeo.Tape.Prog 105 := Prog.map checkMap (lenEqP predLen)

theorem wf_checkP : checkP.WF := (wf_lenEqP _).map (by decide)

theorem coinFree_checkP : checkP.CoinFree := coinFree_mapP _ (coinFree_lenEqP _)

theorem run_checkP (msk C : List Bool) :
    checkP.run (io2 (R := 103) msk C []) =
      Function.update (io2 (R := 103) msk C []) 2 [decide (ValidC C)] := by
  have hi : Function.Injective checkMap := by decide
  have hs : (io2 (R := 103) msk C []) ∘ checkMap = in0 C := by
    funext j
    fin_cases j <;> simp [checkMap, io2, in0]
  rw [checkP, Prog.run_map hi, hs, run_lenEqP, ← hs, extend_update hi, extend_comp_self]
  rfl

/-- Choose the valid or zero-key branch after executing the length check. -/
noncomputable def chooseP (D : Dims) (B r : ℕ) : XProg 105 :=
  .seq (.prog checkP) (.ifBit 2 (validP D B r) (invalidP D))

theorem wf_chooseP (D : Dims) (B r : ℕ) : (chooseP D B r).WF :=
  ⟨wf_checkP, wf_validP D B r, wf_invalidP D⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Both predicate cases realize the implementation-independent word law. -/
theorem law_chooseP (D : Dims) (hb : D.b = 22) (hn : 2 ^ D.b ≤ D.q)
    (B r : ℕ) (hB : 2 ^ B ≤ D.q) (hBK : B ≤ D.K)
    (hr : 2 * r < 2 ^ B) (hq : 2 ^ (B + 1) ≤ D.q) (hcount : 2 * (D.K - B) < D.q)
    (msk : MSKt D) (C : List Bool) :
    (chooseP D B r).law (io2 (R := 103) ((mskEnc D).enc msk) C []) =
      (keyLawW D (kbOf D B hB r) msk C).map
        (fun sk ↦ inputStore (0 : Fin 105) ((skEnc D).enc sk)) := by
  rw [chooseP, XProg.law_seq, XProg.law_prog,
    Prog.law_eq_run_of_coinFree _ coinFree_checkP, run_checkP, PMF.pure_bind]
  have hi (p q : XProg 105) (s : Store 105) :
      (XProg.ifBit 2 p q).law s = if (s 2).head? = some true then p.law s else q.law s := by
    change (if (s 2).head? = some true then p.denote s else q.denote s).eval = _
    split_ifs <;> rfl
  rw [hi]
  simp only [Function.update_self, List.head?_cons, Option.some.injEq, decide_eq_true_eq]
  by_cases hc : ValidC C
  · rw [ite_eq_left hc, law_validP D hb hn B r hB hBK hr hq hcount msk C _
      (by simp [io2]) (by simp [io2])]
    have hk : keyLawW D (kbOf D B hB r) msk C =
        (keyGenLaw (S := setting D) (kbOf D B hB r).Big (kbOf D B hB r).Small
          (kbOf D B hB r).hBig gadDec (helperMap D) msk (bpOf (progOf C))).map
          (fun k ↦ (msk.mpk, k)) := ite_eq_left hc
    rw [hk, PMF.map_comp]
    rfl
  · rw [ite_eq_right hc, law_invalidP D msk _ (by simp [io2])]
    simp [keyLawW, hc]

end AdvancedEncryption.ExpLUT.Prog.KeyCore
