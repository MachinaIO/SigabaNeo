import PE.Impl.ExpLUT.Prog.EncAutomorphisms

/-! # The executable public-matrix encryption row -/
namespace AdvancedEncryption.ExpLUT.Prog.EncW

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo
  SigabaNeo.Lattices.Algo.NegaG SigabaNeo.Tape SigabaNeo.Tape.Prog Matrix

variable (D : Dims)

/-- Templates and blank scratch for the public-matrix row. -/
structure BPhaseOK (S : Store 66) : Prop where
  scratch : ∀ i : Fin 66, 14 ≤ i.val → S i = []
  hK : (S 6).length = D.K
  hN : (S 7).length = D.N
  hNK : (S 8).length = D.N * D.K
  hL : (S 9).length = (Enum.list (α := BCol (Wb D) D.K)).length
  hK1 : (S 10).length = D.K - 1
  h11 : (S 11).length = (D.K + D.K) * (D.N * D.K)
  h12 : (S 12).length = (Enum.list (α := BCol (Wb D) D.K)).length * (D.N * D.K)
  h13 : (S 13).length = ((Enum.list (α := BCol (Wb D) D.K)).length +
    (Enum.list (α := BCol (Wb D) D.K)).length) * (D.N * D.K)

/-- The actual matrix-row program produces the scheme's `b` field and consumes its inputs. -/
theorem run_bPhase_ciphertext (S : Store 66) (h : BPhaseOK D S)
    (mpk : MPKt D) (x : PE.BranchingProgram.Attribute PE.BranchingProgram.w8) (μ : Bool)
    (r : EncCoins (setting D) (Wb D) (Jh D) Pos) (restB restE : List Bool)
    (hs : S 1 = wd D r.s) (hy : (S 2).length = D.N * D.K) (hz : S 3 = wd D 0)
    (hB : S 4 = (matE D (Fin 2) (BCol (Wb D) D.K)).enc mpk.B ++ restB)
    (hE : S 5 = (vecE D (BCol (Wb D) D.K)).enc r.eb ++ restE) :
    mrowP.run S = Function.update (Function.update (Function.update S 0
      ((S 0 ++ (vecE D (BCol (Wb D) D.K)).enc
        (encrypt (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ) r).b).drop
          ((Enum.list (α := BCol (Wb D) D.K)).length * (D.N * D.K)))) 4 restB) 5 restE := by
  have hM : ((matE D (Fin 2) (BCol (Wb D) D.K)).enc mpk.B).length =
      ((Enum.list (α := BCol (Wb D) D.K)).length +
        (Enum.list (α := BCol (Wb D) D.K)).length) * (D.N * D.K) := by
    rw [(matE D (Fin 2) (BCol (Wb D) D.K)).length mpk.B, len_fin]; ring
  have hV : ((vecE D (BCol (Wb D) D.K)).enc r.eb).length =
      (Enum.list (α := BCol (Wb D) D.K)).length * (D.N * D.K) :=
    (vecE D (BCol (Wb D) D.K)).length r.eb
  rw [run_mrowP D.K_pos S h.scratch h.hK h.hN h.hNK h.hL h.hK1 h.h11 h.h12 h.h13
    (by rw [hs, length_wd]) (by rw [hz, length_wd])]
  rw [hs, hz, hB, hE, row_b D mpk.B restB r.s (length_wd D 0) hy (decRM_wd D 0) r.eb restE]
  have dropB := @List.drop_left Bool ((matE D (Fin 2) (BCol (Wb D) D.K)).enc mpk.B) restB
  have dropE := @List.drop_left Bool ((vecE D (BCol (Wb D) D.K)).enc r.eb) restE
  simp only [hM] at dropB
  simp only [hV] at dropE
  rw [dropB, dropE]
  rfl

end AdvancedEncryption.ExpLUT.Prog.EncW
