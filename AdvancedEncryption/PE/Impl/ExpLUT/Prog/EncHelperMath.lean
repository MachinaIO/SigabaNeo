import PE.Impl.ExpLUT.Prog.EncTailMath

/-! # The helper encryption phase agrees with the scheme -/

namespace AdvancedEncryption.ExpLUT.Prog.EncW

open SigabaNeo SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG
  SigabaNeo.Tape SigabaNeo.Tape.Prog Matrix

variable (D : Dims)

/-- A helper row with its actual iterated automorphism word as gadget secret. -/
theorem hRow_helper (H : Matrix (Fin 2) (Col D.K) (Rg D)) (e : Col D.K → Rg D)
    (s : Rg D) (j : ℕ) (rest rest' : List Bool) :
    hRow D.N D.K (wd D s) (autTW D.N D.K (gD D) j (wd D s)) (wd D 1)
      ((matE D (Fin 2) (Col D.K)).enc H ++ rest)
      ((vecE D (Col D.K)).enc e ++ rest') =
      (vecE D (Col D.K)).enc
        (sec s ᵥ* H - sec ((setting D).E.σ ((setting D).idx j) s) ᵥ* GD D + e) := by
  unfold hRow
  rw [row_mat D H rest s (length_wd D 1)
    (length_autTW D.N_pos (length_wd D s) j) e rest', decRM_wd,
    autTW, decRM_autIt D (length_wd D s), decRM_wd, one_smul]

/-- The fixed templates and scratch invariant of the two-helper program. -/
structure HelperOK (S : Store 69) : Prop where
  scratch : ∀ i : Fin 69, 16 ≤ i.val → S i = []
  hK : (S 8).length = D.K
  hN : (S 9).length = D.N
  hNK : (S 10).length = D.N * D.K
  h11 : (S 11).length = D.K + D.K
  h12 : (S 12).length = D.K - 1
  h13 : (S 13).length = (D.K + D.K) * (D.N * D.K)
  h14 : (S 14).length = (D.K + D.K) * (D.N * D.K)
  h15 : (S 15).length = (D.K + D.K + (D.K + D.K)) * (D.N * D.K)

/-- Running one helper pair consumes both matrix/error blocks and writes their scheme rows. -/
theorem run_hBlkP_scheme (S : Store 69) (h : HelperOK D S)
    (H₁ H₂ : Matrix (Fin 2) (Col D.K) (Rg D)) (e₁ e₂ : Col D.K → Rg D)
    (s : Rg D) (j₁ j₂ : ℕ) (rest rest' : List Bool)
    (hs : S 1 = wd D s) (h1 : S 7 = wd D 1) (hg : (S 4).length = gD D)
    (hj₁ : (S 5).length = j₁) (hj₂ : (S 6).length = j₂)
    (hH : S 2 = (matE D (Fin 2) (Col D.K)).enc H₁ ++
      ((matE D (Fin 2) (Col D.K)).enc H₂ ++ rest))
    (he : S 3 = (vecE D (Col D.K)).enc e₁ ++ ((vecE D (Col D.K)).enc e₂ ++ rest')) :
    hBlkP.run S =
      let r₁ := (vecE D (Col D.K)).enc
        (sec s ᵥ* H₁ - sec ((setting D).E.σ ((setting D).idx j₁) s) ᵥ* GD D + e₁)
      let r₂ := (vecE D (Col D.K)).enc
        (sec s ᵥ* H₂ - sec ((setting D).E.σ ((setting D).idx j₂) s) ᵥ* GD D + e₂)
      Function.update (Function.update (Function.update S 0
        ((((S 0 ++ r₁).drop ((D.K + D.K) * (D.N * D.K))) ++ r₂).drop
          ((D.K + D.K) * (D.N * D.K)))) 2 rest) 3 rest' := by
  have hmat (H : Matrix (Fin 2) (Col D.K) (Rg D)) :
      ((matE D (Fin 2) (Col D.K)).enc H).length =
        (D.K + D.K + (D.K + D.K)) * (D.N * D.K) := by
    rw [matE_fin2, List.length_append, length_vecE', length_vecE', length_col]
    ring
  have hvec (e : Col D.K → Rg D) : ((vecE D (Col D.K)).enc e).length =
      (D.K + D.K) * (D.N * D.K) := by rw [length_vecE', length_col]
  have dropM (H : Matrix (Fin 2) (Col D.K) (Rg D)) (r : List Bool) :
      (((matE D (Fin 2) (Col D.K)).enc H) ++ r).drop
        ((D.K + D.K + (D.K + D.K)) * (D.N * D.K)) = r := by
    rw [← hmat H, List.drop_left]
  have dropV (e : Col D.K → Rg D) (r : List Bool) :
      (((vecE D (Col D.K)).enc e) ++ r).drop ((D.K + D.K) * (D.N * D.K)) = r := by
    rw [← hvec e, List.drop_left]
  rw [run_hBlkP D.K_pos D.N_pos S h.scratch h.hK h.hN h.hNK h.h11 h.h12 h.h13
    h.h14 h.h15 (by rw [hs, length_wd]) (by rw [h1, length_wd])]
  simp only [hs, h1, hg, hj₁, hj₂, hH, he, dropM, dropV, hRow_helper]

end AdvancedEncryption.ExpLUT.Prog.EncW
