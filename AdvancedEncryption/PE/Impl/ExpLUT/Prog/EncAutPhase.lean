import PE.Impl.ExpLUT.Prog.EncDigitCodec

/-! # The complete automorphism-encryption block -/

namespace AdvancedEncryption.ExpLUT.Prog.EncW

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo
  SigabaNeo.Lattices.Algo.NegaG SigabaNeo.Tape SigabaNeo.Tape.Prog Matrix

variable (D : Dims)

/-- The helper row recomputed by the automorphism block. -/
noncomputable def helperRow (s : Rg D) (j : ℕ)
    (H : Fin 2 → Col D.K → Rg D) (e : Col D.K → Rg D) : Col D.K → Rg D :=
  sec s ᵥ* H - sec ((setting D).E.σ ((setting D).idx j) s) ᵥ* GD D + e

/-- The pure execution result of the whole automorphism block has the scheme's codec. -/
theorem autOut_encoded (s : Rg D) (j₁ j₂ : ℕ)
    (H₁ H₂ : Fin 2 → Col D.K → Rg D) (e₁ e₂ : Col D.K → Rg D)
    (A : Dig D.K → Fin 2 → Col D.K → Rg D) (E : Dig D.K → Col D.K → Rg D)
    (z2 z4 nE out restH restEh restA restE : List Bool)
    (hz2 : z2.length = (D.K + D.K) * (D.N * D.K))
    (hz4 : z4.length = (D.K + D.K + (D.K + D.K)) * (D.N * D.K))
    (hcount : nE.length = D.K + D.K + (D.K + D.K))
    (hout : (D.K + D.K + (D.K + D.K)) *
      (D.K * ((D.K + D.K) * (D.N * D.K))) ≤ out.length) :
    autOut D.N D.K (gD D) j₁ j₂ (wd D s) (wd D 1)
      ((matE D (Fin 2) (Col D.K)).enc H₁ ++ ((matE D (Fin 2) (Col D.K)).enc H₂ ++ restH))
      ((vecE D (Col D.K)).enc e₁ ++ ((vecE D (Col D.K)).enc e₂ ++ restEh))
      z2 z4 nE out
      ((FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K))).enc A ++ restA)
      ((FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K))).enc E ++ restE) =
      ((out ++ (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K))).enc
        (digitRows D (autTW D.N D.K (gD D) j₁ (wd D s))
          (gcAut (setting D) ((setting D).idx j₁) H₂ (helperRow D s j₂ H₂ e₂)) A E)).drop
            ((D.K + D.K + (D.K + D.K)) * (D.K * ((D.K + D.K) * (D.N * D.K)))),
        restH, restEh, restA, restE) := by
  have dropM (H : Fin 2 → Col D.K → Rg D) (r : List Bool) :
      ((matE D (Fin 2) (Col D.K)).enc H ++ r).drop
        ((D.K + D.K + (D.K + D.K)) * (D.N * D.K)) = r := by
    have hl := (matE D (Fin 2) (Col D.K)).length H
    have hl' : ((matE D (Fin 2) (Col D.K)).enc H).length =
        (D.K + D.K + (D.K + D.K)) * (D.N * D.K) := by
      rw [hl, len_fin, length_col]; ring
    rw [← hl', List.drop_left]
  have dropV (e : Col D.K → Rg D) (r : List Bool) :
      ((vecE D (Col D.K)).enc e ++ r).drop ((D.K + D.K) * (D.N * D.K)) = r := by
    have hl : ((vecE D (Col D.K)).enc e).length = (D.K + D.K) * (D.N * D.K) := by
      rw [length_vecE', length_col]
    rw [← hl, List.drop_left]
  have hh : (z2 ++ hRow D.N D.K (wd D s) (autTW D.N D.K (gD D) j₂ (wd D s))
      (wd D 1) ((matE D (Fin 2) (Col D.K)).enc H₂ ++ restH)
      ((vecE D (Col D.K)).enc e₂ ++ restEh)).drop ((D.K + D.K) * (D.N * D.K)) =
      (vecE D (Col D.K)).enc (helperRow D s j₂ H₂ e₂) := by
    rw [hRow_helper D H₂ e₂ s j₂ restH restEh, ← hz2, List.drop_left]; rfl
  have hg := gcSteps_scheme D j₁ H₂ (helperRow D s j₂ H₂ e₂) z4 restH []
    (by rw [hz4])
  simp only [List.append_nil] at hg
  rw [← hz4, List.drop_left] at hg
  have hd := deSteps_encoded D (length_autTW (g := gD D) D.N_pos (length_wd D s) j₁)
    (gcAut (setting D) ((setting D).idx j₁) H₂ (helperRow D s j₂ H₂ e₂)) A E
    out [] restA restE hout
  simp only [List.append_nil] at hd
  dsimp only [autOut]
  simp only [dropM, dropV, hh, hg, hcount, hd]

/-- The actual automorphism secret word decodes to the scheme's transformed secret. -/
theorem digitRows_autTW (s : Rg D) (j : ℕ) (C : Fin 2 → Col D.K → Rg D)
    (A : Dig D.K → Fin 2 → Col D.K → Rg D) (E : Dig D.K → Col D.K → Rg D) :
    digitRows D (autTW D.N D.K (gD D) j (wd D s)) C A E = fun d ↦
      sec ((setting D).E.σ ((setting D).idx j) s) ᵥ* A d -
        (digits (setting D) C d • sec ((setting D).E.σ ((setting D).idx j) s)) ᵥ* GD D + E d := by
  funext d
  unfold digitRows autTW
  rw [decRM_autIt D (length_wd D s), decRM_wd]

/-- Templates and blank scratch for one complete automorphism block. -/
structure AutBlockOK (S : Store 85) : Prop where
  scratch : ∀ i : Fin 85, 20 ≤ i.val → S i = []
  hK : (S 10).length = D.K
  hN : (S 11).length = D.N
  hNK : (S 12).length = D.N * D.K
  h13 : (S 13).length = D.K + D.K
  hK1 : (S 14).length = D.K - 1
  h15 : (S 15).length = (D.K + D.K) * (D.N * D.K)
  h16 : (S 16).length = (D.K + D.K) * (D.N * D.K)
  h17 : (S 17).length = (D.K + D.K + (D.K + D.K)) * (D.N * D.K)
  h18 : (S 18).length = 1
  h19 : (S 19).length = D.K + D.K + (D.K + D.K)

/-- The full executable automorphism block, from scheme input codecs to its ciphertext rows. -/
theorem run_autBlkP_encoded (S : Store 85) (h : AutBlockOK D S) (s : Rg D) (j₁ j₂ : ℕ)
    (H₁ H₂ : Fin 2 → Col D.K → Rg D) (e₁ e₂ : Col D.K → Rg D)
    (A : Dig D.K → Fin 2 → Col D.K → Rg D) (E : Dig D.K → Col D.K → Rg D)
    (restH restEh restA restE : List Bool)
    (hs : S 1 = wd D s) (h1 : S 9 = wd D 1) (hg : (S 6).length = gD D)
    (hj₁ : (S 7).length = j₁) (hj₂ : (S 8).length = j₂)
    (hH : S 2 = (matE D (Fin 2) (Col D.K)).enc H₁ ++
      ((matE D (Fin 2) (Col D.K)).enc H₂ ++ restH))
    (hEh : S 3 = (vecE D (Col D.K)).enc e₁ ++ ((vecE D (Col D.K)).enc e₂ ++ restEh))
    (hA : S 4 = (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K))).enc A ++ restA)
    (hE : S 5 = (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K))).enc E ++ restE)
    (hout : (D.K + D.K + (D.K + D.K)) *
      (D.K * ((D.K + D.K) * (D.N * D.K))) ≤ (S 0).length) :
    autBlkP.run S = Function.update (Function.update (Function.update (Function.update
      (Function.update S 0
        ((S 0 ++ (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K))).enc
          (digitRows D (autTW D.N D.K (gD D) j₁ (wd D s))
            (gcAut (setting D) ((setting D).idx j₁) H₂ (helperRow D s j₂ H₂ e₂)) A E)).drop
              ((D.K + D.K + (D.K + D.K)) * (D.K * ((D.K + D.K) * (D.N * D.K))))))
        2 restH) 3 restEh) 4 restA) 5 restE := by
  rw [run_autBlkP D.K_pos D.N_pos S h.scratch h.hK h.hN h.hNK h.h13 h.hK1
    h.h15 h.h16 h.h17 h.h18 (by rw [hs, length_wd]) (by rw [h1, length_wd])]
  rw [hs, h1, hg, hj₁, hj₂, hH, hEh, hA, hE,
    autOut_encoded D s j₁ j₂ H₁ H₂ e₁ e₂ A E (S 15) (S 17) (S 19) (S 0)
      restH restEh restA restE h.h15 h.h17 h.h19 hout]

end AdvancedEncryption.ExpLUT.Prog.EncW
