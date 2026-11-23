import PE.Impl.DualUse.ReductionComps
import PE.Impl.DualUse.SimGame3
import PE.Impl.DualUse.SimGame5
import PE.Impl.DualUse.Prog.Decode
import PE.Impl.DualUse.Prog.DecodeLaw

/-!
# The three reductions from their components

For each Ring-LWE step of the hybrid chain (hybrid 3, hybrid 5, the ideal side), component
programs serving the challenger of the step (`spPack` of `view3`/`sd3`, `view5`/`sd5`,
`viewI`/`sdI`, with the setups `setup3`, `setup5`, `setupI`) and the decoder `dec3M`/`dec5M` give a
reduction (`Reduces`) between the real and the ideal words of the decision problem
(`ModuleLWE.realLaw`/`idealLaw` of `params3`/`params5`), with the constant `compConst`:

* `reduces3_of_comps`, `reduces5_of_comps`, `reducesI_of_comps`.

The component programs read the instance from the state word `true :: enc i` (`hinv`); the
decoder writes this word (`run_dec3M`, `run_dec5M`), and the decoded instances have the laws of
`accOn` (`realLaw_map_inst3Of`, …), given that the error law of the parameters is `χR c` (`hχ`).
-/

namespace AdvancedEncryption.DualUse

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib
  Cslib.Probability SigabaNeo.Tape
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow AdvancedEncryption.PE.Generic
open AdvancedEncryption.DualUse.Prog

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k} [NeZero c.d]
variable {nS : ℕ}
set_option linter.unusedSectionVars false

/-- **The reduction of hybrid 3 from its components.** -/
theorem reduces3_of_comps {R : ℕ} {sig : FixedEnc (Inst3T N K k × Sec3 hk c) nS}
    {st : PUniv.Attr → PMF (Inst3T N K k × Sec3 hk c)} {inst : List Bool → Inst3T N K k}
    {IW : List Bool → Prop} {Ok : Inst3T N K k × Sec3 hk c → Prop}
    (cs : Comps R (puCodes sig) (spPack st (view3 hk c) (sd3 hk c))
      (setupPack inst fun _ => setup3 hk c) IW Ok) {W : ℕ}
    (cb : CompBoundsP cs c.L W) (L : ℕ)
    (hpubL : ∀ σ, Ok σ → ((spPack st (view3 hk c) (sd3 hk c)).pub σ).length ≤ L)
    (hkeyL : ∀ σ C, Ok σ → C.length ≤ c.L →
      ∀ sk ∈ ((spPack st (view3 hk c) (sd3 hk c)).key σ C).support, sk.length ≤ L)
    (hchalL : ∀ σ μ, Ok σ → ∀ ct ∈ ((spPack st (view3 hk c) (sd3 hk c)).chal σ μ).support,
      ct.length ≤ L)
    (hinv : ∀ i, inst (true :: (inst3Enc (N := N) (K := K) (k := k)).enc i) = i)
    (hIW : ∀ i, IW (true :: (inst3Enc (N := N) (K := K) (k := k)).enc i) ∧
      (true :: (inst3Enc (N := N) (K := K) (k := k)).enc i).length ≤ W)
    (err : SecretDist) (hχ : χR c = polyOf (N := N) (ModuleLWE.coeffLaw (2 ^ K) err))
    (hdec : ∀ u, gadgetMap (S := Sdw (N := N) hk) (c.dec u) = u)
    (hL : dateBound ≤ c.L) (hcov : SimCovered hk c)
    (C : ℝ) (hC : (compConst cs cb (dec3M N K k) L : ℝ) ≤ C) (A : Machine 3) (D : Machine) :
    Reduces (accOn A D (inst3Real (k := k) (χR c)) (F3 hk c)) (accOn A D inst3Unif (F3 hk c))
      (ModuleLWE.realLaw (params3 N (2 ^ K) k err).toModule)
      (ModuleLWE.idealLaw (params3 N (2 ^ K) k err).toModule) C (A.cost + D.cost) := by
  have hcomp : inst ∘ (fun w => true :: (inst3Enc (N := N) (K := K) (k := k)).enc (inst3Of w)) =
      inst3Of := funext fun w => hinv _
  refine reduces_of_comps cs cb (dec3M N K k) L hpubL hkeyL hchalL
    (fun w => true :: (inst3Enc (N := N) (K := K) (k := k)).enc (inst3Of w)) _ _ _ _
    (fun w hw => run_dec3M err w (Or.inl hw)) (fun w hw => run_dec3M err w (Or.inr hw))
    (fun w _ => ⟨(hIW _).1, (hIW _).2, by simp⟩) (fun w _ => ⟨(hIW _).1, (hIW _).2, by simp⟩)
    (by rw [hcomp, realLaw_map_inst3Of, hχ]) (by rw [hcomp, idealLaw_map_inst3Of])
    (F3 hk c) hdec hL hcov (fun x ab => F3_eq hk c x ab) (fun _ _ => rfl)
    (fun _ x σ hσ => setup3_x hk c x σ hσ) (fun ab x σ hσ => sd3_valid hk c ab x σ hσ) C hC A D

/-- **The reduction of hybrid 5 from its components.** -/
theorem reduces5_of_comps {R : ℕ}
    {sig : FixedEnc ((Pub (Fin c.d) (Rg N K) k × Pub (Fin c.d) (Rg N K) k) × Sec5 hk c) nS}
    {st : PUniv.Attr → PMF ((Pub (Fin c.d) (Rg N K) k × Pub (Fin c.d) (Rg N K) k) ×
      Sec5 hk c)}
    {inst : List Bool → Pub (Fin c.d) (Rg N K) k × Pub (Fin c.d) (Rg N K) k}
    {IW : List Bool → Prop}
    {Ok : (Pub (Fin c.d) (Rg N K) k × Pub (Fin c.d) (Rg N K) k) × Sec5 hk c → Prop}
    (cs : Comps R (puCodes sig) (spPack st (view5 hk c) (sd5 hk c))
      (setupPack inst fun _ => setup5 hk c) IW Ok) {W : ℕ}
    (cb : CompBoundsP cs c.L W) (L : ℕ)
    (hpubL : ∀ σ, Ok σ → ((spPack st (view5 hk c) (sd5 hk c)).pub σ).length ≤ L)
    (hkeyL : ∀ σ C, Ok σ → C.length ≤ c.L →
      ∀ sk ∈ ((spPack st (view5 hk c) (sd5 hk c)).key σ C).support, sk.length ≤ L)
    (hchalL : ∀ σ μ, Ok σ → ∀ ct ∈ ((spPack st (view5 hk c) (sd5 hk c)).chal σ μ).support,
      ct.length ≤ L)
    (hinv : ∀ i, inst (true :: (inst5Enc (N := N) (K := K) (k := k) c.d).enc i) = i)
    (hIW : ∀ i, IW (true :: (inst5Enc (N := N) (K := K) (k := k) c.d).enc i) ∧
      (true :: (inst5Enc (N := N) (K := K) (k := k) c.d).enc i).length ≤ W)
    (err : SecretDist) (hχ : χR c = polyOf (N := N) (ModuleLWE.coeffLaw (2 ^ K) err))
    (hdec : ∀ u, gadgetMap (S := Sdw (N := N) hk) (c.dec u) = u)
    (hL : dateBound ≤ c.L) (hcov : SimCovered hk c)
    (C : ℝ) (hC : (compConst cs cb (dec5M N K k c.d) L : ℝ) ≤ C) (A : Machine 3) (D : Machine) :
    Reduces (accOn A D (nfReal (χR c)) (F5 hk c)) (accOn A D nfUnif (F5 hk c))
      (ModuleLWE.realLaw (params5 N (2 ^ K) k (Fin c.d) err).toModule)
      (ModuleLWE.idealLaw (params5 N (2 ^ K) k (Fin c.d) err).toModule) C (A.cost + D.cost) := by
  have hcomp : inst ∘
      (fun w => true :: (inst5Enc (N := N) (K := K) (k := k) c.d).enc (inst5Of c.d w)) =
      inst5Of c.d := funext fun w => hinv _
  refine reduces_of_comps cs cb (dec5M N K k c.d) L hpubL hkeyL hchalL
    (fun w => true :: (inst5Enc (N := N) (K := K) (k := k) c.d).enc (inst5Of c.d w)) _ _ _ _
    (fun w hw => run_dec5M c.d err w (Or.inl hw)) (fun w hw => run_dec5M c.d err w (Or.inr hw))
    (fun w _ => ⟨(hIW _).1, (hIW _).2, by simp⟩) (fun w _ => ⟨(hIW _).1, (hIW _).2, by simp⟩)
    (by rw [hcomp, realLaw_map_inst5Of, hχ]) (by rw [hcomp, idealLaw_map_inst5Of])
    (F5 hk c) hdec hL hcov (fun x i => F5_eq hk c x i) (fun _ _ => rfl)
    (fun _ x σ hσ => setup5_x hk c x σ hσ) (fun i x σ hσ => sd5_valid hk c i x σ hσ) C hC A D

/-- **The reduction of the ideal side from its components.** -/
theorem reducesI_of_comps {R : ℕ} {sig : FixedEnc (Inst3T N K k × SecI hk c) nS}
    {st : PUniv.Attr → PMF (Inst3T N K k × SecI hk c)} {inst : List Bool → Inst3T N K k}
    {IW : List Bool → Prop} {Ok : Inst3T N K k × SecI hk c → Prop}
    (cs : Comps R (puCodes sig) (spPack st (viewI hk c) (sdI hk c))
      (setupPack inst fun _ => setupI hk c) IW Ok) {W : ℕ}
    (cb : CompBoundsP cs c.L W) (L : ℕ)
    (hpubL : ∀ σ, Ok σ → ((spPack st (viewI hk c) (sdI hk c)).pub σ).length ≤ L)
    (hkeyL : ∀ σ C, Ok σ → C.length ≤ c.L →
      ∀ sk ∈ ((spPack st (viewI hk c) (sdI hk c)).key σ C).support, sk.length ≤ L)
    (hchalL : ∀ σ μ, Ok σ → ∀ ct ∈ ((spPack st (viewI hk c) (sdI hk c)).chal σ μ).support,
      ct.length ≤ L)
    (hinv : ∀ i, inst (true :: (inst3Enc (N := N) (K := K) (k := k)).enc i) = i)
    (hIW : ∀ i, IW (true :: (inst3Enc (N := N) (K := K) (k := k)).enc i) ∧
      (true :: (inst3Enc (N := N) (K := K) (k := k)).enc i).length ≤ W)
    (err : SecretDist) (hχ : χR c = polyOf (N := N) (ModuleLWE.coeffLaw (2 ^ K) err))
    (hdec : ∀ u, gadgetMap (S := Sdw (N := N) hk) (c.dec u) = u)
    (hL : dateBound ≤ c.L) (hcov : SimCovered hk c)
    (C : ℝ) (hC : (compConst cs cb (dec3M N K k) L : ℝ) ≤ C) (A : Machine 3) (D : Machine) :
    Reduces (accOn A D (inst3Real (k := k) (χR c)) (FI hk c)) (accOn A D inst3Unif (FI hk c))
      (ModuleLWE.realLaw (params3 N (2 ^ K) k err).toModule)
      (ModuleLWE.idealLaw (params3 N (2 ^ K) k err).toModule) C (A.cost + D.cost) := by
  have hcomp : inst ∘ (fun w => true :: (inst3Enc (N := N) (K := K) (k := k)).enc (inst3Of w)) =
      inst3Of := funext fun w => hinv _
  refine reduces_of_comps cs cb (dec3M N K k) L hpubL hkeyL hchalL
    (fun w => true :: (inst3Enc (N := N) (K := K) (k := k)).enc (inst3Of w)) _ _ _ _
    (fun w hw => run_dec3M err w (Or.inl hw)) (fun w hw => run_dec3M err w (Or.inr hw))
    (fun w _ => ⟨(hIW _).1, (hIW _).2, by simp⟩) (fun w _ => ⟨(hIW _).1, (hIW _).2, by simp⟩)
    (by rw [hcomp, realLaw_map_inst3Of, hχ]) (by rw [hcomp, idealLaw_map_inst3Of])
    (FI hk c) hdec hL hcov (fun x ab => FI_eq hk c x ab) (fun _ _ => rfl)
    (fun _ x σ hσ => setupI_x hk c x σ hσ) (fun ab x σ hσ => sdI_valid hk c ab x σ hσ) C hC A D

end AdvancedEncryption.DualUse
