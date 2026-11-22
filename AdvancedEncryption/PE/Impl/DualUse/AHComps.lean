import PE.Impl.DualUse.ReductionSteps
import PE.Impl.DualUse.AHAssembly

/-!
# Attribute hiding from the component programs

The component programs of the three reductions are bundled (`Bundle3`, `Bundle5`, `BundleI`):
the programs serving the challenger of the step at `R` scratch tapes, their length bounds, the
answer bound `L` and the facts the generic handlers need. With the three bundles, the hardness of
the three decision problems at `kb` bits and `64 · 2^(2λ) · C ≤ 2^kb` for `C` the largest of the
three constants `compConst`, the implementation has attribute hiding
(`attributeHiding_of_comps`, from `attributeHiding_of_reductions` and `reduces*_of_comps`).
-/

namespace AdvancedEncryption.DualUse

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib
  Cslib.Probability SigabaNeo.Tape
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow AdvancedEncryption.PE.Generic
open AdvancedEncryption.DualUse.Prog
open scoped ENNReal NNReal

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- The components of a reduction whose challenger is `spPack · viewI sdI` on instances `Inst`
encoded by `ienc` behind a `true`, with the setup `setupI`. -/
structure Bundle {Inst Sec : Type} {nI : ℕ} (ienc : FixedEnc Inst nI)
    (setupI : Date → PMF Sec) (viewI : Inst → Sec → PK hk c × CT hk c)
    (sdI : Inst → Sec → SimData hk c) where
  R : ℕ
  nS : ℕ
  sig : FixedEnc (Inst × Sec) nS
  st : dateUniverse.Attr → PMF (Inst × Sec)
  inst : List Bool → Inst
  IW : List Bool → Prop
  Ok : Inst × Sec → Prop
  cs : Comps R (dateCodes sig) (spPack st viewI sdI) (setupPack inst fun _ => setupI) IW Ok
  W : ℕ
  cb : CompBoundsP cs c.L W
  L : ℕ
  hpubL : ∀ σ, Ok σ → ((spPack st viewI sdI).pub σ).length ≤ L
  hkeyL : ∀ σ C, Ok σ → C.length ≤ c.L →
    ∀ sk ∈ ((spPack st viewI sdI).key σ C).support, sk.length ≤ L
  hchalL : ∀ σ μ, Ok σ → ∀ ct ∈ ((spPack st viewI sdI).chal σ μ).support, ct.length ≤ L
  hinv : ∀ i, inst (true :: ienc.enc i) = i
  hIW : ∀ i, IW (true :: ienc.enc i) ∧ (true :: ienc.enc i).length ≤ W

variable {hk c}

/-- The constant of a bundle with the decoder `P`. -/
noncomputable def Bundle.const {Inst Sec : Type} {nI : ℕ} {ienc : FixedEnc Inst nI}
    {setupI : Date → PMF Sec} {viewI : Inst → Sec → PK hk c × CT hk c}
    {sdI : Inst → Sec → SimData hk c} (B : Bundle hk c ienc setupI viewI sdI) (P : Machine) : ℕ :=
  compConst B.cs B.cb P B.L

variable [NeZero c.d]

/-- **Attribute hiding from the component programs of the three reductions.** -/
theorem attributeHiding_of_comps
    (hdec : ∀ u, gadgetMap (S := Sdw (N := N) hk) (c.dec u) = u) (hcov : RealCovered hk c)
    (hL : dateBound ≤ c.L) (hscov : SimCovered hk c)
    {ε : ℝ≥0∞}
    (hflood : ∀ rest ∈ (lawRestC hk c).support, ∀ w : JC (Sdw (N := N) hk) → (Fin c.d → Bool),
      CloseTo ((lawEc hk c).map fun e j => e j + rest.2.1 * wMat w j) (lawEc hk c) ε)
    (hS : statTerm c hk ε ≠ ⊤)
    (hstat : 4 * (2 : ℝ) ^ params.secBits * (statTerm c hk ε).toReal ^ 2 ≤ 1)
    (err : SecretDist) (hχ : χR c = polyOf (N := N) (ModuleLWE.coeffLaw (2 ^ K) err))
    (B3 : Bundle hk c (inst3Enc (N := N) (K := K) (k := k)) (setup3 hk c) (view3 hk c) (sd3 hk c))
    (B5 : Bundle hk c (inst5Enc (N := N) (K := K) (k := k) c.d) (setup5 hk c) (view5 hk c)
      (sd5 hk c))
    (BI : Bundle hk c (inst3Enc (N := N) (K := K) (k := k)) (setupI hk c) (viewI hk c) (sdI hk c))
    (kb : ℕ) (C : ℝ) (hC : 0 < C)
    (hC3 : (B3.const (dec3M N K k) : ℝ) ≤ C) (hC5 : (B5.const (dec5M N K k c.d) : ℝ) ≤ C)
    (hCI : (BI.const (dec3M N K k) : ℝ) ≤ C)
    (hk64 : 64 * ((2 : ℝ) ^ params.secBits) ^ 2 * C ≤ (2 : ℝ) ^ kb)
    (hard3 : (Problem.decision (ModuleLWE.realLaw (params3 N (2 ^ K) k err).toModule)
      (ModuleLWE.idealLaw (params3 N (2 ^ K) k err).toModule)).HardAt kb)
    (hard5 : (Problem.decision (ModuleLWE.realLaw (params5 N (2 ^ K) k (Fin c.d) err).toModule)
      (ModuleLWE.idealLaw (params5 N (2 ^ K) k (Fin c.d) err).toModule)).HardAt kb) :
    AttributeHiding dateUniverse params (impl hk c) :=
  attributeHiding_of_reductions hdec hcov hflood hS hstat _ _ _ _ _ _ kb C hC hk64 hard3 hard5 hard3
    fun A D _ =>
      ⟨reduces3_of_comps B3.cs B3.cb B3.L B3.hpubL B3.hkeyL B3.hchalL B3.hinv B3.hIW err hχ hdec
          hL hscov C hC3 A D,
        reduces5_of_comps B5.cs B5.cb B5.L B5.hpubL B5.hkeyL B5.hchalL B5.hinv B5.hIW err hχ hdec
          hL hscov C hC5 A D,
        reducesI_of_comps BI.cs BI.cb BI.L BI.hpubL BI.hkeyL BI.hchalL BI.hinv BI.hIW err hχ hdec
          hL hscov C hCI A D⟩

/-- **Attribute hiding from the component programs and the registry's decision Ring-LWE** at
the parameters of hybrids 3 and 5 (`params3`, `params5`) with `kb` bits: the premises
`(RingLWE.decision, params3 …, kb)` and `(RingLWE.decision, params5 …, kb)`. -/
theorem attributeHiding_of_comps_rlwe
    (hdec : ∀ u, gadgetMap (S := Sdw (N := N) hk) (c.dec u) = u) (hcov : RealCovered hk c)
    (hL : dateBound ≤ c.L) (hscov : SimCovered hk c)
    {ε : ℝ≥0∞}
    (hflood : ∀ rest ∈ (lawRestC hk c).support, ∀ w : JC (Sdw (N := N) hk) → (Fin c.d → Bool),
      CloseTo ((lawEc hk c).map fun e j => e j + rest.2.1 * wMat w j) (lawEc hk c) ε)
    (hS : statTerm c hk ε ≠ ⊤)
    (hstat : 4 * (2 : ℝ) ^ params.secBits * (statTerm c hk ε).toReal ^ 2 ≤ 1)
    (err : SecretDist) (hχ : χR c = polyOf (N := N) (ModuleLWE.coeffLaw (2 ^ K) err))
    (B3 : Bundle hk c (inst3Enc (N := N) (K := K) (k := k)) (setup3 hk c) (view3 hk c) (sd3 hk c))
    (B5 : Bundle hk c (inst5Enc (N := N) (K := K) (k := k) c.d) (setup5 hk c) (view5 hk c)
      (sd5 hk c))
    (BI : Bundle hk c (inst3Enc (N := N) (K := K) (k := k)) (setupI hk c) (viewI hk c) (sdI hk c))
    (kb : ℕ) (C : ℝ) (hC : 0 < C)
    (hC3 : (B3.const (dec3M N K k) : ℝ) ≤ C) (hC5 : (B5.const (dec5M N K k c.d) : ℝ) ≤ C)
    (hCI : (BI.const (dec3M N K k) : ℝ) ≤ C)
    (hk64 : 64 * ((2 : ℝ) ^ params.secBits) ^ 2 * C ≤ (2 : ℝ) ^ kb)
    (hard3 : RingLWE.decision.HardAt (params3 N (2 ^ K) k err) kb)
    (hard5 : RingLWE.decision.HardAt (params5 N (2 ^ K) k (Fin c.d) err) kb) :
    AttributeHiding dateUniverse params (impl hk c) :=
  attributeHiding_of_comps hdec hcov hL hscov hflood hS hstat err hχ B3 B5 BI kb C hC hC3 hC5 hCI
    hk64 hard3 hard5

end AdvancedEncryption.DualUse
