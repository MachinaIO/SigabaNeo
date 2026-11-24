import PE.Impl.ExpLUT.AH.Stat

/-!
# Attribute hiding of the ExpLUT implementation at the concrete parameters (package G)

* `circParamsD D`: the circular Ring-LWE parameters of the reduction: ring degree `N`, modulus
  `q = 2^K − 1`, CBD(16) secret and errors, `m_B + 1 + τ |J|` plain samples (`mCirc`: the columns
  of `B`, `d`, the second gadget halves of the helpers), the automorphism indices
  `idx (je k) = g^{je k}` of the helpers (`jList`, in the order `jhE`, `|J| = 2b`), `τ = K`;
  `strength_Dc`: **`1155 ≤ CircularRingLWE.decision.H (circParamsD Dc)`** (package B, `m ≤ 2^50`).
* `attributeHiding_Dc`: **`AttributeHiding (univ w8) params impl`** for every implementation whose
  machines meet the specifications at `Dc` (`ImplSpec`, laws `χc`, `χc`, `χfl` of package P), with
  key boxes covering shifts up to `2^18500` (`KbCover`), the flooding step within `ε_fl ≤ 2^{−148}`
  (`hflood`), from `CircularRingLWE.decision.HardAt (circParamsD Dc) kb'` with
  `64 · 2^256 · C ≤ 2^kb'`, given the reduction machines of cost `≤ C (cost A + cost D)²`
  (`RedMachine`).
* `attributeHiding_Dc_registry`: the same from the registered assumption
  (`CircularRingLWE.decision.Holds`) whenever `kb' ≤ 1155`, i.e. `log₂ C ≤ 893`.
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Lattices Cslib Cslib.Probability AdvancedEncryption.PE
open AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.ExpLUT.Params
open scoped ENNReal

/-- The helpers in the order of the key rows: `j ↦ (j / 2, j % 2)` (`finProdFinEquiv`). -/
def jhE (D : Dims) : Fin (D.b * 2) ≃ Jh D := finProdFinEquiv.symm

/-- The automorphism indices of the helpers, in the order of `jhE`. -/
noncomputable def jList (D : Dims) : List ℕ :=
  List.ofFn fun j : Fin (D.b * 2) => (setting D).idx (je D (jhE D j))

/-- The plain samples: the columns of `B` (`m̄ + K`), `d`, the second gadget halves of the helpers
(`K · 2b`). -/
def mCirc (D : Dims) : ℕ := D.mb + D.K + 1 + D.K * (D.b * 2)

/-- **The circular Ring-LWE parameters of the reduction.** -/
noncomputable def circParamsD (D : Dims) : CircularRingLWE.Params :=
  circParams D.N D.K (mCirc D) (by have := D.hK; omega) (jList D) D.K

theorem mCirc_gen {M K : ℕ} (hM : M + K ≤ 2 ^ 42) (hK : K ≤ 2 ^ 16) :
    M + K + 1 + K * (22 * 2) ≤ 2 ^ 50 := by
  have : K * (22 * 2) ≤ 2 ^ 16 * 44 := Nat.mul_le_mul_right _ hK
  omega

theorem mCirc_Dc_le : mCirc Dc ≤ 2 ^ 50 :=
  mCirc_gen mbar_le Kc_le

theorem circParamsD_Dc : circParamsD Dc =
    circParams (2 ^ 24) (2 ^ 16) (mCirc Dc) (by norm_num) (jList Dc) Kc := by
  unfold circParamsD
  have e : Dc.K = 2 ^ 16 := Kc_def
  have hN : Dc.N = 2 ^ 24 := rfl
  congr 1

/-- **The strength of circular Ring-LWE at the reduction's parameters**: `1155` bits. -/
theorem strength_Dc : 1155 ≤ CircularRingLWE.decision.H (circParamsD Dc) := by
  rw [circParamsD_Dc]
  exact circularRingLWE_decision_H_N24 (by unfold mCirc; omega) mCirc_Dc_le _ _

/-- **Attribute hiding at the concrete parameters**, from circular Ring-LWE, given the reduction
machines. -/
theorem attributeHiding_Dc {impl : Impl sig} {kb : KeyBoxes Dc} {L : ℕ}
    (hI : ImplSpec Dc kb L impl χc χc χfl) (hkb : KbCover kb coverBound) {εfl : ℝ≥0∞}
    (hflood : ∀ eb ∈ (iidLaw χc (BCol (Wb Dc) (setting Dc).τ)).support,
      ∀ zr : PrI (setting Dc) Pos → Wb Dc → Bool,
        CloseTo ((floodLaw (setting Dc) Pos χfl).map (· + floodShift eb zr))
          (floodLaw (setting Dc) Pos χfl) εfl)
    (hfl : εfl ≤ ((2 : ℝ≥0∞) ^ 148)⁻¹) (kb' : ℕ) (C : ℝ) (hC : 0 < C)
    (hkb' : 64 * ((2 : ℝ) ^ 128) ^ 2 * C ≤ (2 : ℝ) ^ kb')
    (hard : CircularRingLWE.decision.HardAt (circParamsD Dc) kb')
    (hred : ∀ (A : Machine 3) (Dm : Machine), Admissible (univ w8) params impl (simMachine Dc) A →
      RedMachine Dc kb L (circParamsD Dc) impl χc χc χfl C A Dm) :
    AttributeHiding (univ w8) params impl :=
  attributeHiding_of_reduction hI (realCovW_of hkb) (simCovW_of hkb) (le_of_eq Dc_b.symm)
    (simSpec Dc) hflood (statW_ne_top hfl) (hstat_Dc hfl) _ kb' C hC hkb' hard hred

/-- **Attribute hiding from the registered circular Ring-LWE assumption**, for reduction constants
`C` with `64 · 2^256 · C ≤ 2^1155`. -/
theorem attributeHiding_Dc_registry (hR : CircularRingLWE.decision.Holds) {impl : Impl sig}
    {kb : KeyBoxes Dc} {L : ℕ} (hI : ImplSpec Dc kb L impl χc χc χfl) (hkb : KbCover kb coverBound)
    {εfl : ℝ≥0∞}
    (hflood : ∀ eb ∈ (iidLaw χc (BCol (Wb Dc) (setting Dc).τ)).support,
      ∀ zr : PrI (setting Dc) Pos → Wb Dc → Bool,
        CloseTo ((floodLaw (setting Dc) Pos χfl).map (· + floodShift eb zr))
          (floodLaw (setting Dc) Pos χfl) εfl)
    (hfl : εfl ≤ ((2 : ℝ≥0∞) ^ 148)⁻¹) (C : ℝ) (hC : 0 < C)
    (hkb' : 64 * ((2 : ℝ) ^ 128) ^ 2 * C ≤ (2 : ℝ) ^ 1155)
    (hred : ∀ (A : Machine 3) (Dm : Machine), Admissible (univ w8) params impl (simMachine Dc) A →
      RedMachine Dc kb L (circParamsD Dc) impl χc χc χfl C A Dm) :
    AttributeHiding (univ w8) params impl :=
  attributeHiding_Dc hI hkb hflood hfl 1155 C hC hkb' (hR.hardAt strength_Dc) hred

end AdvancedEncryption.ExpLUT.Prog
