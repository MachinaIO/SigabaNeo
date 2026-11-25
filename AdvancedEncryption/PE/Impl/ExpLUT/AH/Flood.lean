import PE.Impl.ExpLUT.AH.Final
import PE.Impl.ExpLUT.FloodBound
/-!
# The flooding hypothesis at the concrete parameters (package G3)

P's flooding law `χfl` is the library's `floodRing (2^24) q (2^eFl)` (`χfl_eq`, by definition), so
`hflood_floodRing` (`FloodBound`) applies at `Dc` with the CBD(16) error law `χc` (`B_χ = 16`):

* `hflood_Dc`: **the hypothesis `hflood` of `attributeHiding_Dc`** at
  `εflDc = floodCount · N (m̄ · 16) / 2^eFl`;
* `εflDc_le`: `εflDc ≤ 2^{−249}` (`floodCount ≤ lhlCols`, P's `flood_budget`), hence
  `εflDc ≤ 2^{−148}` (`εflDc_le_148`);
* `attributeHiding_Dc'`, `attributeHiding_Dc_registry'`: package G's results without the flooding
  hypothesis.
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Lattices Cslib Cslib.Probability AdvancedEncryption.PE
open AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.ExpLUT.Params
open scoped ENNReal

/-- **P's flooding law is the library's `floodRing`.** -/
theorem χfl_eq : χfl = floodRing (2 ^ en) qc (2 ^ eFl) := rfl

/-- `a · (x / W) ≤ 2^{−k}` from `a x 2^k ≤ W` (generic, so that no power is evaluated). -/
theorem natCast_mul_div_le_inv_pow {a x W k : ℕ} (h : a * x * 2 ^ k ≤ W) :
    (a : ℝ≥0∞) * ((x : ℝ≥0∞) / W) ≤ ((2 : ℝ≥0∞) ^ k)⁻¹ := by
  rw [← mul_div_assoc]
  refine ENNReal.div_le_of_le_mul ?_
  have h2 : (2 : ℝ≥0∞) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
  have h2' : (2 : ℝ≥0∞) ^ k ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have hc : ((a * x * 2 ^ k : ℕ) : ℝ≥0∞) ≤ W := by exact_mod_cast h
  push_cast at hc
  calc (a : ℝ≥0∞) * x = (a * x * 2 ^ k) * ((2 : ℝ≥0∞) ^ k)⁻¹ := by
        rw [mul_assoc _ ((2 : ℝ≥0∞) ^ k), ENNReal.mul_inv_cancel h2 h2', mul_one]
    _ ≤ W * ((2 : ℝ≥0∞) ^ k)⁻¹ := mul_le_mul_left hc _
    _ = ((2 : ℝ≥0∞) ^ k)⁻¹ * W := mul_comm _ _

theorem floodCount_gen (K : ℕ) :
    22 * (2 * (2 * K) * K) * (2 * K) + 16 * (2 * K) + 16 * (2 * (2 * K) * K) * (2 * K) + 2 * K ≤
      2 * K + 16 * (2 * K) + (16 + 22) * (8 * K ^ 3) + 1 := by
  ring_nf; omega

/-- The flooded ring elements at `Dc` are fewer than P's `lhlCols`. -/
theorem floodCount_Dc_le : floodCount (setting Dc) Pos ≤ lhlCols := by
  rw [floodCount_eq]
  have hb : (setting Dc).b = 22 := rfl
  have hτ : (setting Dc).τ = Kc := rfl
  have hp : Fintype.card Pos = 16 := by rw [Fintype.card_fin]; rfl
  rw [hb, hτ, hp]
  exact floodCount_gen Kc

/-- **The flooding distance at `Dc`.** -/
noncomputable def εflDc : ℝ≥0∞ :=
  floodCount (setting Dc) Pos *
    (((Dc.N * (Fintype.card (Wb Dc) * Bχ) : ℕ) : ℝ≥0∞) / ((2 ^ eFl : ℕ) : ℝ≥0∞))

/-- The budget comparison, generic in the sizes. -/
theorem flood_budget_gen {f l m K x B c W : ℕ} (hc : f ≤ l) (hx : 0 < x)
    (h : l * x * ((m + K) * x * B) * c ≤ W) : f * (x * (m * B)) * c ≤ W := by
  refine le_trans (Nat.mul_le_mul_right _ ?_) h
  have hm : m ≤ (m + K) * x := (Nat.le_add_right _ _).trans (Nat.le_mul_of_pos_right _ hx)
  rw [mul_assoc l]
  exact Nat.mul_le_mul hc (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hm))

theorem εflDc_eq : εflDc = floodCount (setting Dc) Pos *
    (((2 ^ en * (mbar * Bχ) : ℕ) : ℝ≥0∞) / ((2 ^ eFl : ℕ) : ℝ≥0∞)) := by
  have hX : Dc.N * (Fintype.card (Wb Dc) * Bχ) = 2 ^ en * (mbar * Bχ) := by
    rw [Fintype.card_fin]; rfl
  exact congrArg (fun X : ℕ => (floodCount (setting Dc) Pos : ℝ≥0∞) *
    ((X : ℝ≥0∞) / ((2 ^ eFl : ℕ) : ℝ≥0∞))) hX

theorem εflDc_le : εflDc ≤ ((2 : ℝ≥0∞) ^ 249)⁻¹ := by
  rw [εflDc_eq]
  exact natCast_mul_div_le_inv_pow
    (flood_budget_gen floodCount_Dc_le (Nat.two_pow_pos en) flood_budget)

theorem εflDc_le_148 : εflDc ≤ ((2 : ℝ≥0∞) ^ 148)⁻¹ :=
  εflDc_le.trans (ENNReal.inv_le_inv.mpr (pow_le_pow_right₀ (by norm_num) (by norm_num)))

/-- **The flooding hypothesis of `attributeHiding_Dc`** at the concrete parameters. -/
theorem hflood_Dc :
    ∀ eb ∈ (iidLaw χc (BCol (Wb Dc) (setting Dc).τ)).support,
      ∀ zr : PrI (setting Dc) Pos → Wb Dc → Bool,
        CloseTo ((floodLaw (setting Dc) Pos χfl).map (· + floodShift eb zr))
          (floodLaw (setting Dc) Pos χfl) εflDc :=
  hflood_floodRing (S := setting Dc) NDc NDc_nrm (2 ^ eFl) χc_short

/-- **Attribute hiding at the concrete parameters**, without the flooding hypothesis. -/
theorem attributeHiding_Dc' {impl : Impl sig} {kb : KeyBoxes Dc} {L : ℕ}
    (hI : ImplSpec Dc kb L impl χc χc χfl) (hkb : KbCover kb coverBound) (kb' : ℕ) (C : ℝ)
    (hC : 0 < C) (hkb' : 64 * ((2 : ℝ) ^ 128) ^ 2 * C ≤ (2 : ℝ) ^ kb')
    (hard : CircularRingLWE.decision.HardAt (circParamsD Dc) kb')
    (hred : ∀ (A : Machine 3) (Dm : Machine), Admissible (univ w8) params impl (simMachine Dc) A →
      RedMachine Dc kb L (circParamsD Dc) impl χc χc χfl C A Dm) :
    AttributeHiding (univ w8) params impl :=
  attributeHiding_Dc hI hkb hflood_Dc εflDc_le_148 kb' C hC hkb' hard hred

/-- **Attribute hiding from the registered assumption**, without the flooding hypothesis. -/
theorem attributeHiding_Dc_registry' (hR : CircularRingLWE.decision.Holds) {impl : Impl sig}
    {kb : KeyBoxes Dc} {L : ℕ} (hI : ImplSpec Dc kb L impl χc χc χfl) (hkb : KbCover kb coverBound)
    (C : ℝ) (hC : 0 < C) (hkb' : 64 * ((2 : ℝ) ^ 128) ^ 2 * C ≤ (2 : ℝ) ^ 1155)
    (hred : ∀ (A : Machine 3) (Dm : Machine), Admissible (univ w8) params impl (simMachine Dc) A →
      RedMachine Dc kb L (circParamsD Dc) impl χc χc χfl C A Dm) :
    AttributeHiding (univ w8) params impl :=
  attributeHiding_Dc_registry hR hI hkb hflood_Dc εflDc_le_148 C hC hkb' hred

end AdvancedEncryption.ExpLUT.Prog
