module

public import SigabaNeo.Lib.Lattices.Research.Wall1.KleinProcedure
public import CslibFrontier.Probability.PMF.Bool
public import CslibFrontier.Probability.PMF.Expect

/-! # The audit counterexample on the integer lattice (Part 140, Audit A1) -/

@[expose] public section

noncomputable section

namespace SigabaNeo.Wall1.ADRS

open Cslib.Probability.PMF
open scoped ENNReal

/-- An exact discrete Gaussian on 2ℤ+c, at the audit width s=2. -/
def auditCosetLaw (c : ℤ) : PMF ℤ :=
  ⟨fun x ↦ ENNReal.ofReal (cosetDraw 2 2 c x), CompleteLattice.summable.hasSum_iff.mpr (by
    have h := cosetDraw_hasSum (s := 2) (q := 2) (by norm_num) (by norm_num) c
    rw [← ENNReal.ofReal_tsum_of_nonneg (cosetDraw_nonneg (by norm_num) (by norm_num) c)
      h.summable, h.tsum_eq, ENNReal.ofReal_one])⟩

/-- The event that two independent inputs from that coset average to an even integer. -/
def auditPairHit (c : ℤ) : PMF Bool :=
  (auditCosetLaw c).bind fun x ↦ (auditCosetLaw c).map fun y ↦ decide ((x+y) % 4 = 0)

private theorem auditCosetLaw_support {c x : ℤ} (hx : x ≡ c [ZMOD 2]) :
    x ∈ (auditCosetLaw c).support := by
  apply (PMF.apply_pos_iff ..).mp
  change 0 < ENNReal.ofReal (cosetDraw 2 2 c x)
  simp only [ENNReal.ofReal_pos, cosetDraw, hx, ite_true]
  exact div_pos (gs_pos ..) (thetaQ_pos (by norm_num) (by norm_num) _)

theorem auditPairHit_pos (c : ℤ) : 0 < (auditPairHit c true).toReal := by
  apply ENNReal.toReal_pos _ (PMF.apply_ne_top _ _)
  apply (PMF.mem_support_iff ..).mp
  refine (PMF.mem_support_bind_iff ..).2 ⟨c, auditCosetLaw_support (Int.ModEq.refl _), ?_⟩
  refine (PMF.mem_support_map_iff ..).2 ⟨-c, auditCosetLaw_support ?_, by simp⟩
  exact Int.modEq_iff_dvd.mpr ⟨c, by ring⟩

/-- Independent hit indicators from one pair in each bin, combined by disjunction. -/
def pairHitOr (P Q : PMF Bool) : PMF Bool :=
  P.bind fun u ↦ Q.map (fun v ↦ u || v)

theorem pairHitOr_prob (P Q : PMF Bool) :
    (pairHitOr P Q true).toReal = 1 - (1-(P true).toReal)*(1-(Q true).toReal) := by
  simp only [pairHitOr, bind_apply_toReal, Fintype.sum_bool, Bool.false_or, Bool.true_or]
  change _ * ((Q.map (Function.const Bool true)) true).toReal + _ * ((Q.map id) true).toReal = _
  rw [PMF.map_id, PMF.map_const, PMF.pure_apply_self, ENNReal.toReal_one,
    toReal_false_eq_one_sub]
  ring

/-- The fair mixtures of bin counts used in the audit. The Boolean argument selects M or M'. -/
def auditCounts (together : Bool) : PMF (ℕ × ℕ) :=
  (uniformOfFintype Bool).map fun b ↦
    if together then (if b then (2,2) else (0,0)) else (if b then (0,2) else (2,0))

/-- Single-step observation for the four bin configurations in the support of the audit laws. -/
def auditStepHit (z : ℕ × ℕ) : PMF Bool :=
  if z.1 = 2 then
    if z.2 = 2 then pairHitOr (auditPairHit 0) (auditPairHit 1) else auditPairHit 0
  else if z.2 = 2 then auditPairHit 1 else PMF.pure false

/-- All input upper orthants are ordered, but the one-output even-coset orthant is reversed. -/
theorem audit_integer_counterexample :
    (∀ i j : ℕ,
      ((auditCounts false).map (fun z ↦ decide (i ≤ z.1 ∧ j ≤ z.2)) true).toReal ≤
      ((auditCounts true).map (fun z ↦ decide (i ≤ z.1 ∧ j ≤ z.2)) true).toReal) ∧
    (((auditCounts true).bind auditStepHit) true).toReal <
      (((auditCounts false).bind auditStepHit) true).toReal := by
  constructor
  · intro i j
    classical
    simp only [auditCounts, PMF.map_comp, toReal_uniformOfFintype_map_apply_true]
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
      by_cases hi₂ : i ≤ 2 <;> by_cases hj₂ : j ≤ 2 <;>
      norm_num [Finset.dens, Fintype.univ_bool, Function.comp_def, hi, hj, hi₂, hj₂,
        Finset.filter_insert, Finset.filter_singleton] at *
  · simp only [auditCounts, PMF.bind_map, toReal_uniformOfFintype_bind_apply, Fintype.card_bool,
      Nat.cast_ofNat, Fintype.expect_eq_sum_div_card, Fintype.sum_bool, Function.comp_def, auditStepHit]
    norm_num [PMF.pure_apply, pairHitOr_prob]
    nlinarith [mul_pos (auditPairHit_pos 0) (auditPairHit_pos 1)]

/-- Substitution of the audit's *rounded* single-pair probabilities. -/
theorem audit_rounded_hits :
    (1 - (1-(0.8536 : ℚ))*(1-0.5))/2 = 0.4634 ∧
      ((0.8536 : ℚ)+0.5)/2 = 0.6768 := by norm_num

end SigabaNeo.Wall1.ADRS

#print axioms SigabaNeo.Wall1.ADRS.auditPairHit_pos
#print axioms SigabaNeo.Wall1.ADRS.pairHitOr_prob
#print axioms SigabaNeo.Wall1.ADRS.audit_integer_counterexample
#print axioms SigabaNeo.Wall1.ADRS.audit_rounded_hits
