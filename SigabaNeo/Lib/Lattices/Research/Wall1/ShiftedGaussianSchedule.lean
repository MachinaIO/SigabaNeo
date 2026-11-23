module

public import SigabaNeo.Lib.Lattices.Research.Wall1.ShiftedGaussianPeak
import Mathlib.Tactic

/-! The explicit Poisson schedule and terminal miss theorem for a shifted lattice.
Only the initial finite-precision sampler and the relative terminal mass enter as
distribution-specific hypotheses. -/

@[expose] public section
noncomputable section
namespace SigabaNeo.Wall1.CVP638

set_option exponentiation.threshold 1200

open SigabaNeo.Wall1.ADRS ProbabilityTheory ZLattice Cslib.Probability.PMF MeasureTheory
open scoped ENNReal NNReal

variable {r : ℕ} [NeZero r]

def peakProb (q : PMF (Fin r)) := (q (peak q)).toNNReal

omit [NeZero r] in
private theorem sum_probs (q : PMF (Fin r)) : ∑ i, (q i).toNNReal = 1 := by
  rw [← ENNReal.toNNReal_sum (fun i _ ↦ PMF.apply_ne_top _ _),
    show (∑ i, q i) = 1 from (tsum_fintype _).symm.trans q.tsum_coe]
  rfl

theorem bins_times_peak (q : PMF (Fin r)) : 1 ≤ (r:ℝ≥0) * peakProb q := by
  calc 1 = ∑ i, (q i).toNNReal := (sum_probs q).symm
       _ ≤ ∑ _i : Fin r, peakProb q := Finset.sum_le_sum fun i _ ↦ le_peak q i
       _ = _ := by simp

private theorem peak_pos (q : PMF (Fin r)) : 0 < peakProb q := by
  by_contra! h
  have hp := bins_times_peak q
  simp [le_antisymm h zero_le] at hp

private theorem collision_le_peak (q : PMF (Fin r)) :
    (collisionMass q).toNNReal ≤ peakProb q := by
  rw [collisionMass, ENNReal.toNNReal_sum (fun i _ ↦ ENNReal.pow_ne_top (PMF.apply_ne_top _ _))]
  calc _ ≤ ∑ i, (q i).toNNReal * peakProb q := by
         apply Finset.sum_le_sum
         intro i _
         rw [ENNReal.toNNReal_pow, sq]
         exact mul_le_mul_right (le_peak q i) _
       _ = _ := by rw [← Finset.sum_mul, sum_probs, one_mul]

/-- The analysis uses this rate only to couple the deterministic pairing steps. -/
def scheduleRate (q : ℕ → PMF (Fin r)) : ℕ → ℝ≥0
  | 0 => initialMean
  | j+1 => scheduleRate q j / 8 * (collisionMass (q j)).toNNReal / peakProb (q j)

private theorem rate_pos (q : ℕ → PMF (Fin r)) (j : ℕ) : 0 < scheduleRate q j := by
  induction j with
  | zero => change (0:ℝ≥0) < ((2^753:ℕ):ℝ≥0); positivity
  | succ j ih =>
    apply div_pos _ (peak_pos _)
    exact mul_pos (by positivity) (ENNReal.toNNReal_pos (collisionMass_ne_zero _) (collisionMass_ne_top _))

private theorem rate_le (q : ℕ → PMF (Fin r)) (j : ℕ) : scheduleRate q j ≤ initialMean := by
  induction j with
  | zero => rfl
  | succ j ih =>
    apply le_trans _ ih
    rw [scheduleRate, div_le_iff₀ (peak_pos _)]
    exact mul_le_mul (div_le_self zero_le (by norm_num)) (collision_le_peak _) zero_le zero_le

def binIntensity (q : ℕ → PMF (Fin r)) (j : ℕ) := scheduleRate q j * peakProb (q j)

private theorem intensity_step (q : ℕ → PMF (Fin r)) (j : ℕ)
    (hpeak : peakProb (q j)^2 ≤ (collisionMass (q j)).toNNReal * peakProb (q (j+1))) :
    binIntensity q j / 8 ≤ binIntensity q (j+1) := by
  unfold binIntensity
  rw [scheduleRate, div_mul_eq_mul_div, le_div_iff₀ (peak_pos _)]
  calc _ = scheduleRate q j / 8 * peakProb (q j)^2 := by ring
       _ ≤ scheduleRate q j / 8 * ((collisionMass (q j)).toNNReal * peakProb (q (j+1))) :=
         mul_le_mul_right hpeak _
       _ = _ := by ring

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
variable (L : Submodule ℤ E) (b : Module.Basis ι ℤ L)
variable (e : (ι → ZMod 2) ≃ Fin (2^638)) [FiniteDimensional ℝ E] [DiscreteTopology L]
variable {s : ℝ} (hs : 0 < s) (t : E)

set_option maxRecDepth 12000 in
/-- For the audited number of labels, the two distributional hypotheses suffice for
a terminal hit on an arbitrary target set (which may contain tied minimizers). -/
theorem scheduled_miss (P : PMF L) (S : Set L)
    (initial_sampler : ∃ J : PMF (L × L), J.map Prod.fst = P ∧
      J.map Prod.snd = discreteGaussian L s hs t ∧
      J.toOuterMeasure {z | z.1 ≠ z.2} ≤ ENNReal.ofReal (1/(2:ℝ)^923))
    (terminal_ratio :
      (peakProb (labelLaw L b (stepWidth_pos hs 36) t e):ℝ) ≤
        16/15 * ((discreteGaussian L (stepWidth s 36) (stepWidth_pos hs 36) t).toOuterMeasure S).toReal) :
    (iid P sampleCount).toOuterMeasure
      {v | ∀ x ∈ terminalBag L b e 36 sampleCount v, x ∉ S} < ENNReal.ofReal (1/(2:ℝ)^168) := by
  let q j := labelLaw L b (stepWidth_pos hs j) t e
  let rate := scheduleRate q
  let A := binIntensity q
  let m j := ⌊(A j:ℝ)/(4*(1/8))-1/2⌋₊
  have h₀ : (2:ℝ)^115 ≤ A 0 := by
    have h := bins_times_peak (q 0)
    have h' : (1:ℝ) ≤ 2^638 * (peakProb (q 0):ℝ) := by exact_mod_cast h
    change (2:ℝ)^115 ≤ ((initialMean:ℝ≥0):ℝ) * (peakProb (q 0):ℝ)
    simp only [initialMean, Nat.cast_pow, Nat.cast_ofNat, NNReal.coe_pow, NNReal.coe_ofNat]
    calc _ = 2^115 * 1 := by ring
         _ ≤ 2^115 * (2^638 * (peakProb (q 0):ℝ)) := mul_le_mul_of_nonneg_left h' (by positivity)
         _ = _ := by rw [← mul_assoc, ← pow_add]
  have hA := intensity_lower (fun j ↦ A j) h₀ (fun j _ ↦ by
    exact_mod_cast intensity_step q j (peak_square L b e (stepWidth_pos hs j) t))
  apply terminal_miss L b e hs t P S rate A m
  · intro j hj
    refine ⟨rate_pos _ _, by norm_num, mul_pos (rate_pos _ _) (peak_pos _),
      fun c ↦ mul_le_mul_right (le_peak _ c) _, rfl, (by omega : 1 ≤ 1999).trans (hA.2.1 j hj), ?_⟩
    change rate j / 8 * _ / peakProb (q j) = 1/8 * rate j^2 * _ / (rate j * peakProb (q j))
    field_simp [(rate_pos q j).ne', (peak_pos (q j)).ne']
    ring
  · intro j _
    have h : (scheduleRate q j:ℝ) ≤ (initialMean:ℝ≥0) := by exact_mod_cast rate_le q j
    simpa only [initialMean, Nat.cast_pow, Nat.cast_ofNat, NNReal.coe_pow, NNReal.coe_ofNat] using h
  · exact hA.2.1
  · rfl
  · exact initial_sampler
  · have hterm := mul_le_mul_of_nonneg_left terminal_ratio (rate 36).coe_nonneg
    have h128 := hA.2.2
    change 128 ≤ (rate 36:ℝ) * (peakProb (q 36):ℝ) at h128
    change (rate 36:ℝ) * (peakProb (q 36):ℝ) ≤ _ at hterm
    linarith

end SigabaNeo.Wall1.CVP638

#print axioms SigabaNeo.Wall1.CVP638.bins_times_peak
#print axioms SigabaNeo.Wall1.CVP638.scheduled_miss
