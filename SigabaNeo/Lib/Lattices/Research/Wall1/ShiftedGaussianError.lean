module

public import SigabaNeo.Lib.Lattices.Research.Wall1.ShiftedGaussianHistory
public import SigabaNeo.Lib.Lattices.Research.Wall1.PoissonOverflow
import CslibFrontier.Probability.IID.Event
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! Error accounting for independent approximate draws followed by deterministic pairing. -/

@[expose] public section
noncomputable section
namespace SigabaNeo.Wall1.CVP638

open SigabaNeo.Wall1.ADRS ProbabilityTheory ZLattice Cslib.Probability.PMF MeasureTheory
open scoped ENNReal NNReal

/-- A coupling for one draw transfers every event on a list of n independent draws. -/
theorem iid_event_transfer {V : Type*} (J : PMF (V × V)) (n : ℕ) (B : Set (Fin n → V)) :
    (iid (J.map Prod.fst) n).toOuterMeasure B ≤ (iid (J.map Prod.snd) n).toOuterMeasure B +
      n * J.toOuterMeasure {z | z.1 ≠ z.2} := by
  rw [iid_map, iid_map, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  let bad : Set (Fin n → V × V) := {v | ∃ i, (v i).1 ≠ (v i).2}
  have hbad : (iid J n).toOuterMeasure bad ≤ n * J.toOuterMeasure {z | z.1 ≠ z.2} := by
    simpa only [bad, Set.mem_ofPred_eq, piFin_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] using toOuterMeasure_piFin_exists_le (fun _ : Fin n ↦ J)
        (fun _ ↦ {z | z.1 ≠ z.2})
  apply le_trans ((iid J n).toOuterMeasure.mono
    (s₂ := (fun (v : Fin n → V × V) i ↦ (v i).2) ⁻¹' B ∪ bad) ?_)
  · exact (measure_union_le ..).trans (add_le_add le_rfl hbad)
  · intro v hv
    by_cases h : ∀ i, (v i).1 = (v i).2
    · exact Or.inl (show (fun i ↦ (v i).2) ∈ B from (funext h) ▸ hv)
    · exact Or.inr (not_forall.mp h)

set_option maxRecDepth 8000 in
/-- Part 140 Lemma 4.3b's actual error expression at one pairing level. -/
theorem step_error_bound (r r' : ℝ≥0) (m : ℕ) (hr : (r:ℝ) ≤ 2^753)
    (hr' : (r':ℝ) ≤ 2^753) (hm : 1999 ≤ m) :
    stepError r r' (1/8) m ≤ ENNReal.ofReal
      ((2:ℝ)^753*8*((1/4)^1999+(3/4)^3999)) := by
  have he : Real.exp 2 ≤ 8 := by
    rw [show (2:ℝ) = 1+1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1,
      mul_self_le_mul_self (Real.exp_pos 1).le Real.exp_one_lt_d9.le]
  have he' : Real.exp (3/2) ≤ 8 := (Real.exp_le_exp.mpr (by norm_num)).trans he
  have bound (x y : ℝ) (h : x ≤ y) (hx : 0 ≤ x) (hy : y ≤ 1) {i j : ℕ} (hj : i ≤ j) :
      x^j ≤ y^i :=
    (pow_le_pow_left₀ hx h j).trans (pow_le_pow_of_le_one (hx.trans h) hy hj)
  have p := bound (4*Real.exp 1*(1/8)^2) (1/4) (by linarith [Real.exp_one_lt_three])
    (by positivity) (by norm_num) hm
  have q := bound (2*Real.exp 1*(1/8)) (3/4) (by linarith [Real.exp_one_lt_three])
    (by positivity) (by norm_num) (show 3999 ≤ 2*m+1 by omega)
  unfold stepError
  apply ENNReal.ofReal_le_ofReal
  push_cast
  rw [mul_add]
  apply add_le_add
  · rw [mul_assoc (2^753:ℝ)]
    apply mul_le_mul hr' _ (by positivity) (by positivity)
    exact (div_le_self (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) m] : 1 ≤ (m:ℝ)+1)).trans
      (mul_le_mul he' p (by positivity) (by norm_num))
  · rw [mul_assoc (2^753:ℝ)]
    apply mul_le_mul hr _ (by positivity) (by positivity)
    exact (div_le_self (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) m] : 1 ≤ 2*(m:ℝ)+2)).trans
      (mul_le_mul he q (by positivity) (by norm_num))

/-- From an initial bin intensity and the factor-of-eight recurrence to all lower bounds. -/
theorem intensity_lower (A : ℕ → ℝ) (h₀ : (2:ℝ)^115 ≤ A 0)
    (hstep : ∀ j < 36, A j / 8 ≤ A (j+1)) :
    (∀ j ≤ 36, (2:ℝ)^115 / 8^j ≤ A j) ∧
    (∀ j < 36, 1999 ≤ ⌊A j / (4*(1/8)) - 1/2⌋₊) ∧ 128 ≤ A 36 := by
  have h (j) (hj : j ≤ 36) : (2:ℝ)^115 / 8^j ≤ A j := by
    induction j with
    | zero => simpa using h₀
    | succ j ih =>
      rw [pow_succ (8:ℝ), ← div_div]
      exact (div_le_div_of_nonneg_right (ih (by omega)) (by norm_num)).trans (hstep j hj)
  refine ⟨h, ?_, ?_⟩
  · intro j hj
    have hp : (8:ℝ)^j ≤ 8^35 := pow_le_pow_right₀ (by norm_num) (by omega)
    have hmin := (div_le_div_of_nonneg_left (by positivity : (0:ℝ) ≤ 2^115)
      (by positivity) hp).trans (h j (by omega))
    apply Nat.le_floor
    norm_num at hmin ⊢
    linarith
  · simpa using (show (128:ℝ) ≤ 2^115/8^36 by norm_num).trans (h 36 le_rfl)

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
variable (L : Submodule ℤ E) (b : Module.Basis ι ℤ L) {r : ℕ} (e : (ι → ZMod 2) ≃ Fin r)
variable [FiniteDimensional ℝ E] [DiscreteTopology L] {s : ℝ} (hs : 0 < s) (t : E)

/-- The deterministic terminal multiset for a given input list. -/
def terminalBag (ℓ n : ℕ) (v : Fin n → L) : Multiset L :=
  sampleBag ((stablePair (binLabel L b e) (latticeMidpoint L))^[ℓ] ⟨n,v⟩)

private theorem run_eq (n j : ℕ) :
    shiftedRun L b e hs t n j =
      (iid (discreteGaussian L s hs t) n).map
        ((stablePair (binLabel L b e) (latticeMidpoint L))^[j] ∘ Sigma.mk n) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [shiftedRun, ih, PMF.map_comp, Function.iterate_succ']
                 rfl

set_option exponentiation.threshold 1200 in
set_option maxRecDepth 12000 in
/-- The physical list misses the target set with probability below the audited budget.
The named inputs give its initial sampler coupling, the valid rate schedule, its initial
Poisson mean, and the terminal Gaussian intensity of the target set. -/
theorem terminal_miss (P : PMF L) (S : Set L)
    (rate A : ℕ → ℝ≥0) (m : ℕ → ℕ)
    (schedule : ShiftedSchedule L b e hs t 36 rate (fun _ ↦ 1/8) A m)
    (rate_cap : ∀ j ≤ 36, (rate j:ℝ) ≤ 2^753)
    (tail_index : ∀ j < 36, 1999 ≤ m j)
    (initial_rate : rate 0 = initialMean)
    (initial_sampler : ∃ J : PMF (L × L), J.map Prod.fst = P ∧
      J.map Prod.snd = discreteGaussian L s hs t ∧
      J.toOuterMeasure {z | z.1 ≠ z.2} ≤ ENNReal.ofReal (1/(2:ℝ)^923))
    (terminal_mass : 120 ≤ (rate 36:ℝ) *
      ((discreteGaussian L (stepWidth s 36) (stepWidth_pos hs 36) t).toOuterMeasure S).toReal) :
    (iid P sampleCount).toOuterMeasure
      {v | ∀ x ∈ terminalBag L b e 36 sampleCount v, x ∉ S} < ENNReal.ofReal (1/(2:ℝ)^168) := by
  have initial_overflow := initial_poisson_overflow
  rw [← initial_rate] at initial_overflow
  obtain ⟨J,hP,hD,hprec⟩ := initial_sampler
  have htransfer := iid_event_transfer J sampleCount {v | ∀ x ∈ terminalBag L b e 36 sampleCount v,
    x ∉ S}
  rw [hP,hD] at htransfer
  have h := poisson_dominated_miss (shiftedRun_domination L b e hs t sampleCount 36 rate
    (fun _ ↦ 1/8) A m schedule) S
  rw [run_eq, PMF.map_comp, PMF.toOuterMeasure_map_apply] at h
  have negMass := neg_le_neg terminal_mass
  rw [← neg_mul] at negMass
  have hm := ENNReal.ofReal_le_ofReal ((Real.exp_le_exp.mpr negMass).trans poisson_miss.le)
  let g : ℝ := 2^753*8*((1/4)^1999+(3/4)^3999)
  have hsum : (∑ j ∈ Finset.range 36, stepError (rate j) (rate (j+1)) (1/8) (m j)) ≤
      ENNReal.ofReal (1/(2:ℝ)^830) := by
    calc _ ≤ ∑ _j ∈ Finset.range 36, ENNReal.ofReal g := Finset.sum_le_sum fun j hj ↦
          step_error_bound _ _ _ (rate_cap _ (Finset.mem_range.mp hj).le)
            (rate_cap _ (Finset.mem_range.mp hj)) (tail_index _ (Finset.mem_range.mp hj))
         _ = ENNReal.ofReal (36*g) := by simp [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 36)]
         _ ≤ _ := ENNReal.ofReal_le_ofReal (by
            unfold g
            have hrat := mismatch_lt.le
            unfold mismatch at hrat
            rw [← mul_assoc, ← mul_assoc]
            have hh : ((36*(2:ℚ)^753*8*((1/4)^1999+(3/4)^3999):ℚ):ℝ) ≤
                ((1/(2:ℚ)^830:ℚ):ℝ) := Rat.cast_le.mpr hrat
            push_cast at hh
            exact hh)
  apply lt_of_le_of_lt (htransfer.trans (add_le_add h (mul_le_mul_of_nonneg_left hprec zero_le)))
  apply lt_of_le_of_lt (add_le_add (add_le_add hm (add_le_add initial_overflow hsum)) le_rfl)
  rw [show (sampleCount:ℝ≥0∞) = ENNReal.ofReal (2^754) by
      rw [← ENNReal.ofReal_natCast]
      congr 1
      simp only [sampleCount, Nat.cast_pow, Nat.cast_ofNat],
    ← ENNReal.ofReal_mul (by positivity)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr
  norm_num

/-- Transfer an event lower bound across four possibly dependent errors on a common
probability space. The caller supplies the event inclusion and the four marginals. -/
theorem four_event_transfer {Ω : Type*} (law : PMF Ω) (credited actual : Set Ω)
    (bad : Fin 4 → Set Ω) (agree : credited ⊆ actual ∪ ⋃ i, bad i)
    (credit : 643162094166/(10:ℝ)^12 < (law.toOuterMeasure credited).toReal)
    (errors : ∀ i, law.toOuterMeasure (bad i) ≤ ENNReal.ofReal (1/(2:ℝ)^168)) :
    6431620941/(10:ℝ)^10 < (law.toOuterMeasure actual).toReal := by
  have err : law.toOuterMeasure (⋃ i, bad i) ≤ ∑ _i : Fin 4, ENNReal.ofReal (1/(2:ℝ)^168) :=
    (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun i _ ↦ errors i)
  have bound := (law.toOuterMeasure.mono agree).trans
    ((measure_union_le ..).trans (add_le_add le_rfl err))
  have R := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨toOuterMeasure_ne_top law actual,
    ENNReal.sum_ne_top.mpr fun _ _ ↦ ENNReal.ofReal_ne_top⟩) bound
  rw [ENNReal.toReal_add (toOuterMeasure_ne_top law actual) (ENNReal.sum_ne_top.mpr
    fun _ _ ↦ ENNReal.ofReal_ne_top), ENNReal.toReal_sum (fun _ _ ↦ ENNReal.ofReal_ne_top)] at R
  simp only [
    ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 1/2^168), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at R
  have margin := (Rat.cast_lt (K := ℝ)).mpr four_loss_margin
  push_cast at margin
  change (law.toOuterMeasure credited).toReal ≤ (law.toOuterMeasure actual).toReal +
    4*(1/(2:ℝ)^168) at R
  linarith only [margin, credit, R]

end SigabaNeo.Wall1.CVP638

#print axioms SigabaNeo.Wall1.CVP638.iid_event_transfer
#print axioms SigabaNeo.Wall1.CVP638.step_error_bound
#print axioms SigabaNeo.Wall1.CVP638.intensity_lower
#print axioms SigabaNeo.Wall1.CVP638.terminal_miss
#print axioms SigabaNeo.Wall1.CVP638.four_event_transfer
