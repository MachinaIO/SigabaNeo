module

public import SigabaNeo.Lib.Lattices.Research.Wall1.AdrsCoupling
public import CslibFrontier.Probability.IID.Event
public import CslibFrontier.Probability.PMF.BindFailure
import CslibFrontier.Probability.PMF.Event
import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic

/-! # Poissonization of finite lists with independent marks -/

@[expose] public section

noncomputable section

namespace SigabaNeo.Wall1.ADRS

open ProbabilityTheory MeasureTheory Cslib.Probability.PMF
open scoped ENNReal NNReal BigOperators

variable {V C : Type*} {r : ℕ}

/-- Counts of each label in an ordered tuple. -/
def binCounts [DecidableEq C] {n : ℕ} (x : Fin n → C) : C → ℕ :=
  ∑ i, Pi.single (x i) 1

/-- Multinomial law for finite label counts. Comparing coefficients of the same
monoid-algebra power counts all orderings with the required histogram. -/
theorem iid_binCounts [Fintype C] [DecidableEq C] (q : PMF C) (n : ℕ) (k : C → ℕ) :
    (iid q n).map binCounts k = if ∑ c, k c = n then
      (Nat.multinomial Finset.univ k : ℝ≥0∞) * ∏ c, q c ^ k c else 0 := by
  classical
  let e (c : C) : C → ℕ := Pi.single c 1
  let f (c : C) : AddMonoidAlgebra ℝ≥0∞ (C → ℕ) := .single (e c) (q c)
  let P := (∑ c, f c)^n
  have hleft : P = ∑ x : Fin n → C, AddMonoidAlgebra.single (binCounts x) (∏ i, q (x i)) := by
    calc P = ∏ _ : Fin n, ∑ c, f c := by simp [P]
         _ = _ := by
           rw [Fintype.prod_sum]
           apply Finset.sum_congr rfl
           intro x _
           exact AddMonoidAlgebra.prod_single ..
  have he (j : C → ℕ) : ∑ c, j c • e c = j := by
    funext c
    classical
    simp [e, Finset.sum_apply, Pi.single_apply]
  have hright : P = ∑ j ∈ Finset.piAntidiag Finset.univ n,
      AddMonoidAlgebra.single j ((Nat.multinomial Finset.univ j : ℝ≥0∞) * ∏ c, q c ^ j c) := by
    unfold P
    rw [Finset.sum_pow_eq_sum_piAntidiag]
    apply Finset.sum_congr rfl
    intro j _
    simp only [f, AddMonoidAlgebra.single_pow, AddMonoidAlgebra.prod_single, he]
    change AddMonoidAlgebra.single 0 _ * _ = _
    rw [AddMonoidAlgebra.single_mul_single, zero_add]
  have h := congrArg (fun a : AddMonoidAlgebra ℝ≥0∞ (C → ℕ) ↦ a.coeff k) (hleft.symm.trans hright)
  simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_piAntidiag,
    Finset.mem_univ, implies_true, and_true] at h
  rw [PMF.map_apply, tsum_fintype]
  simpa only [iid_apply, eq_comm] using h

/-- A Poisson number of iid samples, as a multiset retaining multiplicities. -/
def poissonList (rate : ℝ≥0) (μ : PMF V) : PMF (Multiset V) :=
  (poissonMeasure rate).toPMF.bind fun n ↦ (iid μ n).map fun x ↦ Finset.univ.val.map x

/-- Exact finite-bin Poisson splitting, including zero intensities. -/
theorem poisson_split_bins (rate : ℝ≥0) (q : PMF (Fin r)) :
    ((poissonMeasure rate).toPMF.bind fun n ↦ (iid q n).map binCounts) =
      piFin (fun c ↦ (poissonMeasure (rate * (q c).toNNReal)).toPMF) := by
  classical
  ext k
  rw [PMF.bind_apply, tsum_eq_single (∑ c, k c)]
  · apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
      (PMF.apply_ne_top _ _)) (PMF.apply_ne_top _ _)).mp
    rw [iid_binCounts, ite_eq_left rfl, piFin_apply]
    let a (c : Fin r) : ℝ := (q c).toReal
    have ha : ∑ c, a c = 1 := by
      rw [show (∑ c, a c) = (∑ c, q c).toReal from
        (ENNReal.toReal_sum (fun c _ ↦ PMF.apply_ne_top q c)).symm,
        show (∑ c, q c) = 1 from (tsum_fintype _).symm.trans q.tsum_coe, ENNReal.toReal_one]
    have hp (t : ℝ≥0) (j : ℕ) : ((poissonMeasure t).toPMF j).toReal =
        Real.exp (-t) * (t : ℝ)^j / j.factorial :=
      poissonMeasure_real_singleton t j
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_prod,
      ENNReal.toReal_pow, hp, NNReal.coe_mul, ENNReal.coe_toNNReal_eq_toReal]
    change _ * (_ * ∏ c, a c ^ k c) =
      ∏ c, (Real.exp (-(rate * a c)) * ((rate : ℝ) * a c)^k c / (k c).factorial)
    rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, ← Real.exp_sum,
      Finset.sum_neg_distrib, ← Finset.mul_sum, ha, mul_one]
    simp_rw [mul_pow]
    rw [Finset.prod_mul_distrib, ← Finset.prod_pow_eq_pow_sum]
    have hfac : (∏ c, ((k c).factorial : ℝ)) * (Nat.multinomial Finset.univ k : ℝ) =
        ((∑ c, k c).factorial : ℝ) := by exact_mod_cast Nat.multinomial_spec Finset.univ k
    have hpos : (0 : ℝ) < ∏ c, ((k c).factorial : ℝ) := by positivity
    rw [← hfac]
    have hm : (Nat.multinomial Finset.univ k : ℝ) ≠ 0 :=
      ne_of_gt (by exact_mod_cast Nat.multinomial_pos (s := Finset.univ) (f := k))
    field_simp [hpos.ne', hm]
  · intro j hj
    rw [iid_binCounts, ite_eq_right (Ne.symm hj), mul_zero]

/-- The probability that a Poisson list misses all points of a target set. -/
theorem poissonList_miss (rate : ℝ≥0) (μ : PMF V) (S : Set V) :
    (poissonList rate μ).toOuterMeasure {u | ∀ v ∈ u, v ∉ S} =
      ENNReal.ofReal (Real.exp (-(rate : ℝ) * (μ.toOuterMeasure S).toReal)) := by
  classical
  let p := (μ.toOuterMeasure Sᶜ).toReal
  have hp : 0 ≤ p := ENNReal.toReal_nonneg
  have hpc := toOuterMeasure_toReal_add_compl μ S
  have h (n : ℕ) : ((iid μ n).map (fun x ↦ Finset.univ.val.map x)).toOuterMeasure
      {u | ∀ v ∈ u, v ∉ S} = ENNReal.ofReal (p^n) := by
    rw [PMF.toOuterMeasure_map_apply]
    have he : (fun x : Fin n → V ↦ Finset.univ.val.map x) ⁻¹' {u | ∀ v ∈ u, v ∉ S} =
        {x | ∀ i, x i ∈ Sᶜ} := by ext x; simp
    rw [he, toOuterMeasure_iid_forall, ENNReal.ofReal_pow hp, ENNReal.ofReal_toReal
      (toOuterMeasure_ne_top μ _)]
  let term (n : ℕ) := Real.exp (-(rate : ℝ)) * ((rate : ℝ)*p)^n / n.factorial
  have hsum : HasSum term (Real.exp (-(rate : ℝ)) * Real.exp ((rate : ℝ)*p)) := by
    simpa only [term, mul_div_assoc, Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp ((rate : ℝ)*p)).mul_left (Real.exp (-(rate : ℝ)))
  rw [poissonList, PMF.toOuterMeasure_bind_apply]
  calc _ = ∑' n, ENNReal.ofReal (term n) := by
         apply tsum_congr
         intro n
         rw [h, show (poissonMeasure rate).toPMF n = _ from poissonMeasure_singleton rate n,
           ← ENNReal.ofReal_mul (by positivity)]
         congr 1
         dsimp [term]
         rw [mul_pow]
         ring
       _ = _ := by
         rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by unfold term; positivity) hsum.summable,
           hsum.tsum_eq, ← Real.exp_add]
         congr 2
         dsimp [p]
         nlinarith [congrArg ((rate : ℝ) * ·) hpc]

end SigabaNeo.Wall1.ADRS

#print axioms SigabaNeo.Wall1.ADRS.iid_binCounts
#print axioms SigabaNeo.Wall1.ADRS.poisson_split_bins
#print axioms SigabaNeo.Wall1.ADRS.poissonList_miss
