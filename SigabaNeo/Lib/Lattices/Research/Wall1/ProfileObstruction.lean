module

public import SigabaNeo.Lib.Lattices.Research.Wall1.UniquenessProfile
import all SigabaNeo.Lib.Lattices.Research.Wall1.UniquenessProfile
import all SigabaNeo.Lib.Lattices.Research.Wall1.ThetaProfile
import all SigabaNeo.Lib.Lattices.Research.Wall1.ShiftedTheta
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

public section

namespace SigabaNeo.Wall1

open InnerProductSpace Classical

private theorem theta_three_terms {a : ℝ} (ha : 0 < a) :
    1 + 2 * Real.exp (-a) ≤ thetaFactor a := by
  have h := (gaussian_summable ha).sum_le_tsum ({0, 1, -1} : Finset ℤ)
    (fun _ _ ↦ (Real.exp_pos _).le)
  norm_num [Finset.sum_insert, thetaFactor] at h ⊢
  linarith

private theorem theta_one_le {a : ℝ} (ha : 0 < a) : 1 ≤ thetaFactor a := by
  linarith [theta_three_terms ha, Real.exp_pos (-a)]

private theorem excess_nonneg {d : ℕ} {t : Fin d → ℝ} (ht : ∀ i, 0 < t i)
    {k : ℝ} (hk : 0 < k) : 0 ≤ profileExcess t k := by
  apply sub_nonneg.mpr
  exact Finset.one_le_prod₀ fun i _ ↦ theta_one_le (by have := ht i; positivity)

/-- Even a single coordinate forces a charge in the product bound. -/
theorem coordinate_le_profileExcess {d : ℕ} {t : Fin d → ℝ} (ht : ∀ i, 0 < t i)
    {k : ℝ} (hk : 0 < k) (i : Fin d) :
    2 * Real.exp (-((1 / (12 * k^2)) * (t i)^2)) ≤ profileExcess t k := by
  let f j := thetaFactor ((1 / (12 * k^2)) * (t j)^2)
  have ha j : 0 < (1 / (12 * k^2)) * (t j)^2 := by have := ht j; positivity
  have hrest : 1 ≤ ∏ j ∈ Finset.univ.erase i, f j :=
    Finset.one_le_prod₀ fun j _ ↦ theta_one_le (ha j)
  have h := le_mul_of_one_le_left ((zero_le_one.trans (theta_one_le (ha i))) : 0 ≤ f i) hrest
  rw [Finset.prod_erase_mul _ _ (Finset.mem_univ i)] at h
  change _ ≤ (∏ j, f j) - 1
  have hterm : 1 + 2 * Real.exp (-((1 / (12 * k^2)) * (t i)^2)) ≤ f i :=
    theta_three_terms (ha i)
  linarith

private theorem exp_floor {x : ℝ} (hx : 2 * Real.exp (-x) ≤ 1 / 100) : 5 < x := by
  by_contra! h
  have he : Real.exp 5 < 200 := by
    rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    calc Real.exp 1 ^ 5 ≤ (11 / 4 : ℝ)^5 := by
           gcongr
           linarith [Real.exp_one_lt_d9]
         _ < 200 := by norm_num
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos x)] at hx
  linarith [Real.exp_le_exp.mpr h]

set_option exponentiation.threshold 1024 in
set_option maxRecDepth 8192 in
private theorem determinant_floor {r : ℕ} (hr : r ≤ 511) :
    (3329 : ℝ)^r < 7^(r+7) * 500^505 := by
  by_contra! bad
  have propagate (n : ℕ) (hn : r ≤ n) : (7 : ℝ)^(n+7) * 500^505 ≤ 3329^n := by
    induction n, hn using Nat.le_induction with
    | base => exact bad
    | succ n _ ih =>
      rw [show n+1+7 = n+7+1 by omega, pow_succ, pow_succ (3329 : ℝ)]
      calc 7^(n+7) * 7 * 500^505 = (7^(n+7) * 500^505) * 7 := by ac_rfl
           _ ≤ 3329^n * 7 := mul_le_mul_of_nonneg_right ih (by norm_num)
           _ ≤ _ := mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
  have stop : (3329 : ℝ)^511 < 7^(511+7) * 500^505 := by
    exact_mod_cast (show (3329 : ℕ)^511 < 7^(511+7) * 500^505 by decide)
  exact stop.not_ge (propagate 511 hr)

/-- The recorded covolume rules out the two one-percent allowances for *every*
positive terminal profile, already using only height 67. -/
theorem recordedProfile_impossible {r : ℕ} (hr : r ≤ 511) (p : Fin (r+7) → ℝ)
    (t : Fin 505 → ℝ) (hp : ∀ j, 0 ≤ p j) (ht : ∀ i, 0 < t i)
    (det : (∏ j, p j) * (∏ i, t i) = (3329 : ℝ)^r)
    (prefixBound : (∑ j, 2 * Real.exp (-(p j)^2 / 12)) ≤ 1 / 100)
    (terminal : profileExcess t 67 ≤ 1 / 100) : False := by
  have hp' j : (7 : ℝ) ≤ p j := by
    have h := (Finset.single_le_sum (f := fun j ↦ 2 * Real.exp (-(p j)^2 / 12))
      (fun j _ ↦ by positivity) (Finset.mem_univ j)).trans prefixBound
    rw [neg_div] at h
    have floor := exp_floor h
    by_contra! hsmall
    nlinarith [mul_nonneg (hp j) (sub_nonneg.mpr hsmall.le)]
  have ht' i : (500 : ℝ) ≤ t i := by
    have floor := exp_floor ((coordinate_le_profileExcess ht (k := 67) (by norm_num) i).trans
      terminal)
    by_contra! hsmall
    nlinarith [mul_nonneg (ht i).le (sub_nonneg.mpr hsmall.le)]
  have pprod : (7 : ℝ)^(r+7) ≤ ∏ j, p j := by
    simpa using Finset.prod_le_prod₀ (s := Finset.univ) (fun _ _ ↦ by norm_num : ∀ j ∈
      (Finset.univ : Finset (Fin (r+7))), (0 : ℝ) ≤ 7) (fun j _ ↦ hp' j)
  have tprod : (500 : ℝ)^505 ≤ ∏ i, t i := by
    simpa using Finset.prod_le_prod₀ (s := Finset.univ) (fun _ _ ↦ by norm_num : ∀ i ∈
      (Finset.univ : Finset (Fin 505)), (0 : ℝ) ≤ 500) (fun i _ ↦ ht' i)
  exact (determinant_floor hr).not_ge (det ▸ mul_le_mul pprod tprod (by positivity)
    (Finset.prod_nonneg fun j _ ↦ hp j))

/-- The height-67 obstruction applies to the complete geometry-dependent error. -/
theorem recordedBlock_impossible {r : ℕ} (hr : r ≤ 511) (B : FinalBlock (512+r) 505)
    (p : Fin (r+7) → ℝ) (hp : ∀ j, 0 ≤ p j) (L : ℝ)
    (det : (∏ j, p j) * (∏ i, ‖gramSchmidt ℝ B.basis i‖) = (3329 : ℝ)^r)
    (prefixBound : (∑ j, 2 * Real.exp (-(p j)^2 / 12)) ≤ 1 / 100)
    (terminal : B.errGeom L ≤ 1 / 100) : False := by
  let t i := ‖gramSchmidt ℝ B.basis i‖
  have ht i : 0 < t i := norm_pos_iff.mpr (gramSchmidt_ne_zero i B.basis.linearIndependent)
  apply recordedProfile_impossible hr p t hp ht det prefixBound
  have mem : 67 ∈ Finset.Icc 2 (Nat.sqrt (9*(512+r)+1)) :=
    Finset.mem_Icc.mpr ⟨by decide, Nat.le_sqrt'.mpr (by omega)⟩
  have h := Finset.single_le_sum (f := fun k : ℕ ↦ profileExcess t k)
    (fun k hk ↦ excess_nonneg ht (by
      exact_mod_cast (show 0 < k by have := (Finset.mem_Icc.mp hk).1; omega))) mem
  apply le_trans _ terminal
  unfold FinalBlock.errGeom
  change profileExcess t 67 ≤ _ + profileExcess t 1 + _
  exact h.trans (le_add_of_nonneg_left (add_nonneg (by positivity) (excess_nonneg ht one_pos)))

/-- On any finite distribution of physical profiles at the recorded dimensions,
the geometry-dependent test rejects with probability one. -/
theorem recordedProfile_rejection_eq_one {Z : Type*} [Fintype Z] {r : ℕ} (hr : r ≤ 511)
    (B : Z → FinalBlock (512+r) 505) (p : Z → Fin (r+7) → ℝ) (L : Z → ℝ)
    (hp : ∀ z j, 0 ≤ p z j)
    (det : ∀ z, (∏ j, p z j) * (∏ i, ‖gramSchmidt ℝ (B z).basis i‖) = (3329 : ℝ)^r)
    {ε ℓ : ℝ} (hε : ε ≤ 1/100) (hℓ : ℓ ≤ 1/100)
    (μ : Z → ℝ) (mass : ∑ z, μ z = 1) :
    (∑ z with ¬(B z).profileAccept (p z) (L z) ε ℓ, μ z) = 1 := by
  have reject (z : Z) : ¬(B z).profileAccept (p z) (L z) ε ℓ := by
    rintro ⟨hterm, _, _, _, hpre⟩
    exact recordedBlock_impossible hr (B z) (p z) (hp z) (L z) (det z) (hpre.trans hℓ)
      (hterm.trans hε)
  simpa only [Finset.filter_true_of_mem (fun z _ ↦ reject z)] using mass

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.coordinate_le_profileExcess
#print axioms SigabaNeo.Wall1.recordedProfile_impossible
#print axioms SigabaNeo.Wall1.recordedBlock_impossible
#print axioms SigabaNeo.Wall1.recordedProfile_rejection_eq_one
