module

public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import SigabaNeo.Lib.Lattices.Research.Wall1.MultiBlockAttack
import Mathlib.Tactic

public section
noncomputable section

namespace SigabaNeo.Wall1

open scoped ENNReal Classical
open Finset

/-- Average over an arbitrary seed PMF and a finite weighted sample space independently. -/
theorem pmf_seed_average_le {Ω X : Type*} [Fintype X] (μ : PMF Ω)
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hw₁ : ∑ x, w x = 1) (P : Ω → X → Prop)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ x, μ.toOuterMeasure {ω | P ω x} ≤ ENNReal.ofReal δ) :
    ∑' ω, (μ ω).toReal * ∑ x, (if P ω x then w x else 0) ≤ δ := by
  classical
  apply Real.tsum_le_of_sum_le
  · intro ω
    exact mul_nonneg ENNReal.toReal_nonneg (sum_nonneg fun x _ ↦ by split <;> simp_all)
  intro u
  have column (x : X) : (∑ ω ∈ u, if P ω x then (μ ω).toReal else 0) ≤ δ := by
    let V := {ω | P ω x}
    have hfin (ω : Ω) : V.indicator μ ω ≠ ⊤ := by
      by_cases hv : ω ∈ V <;> simp [hv, μ.apply_ne_top]
    have H : ∑ ω ∈ u, V.indicator μ ω ≤ ENNReal.ofReal δ :=
      (sum_le_tsum u).trans ((μ.toOuterMeasure_apply V).symm.le.trans (h x))
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top H
    rw [ENNReal.toReal_ofReal hδ, ENNReal.toReal_sum (fun ω _ ↦ hfin ω)] at this
    simpa [V, Set.indicator_apply, apply_ite ENNReal.toReal] using this
  simp_rw [mul_sum]
  rw [sum_comm]
  calc
    _ = ∑ x, (∑ ω ∈ u, if P ω x then (μ ω).toReal else 0) * w x := by
      refine sum_congr rfl fun x _ ↦ ?_
      rw [sum_mul]
      exact sum_congr rfl fun ω _ ↦ by by_cases hp : P ω x <;> simp [hp]
    _ ≤ ∑ x, δ * w x := sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_right (column x) (hw x)
    _ = δ := by rw [← mul_sum, hw₁, mul_one]

open MultiBlock SigabaNeo.SampleDeletion

/-- A uniform bound on the seed mass of each sample event bounds its mean LWE probability. -/
theorem lweProb_pmf_seed_average_le {m n q η : ℕ} [Fact q.Prime] {Ω : Type*} (μ : PMF Ω)
    (P : Ω → (Fin n → Digit η) → (Fin m → Digit η) → Matrix (Fin m) (Fin n) (ZMod q) → Prop)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ s e A, μ.toOuterMeasure {ω | P ω s e A} ≤ ENNReal.ofReal δ) :
    ∑' ω, (μ ω).toReal * (Attack.lweProb m n q η (P ω) : ℝ) ≤ δ := by
  classical
  let X := (Fin n → Digit η) × (Fin m → Digit η) × Matrix (Fin m) (Fin n) (ZMod q)
  let w (x : X) : ℝ := ((∏ j, (mass (x.1 j) : ℝ)) * ∏ j, (mass (x.2.1 j) : ℝ)) /
    (((4 ^ η : ℕ) : ℝ) ^ (m + n) * (q : ℝ) ^ (n * m))
  have expand (Q : (Fin n → Digit η) → (Fin m → Digit η) →
      Matrix (Fin m) (Fin n) (ZMod q) → Prop) :
      (Attack.lweProb m n q η Q : ℝ) = ∑ x : X, if Q x.1 x.2.1 x.2.2 then w x else 0 := by
    simp only [X, Fintype.sum_prod_type, Attack.lweProb, Rat.cast_div, Rat.cast_sum,
      Rat.cast_mul, Rat.cast_prod, Rat.cast_pow, Rat.cast_natCast, apply_ite Rat.cast,
      Rat.cast_zero, sum_div, w]
    refine sum_congr rfl fun s _ ↦ sum_congr rfl fun e _ ↦ sum_congr rfl fun A _ ↦ ?_
    split <;> simp_all
  have hfalse : Attack.lweProb m n q η (fun _ _ _ ↦ False) = 0 := by simp [Attack.lweProb]
  have htrue := Attack.lweProb_not m n q η (fun _ _ _ ↦ False)
  simp only [not_false_eq_true, hfalse, sub_zero] at htrue
  have total := expand (fun _ _ _ ↦ True)
  simp only [htrue, Rat.cast_one, ite_true] at total
  simp_rw [expand]
  exact pmf_seed_average_le μ w (fun x ↦ by dsimp [w]; positivity) total.symm
    (fun ω x ↦ P ω x.1 x.2.1 x.2.2) δ hδ (fun x ↦ h x.1 x.2.1 x.2.2)

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.lweProb_pmf_seed_average_le
