import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Gaussian sums over `Z` and `Z^m`, in `ℝ≥0∞`

* `tsum_int_geom`: `Σ_{k∈Z} r^|k| = (1 + r)(1 − r)⁻¹`.
* `tsum_pi_prod`: `Σ_{v ∈ Z^m} Π_i g(v_i) = (Σ_k g k)^m`.
* `exp_neg_sq_le`: `e^{−a k²} ≤ e^{−a |k|}` for `a ≥ 0`, and `exp_neg_sq_le'`:
  `e^{−c² k²} ≤ e^{1/4} e^{−c |k|}`.
-/

namespace SigabaNeo.Lattices

open scoped ENNReal

theorem tsum_int_ennreal (f : ℤ → ℝ≥0∞) :
    ∑' k, f k = ∑' n : ℕ, f n + ∑' n : ℕ, f (-(n + 1 : ℤ)) :=
  tsum_of_nat_of_neg_add_one CompleteLattice.summable CompleteLattice.summable

theorem tsum_int_geom (r : ℝ≥0∞) : ∑' k : ℤ, r ^ k.natAbs = (1 + r) * (1 - r)⁻¹ := by
  rw [tsum_int_ennreal]
  have h1 : ∀ n : ℕ, r ^ ((n : ℤ)).natAbs = r ^ n := fun n => by simp
  have h2 : ∀ n : ℕ, r ^ (-(n + 1 : ℤ)).natAbs = r ^ (n + 1) := fun n => by
    congr 1
  simp only [h1, h2, ENNReal.tsum_geometric, ENNReal.tsum_geometric_add_one]
  ring

theorem tsum_pi_prod (g : ℤ → ℝ≥0∞) : ∀ m : ℕ, ∑' v : Fin m → ℤ, ∏ i, g (v i) = (∑' k, g k) ^ m
  | 0 => by simp
  | m + 1 => by
    rw [← (Fin.consEquiv fun _ => ℤ).tsum_eq, tsum_prod']
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    simp only [ENNReal.tsum_mul_left, tsum_pi_prod g m, ENNReal.tsum_mul_right, pow_succ]
    ring

theorem exp_neg_sq_le {a : ℝ} (ha : 0 ≤ a) (k : ℤ) :
    Real.exp (-a * (k : ℝ) ^ 2) ≤ Real.exp (-a) ^ k.natAbs := by
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have : (k.natAbs : ℝ) ≤ (k : ℝ) ^ 2 := by
    have h := Int.natAbs_le_self_sq k
    have : ((k.natAbs : ℤ) : ℝ) ≤ ((k ^ 2 : ℤ) : ℝ) := by exact_mod_cast h
    simpa using this
  nlinarith

theorem exp_neg_sq_le' (c : ℝ) (k : ℤ) :
    Real.exp (-(c ^ 2) * (k : ℝ) ^ 2) ≤ Real.exp (1 / 4) * Real.exp (-c) ^ k.natAbs := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hk : ((k.natAbs : ℕ) : ℝ) = |(k : ℝ)| := by simp
  rw [hk]
  have := sq_abs (k : ℝ)
  nlinarith [sq_nonneg (c * |(k : ℝ)| - 1 / 2), abs_nonneg (k : ℝ)]

end SigabaNeo.Lattices
