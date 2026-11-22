module

public import SigabaNeo.Lib.Lattices.Research.Wall1.FixedBlockCount
import all SigabaNeo.Lib.Lattices.Research.Wall1.FixedBlockCount
import all SigabaNeo.Lib.Lattices.Research.Wall1.HeightZeroFloor
import all SigabaNeo.Lib.Lattices.Research.Wall1.CBDTail
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic

/-! # The projected CBD norm tail in Part 175 -/

public section
namespace SigabaNeo.Wall1.FinalBlock

open Classical SampleDeletion CBDTail MeasureTheory GaussianFourier
open InnerProductSpace LinearMap
open scoped RealInnerProductSpace

private theorem gaussianIntegral {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (b c : ℝ) (hb : 0 < b) (y : E) :
    Integrable (fun u : E ↦ Real.exp (-b * ‖u‖^2 + c * ⟪y,u⟫)) ∧
    (∫ u : E, Real.exp (-b * ‖u‖^2 + c * ⟪y,u⟫)) =
      (Real.pi / b) ^ ((Module.finrank ℝ E : ℝ)/2) * Real.exp (c^2 * ‖y‖^2/(4*b)) := by
  have h := integrable_cexp_neg_mul_sq_norm_add (b := (b : ℂ)) hb c y
  have conv (u : E) : Complex.exp (-(b : ℂ) * ‖u‖^2 + c * ⟪y,u⟫) =
      (Real.exp (-b * ‖u‖^2 + c * ⟪y,u⟫) : ℂ) := by push_cast; rfl
  constructor
  · simpa only [conv, RCLike.re_to_complex, Complex.ofReal_re] using h.re
  · apply Complex.ofReal_injective
    rw [Complex.ofReal_mul, ← integral_complex_ofReal]
    simp_rw [← conv]
    rw [integral_cexp_neg_mul_sq_norm_add hb]
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast
    rfl

variable {N d : ℕ} (B : FinalBlock N d)

/-- Gaussian integration of the product linear MGF on the image of Q. -/
theorem energy_mgf {t : ℝ} (ht : 0 ≤ t) (ht' : 0 < 1-3*t) :
    (∑ w : Plant N, jointWeight w * Real.exp (t * ‖projectedCBD B.Q w‖^2)) ≤
      (1 / (1-3*t)) ^ ((d : ℝ)/2) := by
  let f := B.Q.toEuclideanLin
  let E := LinearMap.range f
  let x (w : Plant N) : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (fun i ↦ (centered (w i) : ℝ))
  let y (w : Plant N) : E := ⟨f (x w), x w, rfl⟩
  have idem : IsIdempotentElem f := by
    change (B.Q.toEuclideanLin.comp B.Q.toEuclideanLin) = _
    rw [← Matrix.toLpLin_mul_same, B.idempotent]
  have rank : Module.finrank ℝ E = d := by
    have eq := (LinearMap.isProj_range_iff_isIdempotentElem f).2 idem |>.trace
    have tr : LinearMap.trace ℝ _ f = (d : ℝ) := by
      dsimp only [f]
      rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.trace_eq_matrix_trace _
        (EuclideanSpace.basisFun (Fin N) ℝ).toBasis, LinearMap.toMatrix_toLin, B.trace_eq]
    rw [tr] at eq
    exact_mod_cast eq.symm
  have fix (u : E) : B.Q.mulVec (WithLp.ofLp u.val) = WithLp.ofLp u.val := by
    obtain ⟨v, hv⟩ := u.2
    have eq := congrArg (fun l : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] _ ↦ l v) idem
    change f (f v) = f v at eq
    rw [hv] at eq
    exact congrArg WithLp.ofLp eq
  have innerEq (w : Plant N) (u : E) : ⟪y w, u⟫ = projection (WithLp.ofLp u.val) w := by
    change ⟪projectedCBD B.Q w, u.val⟫ = _
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, projectedCBD, WithLp.ofLp_toLp,
      ← Matrix.dotProduct_transpose_mulVec, B.symmetric, fix, dotProduct_comm]
    rfl
  let c := 2 * √t
  have csq : c^2 = 4*t := by dsimp [c]; nlinarith [Real.sq_sqrt ht]
  let F (w : Plant N) (u : E) := Real.exp (-1 * ‖u‖^2 + c * ⟪y w,u⟫)
  let G (u : E) := Real.exp (-(1-3*t) * ‖u‖^2)
  have each w := gaussianIntegral 1 c one_pos (y w)
  have hG := gaussianIntegral (1-3*t) 0 ht' (0 : E)
  have point (u : E) : ∑ w, jointWeight w * F w u ≤ G u := by
    have mgf := product_mgf_le (WithLp.ofLp u.val) c
    rw [← EuclideanSpace.real_norm_sq_eq u.val] at mgf
    have le := mul_le_mul_of_nonneg_left mgf (Real.exp_pos (-1 * ‖u‖^2)).le
    rw [Finset.mul_sum, ← Real.exp_add] at le
    dsimp only [F, G]
    simp_rw [Real.exp_add, innerEq, mul_left_comm (jointWeight _) (Real.exp _)]
    convert le using 1
    congr 1
    change -(1-3*t) * ‖u‖^2 = -1 * ‖u‖^2 + 3*c^2/4 * ‖u‖^2
    rw [csq]; ring
  have hInt (w : Plant N) : Integrable (fun u ↦ jointWeight w * F w u) :=
    (each w).1.const_mul _
  have int := integral_mono (integrable_finsetSum _ fun w _ ↦ hInt w)
    (show Integrable G by simpa [G] using hG.1) point
  rw [integral_finsetSum _ fun w _ ↦ hInt w] at int
  have eval w : (∫ u, F w u) = Real.pi ^ ((d : ℝ)/2) *
      Real.exp (t * ‖projectedCBD B.Q w‖^2) := by
    rw [show (∫ u, F w u) = _ from (each w).2, rank, div_one, csq]
    congr 2
    change 4*t * ‖projectedCBD B.Q w‖^2/(4*1) = _
    ring
  change (∑ w : Plant N, ∫ u : E, jointWeight w * F w u) ≤ ∫ u : E, G u at int
  simp_rw [integral_const_mul, eval] at int
  have distributed (w : Plant N) :
      jointWeight w * (Real.pi ^ ((d : ℝ)/2) * Real.exp (t * ‖projectedCBD B.Q w‖^2)) =
        Real.pi ^ ((d : ℝ)/2) * (jointWeight w * Real.exp (t * ‖projectedCBD B.Q w‖^2)) :=
    mul_left_comm _ _ _
  simp only [distributed] at int
  rw [← Finset.mul_sum] at int
  have evalG : (∫ u, G u) = (Real.pi/(1-3*t)) ^ ((d : ℝ)/2) := by
    simpa [G, rank] using hG.2
  rw [evalG, show Real.pi / (1-3*t) = Real.pi * (1/(1-3*t)) by ring,
    Real.mul_rpow Real.pi_pos.le (by positivity)] at int
  exact (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos Real.pi_pos _)).mp int

/-- The explicit cap charge in the note, with v = 2a/(3d). -/
noncomputable def normChernoff (d : ℕ) (a : ℝ) : ℝ :=
  let v := 2*a / (3*d)
  Real.exp (-(d : ℝ) * (v-1-Real.log v) / 2)

theorem capTail_le_normChernoff {a : ℝ} (hd : 0 < d) (ha : 3*(d : ℝ)/2 < a) :
    B.capTail a ≤ normChernoff d a := by
  let v := 2*a/(3*d)
  let t := (1-1/v)/3
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  have hv : 1 < v := (lt_div_iff₀ (by positivity)).2 (by linarith)
  have hv0 := zero_lt_one.trans hv
  have ht : 0 ≤ t := by dsimp [t]; have := (one_div_lt_one_div_of_lt zero_lt_one hv); linarith
  have β : 1-3*t = 1/v := by dsimp [t]; ring
  have mgf := B.energy_mgf ht (by rw [β]; positivity)
  rw [β, one_div_one_div, Real.rpow_def_of_pos hv0] at mgf
  have mk : B.capTail a * Real.exp (t*a) ≤
      ∑ w : Plant N, jointWeight w * Real.exp (t * ‖projectedCBD B.Q w‖^2) := by
    unfold capTail cbdMass
    rw [Finset.sum_mul, Finset.sum_filter]
    refine Finset.sum_le_sum fun w _ ↦ ?_
    split_ifs with hw
    · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hw.le ht)) (weightNonneg _)
    · exact mul_nonneg (weightNonneg _) (Real.exp_pos _).le
  have h := (le_div_iff₀ (Real.exp_pos _)).2 (mk.trans mgf)
  rw [← Real.exp_sub] at h
  suffices eq : Real.log v * ((d : ℝ)/2) - t*a = -(d : ℝ) * (v-1-Real.log v)/2 by
    exact h.trans_eq (congrArg Real.exp eq)
  have va : v * (3*d) = 2*a := div_mul_cancel₀ _ (by positivity)
  dsimp [t]
  field_simp [hv0.ne']
  nlinarith [congrArg (fun z : ℝ ↦ z*v) va]

/-- Formula (1) with the explicit Chernoff tail, the primal height-one sum, and
the exact higher-height CBD counts. Outside the cap test's domain the bound is one. -/
noncomputable def smoothError (a L : ℝ) : ℝ :=
  if 0 < d ∧ 3*(d : ℝ)/2 < a ∧ √(1+a) < L then
    min 1 (normChernoff d a + B.oneCharge a L +
      ∑ k ∈ Finset.Icc 2 ⌊√(1+a)⌋₊, B.highCharge a L k)
  else 1

/-- The audited fixed-block bound on failure of the signed-plant event. -/
theorem failure_le_smoothError {a L : ℝ} (floor : B.MinFloor L) :
    1 - B.success ≤ B.smoothError a L := by
  apply (B.failure_le_countError (a := a) floor).trans
  unfold smoothError countError
  split_ifs with strict domain domain
  · apply min_le_min_left
    exact add_le_add_left (add_le_add_left
      (B.capTail_le_normChernoff domain.1 domain.2.1) _) _
  · exact min_le_left _ _
  · exact (strict domain.2.2).elim
  · rfl

end SigabaNeo.Wall1.FinalBlock

#print axioms SigabaNeo.Wall1.FinalBlock.capTail_le_normChernoff
#print axioms SigabaNeo.Wall1.FinalBlock.failure_le_smoothError
