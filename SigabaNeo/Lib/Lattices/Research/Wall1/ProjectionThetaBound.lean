module

public import SigabaNeo.Lib.Lattices.Research.Wall1.GaussianGramPivots
public import SigabaNeo.Lib.Lattices.Research.Wall1.LogThetaConvex
import all SigabaNeo.Lib.Lattices.Research.Wall1.GaussianGramPivots
import all SigabaNeo.Lib.Lattices.Research.Wall1.ThetaProfile
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

/-! # Gaussian mass under a balanced Gram-pivot test -/

public section
namespace SigabaNeo.Wall1
open Real Matrix Unitary
open scoped Matrix

variable {N : ℕ}

private theorem theta_pos {a : ℝ} (ha : 0 < a) : 0 < thetaFactor a := by
  have h := (summable_int_gauss ha).sum_le_tsum ({0} : Finset ℤ) (fun n _ ↦ (exp_pos _).le)
  exact one_pos.trans_le (by simpa [thetaFactor] using h)

/-- Positive consecutive Gram pivots telescope to the metric determinant in a unimodular basis. -/
theorem prod_gramPivot (Q : Matrix (Fin N) (Fin N) ℝ) (U : Matrix (Fin N) (Fin N) ℤ)
    (hu : U.det = 1 ∨ U.det = -1) (hp : ∀ j, 0 < gramPivot Q U j) :
    ∏ j, gramPivot Q U j = Q.det := by
  have aux (k : ℕ) (hk : k ≤ N) :
      ∏ j : Fin k, gramPivot Q U (Fin.castLE hk j) = leadingGramDet Q U k hk := by
    induction k with
    | zero => simp [leadingGramDet]
    | succ k ih =>
      let j : Fin N := ⟨k, hk⟩
      rw [Fin.prod_univ_castSucc]
      change (∏ i : Fin k, gramPivot Q U (Fin.castLE (by omega) i)) * gramPivot Q U j = _
      rw [ih]
      have nz := (div_ne_zero_iff.mp (hp j).ne').2
      change leadingGramDet Q U j j.isLt.le * (_ / leadingGramDet Q U j j.isLt.le) = _
      field_simp [nz]
      rfl
  let A := U.map (Int.castRingHom ℝ)
  have h := aux N le_rfl
  change ∏ j, gramPivot Q U j = (Aᵀ * Q * A).det at h
  rw [h, det_mul, det_mul, det_transpose]
  have hA : A.det = (U.det : ℝ) := (RingHom.map_det (Int.castRingHom ℝ) U).symm
  rcases hu with hu|hu <;> simp [hA, hu]

/-- The determinant of a two-eigenvalue metric on a projected subspace and its complement. -/
theorem det_projectionMetric (P : Matrix (Fin N) (Fin N) ℝ) (d : ℕ) (hP : P.IsHermitian)
    (idem : P*P = P) (trace : P.trace = d) (γ v : ℝ) :
    (γ • (1-P) + v • P).det = γ^(N-d)*v^d := by
  classical
  let l := hP.eigenvalues
  let A := conjStarAlgAut ℝ _ hP.eigenvectorUnitary
  have e : P = A (diagonal l) := by simpa [A, l, Function.comp_def] using hP.spectral_theorem
  have id : diagonal l * diagonal l = diagonal l := A.injective (by
    change A (_ * _) = A _
    rw [map_mul, ← e, idem])
  have cases (j) : l j = 0 ∨ l j = 1 := by
    rw [diagonal_mul_diagonal'] at id
    have tmp := congrFun (diagonal_injective id) j
    change l j*l j = l j at tmp
    exact eq_zero_or_one_of_sq_eq_self (by simpa [sq] using tmp)
  let S := Finset.univ.filter (fun i ↦ l i = 1)
  have eq (i : Fin N) : l i = if l i = 1 then 1 else 0 := by
    rcases cases i with h|h <;> simp [h]
  have count : S.card = d := by
    have ht : (∑ i, l i) = (d : ℝ) := by simpa [l] using hP.trace_eq_sum_eigenvalues.symm.trans trace
    conv_lhs at ht => arg 2; intro i; rw [eq i]
    exact_mod_cast (show (S.card : ℝ) = d by simpa [S, ← Finset.sum_filter] using ht)
  have ed : γ • (1-P) + v • P = A (diagonal (fun i ↦ γ*(1-l i)+v*l i)) := by
    rw [e, ← map_one A, ← map_sub, ← map_smul, ← map_smul, ← map_add]
    congr 1
    rw [← diagonal_one', diagonal_sub, ← diagonal_smul, ← diagonal_smul, diagonal_add]
    rfl
  rw [ed, show ∀ X, (A X).det = X.det from fun X ↦ Matrix.det_conj_of_mul_eq_one
      (coe_mul_star_self hP.eigenvectorUnitary) (coe_star_mul_self hP.eigenvectorUnitary),
    det_diagonal]
  have rows i : γ*(1-l i)+v*l i = if i ∈ S then v else γ := by
    rcases cases i with h|h <;> simp [S, h]
  simp_rw [rows]
  rw [Finset.prod_ite]
  simp [S, ← count, Finset.filter_not, Finset.card_sdiff_of_subset (Finset.subset_univ _), mul_comm]

/-- Secant comparison with arbitrary log-mean weights, covering the unequal
endpoint multiplicities of (4) and the equal weights of (5). -/
theorem thetaProduct_secant (p : Fin N → ℝ) {a b w : ℝ} (ha : 0 < a) (hab : a < b)
    (bounds : ∀ j, a ≤ p j ∧ p j ≤ b)
    (mean : ∑ j, log (p j) = w*log a + ((N : ℝ)-w)*log b) :
    ∏ j, thetaFactor (p j) ≤ thetaFactor a ^ w * thetaFactor b ^ ((N : ℝ)-w) := by
  let F x := log (thetaFactor (exp x))
  have hp j := ha.trans_le (bounds j).1
  have hb := ha.trans hab
  have h := sum_logPivot_secant F p (log_lt_log ha hab)
    (logTheta_convex.subset (Set.subset_univ _) (convex_Icc _ _))
    (fun j ↦ ⟨log_le_log ha (bounds j).1, log_le_log (hp j) (bounds j).2⟩) mean
  simp only [F, exp_log ha, exp_log hb, exp_log (hp _)] at h
  rw [← log_prod (fun j _ ↦ (theta_pos (hp j)).ne')] at h
  apply (log_le_log_iff (Finset.prod_pos (fun j _ ↦ theta_pos (hp j))) (mul_pos
    (rpow_pos_of_pos (theta_pos ha) _) (rpow_pos_of_pos (theta_pos hb) _))).mp
  simpa [log_mul (rpow_pos_of_pos (theta_pos ha) _).ne' (rpow_pos_of_pos (theta_pos hb) _).ne',
    log_rpow (theta_pos ha), log_rpow (theta_pos hb), mul_comm] using h

/-- Equation (5) for a positive definite metric with pivot geometric mean `m`. -/
theorem integerTheta_balanced (Q : Matrix (Fin N) (Fin N) ℝ) (hq : Q.PosDef)
    (U : Matrix (Fin N) (Fin N) ℤ) (hu : U.det = 1 ∨ U.det = -1)
    {m c : ℝ} (hm : 0 < m) (hc : 1 < c) (det : Q.det = m^N)
    (bounds : ∀ j, m/c ≤ gramPivot Q U j ∧ gramPivot Q U j ≤ c*m) :
    (∑' z : Fin N → ℤ, exp (-((fun j ↦ (z j : ℝ)) ⬝ᵥ (Q *ᵥ (fun j ↦ (z j : ℝ)))))) ≤
      (thetaFactor (m/c) * thetaFactor (c*m))^((N : ℝ)/2) := by
  have hc0 := zero_lt_one.trans hc
  let p := gramPivot Q U
  have ha := div_pos hm hc0
  have hp j : 0 < p j := ha.trans_le (bounds j).1
  have hab : m/c < c*m := (div_lt_self hm hc).trans (lt_mul_of_one_lt_left hm hc)
  have total := congrArg log ((prod_gramPivot Q U hu hp).trans det)
  rw [log_prod (fun j _ ↦ (hp j).ne'), log_pow] at total
  have mean : ∑ j, log (p j) = ((N : ℝ)/2)*log (m/c) + (N-N/2:ℝ)*log (c*m) := by
    rw [log_div hm.ne' hc0.ne', log_mul hc0.ne' hm.ne', total]; ring
  have bound := thetaProduct_secant p ha hab bounds mean
  rw [show (N : ℝ)-N/2 = N/2 by ring, ← mul_rpow (theta_pos ha).le (theta_pos (mul_pos hc0 hm)).le]
    at bound
  exact (integerTheta_le_gramPivots Q hq U (by rcases hu with h|h <;> simp [h])).trans bound

private theorem projectionMetric_bounds (P : Matrix (Fin N) (Fin N) ℝ)
    (hP : P.IsHermitian) (idem : P*P = P) {v γ : ℝ} (hv : 0 < v) (hvg : v ≤ γ) :
    let Q := γ • (1-P) + v • P
    Q.PosDef ∧ ∀ x : Fin N → ℝ, v*(x ⬝ᵥ x) ≤ x ⬝ᵥ Q *ᵥ x ∧ x ⬝ᵥ Q *ᵥ x ≤ γ*(x ⬝ᵥ x) := by
  intro Q
  have hI : (1-P).IsHermitian := isHermitian_one.sub hP
  have comp : (1-P)*(1-P) = 1-P := by simp [sub_mul, mul_sub, idem]
  have psd (T : Matrix (Fin N) (Fin N) ℝ) (ht : T.IsHermitian) (hi : T*T = T) : T.PosSemidef := by
    simpa only [ht.eq, hi] using posSemidef_conjTranspose_mul_self T
  have bounds (x : Fin N → ℝ) : v*(x ⬝ᵥ x) ≤ x ⬝ᵥ Q *ᵥ x ∧ x ⬝ᵥ Q *ᵥ x ≤ γ*(x ⬝ᵥ x) := by
    have h₁ := (psd P hP idem).dotProduct_mulVec_nonneg x
    have h₂ := (psd _ hI comp).dotProduct_mulVec_nonneg x
    simp only [star_trivial, sub_mulVec, one_mulVec, dotProduct_sub] at h₁ h₂
    dsimp only [Q]
    simp only [add_mulVec, smul_mulVec, sub_mulVec, one_mulVec, dotProduct_add, dotProduct_smul,
      dotProduct_sub, smul_eq_mul]
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hvg) h₁, mul_nonneg (sub_nonneg.mpr hvg) h₂]
  refine ⟨.of_dotProduct_mulVec_pos ((hI.smul (isSelfAdjoint_iff.mpr (star_trivial γ))).add
    (hP.smul (isSelfAdjoint_iff.mpr (star_trivial v)))) ?_, bounds⟩
  intro x hx
  rw [star_trivial]
  exact (mul_pos hv (by simpa only [star_trivial] using (dotProduct_star_self_pos_iff.mpr hx))).trans_le
    (bounds x).1

/-- Equation (5) specialized to the projection metric and the geometric mean in the test. -/
theorem theta_of_gramProjectionTest (P : Matrix (Fin N) (Fin N) ℝ) {d : ℕ} (hN : 0 < N)
    (hP : P.IsHermitian) (idem : P*P = P) (trace : P.trace = d) (hd : d ≤ N)
    {γ D c : ℝ} (hg : 0 < γ) (hD : 1 ≤ D) (hc : 1 < c)
    (test : gramProjectionTest P d γ D c) :
    let Q := γ • (1-P) + (γ/D) • P
    let m := γ * D^(-(d : ℝ)/N)
    (∑' z : Fin N → ℤ, exp (-((fun j ↦ (z j : ℝ)) ⬝ᵥ (Q *ᵥ (fun j ↦ (z j : ℝ)))))) ≤
      (thetaFactor (m/c)*thetaFactor (c*m))^((N : ℝ)/2) := by
  intro Q m
  obtain ⟨U, hu, pivots⟩ := test
  have hD0 := zero_lt_one.trans_le hD
  apply integerTheta_balanced Q (projectionMetric_bounds P hP idem
    (div_pos hg hD0) (div_le_self hg.le hD)).1 U hu (mul_pos hg (rpow_pos_of_pos hD0 _)) hc _ pivots
  rw [det_projectionMetric P d hP idem trace]
  rw [mul_pow, ← rpow_mul_natCast hD0.le, div_mul_cancel₀ _ (by exact_mod_cast hN.ne'),
    rpow_neg hD0.le, rpow_natCast, div_pow, div_eq_mul_inv, ← mul_assoc, ← pow_add,
    Nat.sub_add_cancel hd]

/-- Standard-coordinate Gram pivots of a metric between two Euclidean scalar forms.
The residual has the current coordinate equal to one, since the prefix has zero there. -/
theorem coordinatePivot_bounds (Q : Matrix (Fin N) (Fin N) ℝ) (hq : Q.PosDef)
    {v γ : ℝ} (hv : 0 < v)
    (bound : ∀ x : Fin N → ℝ, v*(x ⬝ᵥ x) ≤ x ⬝ᵥ Q *ᵥ x ∧ x ⬝ᵥ Q *ᵥ x ≤ γ*(x ⬝ᵥ x))
    (j : Fin N) : v ≤ gramPivot Q 1 j ∧ gramPivot Q 1 j ≤ γ := by
  classical
  let ng := Q.toNormedAddCommGroup hq
  let := Q.toInnerProductSpace hq.posSemidef
  let b := Pi.basisFun ℝ (Fin N)
  have nval (x : Fin N → ℝ) : (@Norm.norm _ ng.toNorm x)^2 = x ⬝ᵥ Q *ᵥ x := by
    rw [← @real_inner_self_eq_norm_sq _ (Q.toSeminormedAddCommGroup hq.posSemidef)
      (Q.toInnerProductSpace hq.posSemidef) x]
    change (Q *ᵥ x) ⬝ᵥ star x = _
    rw [star_trivial, dotProduct_comm]
  have gram : Matrix.gram ℝ b = ((1 : Matrix (Fin N) (Fin N) ℤ).map (Int.castRingHom ℝ))ᵀ *
      Q * (1 : Matrix (Fin N) (Fin N) ℤ).map (Int.castRingHom ℝ) := by
    simp only [Matrix.map_one _ (map_zero _) (map_one _), transpose_one, one_mul, mul_one]
    ext i k
    change (Q *ᵥ b k) ⬝ᵥ star (b i) = _
    simp [b, Pi.basisFun_apply, dotProduct_single]
  let pre := (b : Fin N → (Fin N → ℝ)) ∘ Fin.castLE j.isLt.le
  let K := Submodule.span ℝ (Set.range pre)
  let y := Kᗮ.starProjection (b j)
  have eq := gramPivot_eq_residualSq (E := Fin N → ℝ) b b.linearIndependent Q 1 gram j
  change gramPivot Q 1 j = (@Norm.norm _ ng.toNorm y)^2 at eq
  have zeroj : K ≤ (LinearMap.proj j : (Fin N → ℝ) →ₗ[ℝ] ℝ).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change b (Fin.castLE j.isLt.le i) j = 0
    have hj : Fin.castLE j.isLt.le i ≠ j := by intro h; have := congrArg Fin.val h; simp at this; omega
    simp [b, Pi.basisFun_apply, Pi.single_eq_of_ne hj.symm]
  have val : y j = 1 := by
    have h := congrFun (K.starProjection_add_starProjection_orthogonal (b j)) j
    have hz : (K.starProjection (b j)) j = 0 := zeroj (K.starProjection_apply_mem _)
    change (K.starProjection (b j)) j + y j = b j j at h
    rw [hz, zero_add] at h
    exact h.trans (by simp [b, Pi.basisFun_apply])
  have ly : 1 ≤ y ⬝ᵥ y := by
    simpa only [dotProduct, val, one_mul] using Finset.single_le_sum (f := fun i ↦ y i*y i)
      (fun i _ ↦ mul_self_nonneg _) (Finset.mem_univ j)
  have upper := pow_le_pow_left₀ (@norm_nonneg _ ng.toSeminormedAddCommGroup.toSeminormedAddGroup y)
    (Kᗮ.norm_starProjection_apply_le (b j)) 2
  rw [eq, nval]
  refine ⟨(le_mul_of_one_le_right hv.le ly).trans (bound y).1, ?_⟩
  have hby : b j ⬝ᵥ b j = 1 := by simp [b, Pi.basisFun_apply, dotProduct_single]
  change (@Norm.norm _ ng.toNorm y)^2 ≤ (@Norm.norm _ ng.toNorm (b j))^2 at upper
  rw [nval, nval] at upper
  exact upper.trans ((bound (b j)).2.trans_eq (by rw [hby, mul_one]))

/-- Equation (4), for every orthogonal projection of the indicated trace. -/
theorem theta_projection_uniform (P : Matrix (Fin N) (Fin N) ℝ) {d : ℕ} (hP : P.IsHermitian)
    (idem : P*P = P) (trace : P.trace = d) (hd : d ≤ N)
    {v γ : ℝ} (hv : 0 < v) (hg : v < γ) :
    let Q := γ • (1-P) + v • P
    (∑' z : Fin N → ℤ, exp (-((fun j ↦ (z j : ℝ)) ⬝ᵥ (Q *ᵥ (fun j ↦ (z j : ℝ)))))) ≤
      thetaFactor γ^(N-d)*thetaFactor v^d := by
  intro Q
  obtain ⟨hq,bounds⟩ := projectionMetric_bounds P hP idem hv hg.le
  have piv := coordinatePivot_bounds Q hq hv bounds
  have hu : (1 : Matrix (Fin N) (Fin N) ℤ).det = 1 := Matrix.det_one
  have prod := prod_gramPivot Q 1 (Or.inl hu) (fun j ↦ hv.trans_le (piv j).1)
  rw [det_projectionMetric P d hP idem trace] at prod
  have total := congrArg log prod
  rw [log_prod (fun j _ ↦ (hv.trans_le (piv j).1).ne'), log_mul (pow_pos (hv.trans hg) _).ne'
    (pow_pos hv _).ne', log_pow, log_pow, Nat.cast_sub hd, add_comm] at total
  have cmp := thetaProduct_secant _ hv hg piv total
  rw [rpow_natCast, ← Nat.cast_sub hd, rpow_natCast, mul_comm] at cmp
  exact (integerTheta_le_gramPivots Q hq 1 (by simp)).trans cmp

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.prod_gramPivot
#print axioms SigabaNeo.Wall1.det_projectionMetric
#print axioms SigabaNeo.Wall1.thetaProduct_secant
#print axioms SigabaNeo.Wall1.integerTheta_balanced

#print axioms SigabaNeo.Wall1.theta_of_gramProjectionTest
#print axioms SigabaNeo.Wall1.coordinatePivot_bounds
#print axioms SigabaNeo.Wall1.theta_projection_uniform
