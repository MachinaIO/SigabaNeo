import SigabaNeo.Lib.Lattices.Research.Wall1.FixedBlockIntegralAliases
import SigabaNeo.Lib.Lattices.Research.Wall1.FixedBlockCount
import SigabaNeo.Lib.Lattices.Research.Wall1.HeightZeroFloor

/-! # Gaussian majorization of the finite, shifted closed-ball count -/

noncomputable section
namespace SigabaNeo.Wall1.FinalBlock

open ZLattice ProbabilityTheory CBDTail Classical
open scoped RealInnerProductSpace

variable {N d : ℕ} (B : FinalBlock N d)

/-- The horizontal lattice in the subspace's intrinsic Euclidean metric. -/
abbrev horizontal := Submodule.span ℤ (Set.range B.basis)

def modeWeight (s : ℝ) (k : ℕ) (w : metricDual B.horizontal) : ℝ :=
  gaussianWeight (1/s) w.val * ∏ i, Real.cos (Real.pi * (k * w.val.val i))^6

def prefactor (a s : ℝ) (k : ℕ) : ℝ :=
  Real.exp (Real.pi * (1+a-(k:ℝ)^2) / s^2) * s^d / covolume B.horizontal

private theorem summable_modes {s : ℝ} (hs : 0 < s) (k : ℕ) : Summable (B.modeWeight s k) := by
  let D := metricDual B.horizontal
  let : DiscreteTopology D := discreteTopology_dualSubmodule B.horizontal
  have hg := summable_gaussianWeight D (1/s) (by positivity) 0
  simp only [sub_zero] at hg
  apply Summable.of_nonneg_of_le (fun w ↦ mul_nonneg (gaussianWeight_pos _ _).le
    (Finset.prod_nonneg fun _ _ ↦ by positivity)) _ hg
  intro w
  apply mul_le_of_le_one_right (gaussianWeight_pos _ _).le
  apply Finset.prod_le_one₀ (fun _ _ ↦ by positivity)
  intro i _
  calc
    _ ≤ |Real.cos (Real.pi * ((k:ℝ)*w.val.val i))|^6 := by rw [← abs_pow]; exact le_abs_self _
    _ ≤ 1 := pow_le_one₀ (abs_nonneg _) (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)

/-- Residue classes are taken in the retained space modulo its ambient integer section. -/
def dualClass (w : metricDual B.horizontal) := (stdSection B.V).mkQ w.val

theorem modeSum_by_class {s : ℝ} (hs : 0 < s) (k : ℕ) :
    (∑' w, B.modeWeight s k w) = ∑' c : B.V ⧸ stdSection B.V,
      ∑' w : B.dualClass ⁻¹' {c}, B.modeWeight s k w.val :=
  ((B.summable_modes hs k).hasSum.tsum_fiberwise B.dualClass).tsum_eq.symm

/-- The CBD characteristic function on a residue class. -/
def classWeight (k : ℕ) (c : B.V ⧸ stdSection B.V) :=
  ∏ i, Real.cos (Real.pi * (k * c.out.val i))^6

private theorem classWeight_mk (k : ℕ) (w : metricDual B.horizontal) :
    B.classWeight k (B.dualClass w) =
      ∏ i, Real.cos (Real.pi * (k * w.val.val i))^6 := by
  let c := B.dualClass w
  have sub : c.out - w.val ∈ stdSection B.V :=
    (Submodule.Quotient.eq (stdSection B.V)).mp (Submodule.Quotient.mk_out c)
  apply Finset.prod_congr rfl
  intro i _
  obtain ⟨z, hz⟩ := section_coords B.V ⟨_, sub⟩ i
  change (z:ℝ) = c.out.val i - w.val.val i at hz
  change Real.cos (Real.pi * ((k:ℝ)*c.out.val i))^6 = _
  have arg : Real.pi * ((k:ℝ)*c.out.val i) = Real.pi * (k*w.val.val i) +
      (((k:ℤ)*z:ℤ):ℝ)*Real.pi := by push_cast; rw [hz]; ring
  rw [arg, Real.cos_add_int_mul_pi, mul_pow]
  have unit : ((-1:ℝ)^((k:ℤ)*z))^6 = 1 := by
    have ab : |(-1:ℝ)^((k:ℤ)*z)| = 1 := by simp [abs_zpow]
    calc
      _ = |(-1:ℝ)^((k:ℤ)*z)|^6 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
      _ = 1 := by rw [ab]; norm_num
  rw [unit, one_mul]

/-- The cos^6 factor can be taken outside the sum over lifts of each class. Empty
fibers have zero Gaussian mass. -/
theorem modeSum_class_gaussians {s : ℝ} (hs : 0 < s) (k : ℕ) :
    (∑' w, B.modeWeight s k w) = ∑' c : B.V ⧸ stdSection B.V, B.classWeight k c *
      ∑' w : B.dualClass ⁻¹' {c}, gaussianWeight (1/s) w.val.val := by
  rw [B.modeSum_by_class hs k]
  apply tsum_congr
  intro c
  rw [← tsum_mul_left]
  apply tsum_congr
  intro w
  have eq : B.dualClass w.val = c := w.property
  have cw := B.classWeight_mk k w.val
  rw [eq] at cw
  rw [cw, mul_comm]
  rfl

/-- The contribution from the nonzero classes in the quotient by the integer section. -/
def nonintegralModes (s : ℝ) (k : ℕ) := ∑' w : {w : metricDual B.horizontal //
  w.val ∉ stdSection B.V}, B.modeWeight s k w

theorem modes_split {s : ℝ} (hs : 0 < s) (k : ℕ)
    (inside : stdSection B.V ≤ metricDual B.horizontal) :
    (∑' w, B.modeWeight s k w) =
      (∑' w : stdSection B.V, gaussianWeight (1/s) w.val) + B.nonintegralModes s k := by
  let A := {w : metricDual B.horizontal | w.val ∈ stdSection B.V}
  let equiv : A ≃ stdSection B.V :=
    ⟨fun w ↦ ⟨w.val.val, w.property⟩, fun x ↦ ⟨⟨x.val, inside x.property⟩, x.property⟩,
      fun _ ↦ rfl, fun _ ↦ rfl⟩
  rw [← (B.summable_modes hs k).tsum_subtype_add_tsum_subtype_compl A]
  congr 1
  rw [← equiv.tsum_eq]
  apply tsum_congr
  intro w
  unfold modeWeight
  have cos1 i : Real.cos (Real.pi * ((k:ℝ)*w.val.val.val i))^6 = 1 := by
    obtain ⟨z, hz⟩ := section_coords B.V (equiv w) i
    change (z:ℝ) = w.val.val.val i at hz
    rw [← hz, mul_comm Real.pi, ← Int.cast_natCast k, ← Int.cast_mul]
    have ha := Real.abs_cos_int_mul_pi ((k:ℤ)*z)
    calc
      _ = |Real.cos (((k:ℤ)*z:ℤ) * Real.pi)|^6 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
      _ = 1 := by rw [ha]; norm_num

  simp [cos1, equiv]

/-- The integral section lies in the dual when the horizontal lattice is contained in the
projection of the ambient cubic lattice. -/
theorem integral_le_dual (h : B.horizontal ≤
    projectedModule (cubicModule (EuclideanSpace.basisFun (Fin N) ℝ)) B.V) :
    stdSection B.V ≤ metricDual B.horizontal := by
  rw [stdSection, ← metricDual_projected_cubic]
  exact fun _ hw _ hx ↦ hw _ (h hx)

/-- At coprime heights, integrality of k·w is equivalent to integrality of w, provided
q clears the denominators of the dual. -/
theorem exact_alias_iff {q k : ℤ} (hc : IsCoprime q k) (w : metricDual B.horizontal)
    (hq : q • w.val ∈ stdSection B.V) : k • w.val ∈ stdSection B.V ↔ w.val ∈ stdSection B.V := by
  refine ⟨fun hk ↦ ?_, fun hw ↦ (stdSection B.V).smul_mem k hw⟩
  obtain ⟨u, v, eq⟩ := hc
  have h := (stdSection B.V).add_mem ((stdSection B.V).smul_mem u hq)
    ((stdSection B.V).smul_mem v hk)
  rwa [smul_smul, smul_smul, ← add_smul, eq, one_smul] at h

/-- The projected containment qJ ≤ H gives the denominator bound qH* ⊆ T. -/
theorem clears_dual {q : ℤ} (multiple : ∀ j ∈
    projectedModule (cubicModule (EuclideanSpace.basisFun (Fin N) ℝ)) B.V, q • j ∈ B.horizontal)
    (w : metricDual B.horizontal) : q • w.val ∈ stdSection B.V := by
  rw [stdSection, ← metricDual_projected_cubic]
  intro j hj
  have h := w.property _ (multiple j hj)
  change ⟪q • w.val, j⟫ ∈ (1 : Submodule ℤ ℝ)
  change ⟪w.val, q • j⟫ ∈ (1 : Submodule ℤ ℝ) at h
  simpa only [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, real_inner_smul_right] using h

theorem exact_alias_tested {k : ℕ} (hk : k ∈ Finset.Icc 2 30)
    (multiple : ∀ j ∈ projectedModule (cubicModule (EuclideanSpace.basisFun (Fin N) ℝ)) B.V,
      (3329:ℤ) • j ∈ B.horizontal) (w : metricDual B.horizontal) :
    (k:ℤ) • w.val ∈ stdSection B.V ↔ w.val ∈ stdSection B.V := by
  apply B.exact_alias_iff (q := 3329) _ w (B.clears_dual multiple w)
  apply Nat.isCoprime_iff_coprime.mpr
  apply (show Nat.Prime 3329 by norm_num).coprime_iff_not_dvd.mpr
  have := Finset.mem_Icc.mp hk
  exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)

/-- Projection of the integer kernel of a residue map, with each projected point
represented once in the retained space. -/
def projectedIntegerKernel {m q : ℕ} (F : cubicModule (EuclideanSpace.basisFun (Fin N) ℝ) →ₗ[ℤ]
    (Fin m → ZMod q)) : Submodule ℤ B.V :=
  projectedModule (F.ker.map (cubicModule (EuclideanSpace.basisFun (Fin N) ℝ)).subtype) B.V

/-- Both physical lattice inclusions for any modular design matrix acting on the
integer coordinates, before any probability calculation. -/
theorem projectedIntegerKernel_bounds {m q : ℕ}
    (F : cubicModule (EuclideanSpace.basisFun (Fin N) ℝ) →ₗ[ℤ] (Fin m → ZMod q)) :
    B.projectedIntegerKernel F ≤ projectedModule
        (cubicModule (EuclideanSpace.basisFun (Fin N) ℝ)) B.V ∧
      ∀ j ∈ projectedModule (cubicModule (EuclideanSpace.basisFun (Fin N) ℝ)) B.V,
        (q:ℤ) • j ∈ B.projectedIntegerKernel F := by
  constructor
  · rintro _ ⟨_, ⟨x, _, rfl⟩, rfl⟩
    exact ⟨_, x.property, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    let z : cubicModule (EuclideanSpace.basisFun (Fin N) ℝ) := ⟨x, hx⟩
    have kern : (q:ℤ) • z ∈ F.ker := by
      rw [LinearMap.mem_ker, map_smul]
      ext i
      simp [zsmul_eq_mul]
    refine ⟨(q:ℤ) • x, ⟨(q:ℤ) • z, kern, rfl⟩, ?_⟩
    exact map_zsmul _ _ _

private theorem projection_eq (x : Plant N) :
    B.V.orthogonalProjectionOnto (projectedCBD B.Q x) =
      B.V.orthogonalProjectionOnto (cbdVector x) := by
  apply ext_inner_left ℝ
  intro u
  rw [B.V.inner_orthogonalProjectionOnto_eq_of_mem_left,
    B.V.inner_orthogonalProjectionOnto_eq_of_mem_left, real_inner_comm (projectedCBD B.Q x) u.val,
    real_inner_comm (cbdVector x) u.val]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, projectedCBD,
    ← Matrix.dotProduct_transpose_mulVec, B.symmetric, B.fixed, cbdVector]
  exact dotProduct_comm _ _

/-- The Gaussian majorizes the closed-ball indicator, including the boundary. -/
theorem ballMoment_le_dual {s a : ℝ} (hs : 0 < s) (k : ℕ) (hr : 0 ≤ 1+a-(k:ℝ)^2) :
    B.ballMoment a k ≤ B.prefactor a s k * ∑' w, B.modeWeight s k w := by
  let C := Real.exp (Real.pi * (1+a-(k:ℝ)^2)/s^2)
  let P (w : Plant N) := (k:ℝ) • B.V.orthogonalProjectionOnto (cbdVector w)
  have each w : ((B.ballSection ((k:ℝ) • projectedCBD B.Q w) (√(1+a-(k:ℝ)^2))).card : ℝ) ≤
      C * gaussianMass B.horizontal s (-(P w)) := by
    let F := B.ballSection ((k:ℝ) • projectedCBD B.Q w) (√(1+a-(k:ℝ)^2))
    let K := F.subtype (· ∈ B.horizontal)
    have mem h (hh : h ∈ F) : h ∈ B.horizontal ∧ ‖h.val + (k:ℝ) • projectedCBD B.Q w‖ ≤
        √(1+a-(k:ℝ)^2) := by simpa [F, ballSection] using hh
    have card : K.card = F.card := by
      rw [Finset.card_subtype, Finset.filter_true_of_mem fun h hh ↦ (mem h hh).1]
    let f (z : B.horizontal) := C * gaussianWeight s (z.val - -(P w))
    have point z (hz : z ∈ K) : 1 ≤ f z := by
      have hm := (mem _ (Finset.mem_subtype.mp hz)).2
      have proj := B.V.norm_orthogonalProjectionOnto_apply_le
        (z.val.val + (k:ℝ) • projectedCBD B.Q w)
      rw [map_add, map_smul, B.V.orthogonalProjectionOnto_mem_subspace_eq_self,
        B.projection_eq] at proj
      have ns := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).2 (proj.trans hm)
      rw [Real.sq_sqrt hr] at ns
      dsimp only [f, C, gaussianWeight]
      rw [sub_neg_eq_add, ← Real.exp_add, Real.one_le_exp_iff, ← add_div]
      exact div_nonneg (by nlinarith [mul_le_mul_of_nonneg_left ns Real.pi_pos.le]) (sq_nonneg _)
    have bound := (summable_gaussianWeight B.horizontal s hs (-(P w))).mul_left C
    calc
      (F.card:ℝ) = ∑ _z ∈ K, (1:ℝ) := by simp [card]
      _ ≤ ∑ z ∈ K, f z := Finset.sum_le_sum point
      _ ≤ ∑' z, f z := bound.sum_le_tsum _ fun _ _ ↦ mul_nonneg (Real.exp_pos _).le
        (gaussianWeight_pos _ _).le
      _ = _ := tsum_mul_left
  have total := Finset.sum_le_sum (s := Finset.univ) fun w _ ↦
    mul_le_mul_of_nonneg_left (each w) (show 0 ≤ jointWeight w by unfold jointWeight weight; positivity)
  simp_rw [mul_left_comm (jointWeight _) C, ← Finset.mul_sum] at total
  dsimp only [P] at total
  rw [projectedCBD_gaussian_poisson B.V B.horizontal hs (k:ℝ),
    Module.finrank_eq_card_basis B.basis, Fintype.card_fin] at total
  exact total.trans_eq (by unfold prefactor C modeWeight; ring)

/-- The split majorizes the committed higher-height charge for every tested nonnegative
squared radius, with an explicit determinant in the prefactor. -/
theorem highCharge_le_modes {s a : ℝ} (hs : 0 < s) (L : ℝ) (k : ℕ) (hr : 0 ≤ 1+a-(k:ℝ)^2)
    (inside : stdSection B.V ≤ metricDual B.horizontal) :
    B.highCharge a L k ≤ B.prefactor a s k *
      ((∑' w : stdSection B.V, gaussianWeight (1/s) w.val) + B.nonintegralModes s k) := by
  rw [← B.modes_split hs k inside]
  apply le_trans _ (B.ballMoment_le_dual hs k hr)
  unfold highCharge
  split_ifs
  · exact Finset.sum_nonneg fun x _ ↦ mul_nonneg (show 0 ≤ jointWeight x by
      unfold jointWeight weight; positivity) (Nat.cast_nonneg _)
  · exact min_le_right _ _

end SigabaNeo.Wall1.FinalBlock

#print axioms SigabaNeo.Wall1.FinalBlock.modeSum_by_class
#print axioms SigabaNeo.Wall1.FinalBlock.modes_split
#print axioms SigabaNeo.Wall1.FinalBlock.integral_le_dual
#print axioms SigabaNeo.Wall1.FinalBlock.exact_alias_iff
#print axioms SigabaNeo.Wall1.FinalBlock.ballMoment_le_dual
#print axioms SigabaNeo.Wall1.FinalBlock.modeSum_class_gaussians
#print axioms SigabaNeo.Wall1.FinalBlock.exact_alias_tested
#print axioms SigabaNeo.Wall1.FinalBlock.highCharge_le_modes
#print axioms SigabaNeo.Wall1.FinalBlock.projectedIntegerKernel_bounds
