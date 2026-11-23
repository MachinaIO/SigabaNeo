import SigabaNeo.Lib.Lattices.Research.Wall1.ControlledSuffixFamily

/-! Mordell's inequality for the intrinsic Hermite constants used in suffix descent. -/

noncomputable section
namespace SigabaNeo.Wall1.ControlledPlane

open Submodule Module Real TerminalProjection DecoupledDecoder
open scoped RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
private theorem inner_nondeg : (innerₗ V).Nondegenerate := by
  constructor <;> intro x hx <;> exact inner_self_eq_zero.mp (hx x)

private theorem bidual (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] :
    metricDual (metricDual L) = L := by
  let b := Free.chooseBasis ℤ L
  rw [← b.ofZLatticeBasis_span ℝ]
  exact LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_basis (innerₗ V) inner_nondeg
    ⟨fun x y ↦ real_inner_comm _ _⟩ _

private theorem dual_volume [MeasurableSpace V] [BorelSpace V] (L : Submodule ℤ V)
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ZLattice.covolume (metricDual L) = (ZLattice.covolume L)⁻¹ := by
  classical
  let b := (finBasis ℤ L).ofZLatticeBasis ℝ L
  let B := LinearMap.BilinForm.dualBasis (innerₗ V) inner_nondeg b
  let o := (stdOrthonormalBasis ℝ V).reindex (finCongr ((finrank_eq_card_basis b).trans
    (Fintype.card_fin _)))
  let P := o.toBasis.toMatrix b
  let Q := o.toBasis.toMatrix B
  have pair : Q.transpose * P = 1 := by
    ext i j
    rw [Matrix.one_apply]
    change (∑ k, o.repr (B i) k * o.repr (b j) k) = if i = j then 1 else 0
    calc
      _ = ∑ k, inner ℝ (B i) (o k) * inner ℝ (o k) (b j) := by
        apply Finset.sum_congr rfl; intro k _
        rw [o.repr_apply_apply,o.repr_apply_apply,real_inner_comm (o k) (B i)]
      _ = _ := (o.sum_inner_mul_inner _ _).trans
        (LinearMap.BilinForm.apply_dualBasis_left (B := innerₗ V) inner_nondeg b i j)
      _ = _ := by by_cases h : i = j <;> simp [h,Ne.symm]
  have det := congrArg Matrix.det pair
  rw [Matrix.det_mul,Matrix.det_transpose,Matrix.det_one] at det
  have vol (a : Basis (Fin (finrank ℤ L)) ℝ V) :
      ZLattice.covolume (span ℤ (Set.range a)) = |(o.toBasis.toMatrix a).det| := by
    apply (sq_eq_sq₀ ENNReal.toReal_nonneg (abs_nonneg _)).mp
    change ZLattice.covolume (span ℤ (Set.range a)) ^ 2 = _
    rw [covolume_span_sq_eq_gram,Matrix.gram_eq_conjTranspose_mul o,Matrix.det_mul,
      Matrix.det_conjTranspose,star_trivial,sq_abs,sq]
    rfl
  rw [← (finBasis ℤ L).ofZLatticeBasis_span ℝ]
  change ZLattice.covolume (LinearMap.BilinForm.dualSubmodule (innerₗ V) (span ℤ (Set.range b))) = _
  rw [LinearMap.BilinForm.dualSubmodule_span_of_basis (innerₗ V) inner_nondeg,vol,vol]
  exact eq_inv_of_mul_eq_one_left (by simpa [P,Q,B] using congrArg abs det)

private theorem shortest_exists (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    [Nontrivial V] : ∃ x : V, IsShortest L x := by
  have hn : L ≠ ⊥ := by
    intro he
    have hs := IsZLattice.span_top (K:=ℝ) (L:=L)
    simp [he] at hs
  obtain ⟨v,hv,_⟩ := exists_orderedShortest L (fun _ : V ↦ (0:ℕ)) hn
  exact ⟨v,hv⟩

/-- The section perpendicular to a shortest dual vector has rank k and covolume
equal to the primal covolume times the length of that dual vector. -/
private theorem section_family {k : ℕ} (L : Submodule ℤ (CoordSpace (k+1))) [DiscreteTopology L]
    [IsZLattice ℝ L] {v : CoordSpace (k+1)} (hs : IsShortest (metricDual L) v) :
    ∃ f : RankinFamily L k, sqrt (Matrix.gram ℝ f.vec).det = ZLattice.covolume L * ‖v‖ := by
  let D := metricDual L
  let : DiscreteTopology D := ZLattice.discreteTopology_dualSubmodule L
  let : IsZLattice ℝ D := ZLattice.isZLattice_dualSubmodule L
  let S := (ℝ ∙ v)ᗮ
  let K := projectedModule D S
  let : DiscreteTopology K := projectedModule_discrete D hs.1
  let : IsZLattice ℝ K := projectedModule_isZLattice D hs.1
  let T := metricDual K
  let : DiscreteTopology T := ZLattice.discreteTopology_dualSubmodule K
  let : IsZLattice ℝ T := ZLattice.isZLattice_dualSubmodule K
  have dim : finrank ℝ S = k := by
    have h := (ℝ ∙ v).finrank_add_finrank_orthogonal
    rw [finrank_span_singleton hs.2.1,finrank_euclideanSpace_fin] at h
    change 1 + finrank ℝ S = k+1 at h
    omega
  let b := ((finBasis ℤ T).reindex (finCongr ((ZLattice.rank ℝ T).trans dim))).ofZLatticeBasis ℝ T
  have hb : span ℤ (Set.range b) = T := Basis.ofZLatticeBasis_span _ _ _
  let f : Fin k → CoordSpace (k+1) := fun i ↦ b i
  have mem (i : Fin k) : f i ∈ L := by
    have hm := hb ▸ (subset_span (R:=ℤ) (Set.mem_range_self (f:=⇑b) i))
    change b i ∈ metricDual (projectedModule (metricDual L) S) at hm
    rw [metricDual_projectedModule,bidual] at hm
    exact hm
  have hg : Matrix.gram ℝ f = Matrix.gram ℝ b := rfl
  have eq : sqrt (Matrix.gram ℝ f).det = ZLattice.covolume T := by
    rw [hg,← covolume_span_sq_eq_gram,hb,sqrt_sq (ZLattice.covolume_pos T _).le]
  refine ⟨⟨f,mem,b.linearIndependent.map' S.subtype S.ker_subtype⟩,eq.trans ?_⟩
  change ZLattice.covolume (metricDual K) = _
  rw [dual_volume K]
  change (ZLattice.covolume (projectedModule D (ℝ ∙ v)ᗮ))⁻¹ = _
  rw [covolume_project_shortest D hs,dual_volume L]
  simp [div_eq_mul_inv,mul_comm]

/-- Apply the rank-k cap in both dual sections and eliminate the dual minimum. -/
theorem intrinsic_mordell {k : ℕ} (hk : 2 ≤ k) {g : ℝ} (hg : 0 < g) (cap : FamilyHermite k g) :
    IntrinsicHermite (k+1) (g ^ ((k:ℝ)/(k-1:ℝ))) := by
  intro L _ _
  let D := metricDual L
  let : DiscreteTopology D := ZLattice.discreteTopology_dualSubmodule L
  let : IsZLattice ℝ D := ZLattice.isZLattice_dualSubmodule L
  obtain ⟨x,hx⟩ := shortest_exists L
  obtain ⟨y,hy⟩ := shortest_exists D
  obtain ⟨f,hf⟩ := section_family L hy
  obtain ⟨u,hu⟩ := section_family D (v:=x) (by rwa [bidual])
  have h1 := cap L hx f
  have h2 := cap D hy u
  rw [hf] at h1
  rw [hu,dual_volume L] at h2
  refine ⟨⟨x,hx.1⟩,fun e ↦ hx.2.1 (congrArg Subtype.val e),?_⟩
  have px := norm_pos_iff.mpr hx.2.1
  have py := norm_pos_iff.mpr hy.2.1
  have pD := ZLattice.covolume_pos L MeasureTheory.volume
  have hK : (2:ℝ) ≤ k := by exact_mod_cast hk
  have k0 : (0:ℝ) < k := by linarith
  have k1 : 0 < (k:ℝ)-1 := by linarith
  have kp : 0 < (k:ℝ)+1 := by linarith
  apply (log_le_log_iff (sq_pos_of_pos px) (mul_pos (rpow_pos_of_pos hg _) (rpow_pos_of_pos pD _))).mp
  have A := log_le_log (sq_pos_of_pos px) h1
  have B := log_le_log (sq_pos_of_pos py) h2
  simp only [log_pow,log_mul hg.ne' (rpow_pos_of_pos (mul_pos pD py) _).ne',
    log_rpow (mul_pos pD py),log_mul pD.ne' py.ne'] at A
  simp only [log_pow,log_mul hg.ne' (rpow_pos_of_pos (mul_pos (inv_pos.mpr pD) px) _).ne',
    log_rpow (mul_pos (inv_pos.mpr pD) px),log_mul (inv_pos.mpr pD).ne' px.ne',log_inv] at B
  change log (‖x‖^2) ≤ _
  rw [log_pow,log_mul (rpow_pos_of_pos hg _).ne' (rpow_pos_of_pos pD _).ne',log_rpow hg,log_rpow pD,
    Nat.cast_succ]
  field_simp [k0.ne'] at A B
  field_simp [k1.ne',kp.ne']
  push_cast at *
  nlinarith only [mul_le_mul_of_nonneg_right A k0.le,B]

private theorem flag_mordell_four :
    flagGamma 3 ^ ((3:ℝ)/(3-1:ℝ)) = flagGamma 4 := by
  change exp (log 2 / 3) ^ _ = exp (log 4 / 4)
  rw [← exp_mul,show (4:ℝ) = 2^2 by norm_num,log_pow]
  congr 1
  ring

private theorem flag_mordell_eight :
    flagGamma 7 ^ ((7:ℝ)/(7-1:ℝ)) = flagGamma 8 := by
  change exp (log 64 / 7) ^ _ = exp (log 256 / 8)
  rw [← exp_mul,show (64:ℝ) = 2^6 by norm_num,show (256:ℝ) = 2^8 by norm_num,log_pow,log_pow]
  congr 1
  ring

theorem familyHermite_four : FamilyHermite 4 (flagGamma 4) :=
  flag_mordell_four ▸ familyHermite_of_intrinsic (intrinsic_mordell (by decide : 2 ≤ 3)
    (by norm_num [flagGamma,auditedGamma]; positivity) familyHermite_three)

/-- Standard intrinsic Hermite bounds at four ranks suffice for every suffix family. -/
theorem exceptional_of_intrinsic (h5 : IntrinsicHermite 5 (flagGamma 5))
    (h6 : IntrinsicHermite 6 (flagGamma 6)) (h7 : IntrinsicHermite 7 (flagGamma 7))
    (h24 : IntrinsicHermite 24 4) : ExceptionalFamilyBounds := by
  intro k hk
  rcases hk with ⟨lo,hi⟩ | rfl
  · interval_cases k
    · exact familyHermite_four
    · exact familyHermite_of_intrinsic h5
    · exact familyHermite_of_intrinsic h6
    · exact familyHermite_of_intrinsic h7
    · exact flag_mordell_eight ▸ familyHermite_of_intrinsic (intrinsic_mordell (by decide : 2 ≤ 7)
        (by norm_num [flagGamma,auditedGamma]; positivity) (familyHermite_of_intrinsic h7))
  · exact familyHermite_of_intrinsic h24

end SigabaNeo.Wall1.ControlledPlane

#print axioms SigabaNeo.Wall1.ControlledPlane.intrinsic_mordell
#print axioms SigabaNeo.Wall1.ControlledPlane.familyHermite_four
#print axioms SigabaNeo.Wall1.ControlledPlane.exceptional_of_intrinsic
