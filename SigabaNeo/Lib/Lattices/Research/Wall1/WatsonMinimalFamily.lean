import SigabaNeo.Lib.Lattices.Research.Wall1.MordellBlichfeldtEnclosures

/-! Watson's coefficient inequality for the integral span of minimal vectors. -/
noncomputable section
namespace SigabaNeo.Wall1

open Submodule Finset
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι] {L : Submodule ℤ V} {b : ι → V}

/-- A relation d x = ∑ cᵢ bᵢ with x outside the integral span of the minimal
vectors bᵢ must have total absolute coefficient weight at least 2d. -/
theorem watson_coefficient_bound (minimal : ∀ i, DecoupledDecoder.IsShortest L (b i))
    {x : V} (hx : x ∈ L) (outside : x ∉ span ℤ (Set.range b)) (d : ℤ) (c : ι → ℤ)
    (rel : ∑ i, c i • b i = d • x) : 2*d ≤ ∑ i, |c i| := by
  have hnorm : 0 < ‖x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (fun h ↦ outside (h ▸ zero_mem _)))
  have ht (i : ι) : b i ∈ span ℤ (Set.range b) := subset_span (Set.mem_range_self i)
  have sides (i : ι) : |2*⟪x,b i⟫| ≤ ‖x‖^2 := by
    have plus := (minimal i).2.2 (x+b i) (L.add_mem hx (minimal i).1) (fun h ↦
      outside ((eq_neg_of_add_eq_zero_left h) ▸ (span ℤ (Set.range b)).neg_mem (ht i)))
    have minus := (minimal i).2.2 (x-b i) (L.sub_mem hx (minimal i).1)
      (fun h ↦ outside ((sub_eq_zero.mp h) ▸ ht i))
    have hp := pow_le_pow_left₀ (norm_nonneg _) plus 2
    have hm := pow_le_pow_left₀ (norm_nonneg _) minus 2
    rw [norm_add_sq_real] at hp
    rw [norm_sub_sq_real] at hm
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have piece (i : ι) : 2*⟪x,c i • b i⟫ ≤ |(c i:ℝ)| * ‖x‖^2 := by
    rw [← Int.cast_smul_eq_zsmul ℝ,real_inner_smul_right,mul_left_comm]
    apply (le_abs_self _).trans
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (sides i) (abs_nonneg _)
  have H := sum_le_sum (s := univ) (fun i _ ↦ piece i)
  rw [← mul_sum,← inner_sum,rel,← Int.cast_smul_eq_zsmul ℝ,real_inner_smul_right,
    real_inner_self_eq_norm_sq,← sum_mul,← mul_assoc] at H
  exact_mod_cast (le_of_mul_le_mul_right H hnorm)

/-- The span of at most five minimal vectors is 3-saturated inside L. -/
theorem minimal_span_three_saturated (rank : Fintype.card ι ≤ 5)
    (minimal : ∀ i, DecoupledDecoder.IsShortest L (b i)) {x : V} (hx : x ∈ L)
    (triple : (3:ℤ) • x ∈ span ℤ (Set.range b)) : x ∈ span ℤ (Set.range b) := by
  by_contra outside
  obtain ⟨a,ha⟩ := (mem_span_range_iff_exists_fun ℤ).mp triple
  let t (i : ι) := (a i+1)/3
  let c (i : ι) := a i - 3*t i
  let v := ∑ i, t i • b i
  have hv : v ∈ span ℤ (Set.range b) := (mem_span_range_iff_exists_fun ℤ).mpr ⟨t,rfl⟩
  have hvL : v ∈ L := span_le.mpr (Set.range_subset_iff.mpr (fun i ↦ (minimal i).1)) hv
  have out : x-v ∉ span ℤ (Set.range b) := by
    intro h
    exact outside (by simpa using (span ℤ (Set.range b)).add_mem h hv)
  have eq : ∑ i, c i • b i = (3:ℤ) • (x-v) := by
    simp only [c,sub_smul,mul_smul,sum_sub_distrib,← Finset.smul_sum,ha,v,smul_sub]
  have weight := watson_coefficient_bound minimal (L.sub_mem hx hvL) out 3 c eq
  have upper : ∑ i, |c i| ≤ ∑ _i : ι, (1:ℤ) := by
    apply sum_le_sum
    intro i _
    dsimp [c,t]
    rw [abs_le]; omega
  simp only [sum_const,card_univ,nsmul_eq_mul,mul_one] at upper
  omega

open TerminalProjection Module MeasureTheory ControlledPlane ZSpan

/-- In dimension five a real basis consisting of shortest lattice vectors
generates an integral sublattice of index at most two. -/
theorem rank_five_minimal_index (L : Submodule ℤ (CoordSpace 5))
    [DiscreteTopology L] [IsZLattice ℝ L] (B : Basis (Fin 5) ℝ (CoordSpace 5))
    (minimal : ∀ i, DecoupledDecoder.IsShortest L (B i)) :
    (span ℤ (Set.range B)).toAddSubgroup.relIndex L.toAddSubgroup ≤ 2 := by
  classical
  let M := span ℤ (Set.range B)
  have sub : M ≤ L := span_le.mpr (Set.range_subset_iff.mpr fun i ↦ (minimal i).1)
  let I := M.toAddSubgroup.relIndex L.toAddSubgroup
  have indexEq : (I:ℝ)*ZLattice.covolume L = ZLattice.covolume M :=
    ((div_eq_iff (ZLattice.covolume_pos L volume).ne').mp
      (ZLattice.covolume_div_covolume_eq_relIndex' M L sub)).symm
  let e := EuclideanSpace.basisFun (Fin 5) ℝ
  have : Fact (finrank ℝ (CoordSpace 5) = 5) := ⟨by simp [CoordSpace]⟩
  have detBound := e.toBasis.orientation.abs_volumeForm_apply_le (⇑B)
  rw [e.toBasis.orientation.volumeForm_robust e rfl] at detBound
  have vol : ZLattice.covolume M = |e.toBasis.det B| := by
    rw [ZLattice.covolume_eq_det_mul_measureReal M volume (B.restrictScalars ℤ) e.toBasis,
      measureReal_congr (fundamentalDomain_ae_parallelepiped e.toBasis volume)]
    have hv : volume.real (parallelepiped e.toBasis) = 1 := by
      simpa [Measure.real] using congrArg ENNReal.toReal e.volume_parallelepiped
    rw [hv,mul_one]
    congr 2
    funext i
    exact B.restrictScalars_apply ℤ i
  have norms (i : Fin 5) : ‖B i‖ = ‖B 0‖ := le_antisymm
    ((minimal i).2.2 _ (minimal 0).1 (minimal 0).2.1)
    ((minimal 0).2.2 _ (minimal i).1 (minimal i).2.1)
  simp only [norms,prod_const,card_univ,Fintype.card_fin] at detBound
  have rk : finrank ℤ L = 5 := (ZLattice.rank ℝ L).trans (by simp [CoordSpace])
  let C := ((finBasis ℤ L).reindex (finCongr rk)).ofZLatticeBasis ℝ L
  have Cspan : span ℤ (Set.range C) = L := Basis.ofZLatticeBasis_span _ _ _
  let f : RankinFamily L 5 := ⟨C,fun i ↦ Cspan ▸ subset_span (Set.mem_range_self i),C.linearIndependent⟩
  have rad := MordellBlichfeldt.family 5 (by decide) L (minimal 0) f
  change ‖B 0‖^2 ≤ _ * (Real.sqrt (Matrix.gram ℝ C).det)^_ at rad
  rw [← covolume_span_sq_eq_gram,Cspan,Real.sqrt_sq (ZLattice.covolume_pos L volume).le] at rad
  have r5 := pow_le_pow_left₀ (sq_nonneg _) rad 5
  rw [mul_pow,← Real.rpow_mul_natCast (ZLattice.covolume_pos L volume).le] at r5
  norm_num at r5
  have small := pow_le_pow_left₀ (MordellBlichfeldt.gamma_pos 5).le
    MordellBlichfeldt.exceptional_enclosures.2.1 5
  have bound : (MordellBlichfeldt.gamma 5)^5 < 16 := small.trans_lt (by norm_num)
  have iLt : I < 4 := by
    by_contra! h
    have four : (4:ℝ) ≤ I := by exact_mod_cast h
    have a := (mul_le_mul_of_nonneg_right four (ZLattice.covolume_pos L volume).le).trans
      (indexEq.le.trans (vol ▸ detBound))
    have A := pow_le_pow_left₀ (mul_nonneg (by norm_num) (ZLattice.covolume_pos L volume).le) a 2
    nlinarith only [A,r5,mul_lt_mul_of_pos_right bound (sq_pos_of_pos (ZLattice.covolume_pos L volume))]
  change I ≤ 2
  by_contra! h
  have three : I = 3 := by omega
  let K := M.comap L.subtype
  have size : Nat.card (L ⧸ K) = 3 := three
  let : Finite (L ⧸ K) := Nat.finite_of_card_ne_zero (by omega)
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨y,hy⟩ := exists_prime_addOrderOf_dvd_card' (G := L ⧸ K) 3 (by rw [size])
  obtain ⟨x,rfl⟩ := K.mkQ_surjective y
  have hz : (3:ℤ) • K.mkQ x = 0 := by
    change ((3:ℕ):ℤ) • _ = 0
    rw [natCast_zsmul,← hy,addOrderOf_nsmul_eq_zero]
  have hx : (3:ℤ) • x.val ∈ M := (Submodule.Quotient.mk_eq_zero K).mp
    (show K.mkQ ((3:ℤ) • x) = 0 by simpa using hz)
  have mem : x ∈ K := minimal_span_three_saturated (by simp) minimal x.property hx
  rw [show K.mkQ x = 0 from (Submodule.Quotient.mk_eq_zero K).mpr mem,addOrderOf_zero] at hy
  omega

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.watson_coefficient_bound
#print axioms SigabaNeo.Wall1.minimal_span_three_saturated
#print axioms SigabaNeo.Wall1.rank_five_minimal_index
