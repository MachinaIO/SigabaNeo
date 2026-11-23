import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonMinimalFamily

/-! Index and order-five restrictions on shortest families in dimensions six and seven. -/

noncomputable section
namespace SigabaNeo.Wall1.Watson

open Finset Submodule Module MeasureTheory TerminalProjection ControlledPlane ZSpan
open scoped RealInnerProductSpace

private def center5 (z : ℤ) := z - 5*((z+2)/5)

/-- Two applications of Watson's inequality force at least seven nonzero residues
in any coefficient representation of a nontrivial order-five coset. -/
theorem order_five_support {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {ι : Type*} [Fintype ι] {L : Submodule ℤ V} {b : ι → V}
    (minimal : ∀ i, DecoupledDecoder.IsShortest L (b i)) {x : V} (hx : x ∈ L)
    (out : x ∉ span ℤ (Set.range b)) (a : ι → ℤ) (rel : ∑ i, a i • b i = (5 : ℤ) • x) :
    7 ≤ (univ.filter fun i ↦ a i % 5 ≠ 0).card := by
  classical
  let M := span ℤ (Set.range b)
  have sub : M ≤ L := span_le.mpr (Set.range_subset_iff.mpr fun i ↦ (minimal i).1)
  have weight (k : ℤ) (outside : k • x ∉ M) : 10 ≤ ∑ i, |center5 (k*a i)| := by
    let u (i : ι) := (k*a i+2)/5
    let w := ∑ i, u i • b i
    have hw : w ∈ M := (mem_span_range_iff_exists_fun ℤ).mpr ⟨u,rfl⟩
    have h' : k • x-w ∉ M := fun h ↦ outside (by simpa using M.add_mem h hw)
    apply watson_coefficient_bound minimal (L.sub_mem (L.smul_mem k hx) (sub hw)) h' 5
    simp only [center5,sub_smul,mul_smul,sum_sub_distrib,← Finset.smul_sum,rel,w,u,smul_sub,
      smul_comm k (5 : ℤ)]
  have h₁ := weight 1 (by simpa using out)
  have h₂ := weight 2 (by
    intro h
    have h₅ : (5 : ℤ) • x ∈ M := (mem_span_range_iff_exists_fun ℤ).mpr ⟨a,rel⟩
    apply out
    convert M.sub_mem h₅ (M.smul_mem (2 : ℤ) h) using 1
    module)
  simp only [one_mul] at h₁
  have pair (z : ℤ) :
      |center5 z| + |center5 (2*z)| = if z % 5 ≠ 0 then (3 : ℤ) else 0 := by
    let r := z % 5
    have hr : r < 5 := Int.emod_lt_of_pos z (by decide)
    have hr₀ : 0 ≤ r := Int.emod_nonneg z (by decide)
    have decomp : z = r + 5 * (z/5) := by dsimp [r]; omega
    generalize z/5 = k at decomp
    rw [decomp]
    interval_cases r <;> simp only [center5, abs_eq_max_neg] <;> split_ifs <;> omega
  have eq := sum_congr (s₁ := (univ : Finset ι)) rfl fun i _ ↦ pair (a i)
  simp only [sum_add_distrib, sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul] at eq
  omega

/-- General index estimate obtained by applying the available Hermite profile and
Hadamard's inequality to an independent family of shortest vectors. -/
private theorem index_sq_le (n : ℕ) (hn : 2 ≤ n) (L : Submodule ℤ (CoordSpace n))
    [DiscreteTopology L] [IsZLattice ℝ L] (B : Basis (Fin n) ℝ (CoordSpace n))
    (minimal : ∀ i, DecoupledDecoder.IsShortest L (B i)) :
    (((span ℤ (Set.range B)).toAddSubgroup.relIndex L.toAddSubgroup : ℕ) : ℝ)^2 ≤
      (MordellBlichfeldt.gamma n)^n := by
  classical
  have : NeZero n := ⟨by omega⟩
  let M := span ℤ (Set.range B)
  let I : ℝ := M.toAddSubgroup.relIndex L.toAddSubgroup
  have sub : M ≤ L := span_le.mpr (Set.range_subset_iff.mpr fun i ↦ (minimal i).1)
  have vol := ZLattice.covolume_pos L volume
  have hi : I * ZLattice.covolume L = ZLattice.covolume M :=
    ((div_eq_iff vol.ne').mp (ZLattice.covolume_div_covolume_eq_relIndex' M L sub)).symm
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have : Fact (finrank ℝ (CoordSpace n) = n) := ⟨by simp [CoordSpace]⟩
  have had := e.toBasis.orientation.abs_volumeForm_apply_le (⇑B)
  rw [e.toBasis.orientation.volumeForm_robust e rfl] at had
  have eq : ZLattice.covolume M = |e.toBasis.det B| := by
    rw [ZLattice.covolume_eq_det_mul_measureReal M volume (B.restrictScalars ℤ) e.toBasis,
      measureReal_congr (fundamentalDomain_ae_parallelepiped e.toBasis volume)]
    have hv : volume.real (parallelepiped e.toBasis) = 1 := by
      simpa [Measure.real] using congrArg ENNReal.toReal e.volume_parallelepiped
    rw [hv,mul_one]
    congr 2
    funext i
    exact B.restrictScalars_apply ℤ i
  have norms (i : Fin n) : ‖B i‖ = ‖B 0‖ := le_antisymm
    ((minimal i).2.2 _ (minimal 0).1 (minimal 0).2.1)
    ((minimal 0).2.2 _ (minimal i).1 (minimal i).2.1)
  simp only [norms,prod_const,card_univ,Fintype.card_fin,← eq,← hi] at had
  have rk : finrank ℤ L = n := (ZLattice.rank ℝ L).trans (by simp [CoordSpace])
  let C := ((finBasis ℤ L).reindex (finCongr rk)).ofZLatticeBasis ℝ L
  have Cspan : span ℤ (Set.range C) = L := Basis.ofZLatticeBasis_span _ _ _
  let f : RankinFamily L n :=
    ⟨C,fun i ↦ Cspan ▸ subset_span (Set.mem_range_self i),C.linearIndependent⟩
  have rad := MordellBlichfeldt.family n hn L (minimal 0) f
  change ‖B 0‖^2 ≤ _ * (Real.sqrt (Matrix.gram ℝ C).det)^_ at rad
  rw [← covolume_span_sq_eq_gram,Cspan,Real.sqrt_sq vol.le] at rad
  have r := pow_le_pow_left₀ (sq_nonneg _) rad n
  rw [mul_pow,← Real.rpow_mul_natCast vol.le, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr
    (NeZero.ne n)),Real.rpow_two] at r
  have h := pow_le_pow_left₀ (by rw [hi]; exact (ZLattice.covolume_pos M volume).le) had 2
  rw [mul_pow,← pow_mul,Nat.mul_comm, pow_mul] at h
  exact le_of_mul_le_mul_right (h.trans r) (sq_pos_of_pos vol)

theorem rank_six_minimal_index (L : Submodule ℤ (CoordSpace 6)) [DiscreteTopology L]
    [IsZLattice ℝ L] (B : Basis (Fin 6) ℝ (CoordSpace 6))
    (minimal : ∀ i, DecoupledDecoder.IsShortest L (B i)) :
    (span ℤ (Set.range B)).toAddSubgroup.relIndex L.toAddSubgroup ≤ 4 := by
  classical
  let M := span ℤ (Set.range B)
  let I := M.toAddSubgroup.relIndex L.toAddSubgroup
  have hi := index_sq_le 6 (by decide) L B minimal
  have h := pow_le_pow_left₀ (MordellBlichfeldt.gamma_pos 6).le
    MordellBlichfeldt.exceptional_enclosures.2.2.2.1 6
  change (I : ℝ)^2 ≤ _ at hi
  have lt : I < 6 := by
    by_contra! big
    have six : (6 : ℝ) ≤ I := by exact_mod_cast big
    nlinarith only [hi,h,pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 6) six 2]
  by_contra! big
  change 4 < I at big
  have five : I = 5 := by omega
  let K := M.comap L.subtype
  have size : Nat.card (L ⧸ K) = 5 := five
  let : Finite (L ⧸ K) := Nat.finite_of_card_ne_zero (by omega)
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨y,hy⟩ := exists_prime_addOrderOf_dvd_card' (G := L ⧸ K) 5 (by rw [size])
  obtain ⟨x,rfl⟩ := K.mkQ_surjective y
  have hz : (5 : ℕ) • K.mkQ x = 0 := by rw [← hy,addOrderOf_nsmul_eq_zero]
  have hm : (5 : ℤ) • x.val ∈ M := (Submodule.Quotient.mk_eq_zero K).mp
    (show K.mkQ ((5 : ℕ) • x) = 0 by simpa using hz)
  obtain ⟨a,ha⟩ := (mem_span_range_iff_exists_fun ℤ).mp hm
  have out : x.val ∉ M := by
    intro hx
    rw [show K.mkQ x = 0 from (Submodule.Quotient.mk_eq_zero K).mpr hx,addOrderOf_zero] at hy
    omega
  have many := order_five_support minimal x.property out a ha
  have few := card_le_univ (univ.filter fun i ↦ a i % 5 ≠ 0)
  simp only [Fintype.card_fin] at few
  omega

theorem rank_seven_minimal_index (L : Submodule ℤ (CoordSpace 7)) [DiscreteTopology L]
    [IsZLattice ℝ L] (B : Basis (Fin 7) ℝ (CoordSpace 7))
    (minimal : ∀ i, DecoupledDecoder.IsShortest L (B i)) :
    (span ℤ (Set.range B)).toAddSubgroup.relIndex L.toAddSubgroup ≤ 10 := by
  have hi := index_sq_le 7 (by decide) L B minimal
  have h := pow_le_pow_left₀ (MordellBlichfeldt.gamma_pos 7).le
    MordellBlichfeldt.exceptional_enclosures.2.2.2.2.2.1 7
  by_contra! big
  have eleven : (11 : ℝ) ≤ (span ℤ (Set.range B)).toAddSubgroup.relIndex L.toAddSubgroup := by
    exact_mod_cast big
  nlinarith only [hi,h,pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 11) eleven 2]

end SigabaNeo.Wall1.Watson

#print axioms SigabaNeo.Wall1.Watson.order_five_support
#print axioms SigabaNeo.Wall1.Watson.rank_six_minimal_index
#print axioms SigabaNeo.Wall1.Watson.rank_seven_minimal_index
