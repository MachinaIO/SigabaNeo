import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonFiveSupport

/-! The sharp rank-five Hermite inequality for an index-two minimal family. -/

noncomputable section
namespace SigabaNeo.Wall1.Watson

open Finset Submodule Module MeasureTheory TerminalProjection
open scoped RealInnerProductSpace

/-- Reduce the coefficients of a doubled coset representative modulo two.
The reduced half-sum has support at least four by Watson's inequality. -/
theorem half_support {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {ι : Type*} [Fintype ι] {L : Submodule ℤ V} {b : ι → V}
    (minimal : ∀ i, DecoupledDecoder.IsShortest L (b i)) {x : V}
    (hx : x ∈ L) (out : x ∉ span ℤ (Set.range b))
    (twice : (2 : ℤ) • x ∈ span ℤ (Set.range b)) :
    ∃ (s : Finset ι) (y : V), y ∈ L ∧ y ∉ span ℤ (Set.range b) ∧
      4 ≤ s.card ∧ ∑ i ∈ s, b i = y + y := by
  classical
  obtain ⟨a, ha⟩ := (mem_span_range_iff_exists_fun ℤ).mp twice
  let s := univ.filter fun i ↦ a i % 2 = 1
  let c (i : ι) : ℤ := if i ∈ s then 1 else 0
  let u (i : ι) := a i / 2
  let w := ∑ i, u i • b i
  have hw : w ∈ span ℤ (Set.range b) := (mem_span_range_iff_exists_fun ℤ).mpr ⟨u,rfl⟩
  have sub : span ℤ (Set.range b) ≤ L :=
    span_le.mpr (Set.range_subset_iff.mpr fun i ↦ (minimal i).1)
  have hy := L.sub_mem hx (sub hw)
  have ho : x-w ∉ span ℤ (Set.range b) := fun h ↦ out (by
    simpa using (span ℤ (Set.range b)).add_mem h hw)
  have hc (i : ι) : c i = a i - 2*u i := by
    dsimp [c,s,u]
    simp only [mem_filter,mem_univ,true_and]
    split <;> omega
  have eq : ∑ i, c i • b i = (2 : ℤ) • (x-w) := by
    simp only [hc,sub_smul,mul_smul,sum_sub_distrib,← Finset.smul_sum,ha,w,smul_sub]
  have wt := watson_coefficient_bound minimal hy ho 2 c eq
  have weight : ∑ i, |c i| = (s.card : ℤ) := by simp [c, apply_ite abs, sum_ite_mem]
  rw [weight] at wt
  refine ⟨s,x-w,hy,ho,by exact_mod_cast wt,?_⟩
  simpa [c, ite_smul, sum_ite_mem, two_zsmul] using eq

/-- Whenever five independent shortest vectors generate an index-two sublattice,
the sharp rank-five upper bound holds in the full lattice. -/
theorem rank_five_index_two (L : Submodule ℤ (CoordSpace 5))
    [DiscreteTopology L] [IsZLattice ℝ L] (B : Basis (Fin 5) ℝ (CoordSpace 5))
    (minimal : ∀ i, DecoupledDecoder.IsShortest L (B i))
    (index : (span ℤ (Set.range B)).toAddSubgroup.relIndex L.toAddSubgroup = 2) :
    ‖B 4‖^10 ≤ 8 * ZLattice.covolume L ^ 2 := by
  classical
  let M := span ℤ (Set.range B)
  have hnot : ¬ L ≤ M := fun h ↦ by
    have h1 : M.toAddSubgroup.relIndex L.toAddSubgroup = 1 := AddSubgroup.relIndex_eq_one.mpr h
    change M.toAddSubgroup.relIndex L.toAddSubgroup = 2 at index
    omega
  obtain ⟨x,hx,ho⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  let K := M.comap L.subtype
  let z : L := ⟨x,hx⟩
  have card : Nat.card (L ⧸ K) = 2 := index
  have hz : (2 : ℕ) • K.mkQ z = 0 := by rw [← card]; exact card_nsmul_eq_zero'
  have hmem : (2 : ℤ) • x ∈ M := (Submodule.Quotient.mk_eq_zero K).mp
    (show K.mkQ ((2 : ℕ) • z) = 0 by simpa using hz)
  obtain ⟨s,y,hy,out,hs,rel⟩ := half_support minimal hx ho hmem
  by_cases all : s = univ
  · exact five_covolume L B minimal hy out (all ▸ rel)
  obtain ⟨j,hj⟩ : ∃ j, j ∉ s := by
    by_contra! h
    exact all (eq_univ_of_forall h)
  have es : s = univ.erase j := eq_of_subset_of_card_le
    (fun i hi ↦ mem_erase.mpr ⟨fun hij ↦ hj (hij ▸ hi), mem_univ _⟩)
    (by simpa using hs)
  let e := Equiv.swap j (4 : Fin 5)
  let C := B.reindex e
  have hc (i : Fin 5) : C i = B (e.symm i) := B.reindex_apply e i
  have hc4 : C 4 = B j := by simp [hc, e]
  have hspan : Set.range (C : Fin 5 → CoordSpace 5) = Set.range B := by
    rw [show (C : Fin 5 → _) = B ∘ e.symm from B.coe_reindex e]
    exact e.symm.surjective.range_comp _
  have hsum : ∑ i, C i = ∑ i, B i := by
    simp only [hc]
    exact e.symm.sum_comp B
  rw [Fin.sum_univ_castSucc] at hsum
  have hsum' := add_sum_erase univ B (mem_univ j)
  rw [← es,rel] at hsum'
  have hrel : ∑ i : Fin 4, C i.castSucc = y + y := by
    change (∑ i : Fin 4, C i.castSucc) + C 4 = _ at hsum
    rw [hc4, ← hsum', add_comm (B j)] at hsum
    exact add_right_cancel hsum
  have h := four_covolume L C (fun i ↦ hc i ▸ minimal _) hy (hspan ▸ out) hrel
  have hn := (minimal 4).2.2 _ (minimal j).1 (minimal j).2.1
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 10).trans (hc4 ▸ h)

/-- In a putative rank-five counterexample every independent minimal family
is an integral basis. Equivalently every full Gram minor of minimal vectors
is either zero or the squared covolume. -/
theorem rank_five_minimal_determinants (L : Submodule ℤ (CoordSpace 5))
    [DiscreteTopology L] [IsZLattice ℝ L] {v : CoordSpace 5}
    (hv : DecoupledDecoder.IsShortest L v) (gap : 8 * ZLattice.covolume L^2 < ‖v‖^10)
    (b : Fin 5 → CoordSpace 5) (minimal : ∀ i, DecoupledDecoder.IsShortest L (b i)) :
    (Matrix.gram ℝ b).det = 0 ∨
      (span ℤ (Set.range b) = L ∧ (Matrix.gram ℝ b).det = ZLattice.covolume L^2) := by
  classical
  by_cases ind : LinearIndependent ℝ b
  · right
    let B := basisOfLinearIndependentOfCardEqFinrank ind (by simp [CoordSpace])
    have hb : (B : Fin 5 → CoordSpace 5) = b := coe_basisOfLinearIndependentOfCardEqFinrank _ _
    let M := span ℤ (Set.range B)
    have hmin : ∀ i, DecoupledDecoder.IsShortest L (B i) := hb ▸ minimal
    have sub : M ≤ L := span_le.mpr (Set.range_subset_iff.mpr fun i ↦ (hmin i).1)
    let I := M.toAddSubgroup.relIndex L.toAddSubgroup
    have pos : 0 < I := by
      have heq := ZLattice.covolume_div_covolume_eq_relIndex' M L sub
      have hp := div_pos (ZLattice.covolume_pos M volume) (ZLattice.covolume_pos L volume)
      rw [heq] at hp
      exact_mod_cast hp
    have cap : I ≤ 2 := rank_five_minimal_index L B hmin
    have one : I = 1 := by
      by_contra h
      have two : I = 2 := by omega
      have h₁ := rank_five_index_two L B hmin two
      have h₂ := hv.2.2 _ (hmin 4).1 (hmin 4).2.1
      exact gap.not_ge ((pow_le_pow_left₀ (norm_nonneg _) h₂ 10).trans h₁)
    have eq : M = L := le_antisymm sub (AddSubgroup.relIndex_eq_one.mp one)
    rw [← hb]
    exact ⟨eq, (covolume_span_sq_eq_gram B).symm.trans (congrArg (ZLattice.covolume · ^ 2) eq)⟩
  · exact Or.inl (not_ne_iff.mp (fun h ↦ ind (Matrix.linearIndependent_of_det_gram_ne_zero h)))

end SigabaNeo.Wall1.Watson

#print axioms SigabaNeo.Wall1.Watson.half_support
#print axioms SigabaNeo.Wall1.Watson.rank_five_index_two
#print axioms SigabaNeo.Wall1.Watson.rank_five_minimal_determinants
