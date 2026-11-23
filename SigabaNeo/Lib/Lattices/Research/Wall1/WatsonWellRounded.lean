import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonIndexTwo
import SigabaNeo.Lib.Lattices.Research.Wall1.MinkowskiBound
import Mathlib.LinearAlgebra.Transvection.Basic

/-! Deformation to a well-rounded lattice while preserving the minimum. -/

noncomputable section
namespace SigabaNeo.Wall1.Watson

open Submodule Module MeasureTheory TerminalProjection DecoupledDecoder

variable {n : ℕ}
local notation "E" => CoordSpace n

/-- The real span of all vectors attaining the first minimum. -/
def minimalSpan (L : Submodule ℤ E) : Submodule ℝ E :=
  span ℝ {x | IsShortest L x}

/-- Contract a direction transverse to the minimal span until a vector outside the fixed
hyperplane attains the old minimum. On the positive parameter interval used here, every
possible contact vector belongs to a single bounded subset of the original lattice. -/
private theorem contact (L : Submodule ℤ E) [DiscreteTopology L] {v y : E}
    (hv : IsShortest L v) (hy : y ∈ L) (f : E →ₗ[ℝ] ℝ) (fy : f y = 1)
    (fixed : minimalSpan L ≤ LinearMap.ker f) :
    ∃ e : E ≃ₗ[ℝ] E, (0 < e.toLinearMap.det ∧ e.toLinearMap.det < 1) ∧
      (∀ x ∈ minimalSpan L, e x = x) ∧ (∀ x ∈ L, x ≠ 0 → ‖v‖ ≤ ‖e x‖) ∧
      ∃ x ∈ L, e x ∉ minimalSpan L ∧ ‖e x‖ = ‖v‖ := by
  classical
  let T (t : ℝ) := LinearMap.transvection f ((t-1) • y)
  have app (t : ℝ) (x : E) : T t x = x + (f x * (t-1)) • y := by
    simp only [T, LinearMap.transvection.apply, smul_smul]
  have scale (t : ℝ) (x : E) : f (T t x) = t * f x := by
    simp [app, fy]; ring
  have y0 : y ≠ 0 := by intro h; simp [h] at fy
  let a := ‖v‖ / ‖y‖
  have ypos := norm_pos_iff.mpr y0
  have apos : 0 < a := div_pos (norm_pos_iff.mpr hv.2.1) ypos
  have a1 : a ≤ 1 := (div_le_one ypos).mpr (hv.2.2 _ hy y0)
  let C := ‖f.toContinuousLinearMap‖
  have cb (x : E) : |f x| ≤ C * ‖x‖ := f.toContinuousLinearMap.le_opNorm x
  let R := ‖v‖ + (C * ‖v‖ / a) * ‖y‖
  have bounded {t : ℝ} (ht : t ∈ Set.Icc a 1) (x : E) (hx : ‖T t x‖ ≤ ‖v‖) :
      ‖x‖ ≤ R := by
    have tp := apos.trans_le ht.1
    have hh := (cb (T t x)).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
    rw [scale,abs_mul,abs_of_pos tp] at hh
    have hf : |f x| ≤ C * ‖v‖ / a := (le_div_iff₀ apos).mpr (by
      nlinarith only [hh,mul_le_mul_of_nonneg_right ht.1 (abs_nonneg (f x))])
    have hsmall : |t-1| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith [ht.2]⟩
    have back : x = T t x - (f x * (t-1)) • y := by simp [app]
    calc
      ‖x‖ = ‖T t x - (f x * (t-1)) • y‖ := congrArg norm back
      _ ≤ ‖T t x‖ + ‖(f x * (t-1)) • y‖ := norm_sub_le ..
      _ ≤ R := by
        rw [norm_smul, Real.norm_eq_abs, abs_mul]
        exact add_le_add hx (mul_le_mul_of_nonneg_right
          ((mul_le_mul_of_nonneg_left hsmall (abs_nonneg _)).trans (by simpa using hf))
          (norm_nonneg _))
  have ay : ‖T a y‖ = ‖v‖ := by
    rw [app,fy,one_mul,sub_smul,one_smul,show y + (a • y - y) = a • y by abel, norm_smul,
      Real.norm_eq_abs, abs_of_pos apos,div_mul_cancel₀ _ ypos.ne']
  have fin : (Metric.closedBall (0 : E) R ∩ (L : Set E)).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete Metric.isBounded_closedBall
      L.toAddSubgroup.isClosed_of_discreteTopology
  let S := fin.toFinset.filter fun x ↦ f x ≠ 0
  have mem (x : E) : x ∈ S ↔ ‖x‖ ≤ R ∧ x ∈ L ∧ f x ≠ 0 := by
    simp [S, and_assoc]
  have ys : y ∈ S := (mem y).mpr ⟨bounded ⟨le_rfl,a1⟩ y ay.le,hy,by simp [fy]⟩
  let m (t : ℝ) := S.inf' ⟨y,ys⟩ (fun x ↦ ‖T t x‖)
  have cont : Continuous m := Continuous.finset_inf'_apply _ fun x _ ↦ by
    simp only [app]
    fun_prop
  have ma : m a ≤ ‖v‖ := (Finset.inf'_le _ ys).trans ay.le
  have m1 : ‖v‖ < m 1 := by
    apply (Finset.lt_inf'_iff _).mpr
    intro x hx
    obtain ⟨_,hxL,hfx⟩ := (mem x).mp hx
    have hx0 : x ≠ 0 := fun h ↦ hfx (h ▸ map_zero f)
    simp only [app,sub_self,mul_zero,zero_smul,add_zero]
    apply lt_of_le_of_ne (hv.2.2 _ hxL hx0)
    intro he
    exact hfx (fixed (subset_span (show IsShortest L x from
      ⟨hxL,hx0,fun w hw hn ↦ he ▸ hv.2.2 w hw hn⟩)))
  obtain ⟨t,ht,hm⟩ := intermediate_value_Icc a1 cont.continuousOn ⟨ma,m1.le⟩
  have tp := apos.trans_le ht.1
  have t1 : t < 1 := lt_of_le_of_ne ht.2 (fun h ↦ by subst t; linarith)
  have dt : (T t).det = t := by simp [T,LinearMap.transvection.det,fy]
  let e := LinearMap.equivOfIsUnitDet (f := T t) (by rw [dt]; exact isUnit_iff_ne_zero.mpr tp.ne')
  have he : e.toLinearMap = T t := LinearMap.coe_equivOfIsUnitDet _
  have ev (x : E) : e x = T t x := LinearMap.congr_fun he x
  refine ⟨e,by simpa [he,dt] using And.intro tp t1,?_,?_,?_⟩
  · intro x hx
    simp [ev,app,show f x = 0 from fixed hx]
  · intro x hx hn
    by_cases hz : f x = 0
    · simpa [ev,app,hz] using hv.2.2 x hx hn
    by_contra! bad
    rw [ev] at bad
    have hS := (mem x).mpr ⟨bounded ht x bad.le,hx,hz⟩
    exact bad.not_ge (hm ▸ (Finset.inf'_le (fun z ↦ ‖T t z‖) hS : m t ≤ _))
  · obtain ⟨x,hx,eq⟩ := Finset.exists_mem_eq_inf' ⟨y,ys⟩ (fun z ↦ ‖T t z‖)
    obtain ⟨_,hxL,hfx⟩ := (mem x).mp hx
    refine ⟨x,hxL,?_,(ev x ▸ eq.symm.trans hm)⟩
    intro hx'
    have hz : f (e x) = 0 := fixed hx'
    rw [ev,scale] at hz
    exact (mul_ne_zero tp.ne' hfx) hz

private abbrev lattice (B : Basis (Fin n) ℝ E) := span ℤ (Set.range B)

/-- Iteration terminates because contact strictly increases the dimension of the minimal span. -/
private theorem round_basis (B : Basis (Fin n) ℝ E) {v : E} (hv : IsShortest (lattice B) v) :
    ∃ C : Basis (Fin n) ℝ E, IsShortest (lattice C) v ∧ minimalSpan (lattice C) = ⊤ ∧
      ZLattice.covolume (lattice C) ≤ ZLattice.covolume (lattice B) := by
  classical
  let L := lattice B
  by_cases full : minimalSpan L = ⊤
  · exact ⟨B,hv,full,le_rfl⟩
  have out : ¬ (L : Set E) ⊆ minimalSpan L := fun h ↦ full (top_unique
    ((IsZLattice.span_top (K := ℝ) (L := L)).ge.trans (span_le.mpr h)))
  obtain ⟨y,hy,hout⟩ := Set.not_subset.mp out
  obtain ⟨f,hfix,fy⟩ := LinearMap.exists_extend_of_notMem
    (0 : minimalSpan L →ₗ[ℝ] ℝ) hout 1
  have hker : minimalSpan L ≤ LinearMap.ker f := fun x hx ↦
    show f x = 0 from LinearMap.congr_fun hfix ⟨x,hx⟩
  obtain ⟨e,de,fixes,floor, x,hx,outside,len⟩ := contact L hv hy f fy hker
  let D := B.map e
  have mapL : L.map (e.toLinearMap.restrictScalars ℤ) = lattice D := by
    rw [show L = span ℤ (Set.range B) from rfl, map_span, ← Set.range_comp]
    rfl
  have img (z : E) (hz : z ∈ L) : e z ∈ lattice D := mapL ▸ mem_map_of_mem hz
  have vfixed := fixes v (subset_span hv)
  have newfloor (w : E) (hw : w ∈ lattice D) (hn : w ≠ 0) : ‖v‖ ≤ ‖w‖ := by
    rw [← mapL] at hw
    obtain ⟨z,hz,rfl⟩ := hw
    exact floor z hz (fun h ↦ hn (by simp [h]))
  have incl : minimalSpan L ≤ minimalSpan (lattice D) := by
    apply span_le.mpr
    intro z hz
    have h : IsShortest L z := hz
    have eq := fixes z (subset_span hz)
    exact subset_span (show IsShortest (lattice D) z from
      ⟨eq ▸ img z h.1,h.2.1,fun w hw hn ↦ (h.2.2 v hv.1 hv.2.1).trans (newfloor w hw hn)⟩)
  have extra : IsShortest (lattice D) (e x) := ⟨img x hx,
    fun h ↦ outside (h ▸ zero_mem _), fun w hw hn ↦ len ▸ newfloor w hw hn⟩
  have inc := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne incl
    (fun he ↦ outside (he ▸ subset_span extra)))
  have hvol : ZLattice.covolume (lattice D) ≤ ZLattice.covolume L := by
    change ZLattice.covolume (span ℤ (Set.range D)) ≤ ZLattice.covolume (span ℤ (Set.range B))
    rw [minkowski_covolume_eq_abs_det,minkowski_covolume_eq_abs_det]
    change |(EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det (e.toLinearMap ∘ B)| ≤ _
    rw [Basis.det_comp,abs_mul,abs_of_pos de.1]
    exact mul_le_of_le_one_left (abs_nonneg _) de.2.le
  have vmin : IsShortest (lattice D) v := ⟨vfixed ▸ img v hv.1,hv.2.1,newfloor⟩
  obtain ⟨C,hC,spanC,volC⟩ := round_basis D vmin
  exact ⟨C,hC,spanC,volC.trans hvol⟩
termination_by n - finrank ℝ (minimalSpan (lattice B))
decreasing_by
  change n - finrank ℝ (minimalSpan (lattice D)) < n - finrank ℝ (minimalSpan (lattice B))
  have hi : finrank ℝ (minimalSpan (lattice D)) ≤ n :=
    (Submodule.finrank_le _).trans_eq finrank_euclideanSpace_fin
  change finrank ℝ (minimalSpan (lattice B)) < finrank ℝ (minimalSpan (lattice D)) at inc
  omega

/-- Every full lattice can be replaced by one with the same shortest vector, no greater
covolume, and a real basis of shortest vectors. The integral generators are supplied by C. -/
theorem wellRounded_reduction (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {v : E} (hv : IsShortest L v) :
    ∃ C D : Basis (Fin n) ℝ E, IsShortest (span ℤ (Set.range C)) v ∧
      (∀ i, IsShortest (span ℤ (Set.range C)) (D i)) ∧
      ZLattice.covolume (span ℤ (Set.range C)) ≤ ZLattice.covolume L := by
  classical
  have rk : finrank ℤ L = n := (ZLattice.rank ℝ L).trans (by simp [CoordSpace])
  let B := ((finBasis ℤ L).reindex (finCongr rk)).ofZLatticeBasis ℝ L
  have hB : lattice B = L := Basis.ofZLatticeBasis_span _ _ _
  obtain ⟨C,hC,hspan,hvol⟩ := round_basis B (v := v) (hB ▸ hv)
  let s : Set (CoordSpace n) := {x | IsShortest (lattice C : Set (CoordSpace n)) x}
  have hs : ⊤ ≤ span ℝ s := hspan.ge
  let D := Basis.ofSpan hs
  let := FiniteDimensional.fintypeBasisIndex D
  let e := Fintype.equivFinOfCardEq ((finrank_eq_card_basis D).symm.trans
    (show finrank ℝ E = n by simp [CoordSpace]))
  refine ⟨C,D.reindex e,hC,fun i ↦ ?_,hB ▸ hvol⟩
  rw [Basis.reindex_apply]
  exact Basis.ofSpan_subset hs (Set.mem_range_self _)

end SigabaNeo.Wall1.Watson

#print axioms SigabaNeo.Wall1.Watson.wellRounded_reduction
