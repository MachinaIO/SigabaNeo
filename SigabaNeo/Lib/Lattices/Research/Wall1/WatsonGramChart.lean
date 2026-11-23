import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonPivotChecks

/-! The ten-coordinate chart and its signed permutation symmetries. -/
noncomputable section
namespace SigabaNeo.Wall1.Watson.Pivot

open Finset Matrix
abbrev I := Fin 5
abbrev M := Matrix I I ℝ

def edgeMap : E →ₗ[ℝ] M where
  toFun x i j := if i = j then 0 else x (edgeIndex i j) / 4
  map_add' x y := by
    ext i j
    change (if i = j then 0 else (x (edgeIndex i j) + y (edgeIndex i j))/4) =
      (if i = j then 0 else x (edgeIndex i j)/4) + (if i = j then 0 else y (edgeIndex i j)/4)
    by_cases h : i = j <;> simp [h,add_div]
  map_smul' a x := by
    ext i j
    change (if i = j then 0 else (a * x (edgeIndex i j))/4) =
      a * (if i = j then 0 else x (edgeIndex i j)/4)
    by_cases h : i = j <;> simp [h,mul_div_assoc]

@[simp] theorem edgeMap_apply (x : E) (i j : I) :
    edgeMap x i j = if i = j then 0 else x (edgeIndex i j) / 4 := rfl

def chart (x : E) : M := 1 + edgeMap x

def coords (A : M) (t : Fin 10) := 4 * A (left t) (right t)

theorem chart_apply (x : E) (i j : I) :
    chart x i j = if i = j then 1 else x (edgeIndex i j) / 4 := by
  by_cases h : i = j <;> simp [chart,h,Matrix.one_apply]

theorem chart_coords {A : M} (sym : A.IsHermitian) (diag : ∀ i, A i i = 1) :
    chart (coords A) = A := by
  have sw (i j : I) : A j i = A i j := by simpa using sym.apply i j
  ext i j
  rw [chart_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [coords,edgeIndex,left,right,Matrix.cons_val,Matrix.of_apply,diag] <;> apply sw

set_option maxHeartbeats 2000000 in
theorem centers_eq (k : Fin 24) : lift (centers k) = vertexEdges k := by
  funext i
  fin_cases k <;> fin_cases i <;> first | rfl | norm_num [lift,centers,unpack,vertexEdges,Matrix.cons_val]

theorem chart_center (k : Fin 24) : chart (lift (centers k)) = gramVertex k := by
  rw [centers_eq]
  ext i j
  rw [chart_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [gramVertex,Five.mat,edgeIndex,Matrix.cons_val,Matrix.of_apply] <;> ring

theorem chart_energy (x : E) (z : Z) :
    2 * (gramValue (chart x) z - 1) =
      2 * ((sqSum z : ℝ) - 1) + lift (normal z) ⬝ᵥ x := by
  simp [gramValue, dotProduct, mulVec, Fin.sum_univ_succ, chart_apply, edgeIndex, normal, lift,
    left, right, sqSum, Matrix.cons_val, Matrix.of_apply]
  ring

def coeff (s : I → Bool) (i : I) : ℝ := signInt (s i)

@[simp] theorem coeff_abs (s : I → Bool) (i : I) : |coeff s i| = 1 := by
  cases h : s i <;> norm_num [coeff,signInt,h]

@[simp] theorem coeff_sq (s : I → Bool) (i : I) : coeff s i * coeff s i = 1 := by
  cases h : s i <;> norm_num [coeff,signInt,h]

structure Action where
  perm : Equiv.Perm I
  flip : I → Bool
  deriving Fintype

def Action.map (a : Action) : M →ₗ[ℝ] M where
  toFun A i j := coeff a.flip i * coeff a.flip j * A (a.perm i) (a.perm j)
  map_add' X Y := by ext i j; exact mul_add _ _ _
  map_smul' c X := by ext i j; exact mul_left_comm _ _ _

@[simp] theorem Action.map_apply (a : Action) (A : M) (i j : I) :
    a.map A i j = coeff a.flip i * coeff a.flip j * A (a.perm i) (a.perm j) := rfl

def Action.comp (a b : Action) : Action :=
  ⟨a.perm.trans b.perm, fun i ↦ (a.flip i).xor (b.flip (a.perm i))⟩

def Action.inv (a : Action) : Action := ⟨a.perm.symm, fun i ↦ a.flip (a.perm.symm i)⟩

theorem Action.map_comp (a b : Action) (X : M) : (a.comp b).map X = a.map (b.map X) := by
  have sign (i : I) : coeff (a.comp b).flip i = coeff a.flip i * coeff b.flip (a.perm i) := by
    cases h : a.flip i <;> cases h' : b.flip (a.perm i) <;> norm_num [Action.comp, coeff,signInt,h,h']
  ext i j
  change coeff (a.comp b).flip i * coeff (a.comp b).flip j * _ = _ * _ * (_ * _ * _)
  rw [sign,sign]
  dsimp [Action.comp]
  ring

theorem Action.map_inv (a : Action) (X : M) : a.map (a.inv.map X) = X := by
  ext i j
  cases hi : a.flip i <;> cases hj : a.flip j <;> simp [Action.inv,coeff,signInt,hi,hj]

theorem Action.map_mem (a : Action) {X : M} (h : X ∈ gramPolytope) :
    a.map X ∈ gramPolytope := by
  obtain ⟨⟨⟨box,sym⟩,diag⟩,tests⟩ := h
  refine ⟨⟨⟨fun i j ↦ ?_,?_⟩,fun i ↦ ?_⟩,fun z hn ht ↦ ?_⟩
  · apply abs_le.mp
    simpa [abs_mul] using abs_le.mpr (box (a.perm i) (a.perm j))
  · ext i j
    have hh := sym.apply (a.perm i) (a.perm j)
    simp only [star_trivial] at hh
    simp [hh,mul_comm]
  · rw [Action.map_apply,coeff_sq,one_mul,diag]
  · let w : Z := fun t ↦ signInt (a.flip (a.perm.symm t)) * z (a.perm.symm t)
    have absw (i : I) : |w i| = |z (a.perm.symm i)| := by
      cases hh : a.flip (a.perm.symm i) <;> simp [w,hh,signInt]
    have wn : w ≠ 0 := by
      intro hw
      apply hn
      funext i
      have := absw (a.perm i)
      simpa [hw,eq_comm] using this
    have wt : GramTest w := by
      rcases ht with h | ⟨i,hi,hr⟩
      · exact Or.inl fun j ↦ (absw j).trans_le (h _)
      · refine Or.inr ⟨a.perm i,by simpa [absw] using hi,fun j ne ↦ ?_⟩
        rw [absw,hr]
        exact fun he ↦ ne (a.perm.symm_apply_eq.mp he)
    have eq : gramValue X w = gramValue (a.map X) z := by
      simp only [gramValue,dotProduct,mulVec,Finset.mul_sum]
      rw [← Equiv.sum_comp a.perm]
      apply sum_congr rfl
      intro i _
      rw [← Equiv.sum_comp a.perm]
      apply sum_congr rfl
      intro j _
      simp [w,coeff]
      ring
    exact eq ▸ tests w wn wt

theorem chart_image {im : Image} (h : im.Valid) :
    ∃ a : Action, chart (lift (unpack im.edges)) = a.map (gramVertex im.rep) := by
  let a : Action := ⟨Equiv.ofBijective im.permutation
    ((Finite.injective_iff_bijective).mp h.1), im.flip⟩
  refine ⟨a,?_⟩
  rw [← chart_center]
  have lr (i : Fin 10) : left i ≠ right i := by fin_cases i <;> decide
  have ij (i : Fin 10) : a.perm (left i) ≠ a.perm (right i) := a.perm.injective.ne (lr i)
  have edge (i : Fin 10) : chart (lift (unpack im.edges)) (left i) (right i) =
      a.map (chart (lift (centers im.rep))) (left i) (right i) := by
    have idx : edgeIndex (left i) (right i) = i := by fin_cases i <;> rfl
    have ne : im.permutation (left i) ≠ im.permutation (right i) := ij i
    simp [chart_apply,lr i,ne,idx,lift,h.2 i,coeff,a,mul_div_assoc]
  have sym (x : E) (i j : I) : chart x j i = chart x i j := by
    rw [chart_apply,chart_apply]
    fin_cases i <;> fin_cases j <;> rfl
  have sym' (i j : I) : a.map (chart (lift (centers im.rep))) j i =
      a.map (chart (lift (centers im.rep))) i j := by
    simp [sym _ (a.perm i) (a.perm j),mul_comm]
  ext i j
  by_cases eq : i = j
  · subst j
    simp [chart_apply]
  · have unordered : ∃ t, (i = left t ∧ j = right t) ∨ (j = left t ∧ i = right t) := by
      fin_cases i <;> fin_cases j <;> first | contradiction | decide
    obtain ⟨t,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := unordered
    · exact edge t
    · rw [sym,sym']; exact edge t

end SigabaNeo.Wall1.Watson.Pivot

#print axioms SigabaNeo.Wall1.Watson.Pivot.chart_image
#print axioms SigabaNeo.Wall1.Watson.Pivot.Action.map_mem
