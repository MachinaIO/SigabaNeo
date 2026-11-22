import SigabaNeo.Lib.Lattices.Research.Wall1.TransverseHaar

/-! Left invariance of the unfolded integral for tests of the unlabelled projection. -/

noncomputable section
open MeasureTheory Matrix SigabaNeo.Rogers
open scoped ENNReal Pointwise
namespace SigabaNeo.Wall1

private def content {n : ℕ} (v : Fin n → ℤ) := Finset.univ.gcd fun i ↦ (v i).natAbs

private theorem content_dvd_act {n : ℕ} (a : Matrix.SpecialLinearGroup (Fin n) ℤ)
    (v : Fin n → ℤ) : content v ∣ content (a • v) := by
  apply Finset.dvd_gcd
  intro i _
  apply Int.natCast_dvd.mp
  change (content v : ℤ) ∣ ∑ j, a.val i j * v j
  exact Finset.dvd_sum fun j _ ↦ dvd_mul_of_dvd_right
    (Int.natCast_dvd.mpr (Finset.gcd_dvd (f := fun i ↦ (v i).natAbs) (Finset.mem_univ j))) _

private def actPrim {n : ℕ} (a : Matrix.SpecialLinearGroup (Fin n) ℤ)
    (v : ContentFiber n 1) : ContentFiber n 1 :=
  ⟨⟨a • v.val.val, fun h ↦ v.val.property ((MulAction.injective a)
    (h.trans (Matrix.mulVec_zero a.val).symm))⟩, by
    change content (a • v.val.val) = 1
    refine Eq.trans (b := content v.val.val) ?_ v.property
    apply Nat.dvd_antisymm _ (content_dvd_act a _)
    simpa using content_dvd_act a⁻¹ (a • v.val.val)⟩

private def primEquiv {n : ℕ} (a : Matrix.SpecialLinearGroup (Fin n) ℤ) :
    ContentFiber n 1 ≃ ContentFiber n 1 where
  toFun := actPrim a
  invFun := actPrim a⁻¹
  left_inv _ := Subtype.ext (Subtype.ext (inv_smul_smul a _))
  right_inv _ := Subtype.ext (Subtype.ext (smul_inv_smul a _))

private theorem point_cast {n : ℕ} (g : SL n) (a : SpecialLinearGroup (Fin n) ℤ)
    (z : Fin n → ℤ) :
    latticePoint (g * SpecialLinearGroup.map (Int.castRingHom ℝ) a) z =
      latticePoint g (a • z) := by
  change WithLp.toLp 2 ((_ * _) • _) = WithLp.toLp 2 (_ • _)
  rw [mul_smul]
  congr 2
  exact funext fun j ↦ (RingHom.map_mulVec (Int.castRingHom ℝ) a.val z j).symm

private theorem projected_cast {n : ℕ} (g : SL n) (a : SpecialLinearGroup (Fin n) ℤ)
    (z : Fin n → ℤ) :
    projectedPoints (g * SpecialLinearGroup.map (Int.castRingHom ℝ) a) z =
      projectedPoints g (a • z) := by
  unfold projectedPoints
  simp_rw [point_cast]
  have hs : Function.Surjective (fun u : Fin n → ℤ ↦ a • u) := MulAction.surjective a
  exact hs.range_comp (fun u ↦ (ℝ ∙ latticePoint g (a • z))ᗮ.starProjection (latticePoint g u))

/-- Left translation of a real frame preserves every unfolded integral depending
only on the marked column and its unlabelled projected lattice. The projection on
the translated side is recomputed after applying the real linear transformation. -/
theorem transverse_left_invariant {n : ℕ} (hn : 2 ≤ n) (D : Set (SL n))
    (hm : MeasurableSet D) (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    (a : SL n) (F : E n → Set (E n) → ℝ≥0∞)
    (hF : Measurable fun g ↦ F (markedColumn hn g)
      (projectedPoints g (Pi.single (⟨0, by omega⟩ : Fin n) 1))) :
    (∫⁻ g, F (markedColumn hn (a * g))
      (projectedPoints (a * g) (Pi.single (⟨0, by omega⟩ : Fin n) 1))
      ∂primitiveIncidence hn D) =
    ∫⁻ g, F (markedColumn hn g)
      (projectedPoints g (Pi.single (⟨0, by omega⟩ : Fin n) 1))
      ∂primitiveIncidence hn D := by
  have : Countable (Matrix (Fin n) (Fin n) ℤ) := inferInstanceAs (Countable (Fin n → Fin n → ℤ))
  let φ := Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (n := Fin n)
  have : Countable (Matrix.SpecialLinearGroup (Fin n) ℤ) := Subtype.val_injective.countable
  have : Countable (integerGroup n) := φ.rangeRestrict_surjective.countable
  have : Countable (integerGroup n).op := (integerGroup n).equivOp.surjective.countable
  let := groupHaar_rightInvariant n
  let : BorelSpace (SL n) := ⟨rfl⟩
  let : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℝ))
  let : LocallyCompactSpace (SL n) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace
  let : (groupHaar n).IsMulLeftInvariant :=
    inferInstanceAs (Measure.haar : Measure (SL n)).IsMulLeftInvariant
  let e := MeasurableEquiv.mulLeft a
  have hd' := hd.image_of_equiv e.toEquiv
    (measurePreserving_mul_left (groupHaar n) a⁻¹).quasiMeasurePreserving
    (Equiv.refl _) (fun b x ↦ (mul_assoc a x b.val.unop).symm)
  let U := ⋃ v, primitiveTranslate hn v • D
  have image : e '' U = ⋃ v, primitiveTranslate hn v • (e '' D) := by
    unfold U
    rw [Set.image_iUnion]
    congr 1
    funext v
    change e '' ((fun g ↦ g * _) '' D) = (fun g ↦ g * _) '' (e '' D)
    simp only [Set.image_image]
    congr 1
    funext g
    exact (mul_assoc ..).symm
  let W := fun g : SL n ↦ ∑' v : ContentFiber n 1,
    F (latticePoint g v.val.val) (projectedPoints g v.val.val)
  have inv (b : (integerGroup n).op) (g : SL n) : W (b • g) = W g := by
    obtain ⟨t, ht⟩ := (show b.val.unop ∈ integerGroup n from b.property)
    unfold W
    rw [← (primEquiv t).tsum_eq (fun v ↦ F (latticePoint g v.val.val)
      (projectedPoints g v.val.val))]
    apply tsum_congr
    intro v
    change F (latticePoint (g * b.val.unop) _) (projectedPoints (g * b.val.unop) _) = _
    rw [← ht, point_cast, projected_cast]
    rfl
  unfold primitiveIncidence
  rw [lintegral_smul_measure, lintegral_smul_measure]
  congr 1
  change (∫⁻ g in U, _ ∂groupHaar n) = _
  rw [(measurePreserving_mul_left (groupHaar n) a).setLIntegral_comp_emb
    e.measurableEmbedding (fun g ↦ F (markedColumn hn g)
      (projectedPoints g (Pi.single (⟨0, by omega⟩ : Fin n) 1))) U]
  change (∫⁻ g in e '' U, _ ∂groupHaar n) = _
  rw [image]
  unfold markedColumn
  rw [← primitive_projected_unfolding hn (e '' D)
    (e.measurableEmbedding.measurableSet_image.mpr hm) hd' F hF,
    ← primitive_projected_unfolding hn D hm hd F hF]
  exact hd'.setLIntegral_eq hd W inv

/-- Joint invariance for the range of the determinant-normalized projection. -/
theorem normalizedProjection_left_invariant {n : ℕ} (hn : 2 ≤ n) (D : Set (SL n))
    (hm : MeasurableSet D) (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    (a : SL n) (F : E n → Set (E n) → ℝ≥0∞)
    (hF : Measurable fun g ↦ F (markedColumn hn g)
      (Set.range (normalizedProjection hn g))) :
    (∫⁻ g, F (markedColumn hn (a * g))
      (Set.range (normalizedProjection hn (a * g)))
      ∂primitiveIncidence hn D) =
    ∫⁻ g, F (markedColumn hn g)
      (Set.range (normalizedProjection hn g))
      ∂primitiveIncidence hn D := by
  let H := fun (x : E n) (P : Set (E n)) ↦
    F x ((fun y ↦ ‖x‖ ^ ((n - 1 : ℕ) : ℝ)⁻¹ • y) '' P)
  have eqn (g : SL n) : H (markedColumn hn g)
      (projectedPoints g (Pi.single (⟨0, by omega⟩ : Fin n) 1)) =
      F (markedColumn hn g) (Set.range (normalizedProjection hn g)) := by
    simp only [H, projectedPoints, ← Set.range_comp]
    rfl
  simpa only [eqn] using transverse_left_invariant hn D hm hd a H (by simpa only [eqn] using hF)

#print axioms normalizedProjection_left_invariant
#print axioms transverse_left_invariant
end SigabaNeo.Wall1
