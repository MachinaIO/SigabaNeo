import SigabaNeo.Lib.Lattices.Research.Wall1.QuotientMinimum
import SigabaNeo.Lib.Lattices.Reduction.Slide.Update

/-! Primitive unfolding before disintegration over the marked vector. -/

noncomputable section
open MeasureTheory Matrix SigabaNeo.Rogers
open scoped ENNReal Pointwise
namespace SigabaNeo.Wall1

private theorem exists_completion {n : ℕ} (hn : 2 ≤ n) (v : ContentFiber n 1) :
    ∃ A : SpecialLinearGroup (Fin n) ℤ, A.val *ᵥ Pi.single (⟨0, by omega⟩ : Fin n) 1 =
      v.val.val := by
  classical
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hji : j ≠ i := by intro h; have := congrArg Fin.val h; simp [i, j] at this
  obtain ⟨U,V,hVU,hUv⟩ := SigabaNeo.Slide.primitive_completion v.val.val i v.val.property
    (by
      intro t z h
      have hc := v.property
      change (Finset.univ.gcd fun a ↦ (v.val.val a).natAbs) = 1 at hc
      rw [h] at hc
      simp only [Pi.smul_apply, smul_eq_mul, Int.natAbs_mul, Finset.gcd_mul_left,
        normalize_eq] at hc
      exact Int.isUnit_iff.mp <| Int.isUnit_iff_natAbs_eq.mpr (Nat.eq_one_of_dvd_one ⟨_, hc.symm⟩))
  have hd := congrArg Matrix.det hVU
  rw [det_mul, det_one] at hd
  have hd' : V.det = 1 ∨ V.det = -1 := Int.isUnit_iff.mp (isUnit_of_dvd_one ⟨_, hd.symm⟩)
  let d := Function.update (fun _ : Fin n ↦ (1 : ℤ)) j V.det
  have hdet : (diagonal d).det = V.det := by simp [d, det_diagonal, Finset.prod_update_of_mem]
  refine ⟨⟨V * diagonal d, by rw [det_mul, hdet]; rcases hd' with h|h <;> simp [h]⟩, ?_⟩
  change (V * diagonal d) *ᵥ Pi.single i 1 = _
  have hfix : diagonal d *ᵥ Pi.single i 1 = Pi.single i 1 := by
    ext k
    by_cases hk : k = i
    · subst k; simp [mulVec_diagonal, d, Ne.symm hji]
    · simp [mulVec_diagonal, Pi.single_eq_of_ne hk]
  rw [← mulVec_mulVec, hfix, ← hUv, mulVec_mulVec, hVU, one_mulVec]

/-- One determinant-one integral completion for each oriented primitive mark. -/
def primitiveFrame {n : ℕ} (hn : 2 ≤ n) (v : ContentFiber n 1) :=
  (exists_completion hn v).choose

theorem primitiveFrame_column {n : ℕ} (hn : 2 ≤ n) (v : ContentFiber n 1) :
    (primitiveFrame hn v).val *ᵥ Pi.single (⟨0, by omega⟩ : Fin n) 1 = v.val.val :=
  (exists_completion hn v).choose_spec

/-- Right translation taking the first coordinate mark to the given primitive mark. -/
def primitiveTranslate {n : ℕ} (hn : 2 ≤ n) (v : ContentFiber n 1) : (integerGroup n).op :=
  ⟨MulOpposite.op (SpecialLinearGroup.map (Int.castRingHom ℝ) (primitiveFrame hn v)),
    ⟨primitiveFrame hn v, rfl⟩⟩

private theorem translate_injective {n : ℕ} (hn : 2 ≤ n) :
    Function.Injective (primitiveTranslate hn) := by
  intro v w h
  have e : (primitiveFrame hn v).val = (primitiveFrame hn w).val := by
    ext i j
    have := congrArg (fun a : (integerGroup n).op ↦ a.val.unop.val i j) h
    change ((primitiveFrame hn v).val i j : ℝ) = ((primitiveFrame hn w).val i j : ℝ) at this
    exact_mod_cast this
  exact Subtype.ext (Subtype.ext (by rw [← primitiveFrame_column hn v, ← primitiveFrame_column hn w, e]))

/-- Unfold the oriented primitive sum onto a union of right translates. The test may
inspect every column of the completed frame. Stabilizer-invariant tests in particular
can inspect the projected lattice. -/
theorem primitive_frame_unfolding {n : ℕ} (hn : 2 ≤ n) (D : Set (SL n))
    (hm : MeasurableSet D) (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    (F : SL n → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ g in D, ∑' v, F (primitiveTranslate hn v • g) ∂groupHaar n) =
      ∫⁻ g in ⋃ v, primitiveTranslate hn v • D, F g ∂groupHaar n := by
  let := groupHaar_rightInvariant n
  let : BorelSpace (SL n) := ⟨rfl⟩
  let e (v : ContentFiber n 1) := MeasurableEquiv.mulRight (primitiveTranslate hn v).val.unop
  have he (v : ContentFiber n 1) : e v '' D = primitiveTranslate hn v • D := rfl
  change (∫⁻ g in D, ∑' v, (F ∘ e v) g ∂groupHaar n) = _
  rw [lintegral_tsum (fun v ↦ (hF.comp (e v).measurable).aemeasurable)]
  rw [lintegral_iUnion₀ (s := fun v ↦ primitiveTranslate hn v • D) (fun v ↦ (he v ▸ (e v).measurableEmbedding.measurableSet_image.mpr hm).nullMeasurableSet)
    (fun _ _ h ↦ hd.aedisjoint ((translate_injective hn).ne h))]
  exact tsum_congr fun v ↦ (measurePreserving_mul_right (groupHaar n) _).setLIntegral_comp_emb
    (e v).measurableEmbedding F D

private def axis {n : ℕ} (hn : 2 ≤ n) : Fin n → ℤ :=
  Pi.single ⟨0, by omega⟩ 1

private theorem latticePoint_translate {n : ℕ} (hn : 2 ≤ n) (g : SL n)
    (v : ContentFiber n 1) (z : Fin n → ℤ) :
    latticePoint (primitiveTranslate hn v • g) z =
      latticePoint g (primitiveFrame hn v • z) := by
  change WithLp.toLp 2 ((g * _) • _) = WithLp.toLp 2 (g • _)
  rw [mul_smul]
  congr 2
  exact funext fun j ↦ (RingHom.map_mulVec (Int.castRingHom ℝ) (primitiveFrame hn v).val z j).symm

/-- Physical projected lattice, expressed in the ambient Euclidean coordinates. -/
def projectedPoints {n : ℕ} (g : SL n) (z : Fin n → ℤ) : Set (E n) :=
  Set.range fun u ↦ (ℝ ∙ latticePoint g z)ᗮ.starProjection (latticePoint g u)

/-- Unfold a test of the marked vector and its entire physical projected lattice.
Measurability is required only of its pullback to real frames. -/
theorem primitive_projected_unfolding {n : ℕ} (hn : 2 ≤ n) (D : Set (SL n))
    (hm : MeasurableSet D) (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    (F : E n → Set (E n) → ℝ≥0∞)
    (hF : Measurable fun g ↦ F (latticePoint g (Pi.single (⟨0, by omega⟩ : Fin n) 1))
      (projectedPoints g (Pi.single (⟨0, by omega⟩ : Fin n) 1))) :
    (∫⁻ g in D, ∑' v : ContentFiber n 1,
      F (latticePoint g v.val.val) (projectedPoints g v.val.val) ∂groupHaar n) =
      ∫⁻ g in ⋃ v, primitiveTranslate hn v • D,
        F (latticePoint g (Pi.single (⟨0, by omega⟩ : Fin n) 1))
          (projectedPoints g (Pi.single (⟨0, by omega⟩ : Fin n) 1)) ∂groupHaar n := by
  rw [← primitive_frame_unfolding hn D hm hd _ hF]
  apply lintegral_congr
  intro g
  apply tsum_congr
  intro v
  have col : primitiveFrame hn v • axis hn = v.val.val := primitiveFrame_column hn v
  change F _ _ = F (latticePoint (primitiveTranslate hn v • g) (axis hn)) _
  rw [latticePoint_translate, col]
  congr 1
  unfold projectedPoints
  simp_rw [latticePoint_translate]
  change Set.range _ = Set.range (fun u ↦ (ℝ ∙ latticePoint g (primitiveFrame hn v • axis hn))ᗮ.starProjection
    (latticePoint g (primitiveFrame hn v • u)))
  rw [col]
  exact ((MulAction.surjective (primitiveFrame hn v)).range_comp _).symm

private theorem measurable_point {n : ℕ} (z : Fin n → ℤ) :
    Measurable (fun g : SL n ↦ latticePoint g z) := by
  let : BorelSpace (SL n) := ⟨rfl⟩
  apply Continuous.measurable
  apply (PiLp.continuous_toLp 2 _).comp
  change Continuous (fun g : SL n ↦ g.val.mulVec _)
  unfold Matrix.mulVec dotProduct
  fun_prop

/-- The first-column marginal of the unfolded domain, divided by the original
domain mass, is Lebesgue measure divided by the positive zeta series. -/
theorem primitive_unfolded_marginal {n : ℕ} (hn : 2 ≤ n) (D : Set (SL n))
    (hm : MeasurableSet D) (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    (hp : groupHaar n D ≠ 0) (hf : groupHaar n D ≠ ⊤) (f : E n → ℝ≥0∞)
    (h : Measurable f) :
    (∫⁻ g in ⋃ v, primitiveTranslate hn v • D,
      f (latticePoint g (Pi.single (⟨0, by omega⟩ : Fin n) 1)) ∂groupHaar n) / groupHaar n D =
      (∫⁻ x, f x) / ∑' k, dilationWeight n k := by
  have eqn := primitive_projected_unfolding hn D hm hd (fun x _ ↦ f x)
    (h.comp (measurable_point _))
  rw [← eqn]
  have meas (v : ContentFiber n 1) : Measurable (fun g : SL n ↦ f (latticePoint g v.val.val)) :=
    h.comp (measurable_point _)
  rw [lintegral_tsum (fun v ↦ (meas v).aemeasurable)]
  obtain ⟨C, prim, mass⟩ := siegel_primitive_orbit_covolume n hn D hm hd hf
  have hc : C ≠ 0 := fun e ↦ hp (by simpa [e] using mass.symm)
  have hz : (∑' k, dilationWeight n k) ≠ 0 := fun e ↦ hp (by simpa [e] using mass.symm)
  have hfin := (ENNReal.lt_top_of_mul_ne_top_left (mass ▸ hf) hz).ne
  change (∑' v : ContentFiber n 1, vectorOrbitalIntegral D f v.val) / _ = _
  rw [prim f h, ← mass, ENNReal.mul_div_mul_left _ _ hc hfin]

#print axioms primitiveFrame_column
#print axioms primitive_frame_unfolding
#print axioms primitive_projected_unfolding
#print axioms primitive_unfolded_marginal
end SigabaNeo.Wall1
