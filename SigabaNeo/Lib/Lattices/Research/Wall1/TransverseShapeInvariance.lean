import SigabaNeo.Lib.Lattices.Research.Wall1.TransverseUniqueness

/-! Parent invariance of the joint law on marks and arithmetic quotient shapes. -/
noncomputable section
open MeasureTheory SigabaNeo.Rogers
open scoped ENNReal
namespace SigabaNeo.Wall1

/-- The geometric point set determines the arithmetic coset. -/
theorem latticeSpace_points_injective {m : ℕ} : Function.Injective (@points m) := by
  intro L L' hp
  induction L using Quotient.inductionOn with
  | _ g =>
    induction L' using Quotient.inductionOn with
    | _ h =>
      change points (QuotientGroup.mk g) = points (QuotientGroup.mk h) at hp
      rw [points_mk, points_mk] at hp
      have col (j : Fin m) : ∃ z : Fin m → ℤ, g • (fun k ↦ (z k : ℝ)) =
          h.val.col j := by
        have hmem : WithLp.toLp 2 (h.val.col j) ∈ Set.range (fun z : Fin m → ℤ ↦
            WithLp.toLp 2 (h • fun k ↦ (z k : ℝ))) := by
          refine ⟨Pi.single j 1, ?_⟩
          apply congrArg (WithLp.toLp 2)
          change h.val.mulVec _ = _
          convert Matrix.mulVec_single_one h.val j using 2
          ext k
          by_cases hk : k = j <;> simp [hk]
        rw [← hp] at hmem
        obtain ⟨z, hz⟩ := hmem
        exact ⟨z, WithLp.toLp_injective 2 hz⟩
      choose z hz using col
      let A : Matrix (Fin m) (Fin m) ℤ := Matrix.of fun i j ↦ z j i
      have hmat : g.val * A.map (Int.castRingHom ℝ) = h.val := by
        ext i j
        exact congrFun (hz j) i
      have hc : A.det = 1 := by
        have e := congrArg Matrix.det hmat
        rw [Matrix.det_mul, g.property, h.property, one_mul] at e
        have ed := (Int.castRingHom ℝ).map_det A
        change (A.det : ℝ) = (A.map (Int.castRingHom ℝ)).det at ed
        exact_mod_cast ed.trans e
      apply QuotientGroup.eq.mpr
      refine ⟨⟨A, hc⟩, ?_⟩
      apply (mul_left_cancel (a := g))
      rw [← mul_assoc, mul_inv_cancel, one_mul]
      exact Subtype.ext hmat

/-- Joint left invariance for arbitrary measurable tests on mark and transverse shape. -/
theorem transverseShape_left_invariant {m : ℕ} (i : Fin m) (hn : 2 ≤ m+1)
    (D : Set (SL (m+1))) (hm : MeasurableSet D)
    (hd : IsFundamentalDomain (integerGroup (m+1)).op D (groupHaar (m+1)))
    (a : SL (m+1)) (F : E (m+1) × LatticeSpace m → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ g, F (markedColumn hn (a * g), transverseShape i (a * g)) ∂primitiveIncidence hn D) =
      ∫⁻ g, F (markedColumn hn g, transverseShape i g) ∂primitiveIncidence hn D := by
  let tail (x y : E (m+1)) := WithLp.toLp 2 (fun j : Fin m ↦ transverseRotation i x y j.succ)
  let test (x : E (m+1)) (P : Set (E (m+1))) :=
    F (x, Function.invFun (@points m) (tail x '' P))
  have eqn (g : SL (m+1)) :
      test (markedColumn hn g) (Set.range (normalizedProjection hn g)) =
      F (markedColumn hn g, transverseShape i g) := by
    unfold test
    rw [← Set.range_comp, show Set.range (tail (markedColumn hn g) ∘ normalizedProjection hn g) =
      points (transverseShape i g) from (transverseShape_points i hn g).symm,
      Function.leftInverse_invFun latticeSpace_points_injective]
  simpa only [eqn] using normalizedProjection_left_invariant hn D hm hd a test (by
    simp only [eqn]
    exact hF.comp ((measurable_markedColumn hn).prodMk (measurable_transverseShape i)))

#print axioms latticeSpace_points_injective
#print axioms transverseShape_left_invariant
end SigabaNeo.Wall1
