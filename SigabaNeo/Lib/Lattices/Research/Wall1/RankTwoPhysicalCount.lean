import SigabaNeo.Lib.Lattices.Research.Wall1.RankTwoProduct
import SigabaNeo.Lib.Lattices.Research.Wall1.RankTwoOuterGeometry

/-! The bounded physical count with one summand per saturated grid plane. -/
noncomputable section
open MeasureTheory SigabaNeo.Rogers
open scoped ENNReal
namespace SigabaNeo.Wall1.RankTwo

variable {r : ℕ}
local notation "n" => (r+2)
local notation "m" => (r+1)

/-- The two-vector basis chosen by the existing Borel basis domain for a saturated plane. -/
def selectedPhysical (hr : 2 ≤ m) (g : SL n) (P : Plane n) : Frames n :=
  physical hr g 0 0 (unique_basis hr g P).exists.choose.val

def physicalGate (a ℓ c : ℝ) (g : SL n) (x : Frames n) : Prop :=
  x ∈ planeWindow n a ℓ ∧ ∃ z : IV n,
    let v := (Submodule.span ℝ (Set.range x))ᗮ.starProjection (latticePoint g z)
    0 < ‖v‖ ∧ ‖v‖ < c

/-- The joint measure of the bounded event is the expected number of saturated planes
passing the area, internal length, and physical twice-projected minimum tests. -/
theorem physical_count_eq (i : Fin m) (j : Fin r) (D : Set (SL n)) (a ℓ c : ℝ) :
    let hr : 2 ≤ m := by have := j.isLt; omega
    (∫⁻ g in D, ∑' P : Plane n, {x | physicalGate a ℓ c g x}.indicator 1
      (selectedPhysical hr g P) ∂groupHaar n) / groupHaar n D =
        joint i j D (boundedEvent r a ℓ c) := by
  classical
  intro hr
  rw [joint_apply i j D _ (measurableSet_boundedEvent ..)]
  congr 1
  apply lintegral_congr
  intro g
  let f (p : Core m) := ((Prod.fst ⁻¹' basisDomain n) ∩ boundedEvent r a ℓ c).indicator
    (1 : Frames n × LatticeSpace r → ℝ≥0∞) (incidenceMark i j p g)
  change _ = ∑' p, f p
  rw [← (Equiv.sigmaFiberEquiv (plane hr)).tsum_eq f, tsum_sigma']
  apply tsum_congr
  intro P
  let u := (unique_basis hr g P).exists.choose
  have hu : physical hr g 0 0 u.val ∈ basisDomain n := (unique_basis hr g P).exists.choose_spec
  rw [tsum_eq_single u]
  · let x := physical hr g 0 0 u.val
    change {v | physicalGate a ℓ c g v}.indicator 1 x = f u.val
    have hgeo := outerMinimumGeometry i j g u.val c
    change QuotientGroup.mk (outerFrame i j u.val g) ∈ shortShape (c * area x ^ (r : ℝ)⁻¹) ↔ _ at hgeo
    have e : incidenceMark i j u.val g ∈ (Prod.fst ⁻¹' basisDomain n) ∩ boundedEvent r a ℓ c ↔
        physicalGate a ℓ c g x := by
      exact ⟨fun h ↦ ⟨h.2.1,hgeo.mp h.2.2⟩, fun h ↦ ⟨hu,h.1,hgeo.mpr h.2⟩⟩
    unfold f
    by_cases h : physicalGate a ℓ c g x
    · rw [Set.indicator_of_mem (e.mpr h), Set.indicator_of_mem h]
      rfl
    · rw [Set.indicator_of_notMem (e.not.mpr h), Set.indicator_of_notMem h]
  · intro q hq
    apply Set.indicator_of_notMem
    intro h
    exact hq ((unique_basis hr g P).unique h.1 hu)

/-- An unconditional bound on the physical count against the plane marginal. -/
theorem bounded_physical_count (hr : 2 ≤ r) (D : Set (SL n))
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hf : groupHaar n D ≠ ⊤)
    (hp : groupHaar n D ≠ 0) (a ℓ c : ℝ) (hc : 0 < c) :
    (∫⁻ g in D, ∑' P : Plane n, {x | physicalGate a ℓ c g x}.indicator 1
      (selectedPhysical (by omega) g P) ∂groupHaar n) / groupHaar n D ≤
      ∫⁻ x in planeWindow n a ℓ,
        min 1 (ENNReal.ofReal (c^r * area x) * volume (Metric.ball (0 : E r) 1) /
          (2 * zetaFactor r)) ∂planeMarginal n := by
  let j : Fin r := ⟨0, by omega⟩
  rw [physical_count_eq (0 : Fin m) j]
  exact bounded_count 0 j hr D hd hf hp a ℓ c hc

end SigabaNeo.Wall1.RankTwo

#print axioms SigabaNeo.Wall1.RankTwo.physical_count_eq
#print axioms SigabaNeo.Wall1.RankTwo.bounded_physical_count
