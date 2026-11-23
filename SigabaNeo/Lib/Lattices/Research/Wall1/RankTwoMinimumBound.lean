import SigabaNeo.Lib.Lattices.Research.Wall1.RankTwoTransverse

/-! The area and short-internal-vector window of Part 190, for a unimodular parent.
The bound below takes the general rank-two Haar product as an explicit hypothesis. -/

noncomputable section
open MeasureTheory SigabaNeo.Rogers
open scoped ENNReal
namespace SigabaNeo.Wall1.RankTwo

/-- Covolume of the two-vector parallelogram. -/
def area {n : ℕ} (x : Frames n) := Real.sqrt (Matrix.gram ℝ x).det

theorem measurable_area {n : ℕ} : Measurable (@area n) := by
  unfold area
  simp only [Matrix.det_fin_two, Matrix.gram_apply]
  fun_prop

/-- Area at most a, and a nonzero integer linear combination of length at most ℓ. -/
def planeWindow (n : ℕ) (a ℓ : ℝ) : Set (Frames n) :=
  {x | area x ≤ a ∧ ∃ s t : ℤ, 0 < ‖s • x 0 + t • x 1‖ ∧ ‖s • x 0 + t • x 1‖ ≤ ℓ}

theorem measurableSet_planeWindow (n : ℕ) (a ℓ : ℝ) : MeasurableSet (planeWindow n a ℓ) := by
  unfold planeWindow
  rw [Set.ofPred_and]
  apply (measurableSet_le measurable_area measurable_const).inter
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion; intro s
  apply MeasurableSet.iUnion; intro t
  have h : Measurable (fun x : Frames n ↦ ‖s • x 0 + t • x 1‖) :=
    (((measurable_pi_apply 0).const_smul s).add ((measurable_pi_apply 1).const_smul t)).norm
  exact (measurableSet_lt measurable_const h).inter (measurableSet_le h measurable_const)

variable {r : ℕ}
local notation "n" => (r+2)

/-- Test the strict outer minimum at the cutoff c A^(1/r) in unimodular coordinates. -/
def boundedEvent (r : ℕ) (a ℓ c : ℝ) : Set (Frames (r+2) × LatticeSpace r) :=
  {p | p.1 ∈ planeWindow (r+2) a ℓ ∧ p.2 ∈ shortShape (c * area p.1 ^ (r : ℝ)⁻¹)}

theorem measurableSet_boundedEvent (a ℓ c : ℝ) : MeasurableSet (boundedEvent r a ℓ c) := by
  unfold boundedEvent
  rw [Set.ofPred_and]
  apply (measurable_fst (measurableSet_planeWindow n a ℓ)).inter
  have he : {p : Frames n × LatticeSpace r | p.2 ∈ shortShape (c * area p.1 ^ (r : ℝ)⁻¹)} =
      ⋃ q : ℚ, (Prod.snd ⁻¹' shortShape (q : ℝ)) ∩ {p | (q : ℝ) < c * area p.1 ^ (r : ℝ)⁻¹} := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨v,hv,hp,ht⟩
      obtain ⟨q,hq,hq'⟩ := exists_rat_btwn ht
      exact ⟨q,⟨v,hv,hp,hq⟩,hq'⟩
    · rintro ⟨q,⟨v,hv,hp,ht⟩,hq⟩; exact ⟨v,hv,hp,ht.trans hq⟩
  rw [he]
  exact MeasurableSet.iUnion fun q ↦ (measurable_snd (measurableSet_shortShape _)).inter
    (measurableSet_lt measurable_const (measurable_const.mul
      ((measurable_area.comp measurable_fst).pow_const _)))

/-- Part 190's bounded count, retaining the cap at one and integrating the actual
internal window against its proved marginal. Only the outer fiber law is assumed. -/
theorem bounded_count_of_haar (hr : 2 ≤ r) (i : Fin (r+1)) (j : Fin r)
    (D : Set (SL n)) (Q : Set (SL r)) (hqM : MeasurableSet Q)
    (hq : IsFundamentalDomain (integerGroup r).op Q (groupHaar r))
    (qp : groupHaar r Q ≠ 0) (qf : groupHaar r Q ≠ ⊤) (law : HaarProduct i j D Q)
    (a ℓ c : ℝ) (hc : 0 < c) :
    joint i j D (boundedEvent r a ℓ c) ≤ ∫⁻ x in planeWindow n a ℓ,
      min 1 (ENNReal.ofReal (c^r * area x) * volume (Metric.ball (0 : E r) 1) /
        (2 * zetaFactor r)) ∂planeMarginal n := by
  classical
  let H := domainProbability (groupHaar r) Q
  have hH : IsProbabilityMeasure H := domainProbability_probability _ _ qp qf
  let t (x : Frames n) := c * area x ^ (r : ℝ)⁻¹
  have hf (x : Frames n) : H (shortShape (t x)) ≤
      min 1 (ENNReal.ofReal (c^r * area x) * volume (Metric.ball (0 : E r) 1) /
        (2 * zetaFactor r)) := by
    refine le_min (prob_le_one) ?_
    have hA : 0 ≤ area x := Real.sqrt_nonneg _
    rcases hA.eq_or_lt with h0 | hpos
    · have ht : t x = 0 := by
        simp [t, ← h0, Real.zero_rpow (inv_ne_zero (by positivity : (r : ℝ) ≠ 0))]
      have hs : shortShape (m := r) 0 = ∅ := by
        ext L; exact ⟨fun ⟨_,_,hp,hn⟩ ↦ (hp.trans hn).false.elim, False.elim⟩
      simp [ht,hs]
    · have ht : 0 < t x := mul_pos hc (Real.rpow_pos_of_pos hpos _)
      have pow_eq : t x ^ r = c ^ r * area x := by
        dsimp only [t]
        rw [mul_pow, ← Real.rpow_mul_natCast hA, inv_mul_cancel₀ (by positivity : (r : ℝ) ≠ 0),
          Real.rpow_one]
      simpa only [H, ← pow_eq] using domainProbability_shortShape_le hr Q hqM hq qp qf ht
  rw [law, Measure.prod_apply (measurableSet_boundedEvent ..),
    ← lintegral_indicator (measurableSet_planeWindow n a ℓ)]
  apply lintegral_mono
  intro x
  dsimp only
  by_cases hx : x ∈ planeWindow n a ℓ
  · have hpre : Prod.mk x ⁻¹' boundedEvent r a ℓ c = shortShape (t x) := by
      ext; simp [boundedEvent,hx,t]
    rw [hpre, Set.indicator_of_mem hx]
    exact hf x
  · have hpre : Prod.mk x ⁻¹' boundedEvent r a ℓ c = ∅ := by ext; simp [boundedEvent,hx]
    simp [hpre,hx]

/-- Kim's unoriented rank-two area coefficient in determinant one. -/
def planeConstant (d : ℕ) : ℝ≥0∞ :=
  (d-1 : ℕ) * ENNReal.ofReal Real.pi * volume (Metric.ball (0 : E d) 1) *
    volume (Metric.ball (0 : E (d-1)) 1) / (24 * zetaFactor d * zetaFactor (d-1))

/-- Hyperbolic area fraction for a planar nonzero vector of length at most ℓ. -/
def shapeFraction (A ℓ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (3 / Real.pi) * ∫⁻ u in Set.Icc (-(1/2) : ℝ) (1/2),
    ENNReal.ofReal (max (Real.sqrt (1-u^2)) (A / ℓ^2))⁻¹

/-- Remaining Archimedean integration statement for the area and internal-length gates. -/
def ShapeWindowLaw (d : ℕ) : Prop :=
  ∀ (a ℓ : ℝ), 0 < a → 0 < ℓ → ∀ f : ℝ → ℝ≥0∞, Measurable f →
    (∫⁻ x in planeWindow d a ℓ, f (area x) ∂planeMarginal d) =
      d * planeConstant d * ∫⁻ A in Set.Ioc 0 a,
        ENNReal.ofReal (A^(d-1)) * shapeFraction A ℓ * f A

/-- Remaining metric bridge between the two concrete transverse frames and the direct
orthogonal projection by the real plane spanned by the original pair. -/
def OuterMinimumGeometry (i : Fin (r+1)) (j : Fin r) : Prop :=
  ∀ (g : SL n) (p : Core (r+1)) (c : ℝ),
    let x := physical (by have := j.isLt; omega) g 0 0 p
    QuotientGroup.mk (outerFrame i j p g) ∈ shortShape (c * area x ^ (r : ℝ)⁻¹) ↔
      ∃ z : IV n, let v := (Submodule.span ℝ (Set.range x))ᗮ.starProjection (latticePoint g z)
                  0 < ‖v‖ ∧ ‖v‖ < c

theorem bounded_area_integral_of_laws (hr : 2 ≤ r) (i : Fin (r+1)) (j : Fin r)
    (D : Set (SL n)) (Q : Set (SL r)) (hqM : MeasurableSet Q)
    (hq : IsFundamentalDomain (integerGroup r).op Q (groupHaar r))
    (qp : groupHaar r Q ≠ 0) (qf : groupHaar r Q ≠ ⊤)
    (law : HaarProduct i j D Q) (shape : ShapeWindowLaw n)
    (a ℓ c : ℝ) (ha : 0 < a) (hℓ : 0 < ℓ) (hc : 0 < c) :
    joint i j D (boundedEvent r a ℓ c) ≤
      ((n : ℕ) : ℝ≥0∞) * planeConstant n * ∫⁻ A in Set.Ioc 0 a,
        ENNReal.ofReal (A^(n-1)) * shapeFraction A ℓ *
          min 1 (ENNReal.ofReal (c^r * A) * volume (Metric.ball (0 : E r) 1) /
            (2 * zetaFactor r)) := by
  refine (bounded_count_of_haar hr i j D Q hqM hq qp qf law a ℓ c hc).trans_eq ?_
  exact shape a ℓ ha hℓ (fun A ↦ min 1
    (ENNReal.ofReal (c^r * A) * volume (Metric.ball (0 : E r) 1) / (2 * zetaFactor r)))
    (by fun_prop)

/-!
## Remaining statements for the area-coordinate formula

For a fundamental domain Q of positive finite Haar mass, the open fiber lemma in outer
rank r ≥ 2 is `HaarProduct i j D Q`. One route is to transport the two ordered columns
under left SL(n), compute the successive transverse cocycles, and show that the pointwise
two-column stabilizer induces all of SL(r) on the last block. Apply uniqueness of invariant
measure with `orderedMeasure_eq` as the marginal, then restrict to `basisDomain`.

The Archimedean computation left after `plane_mean` is the following measure identity.
For A > 0, disintegrating `planeMarginal n` by area and intrinsic unit-area planar shape
should give n Cₙ A^(n-1) dA times Haar probability on X₂. Here
Cₙ = (n-1) π Vₙ Vₙ₋₁ / (24 ζ(n) ζ(n-1)). Reduce the two-column basis to the modular
domain |u| ≤ 1/2, u²+y² ≥ 1, y > 0. Its normalized shape measure is 3 du dy/(π y²).
On this domain the internal length test is A/y ≤ ℓ². Substitution in
`bounded_count_of_haar` gives the one-dimensional bound of Part 190 for determinant one.

For the physical reading of the outer cutoff, identify the two successive orthogonal
projections with projection onto the orthogonal complement of the marked plane. The
first length normalization is |x|^(1/(n-1)). If y⊥ is the second column projected off
the first, the two successive scales multiply to (|x| |y⊥|)^(1/(n-2)) = A^(1/(n-2)).
-/

end SigabaNeo.Wall1.RankTwo

#print axioms SigabaNeo.Wall1.RankTwo.measurableSet_boundedEvent
#print axioms SigabaNeo.Wall1.RankTwo.bounded_count_of_haar

#print axioms SigabaNeo.Wall1.RankTwo.bounded_area_integral_of_laws
