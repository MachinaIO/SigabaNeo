import SigabaNeo.Lib.Lattices.Research.Wall1.RankTwoSaturation
import SigabaNeo.Lib.Lattices.Research.Wall1.RankTwoMean

/-! A Borel basis domain and the primitive mean with one summand per unoriented plane. -/

noncomputable section
open MeasureTheory Submodule SigabaNeo.Rogers
open scoped ENNReal
namespace SigabaNeo.Wall1.RankTwo

private abbrev Coeff := Fin 2 → ℤ × ℤ
private def mix {d : ℕ} (A : Coeff) (x : Frames d) : Frames d :=
  fun j ↦ (A j).1 • x 0 + (A j).2 • x 1

private theorem mix_meas {d : ℕ} (A : Coeff) : Measurable (@mix d A) := by
  apply Measurable.of_eval
  intro j
  exact ((measurable_pi_apply 0).const_smul _).add ((measurable_pi_apply 1).const_smul _)

private theorem span_le_iff {d : ℕ} (x y : Frames d) :
    pairSpan x ≤ pairSpan y ↔ ∃ A, mix A y = x := by
  constructor
  · intro h
    have hs (i) := (pairSpan_mem y (x i)).mp (h (Submodule.subset_span ⟨i,rfl⟩))
    choose a b he using hs
    exact ⟨fun i ↦ (a i, b i), funext he⟩
  · rintro ⟨A,rfl⟩
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact (pairSpan_mem y _).mpr ⟨_,_,rfl⟩

private def precedes {d : ℕ} (x y : Frames d) : Prop :=
  ‖x‖ ≤ ‖y‖ ∧ (‖y‖ ≤ ‖x‖ → embeddingReal _ x ≤ embeddingReal _ y)

/-- One basis of each grid plane. Minimize the frame norm, breaking ties with a Borel embedding.
All orientation and basis changes are included in the comparison. -/
def basisDomain (d : ℕ) : Set (Frames d) :=
  {x | ∀ y, pairSpan y = pairSpan x → precedes x y}

theorem measurableSet_basisDomain (d : ℕ) : MeasurableSet (basisDomain d) := by
  have he : basisDomain d = {x | ∀ A B : Coeff, mix B (mix A x) = x → precedes x (mix A x)} := by
    ext x
    constructor
    · intro h A B hB
      exact h _ (le_antisymm ((span_le_iff ..).mpr ⟨A,rfl⟩) ((span_le_iff ..).mpr ⟨B,hB⟩))
    · intro h y hy
      obtain ⟨A,rfl⟩ := (span_le_iff y x).mp hy.le
      obtain ⟨B,hB⟩ := (span_le_iff x _).mp hy.ge
      exact h A B hB
  rw [he]
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter; intro A
  apply MeasurableSet.iInter; intro B
  rw [show {x : Frames d | mix B (mix A x) = x → precedes x (mix A x)} =
    {x | mix B (mix A x) = x}ᶜ ∪
      ({x | ‖x‖ ≤ ‖mix A x‖} ∩
      ({x | ‖mix A x‖ ≤ ‖x‖}ᶜ ∪ {x | embeddingReal _ x ≤ embeddingReal _ (mix A x)})) by
        ext; simp [precedes, imp_iff_not_or]]
  exact (measurableSet_eq_fun ((mix_meas B).comp (mix_meas A)) measurable_id).compl.union
    ((measurableSet_le measurable_norm (mix_meas A).norm).inter
      ((measurableSet_le (mix_meas A).norm measurable_norm).compl.union
        (measurableSet_le (measurable_embeddingReal _) ((measurable_embeddingReal _).comp
          (mix_meas A)))))

private def eval {d : ℕ} (g : SL d) (z : Fin 2 → IV d) : Frames d := latticePoint g ∘ z

private theorem point_embedding {d : ℕ} (g : SL d) : Topology.IsClosedEmbedding (latticePoint g) :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm.toHomeomorph.isClosedEmbedding.comp
    (g.toLin'.toContinuousLinearEquiv.toHomeomorph.isClosedEmbedding.comp
      (Topology.IsClosedEmbedding.piMap fun _ : Fin d ↦ Int.isClosedEmbedding_coe_real))

private theorem eval_embedding {d : ℕ} (g : SL d) : Topology.IsClosedEmbedding (eval g) :=
  Topology.IsClosedEmbedding.piMap fun _ ↦ point_embedding g

def physicalPlane {d : ℕ} (g : SL d) (P : Plane d) : Submodule ℤ (E d) :=
  P.val.map (latticePoint g).toIntLinearMap

private theorem eval_span {d : ℕ} (g : SL d) (z : Fin 2 → IV d) :
    pairSpan (eval g z) = (pairSpan z).map (latticePoint g).toIntLinearMap := by
  rw [pairSpan, eval, Set.range_comp, pairSpan, Submodule.map_span]
  rfl

private theorem phys_eq_eval {m : ℕ} (hm : 2 ≤ m) (g : SL (m+1)) (p : Core m) :
    physical hm g 0 0 p = eval g (gridFrame hm 0 0 p) := by
  funext j; fin_cases j <;> rfl

private theorem physical_span {m : ℕ} (hm : 2 ≤ m) (g : SL (m+1)) (p : Core m) :
    pairSpan (physical hm g 0 0 p) = physicalPlane g (plane hm p) := by
  rw [phys_eq_eval, eval_span]; rfl

private theorem lift_basis {m : ℕ} (hm : 2 ≤ m) (g : SL (m+1)) (P : Plane (m+1))
    (y : Frames (m+1)) (h : pairSpan y = physicalPlane g P) :
    ∃ p, plane hm p = P ∧ physical hm g 0 0 p = y := by
  have hy (j) : y j ∈ physicalPlane g P := h ▸ Submodule.subset_span ⟨j,rfl⟩
  choose z hz he using hy
  have he' : eval g z = y := funext he
  have hP : pairSpan z = P.val := by
    apply Submodule.map_injective_of_injective (f := (latticePoint g).toIntLinearMap)
      (point_embedding g).injective
    rw [← eval_span, he']; exact h
  have li : LinearIndependent ℤ z := by
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    change Fintype.card (Fin 2) = Module.finrank ℤ (pairSpan z)
    rw [hP, P.property.1, Fintype.card_fin]
  obtain ⟨p,hp⟩ := (primitive_basis_iff hm z li).mp (hP ▸ P.property.2)
  exact ⟨p, Subtype.ext ((congrArg pairSpan hp).trans hP), by rw [phys_eq_eval,hp,he']⟩

/-- Every saturated plane has exactly one selected ordered basis in any parent frame. -/
theorem unique_basis {m : ℕ} (hm : 2 ≤ m) (g : SL (m+1)) (P : Plane (m+1)) :
    ∃! p : {p : Core m // plane hm p = P}, physical hm g 0 0 p.val ∈ basisDomain (m+1) := by
  classical
  let bases := {y | pairSpan y = physicalPlane g P}
  obtain ⟨q,hq⟩ := plane_surjective hm P
  let x := physical hm g 0 0 q
  have hx : x ∈ bases := (physical_span hm g q).trans (congrArg _ hq)
  let W := bases ∩ Metric.closedBall 0 ‖x‖
  have hW : W.Finite := by
    have hf := ((eval_embedding g).isCompact_preimage (isCompact_closedBall (0 : Frames (m+1))
      ‖x‖)).finite_of_discrete
    apply (hf.image (eval g)).subset
    intro y hy
    obtain ⟨p,_,hp⟩ := lift_basis hm g P y hy.1
    rw [phys_eq_eval] at hp
    refine ⟨_, ?_, hp⟩
    change eval g (gridFrame hm 0 0 p) ∈ Metric.closedBall 0 ‖x‖
    rw [hp]; exact hy.2
  obtain ⟨u,hu,hmin⟩ := Set.exists_min_image W norm hW ⟨x,hx,by simp⟩
  let T := {v ∈ W | ‖v‖ = ‖u‖}
  obtain ⟨v,hv,hkey⟩ := Set.exists_min_image T (embeddingReal _) (hW.subset (fun _ h ↦ h.1))
    ⟨u,hu,rfl⟩
  have order (y) (hy : y ∈ bases) : precedes v y := by
    by_cases h : ‖y‖ ≤ ‖x‖
    · have yw : y ∈ W := ⟨hy, by simpa using h⟩
      have hle := hmin y yw
      exact ⟨hv.2.trans_le hle, fun hh ↦ hkey y ⟨yw,le_antisymm (hh.trans_eq hv.2) hle⟩⟩
    · have lt : ‖v‖ < ‖y‖ := lt_of_le_of_lt (by simpa using hv.1.2) (lt_of_not_ge h)
      exact ⟨lt.le, fun h' ↦ (lt.not_ge h').elim⟩
  obtain ⟨p,hp,hv'⟩ := lift_basis hm g P v hv.1.1
  refine ⟨⟨p,hp⟩, ?_, ?_⟩
  · change physical hm g 0 0 p ∈ basisDomain (m+1)
    rw [hv']; exact fun y hy ↦ order y (hy.trans hv.1.1)
  · intro q hq'
    let y := physical hm g 0 0 q.val
    have hy : y ∈ bases := (physical_span hm g q.val).trans (congrArg _ q.property)
    have fwd := order y hy
    have rev := hq' v (hv.1.1.trans hy.symm)
    have e := (measurableEmbedding_embeddingReal _).injective
      (le_antisymm (rev.2 fwd.1) (fwd.2 rev.1))
    apply Subtype.ext
    apply gridFrame_injective hm
    apply (eval_embedding g).injective
    rw [← phys_eq_eval hm, ← phys_eq_eval hm, hv']
    exact e

/-- Primitive sublattice Siegel identity on an ambient fundamental domain. The right side
integrates over the Borel domain of unoriented lattice bases in two-vector space. -/
theorem plane_mean {m : ℕ} (hm : 2 ≤ m) (D : Set (SL (m+1)))
    (hd : IsFundamentalDomain (integerGroup (m+1)).op D (groupHaar (m+1)))
    (hf : groupHaar (m+1) D ≠ ⊤) (hp : groupHaar (m+1) D ≠ 0)
    (F : Submodule ℤ (E (m+1)) → ℝ≥0∞) (hF : Measurable (F ∘ pairSpan)) :
    (∫⁻ g in D, ∑' P : Plane (m+1), F (physicalPlane g P) ∂groupHaar (m+1)) /
      groupHaar (m+1) D =
      (∫⁻ x in basisDomain (m+1), F (pairSpan x) ∂frameVolume (m+1)) /
        (zetaFactor (m+1) * zetaFactor m) := by
  classical
  let f := (basisDomain (m+1)).indicator (F ∘ pairSpan)
  have hf' : Measurable f := hF.indicator (measurableSet_basisDomain _)
  have he (g : SL (m+1)) : (∑' p : Core m, f (physical hm g 0 0 p)) =
      ∑' P : Plane (m+1), F (physicalPlane g P) := by
    rw [← (Equiv.sigmaFiberEquiv (plane hm)).tsum_eq (fun p ↦ f (physical hm g 0 0 p)),
      tsum_sigma']
    apply tsum_congr
    intro P
    obtain ⟨p,hp,huniq⟩ := unique_basis hm g P
    rw [tsum_eq_single p]
    · change f (physical hm g 0 0 p.val) = _
      simp [f, hp, physical_span, p.property]
    · intro q hq
      exact Set.indicator_of_notMem (fun h ↦ hq (huniq q h)) _
  simp_rw [← he]
  rw [← orderedMeasure_integral hm D _ hf', orderedMeasure_eq hm D hd hf,
    lintegral_smul_measure, smul_eq_mul, lintegral_indicator (measurableSet_basisDomain _)]
  simp only [div_eq_mul_inv, Function.comp_apply]
  calc
    _ = (groupHaar (m+1) D * (groupHaar (m+1) D)⁻¹) *
        ((∫⁻ x in basisDomain (m+1), F (pairSpan x) ∂frameVolume (m+1)) *
          (zetaFactor (m+1) * zetaFactor m)⁻¹) := by ac_rfl
    _ = _ := by rw [ENNReal.mul_inv_cancel hp hf, one_mul]

end SigabaNeo.Wall1.RankTwo

#print axioms SigabaNeo.Wall1.RankTwo.measurableSet_basisDomain
#print axioms SigabaNeo.Wall1.RankTwo.unique_basis
#print axioms SigabaNeo.Wall1.RankTwo.plane_mean
