import SigabaNeo.Lib.Lattices.Research.Wall1.RankTwoTransport

/-! Arithmetic and real invariance of ordered plane incidence before selecting a basis. -/
noncomputable section
open Matrix MeasureTheory SigabaNeo.Rogers
open scoped ENNReal
namespace SigabaNeo.Wall1.RankTwo

variable {r : ℕ} (i : Fin (r+1)) (j : Fin r)
local notation "n" => (r+2)
local notation "m" => (r+1)
private theorem dim (j : Fin r) : 2 ≤ m := by have := j.isLt; omega

def incidenceMark (p : Core m) (g : SL n) : Frames n × LatticeSpace r :=
  (physical (dim j) g 0 0 p, QuotientGroup.mk (outerFrame i j p g))

theorem measurable_incidenceMark (p : Core m) : Measurable (incidenceMark i j p) :=
  (measurable_physical (dim j) 0 0 p).prodMk (measurable_quotient_mk''.comp
    (measurable_outerFrame i j p))

def incidenceAction (a : SL n) (u : Frames n × LatticeSpace r) : Frames n × LatticeSpace r :=
  (frameAction a u.1, outerCocycle i j a u.1 • u.2)

theorem incidenceAction_mul (a b : SL n) (u : Frames n × LatticeSpace r) :
    incidenceAction i j (a*b) u = incidenceAction i j a (incidenceAction i j b u) := by
  simp [incidenceAction, outerCocycle_mul, mul_smul]
  exact funext fun k ↦ markAction_mul a b (u.1 k)

theorem incidenceAction_one (u : Frames n × LatticeSpace r) : incidenceAction i j 1 u = u := by
  simp [incidenceAction, outerCocycle, transverseCocycle]
  refine Prod.ext ?_ rfl
  exact funext fun k ↦ by simp [frameAction, markAction]

theorem measurable_incidenceAction :
    Measurable fun v : SL n × (Frames n × LatticeSpace r) ↦ incidenceAction i j v.1 v.2 := by
  let pol (d : ℕ) : PolishSpace (Matrix (Fin d) (Fin d) ℝ) :=
    inferInstanceAs (PolishSpace (Fin d → Fin d → ℝ))
  let pol' (d : ℕ) : PolishSpace (SL d) := SpecialLinearGroup.isClosedEmbedding_val.polishSpace
  let bor (d : ℕ) : BorelSpace (SL d) := ⟨rfl⟩
  have he : Topology.IsClosedEmbedding (Int.castRingHom ℝ) := Int.isClosedEmbedding_coe_real
  have : IsClosed (integerGroup r : Set (SL r)) := he.specialLinearGroup_map.isClosed_range
  let : BorelSpace (LatticeSpace r) := CosetSpace.borelSpace
  have mx (k : Fin 2) : Measurable (fun v : SL n × (Frames n × LatticeSpace r) ↦ v.2.1 k) := (measurable_pi_apply k (X := fun _ : Fin 2 ↦ E n)).comp
    (measurable_fst.comp (measurable_snd (α := SL n) (β := Frames n × LatticeSpace r)))
  apply Measurable.prodMk
  · apply Measurable.of_eval
    intro k
    apply Continuous.measurable
    apply (PiLp.continuous_toLp 2 _).comp
    change Continuous fun v : SL n × (Frames n × LatticeSpace r) ↦
      v.1.val.mulVec (WithLp.ofLp (v.2.1 k))
    unfold Matrix.mulVec dotProduct
    fun_prop
  · refine Measurable.smul (f := fun v : SL n × (Frames n × LatticeSpace r) ↦ outerCocycle i j v.1 v.2.1) ?_ (measurable_snd.comp measurable_snd)
    refine (measurable_transverseCocycle j).comp (f := fun v : SL n × (Frames n × LatticeSpace r) ↦
      (transverseCocycle i v.1 (v.2.1 0), normalizedTail i (v.2.1 0) (v.2.1 1))) ?_
    apply Measurable.prodMk ((measurable_transverseCocycle i).comp (measurable_fst.prodMk (mx 0)))
    change Measurable fun v : SL n × (Frames n × LatticeSpace r) ↦ WithLp.toLp 2
      (fun k : Fin m ↦ ‖v.2.1 0‖ ^ ((m : ℕ) : ℝ)⁻¹ * transverseRotation i (v.2.1 0) (v.2.1 1) k.succ)
    apply (PiLp.continuous_toLp 2 _).measurable.comp
    apply Measurable.of_eval
    intro k
    exact ((mx 0).norm.pow_const _).mul ((PiLp.continuous_apply 2 _ k.succ).measurable.comp
      ((measurable_transverseRotation i).comp ((mx 0).prodMk (mx 1))))

theorem incidenceMark_mul (a g : SL n) (p : Core m) :
    incidenceMark i j p (a*g) = incidenceAction i j a (incidenceMark i j p g) := by
  have h : adaptedFrame j p (a*g) = a * adaptedFrame j p g := by
    change (a*g)*_ * _ = a*(g*_ * _)
    simp only [mul_assoc]
  unfold incidenceMark incidenceAction
  simp only [← adaptedFrame_columns j, ← adaptedFrame_outer i j, h, columns_mul, iteratedFrame_mul]
  rfl

theorem incidenceAction_trans {u v : Frames n × LatticeSpace r}
    (hu : u.1 ∈ Set.range (@columns r)) (hv : v.1 ∈ Set.range (@columns r)) :
    ∃ a, incidenceAction i j a u = v := by
  obtain ⟨g,hg⟩ := hu
  obtain ⟨t,ht⟩ := hv
  let b := t*g⁻¹
  have hb : frameAction b u.1 = v.1 := by rw [← hg, ← columns_mul]; simpa [b,mul_assoc] using ht
  obtain ⟨h,hh⟩ := MulAction.exists_smul_eq (SL r) (incidenceAction i j b u).2 v.2
  obtain ⟨a,ha,ha'⟩ := outerCocycle_stabilizer i j t h
  rw [ht] at ha ha'
  refine ⟨a*b, ?_⟩
  rw [incidenceAction_mul]
  apply Prod.ext
  · change frameAction a (frameAction b u.1) = v.1
    rw [hb,ha]
  · change outerCocycle i j a (frameAction b u.1) • _ = _
    rw [hb,ha',hh]

/-- Two projections in fixed coordinates, applied to an ambient point. -/
def outerCoordinates (x : Frames n) :=
  (normalizedTail j (normalizedTail i (x 0) (x 1))).comp (normalizedTail i (x 0))

theorem iteratedFrame_points (g : SL n) :
    points (QuotientGroup.mk (iteratedFrame i j g)) =
      outerCoordinates i j (columns g) '' Set.range (latticePoint g) := by
  rw [points_mk, ← Set.range_comp]
  let tail (z : IV n) : IV r := fun k ↦ z k.succ.succ
  have ht : Function.Surjective tail := fun z ↦ ⟨Fin.cons 0 (Fin.cons 0 z), rfl⟩
  change Set.range (latticePoint (iteratedFrame i j g)) = _
  rw [← ht.range_comp (latticePoint (iteratedFrame i j g))]
  apply congrArg Set.range
  funext z
  change _ = normalizedTail j (normalizedTail i (column g 0) (column g (0 : Fin m).succ))
    (normalizedTail i (column g 0) (WithLp.toLp 2 (g • _)))
  rw [normalizedTail_col, normalizedTail_mulVec, normalizedTail_mulVec]
  rfl

private theorem point_cast {d : ℕ} (g : SL d) (a : SpecialLinearGroup (Fin d) ℤ) (z : IV d) :
    latticePoint (g * SpecialLinearGroup.map (Int.castRingHom ℝ) a) z = latticePoint g (a • z) := by
  change WithLp.toLp 2 ((_ * _) • _) = WithLp.toLp 2 (_ • _)
  rw [mul_smul]
  congr 2
  exact funext fun k ↦ (RingHom.map_mulVec (Int.castRingHom ℝ) a.val z k).symm

private theorem points_cast {d : ℕ} (g : SL d) (a : SpecialLinearGroup (Fin d) ℤ) :
    Set.range (latticePoint (g * SpecialLinearGroup.map (Int.castRingHom ℝ) a)) =
      Set.range (latticePoint g) := by
  change Set.range (fun z ↦ latticePoint _ z) = _
  simp_rw [point_cast]
  exact (MulAction.surjective a).range_comp _

theorem incidenceMark_points (p : Core m) (g : SL n) :
    points (incidenceMark i j p g).2 =
      outerCoordinates i j (incidenceMark i j p g).1 '' Set.range (latticePoint g) := by
  change points (QuotientGroup.mk (outerFrame i j p g)) = outerCoordinates i j (physical (dim j) g 0 0 p) '' _
  rw [← adaptedFrame_columns j, ← adaptedFrame_outer i j, iteratedFrame_points]
  congr 1
  let f := primitiveFrame (by omega : 2 ≤ n) p.1
  let t := primitiveFrame (dim j) p.2.2
  let e := extend (Pi.single 0 p.2.1) t
  have he : extend (Pi.single 0 (p.2.1 : ℝ)) (primitiveTranslate (dim j) p.2.2).val.unop =
      SpecialLinearGroup.map (Int.castRingHom ℝ) e := by
    apply Subtype.ext
    ext a b
    change (extend _ _).val a b = ((e.val a b : ℤ) : ℝ)
    refine Fin.cases ?_ (fun a ↦ ?_) a <;> refine Fin.cases ?_ (fun b ↦ ?_) b <;>
      simp [extend,e,t,primitiveTranslate,Pi.single_apply]
  unfold adaptedFrame
  rw [he, points_cast]
  exact points_cast g f

private theorem physical_grid (p : Core m) (g : SL n) :
    physical (dim j) g 0 0 p = fun k ↦ latticePoint g (gridFrame (dim j) 0 0 p k) := by
  funext k; fin_cases k <;> rfl

private theorem exists_reindex (a : SpecialLinearGroup (Fin n) ℤ) (p : Core m) :
    ∃ q, gridFrame (dim j) 0 0 q = fun k ↦ a • gridFrame (dim j) 0 0 p k := by
  let x := gridFrame (dim j) 0 0 p
  let e := a.toLin'
  have li : LinearIndependent ℤ x := independent (by omega) 0 0 p
  have h : pairSpan (fun k ↦ e (x k)) = (pairSpan x).map e.toLinearMap := by
    rw [pairSpan, pairSpan, Submodule.map_span, ← Set.range_comp]; rfl
  apply (primitive_basis_iff (dim j) (fun k ↦ e (x k))
    (li.map' _ (LinearMap.ker_eq_bot.mpr e.injective))).mp
  rw [h]
  intro d hd z hz
  obtain ⟨u,rfl⟩ := e.surjective z
  rw [← map_smul] at hz
  obtain ⟨v,hv,he⟩ := hz
  exact ⟨u,(plane (dim j) p).property.2 d hd u (e.injective he ▸ hv),rfl⟩

private def coreEquiv (a : SpecialLinearGroup (Fin n) ℤ) : Core m ≃ Core m where
  toFun p := (exists_reindex j a p).choose
  invFun p := (exists_reindex j a⁻¹ p).choose
  left_inv p := by
    apply gridFrame_injective (dim j)
    rw [(exists_reindex j a⁻¹ _).choose_spec, (exists_reindex j a p).choose_spec]
    simp
  right_inv p := by
    apply gridFrame_injective (dim j)
    rw [(exists_reindex j a _).choose_spec, (exists_reindex j a⁻¹ p).choose_spec]
    simp

private theorem mark_cast (g : SL n) (a : SpecialLinearGroup (Fin n) ℤ) (p : Core m) :
    incidenceMark i j p (g * SpecialLinearGroup.map (Int.castRingHom ℝ) a) =
      incidenceMark i j (coreEquiv j a p) g := by
  have he : (incidenceMark i j p (g * SpecialLinearGroup.map (Int.castRingHom ℝ) a)).1 =
      (incidenceMark i j (coreEquiv j a p) g).1 := by
    change physical (dim j) _ _ _ _ = physical (dim j) _ _ _ _
    simp only [physical_grid j, point_cast]
    rw [show gridFrame (dim j) 0 0 (coreEquiv j a p) = _ from (exists_reindex j a p).choose_spec]
  exact Prod.ext he (latticeSpace_points_injective (by rw [incidenceMark_points,
    incidenceMark_points, he, points_cast]))

def orderedJoint (D : Set (SL n)) : Measure (Frames n × LatticeSpace r) :=
  Measure.sum fun p ↦ ((groupHaar n).restrict D).map (incidenceMark i j p)

theorem orderedJoint_integral (D : Set (SL n)) (F : Frames n × LatticeSpace r → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ u, F u ∂orderedJoint i j D) =
      ∫⁻ g in D, ∑' p, F (incidenceMark i j p g) ∂groupHaar n := by
  rw [orderedJoint, lintegral_sum_measure, lintegral_tsum (f := fun p g ↦ F (incidenceMark i j p g))
    (fun p ↦ (hF.comp (measurable_incidenceMark i j p)).aemeasurable)]
  exact tsum_congr fun p ↦ lintegral_map hF (measurable_incidenceMark i j p)

theorem orderedJoint_fst (D : Set (SL n)) :
    (orderedJoint i j D).map Prod.fst = orderedMeasure (dim j) D := by
  rw [orderedJoint, Measure.map_sum measurable_fst.aemeasurable]
  simp only [Measure.map_map measurable_fst (measurable_incidenceMark i j _)]
  rfl

theorem orderedJoint_invariant (D : Set (SL n))
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (a : SL n) :
    (orderedJoint i j D).map (incidenceAction i j a) = orderedJoint i j D := by
  let φ : SpecialLinearGroup (Fin n) ℤ →* SL n := SpecialLinearGroup.map (Int.castRingHom ℝ)
  have : Countable (Matrix (Fin n) (Fin n) ℤ) := inferInstanceAs (Countable (Fin n → Fin n → ℤ))
  have : Countable (SpecialLinearGroup (Fin n) ℤ) := Subtype.val_injective.countable
  have : Countable (integerGroup n) := φ.rangeRestrict_surjective.countable
  have : Countable (integerGroup n).op := (integerGroup n).equivOp.surjective.countable
  let := groupHaar_rightInvariant n
  let : BorelSpace (SL n) := ⟨rfl⟩
  let : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℝ))
  let : LocallyCompactSpace (SL n) := SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace
  let : (groupHaar n).IsMulLeftInvariant :=
    inferInstanceAs (Measure.haar : Measure (SL n)).IsMulLeftInvariant
  let e := MeasurableEquiv.mulLeft a
  have hd' := hd.image_of_equiv e.toEquiv
    (measurePreserving_mul_left (groupHaar n) a⁻¹).quasiMeasurePreserving
    (Equiv.refl _) (fun b x ↦ (mul_assoc a x b.val.unop).symm)
  have ma : Measurable (incidenceAction i j a) := (measurable_incidenceAction i j).comp (measurable_const (a := a) |>.prodMk measurable_id)
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF ma, orderedJoint_integral i j D (fun u ↦ F (incidenceAction i j a u)) (hF.comp ma),
    orderedJoint_integral i j D F hF]
  simp_rw [← incidenceMark_mul]
  let W (g : SL n) := ∑' p, F (incidenceMark i j p g)
  apply ((measurePreserving_mul_left (groupHaar n) a).setLIntegral_comp_emb
    e.measurableEmbedding W D).trans
  apply hd'.setLIntegral_eq hd
  intro b g
  obtain ⟨c,hc⟩ := (show b.val.unop ∈ integerGroup n from b.property)
  change (∑' p, F (incidenceMark i j p (g*b.val.unop))) = _
  simp_rw [← hc,mark_cast]
  exact (coreEquiv j c).tsum_eq (fun p ↦ F (incidenceMark i j p g))

end SigabaNeo.Wall1.RankTwo

#print axioms SigabaNeo.Wall1.RankTwo.incidenceAction_trans
#print axioms SigabaNeo.Wall1.RankTwo.incidenceMark_points
#print axioms SigabaNeo.Wall1.RankTwo.orderedJoint_invariant
