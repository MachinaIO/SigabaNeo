import SigabaNeo.Lib.Lattices.Research.Wall1.TransverseCount

/-! Uniqueness of the invariant probability on the transverse arithmetic quotient. -/
noncomputable section
open MeasureTheory ProbabilityTheory SigabaNeo.Rogers
open scoped ENNReal
namespace SigabaNeo.Wall1

/-- A jointly measurable transitive action admits at most one invariant probability when the
acting group has a nonzero sigma-finite right invariant measure. -/
theorem transitive_probability_unique {G X : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableSpace X] [MulAction G X] [MeasurableSMul₂ G X]
    [MulAction.IsPretransitive G X] (ρ : Measure G) [SigmaFinite ρ] [NeZero ρ]
    [ρ.IsMulRightInvariant] (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [SMulInvariantMeasure G X μ] [SMulInvariantMeasure G X ν] : μ = ν := by
  let τ := μ + ν
  have : NeZero τ := ⟨fun h ↦ by have := congrArg (fun η : Measure X ↦ η Set.univ) h; simp [τ] at this⟩
  let f : X → ℝ≥0∞ := μ.rnDeriv τ
  have hf : Measurable f := Measure.measurable_rnDeriv _ _
  have hinv (a : G) : ∀ᵐ x ∂τ, f (a • x) = f x := by
    have h := (measurableEmbedding_const_smul (α := X) a).rnDeriv_map μ τ
    have ht : τ.map (a • ·) = τ := by
      simp [τ, Measure.map_add, measurable_const_smul, (measurePreserving_smul a μ).map_eq,
        (measurePreserving_smul a ν).map_eq]
    simpa only [f, Filter.EventuallyEq, (measurePreserving_smul a μ).map_eq, ht] using h
  have hswap : ∀ᵐ x ∂τ, ∀ᵐ a ∂ρ, f (a • x) = f x :=
    (Measure.ae_ae_comm (μ := ρ) (ν := τ)
      (measurableSet_eq_fun (hf.comp (measurable_fst.smul measurable_snd))
        (hf.comp measurable_snd))).mp (Filter.Eventually.of_forall hinv)
  obtain ⟨x, hx⟩ := hswap.exists
  have hc : f =ᵐ[τ] fun _ ↦ f x := by
    filter_upwards [hswap] with y hy
    obtain ⟨b, hb⟩ := MulAction.exists_smul_eq G x y
    have hh := (measurePreserving_mul_right ρ b).quasiMeasurePreserving.ae hx
    obtain ⟨a, ha, ha'⟩ := (hy.and hh).exists
    exact ha.symm.trans (by simpa [← hb, mul_smul] using ha')
  have he : μ = f x • τ := by
    rw [← Measure.withDensity_rnDeriv_eq μ τ ((Measure.AbsolutelyContinuous.rfl (μ := μ)).add_right ν), withDensity_congr_ae hc, withDensity_const]
  have mass := congrArg (fun η : Measure X ↦ η Set.univ) he
  have hmass : f x + f x = 1 := by simpa [τ, Measure.smul_apply] using mass.symm
  have hn : f x ≠ 0 := by intro h; simp [h] at hmass
  have ht : f x ≠ ⊤ := by intro h; simp [h] at hmass
  have h₂ : μ = f x • μ + f x • μ := by
    rw [← add_smul, hmass, one_smul]
  change μ = f x • (μ + ν) at he
  rw [smul_add] at he
  have : IsFiniteMeasure (f x • μ) := ⟨by simpa [Measure.smul_apply] using ht.lt_top⟩
  have hν := (Measure.add_right_inj _ _ _).mp (he.symm.trans h₂)
  simpa [smul_smul, ENNReal.inv_mul_cancel hn ht] using
    (congrArg (fun η : Measure X ↦ (f x)⁻¹ • η) hν.symm)

/-- Identification of any invariant probability with normalized domain Haar, for the actual
arithmetic subgroup (which need not be normal). -/
theorem transverse_invariant_probability_eq {m : ℕ} (D : Set (SL m))
    (hd : IsFundamentalDomain (integerGroup m).op D (groupHaar m))
    (hp : groupHaar m D ≠ 0) (hf : groupHaar m D ≠ ⊤)
    (μ : Measure (LatticeSpace m)) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure (SL m) (LatticeSpace m) μ] : μ = domainProbability (groupHaar m) D := by
  let : PolishSpace (Matrix (Fin m) (Fin m) ℝ) :=
    inferInstanceAs (PolishSpace (Fin m → Fin m → ℝ))
  let : LocallyCompactSpace (Matrix (Fin m) (Fin m) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin m → Fin m → ℝ))
  let : LocallyCompactSpace (SL m) := Matrix.SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace
  let : PolishSpace (SL m) := Matrix.SpecialLinearGroup.isClosedEmbedding_val.polishSpace
  let : BorelSpace (SL m) := ⟨rfl⟩
  have he : Topology.IsClosedEmbedding (Int.castRingHom ℝ) := Int.isClosedEmbedding_coe_real
  have : IsClosed (integerGroup m : Set (SL m)) := he.specialLinearGroup_map.isClosed_range
  let : BorelSpace (LatticeSpace m) := CosetSpace.borelSpace
  let := groupHaar_rightInvariant m
  let : (groupHaar m).IsMulLeftInvariant :=
    inferInstanceAs (Measure.haar : Measure (SL m)).IsMulLeftInvariant
  let := domainProbability_invariant _ hd
  let := domainProbability_probability _ _ hp hf
  have : SigmaFinite (groupHaar m) := inferInstanceAs (SigmaFinite (Measure.haar : Measure (SL m)))
  have : NeZero (groupHaar m) := inferInstanceAs (NeZero (Measure.haar : Measure (SL m)))
  exact transitive_probability_unique (groupHaar m) μ _

/-- Fixed-parent covariance implies simultaneous covariance under every stabilizer element
at almost every mark. Right translation is performed after the Fubini exchange, so no
uncountable intersection of full-measure sets is needed. The target can itself be a space
of conditional laws. -/
theorem ae_stabilizer_of_cocycle_covariance {G H X Y : Type*} [Group G] [Group H]
    [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableSpace X] [MulAction G X]
    [MulAction H Y] (ρ : Measure G) [SigmaFinite ρ] [NeZero ρ] [ρ.IsMulRightInvariant]
    (ξ : Measure X) [SigmaFinite ξ] (T : G → X → H) (K : X → Y)
    (cocycle : ∀ a b x, T (a * b) x = T a (b • x) * T b x)
    (hm : MeasurableSet {p : G × X | K (p.1 • p.2) = T p.1 p.2 • K p.2})
    (cov : ∀ a, ∀ᵐ x ∂ξ, K (a • x) = T a x • K x) :
    ∀ᵐ x ∂ξ, ∀ b : G, b • x = x → T b x • K x = K x := by
  have good := (Measure.ae_ae_comm (μ := ρ) (ν := ξ) hm).mp
    (Filter.Eventually.of_forall cov)
  filter_upwards [good] with x hx
  intro b hb
  have hh := (measurePreserving_mul_right ρ b).quasiMeasurePreserving.ae hx
  obtain ⟨a, ha, hab⟩ := (hx.and hh).exists
  change K ((a * b) • x) = T (a * b) x • K x at hab
  rw [mul_smul, hb, cocycle, hb, mul_smul, ha] at hab
  exact MulAction.injective (T a x) hab.symm

/-- Part 105's window estimate given simultaneous almost-everywhere invariance of the
conditional laws. The base window may have infinite volume. -/
theorem transverse_window_le_of_ae_invariant {m : ℕ} (hn : 2 ≤ m)
    (D : Set (SL m)) (hm : MeasurableSet D)
    (hd : IsFundamentalDomain (integerGroup m).op D (groupHaar m))
    (hp : groupHaar m D ≠ 0) (hf : groupHaar m D ≠ ⊤)
    (K : Kernel (E (m+1)) (LatticeSpace m)) [IsMarkovKernel K]
    (hinv : ∀ᵐ x ∂volume, SMulInvariantMeasure (SL m) (LatticeSpace m) (K x))
    (W : Set (E (m+1))) {c : ℝ} (hc : 0 < c) :
    (∫⁻ x in W, K x (shortShape c)) / ∑' k, dilationWeight (m+1) k ≤
      (volume W / ∑' k, dilationWeight (m+1) k) *
        (ENNReal.ofReal (c ^ m) * volume (Metric.ball (0 : E m) 1) /
          (2 * ∑' k, dilationWeight m k)) := by
  let B := ENNReal.ofReal (c ^ m) * volume (Metric.ball (0 : E m) 1) /
    (2 * ∑' k, dilationWeight m k)
  have h : (∫⁻ x in W, K x (shortShape c)) ≤ ∫⁻ _x in W, B := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_of_ae hinv] with x hx
    rw [transverse_invariant_probability_eq D hd hp hf (K x)]
    exact domainProbability_shortShape_le hn D hm hd hp hf hc
  simpa [B, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    ENNReal.div_le_div_right h (∑' k, dilationWeight (m+1) k)

#print axioms ae_stabilizer_of_cocycle_covariance
#print axioms transverse_window_le_of_ae_invariant
#print axioms transitive_probability_unique
#print axioms transverse_invariant_probability_eq
end SigabaNeo.Wall1
