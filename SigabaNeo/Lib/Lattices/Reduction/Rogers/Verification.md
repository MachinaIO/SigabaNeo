# Rogers and spherical Gram formalization

## Scope

The local Rogers structure models the three fields of Laarhoven's v1
`QuotientHanRogers.ClassicalRogersFormula`. For a Han matrix with physical
denominator Q, the coefficient implemented here is the inverse n-th power of
the size of the row image modulo Q. Primitivity implies Q divides that size.
At Q = 1 the image is trivial. Thus both coefficient fields hold in every
order. The local equivalence leaves exactly the workload identity. Order one
has a single diagram and gives Siegel's conclusion conditional on Rogers.
The low-order specialization covers 1 ≤ k ≤ 3 and k < n.

For the Gram law, the scalar candidate at exponent p has constant
1 / (2 · 4^p · B(p+1,p+1)). The triple density at p = (n−4)/2 has constant
C(p+1/2)^2 C(p), where C is the scalar constant. Both densities have total
mass one in the requested dimensions. The affine change of the last
coordinate has Jacobian sqrt((1−a²)(1−b²)); integrating it out gives
the product of the two pair marginals. The general Gamma-product coefficient
and the positive-definite support appear in `SphericalGramFormula`.

## Open obligations

1. `pair_law` proves the local pair law for every n ≥ 3. For triples,
   `axial_pair_law` gives the independent axial coordinates for each fixed pole.
   `transverse_inner` expresses the third inner product in terms of the two
   axial coordinates and the normalized transverse directions, including zero residuals.
   `AngularDisintegration n` still requires the joint sampling law of those directions.
   The Jacobian and subsequent integration against nonnegative measurable tests are proved.
   The general-s law and transport to the archive remain open.
2. `groupHaar_two_rightInvariant` proves right invariance in dimension two.
   In general `groupHaar_rightInvariant_of_perfect` reduces it to perfectness
   of the real special linear group. For a nonzero right-invariant measure
   `domain_mass_ne_zero` proves positivity on every arithmetic fundamental domain.
   Constructing such a domain of finite mass remains open.
3. `tupleWorkload_measurable` proves quotient measurability for every finite tuple length
   by reindexing each representative's sum over nonzero integer vectors.
   `siegel_of_measurable_unfolding` uses this and domain positivity. Its
   unnormalized integral identity still requires arithmetic unfolding. The local
   conclusion concerns nonnegative tests. Signed tests additionally require
   integrability and passage to positive and negative parts. For
   higher orders one needs the integral tuple-orbit decomposition, orbit
   measures with their stabilizer covolumes, and the resulting weights for
   primitive and dependent tuples. The modular-index bound alone does not
   identify Haar integrals. Neither the k=2,3 workload equality nor the
   arbitrary-order equality used by the growing-moment theorem is proved.
4. The statements use a local presentation of the quotient workload. The
   point set is proved independent of the representative. A formal transport
   to the archive's measurable basis-coordinate sum and its definitions
   remains open. No archive module has been modified or rebuilt.

## Pair law by slicing (mathematical proof)

By `cone_volume_eq`, take the first coordinate as pole. For 0 < t < 1,
write a point as (u,w) with transverse dimension n−1. In the open unit ball
the condition for the cap is u ≥ t‖(u,w)‖. At 0 < u < 1 its section is a
ball up to its boundary, of radius
min(√(1−u²), u√(1−t²)/t). The two radii agree at u=t. Its boundary has
zero transverse volume. Write V for the transverse unit-ball volume.
Integrating the smaller radius to the power n−1 gives

    volume(cap) / V = t/n · (1−t²)^((n−1)/2) + ∫_[t,1] (1−u²)^((n−1)/2) du.

The first term integrates the cone portion from 0 to t. The second
integrates the remaining ball sections. By `capSlice_derivative` the
negative derivative is (n−1)/n · (1−t²)^((n−3)/2). The total sphere mass
in the cone formula is n times the ambient unit-ball volume. Hence the
normalized angular density on (0,1) is proportional to that power.
Gamma duplication and the Euclidean unit-ball volume formula identify the coefficient
in `transverse_ball_volume`. Continuity of measure on nested half-lines gives the
positive closed tails, including the endpoint. Reflection at the opposite pole,
evenness of the weight and total mass one give the nonpositive closed tails.
Integrating the fixed-pole law over the independent first point yields the pair law.

## Verbatim public theorem statements


```lean
theorem denominator_dvd_rowIndex {r k q : ℕ} (D : Diagram r k q) :
    q ∣ Nat.card (rowImage D)
```

```lean
theorem coefficient_bound (n k : ℕ) (r : Fin k) (q : ℕ) (D : Diagram (r.val+1) k (q+1)) :
    congruenceCoefficient n k r q D ≤ ENNReal.ofReal (((q+1 : ℕ) : ℝ) ^ (-(n : ℝ)))
```

```lean
theorem coefficient_one (n k : ℕ) (r : Fin k) (D : Diagram (r.val+1) k 1) :
    congruenceCoefficient n k r 0 D = 1
```

```lean
theorem classicalRogersFormula_iff {n : ℕ} (ν : Measure (LatticeSpace n)) :
    ClassicalRogersFormula ν (congruenceCoefficient n) ↔
      ∀ k, 1 ≤ k → k < n → ∀ F : (Fin k → E n) → ℝ≥0∞, Admissible F →
        (∫⁻ L, tupleWorkload F L ∂ν) = diagramSum (congruenceCoefficient n) F
```

```lean
theorem weight_integral {p : ℝ} (hp : -1 < p) : ∫⁻ t, weight p t = 1
```

```lean
theorem det3_fiber (a b t : ℝ) (ha : a ∈ Ioo (-1 : ℝ) 1) (hb : b ∈ Ioo (-1 : ℝ) 1) :
    det3 a b (a*b + Real.sqrt ((1-a^2)*(1-b^2))*t) = (1-a^2)*(1-b^2)*(1-t^2)
```

```lean
theorem fiber_integral (a b p : ℝ) (ha : a ∈ Ioo (-1 : ℝ) 1) (hb : b ∈ Ioo (-1 : ℝ) 1)
    (F : ℝ → ℝ≥0∞) :
    let u := (1-a^2)*(1-b^2)
    ∫⁻ c in {c | 0 < det3 a b c}, ENNReal.ofReal (det3 a b c ^ p) * F c =
      ∫⁻ t in Ioo (-1 : ℝ) 1, ENNReal.ofReal (u ^ (p+1/2) * (1-t^2)^p) *
        F (a*b + Real.sqrt u*t)
```

```lean
theorem uniform_probability {n : ℕ} (hn : 0 < n) : IsProbabilityMeasure (uniform n)
```

```lean
theorem pairLaw_of_coneVolumes {n : ℕ} (hn : 3 ≤ n)
    (h : ∀ (x : Sphere n) (s : Set ℝ), MeasurableSet s →
      ((volume : Measure (Ambient n)).toSphere univ)⁻¹ *
        (n * volume (Ioo (0:ℝ) 1 • (Subtype.val ''
          {y : Sphere n | inner ℝ (x : Ambient n) (y : Ambient n) ∈ s}))) =
        (volume.withDensity (weight (((n:ℝ)-3)/2))) s) : PairLaw n
```

```lean
theorem triple_marginal (n : ℕ) (hn : 3 ≤ n) (a b : ℝ) :
    ∫⁻ c, tripleWeight n (a,b,c) =
      weight (((n:ℝ)-4)/2+1/2) a * weight (((n:ℝ)-4)/2+1/2) b
```

```lean
theorem triple_integral (n : ℕ) (hn : 3 ≤ n) : ∫⁻ x, tripleWeight n x = 1
```

```lean
theorem points_mk {n : ℕ} (g : SL n) :
    points (QuotientGroup.mk g) =
      Set.range (fun z : Fin n → ℤ ↦ WithLp.toLp 2 (g • (fun i ↦ (z i : ℝ))))
```

```lean
theorem fullRank_denominator {k q : ℕ} (D : Diagram k k q) : q = 1
```

```lean
theorem sieveWorkload {n k : ℕ} {ν : Measure (LatticeSpace n)} {c : Coefficients}
    (h : ClassicalRogersFormula ν c) (hk : k ∈ Finset.Icc 1 3) (hn : k < n)
    {F : (Fin k → E n) → ℝ≥0∞} (hF : Admissible F) :
    (∫⁻ L, tupleWorkload F L ∂ν) = diagramSum c F
```

```lean
theorem diagramSum_one {n : ℕ} {c : Coefficients} (hc : ∀ D, c 1 0 0 D = 1)
    (f : E n → ℝ≥0∞) :
    diagramSum c (fun v : Fin 1 → E n ↦ f (v 0)) = ∫⁻ x, f x
```

```lean
theorem siegel_of_rogers {n : ℕ} {ν : Measure (LatticeSpace n)} {c : Coefficients}
    (h : ClassicalRogersFormula ν c) (hn : 1 < n) (f : E n → ℝ≥0∞)
    (hf : Admissible (fun v : Fin 1 → E n ↦ f (v 0))) :
    (∫⁻ L, tupleWorkload (fun v : Fin 1 → E n ↦ f (v 0)) L ∂ν) = ∫⁻ x, f x
```

~~~lean
theorem cone_volume_eq {n : ℕ} (x y : Sphere n) (s : Set ℝ) :
    volume (cone x s) = volume (cone y s)
~~~

~~~lean
theorem pairLaw_of_pole {n : ℕ} (hn : 3 ≤ n) (pole : Sphere n)
    (h : ∀ s : Set ℝ, MeasurableSet s →
      ((volume : Measure (Ambient n)).toSphere univ)⁻¹ * (n * volume (cone pole s)) =
        (volume.withDensity (weight (((n : ℝ) - 3) / 2))) s) : PairLaw n
~~~

~~~lean
theorem cone_Ici_eq {n : ℕ} (pole : Sphere n) (t : ℝ) :
    cone pole (Ici t) = {z | 0 < ‖z‖ ∧ ‖z‖ < 1 ∧ t * ‖z‖ ≤ inner ℝ (pole : Ambient n) z}
~~~

~~~lean
theorem capSlice_derivative {d t : ℝ} (hd : 3 ≤ d) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (capSlice d) (-((d-1)/d) * (1-t^2)^((d-3)/2)) t
~~~

~~~lean
theorem pairLaw_of_capVolumes {n : ℕ} (hn : 3 ≤ n) (pole : Sphere n)
    (h : ∀ t : ℝ, ((volume : Measure (Ambient n)).toSphere univ)⁻¹ *
      (n * volume {z : Ambient n | 0 < ‖z‖ ∧ ‖z‖ < 1 ∧ t * ‖z‖ ≤ inner ℝ (pole : Ambient n) z}) =
      (volume.withDensity (weight (((n : ℝ)-3)/2))) (Ici t)) : PairLaw n
~~~

~~~lean
theorem triple_fiber_test (n : ℕ) (hn : 3 ≤ n) (a b : ℝ)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    let p := ((n : ℝ)-4)/2
    ∫⁻ c, tripleWeight n (a,b,c) * F c =
      weight (p+1/2) a * weight (p+1/2) b *
        ∫⁻ t, weight p t * F (angularThird a b t)
~~~

~~~lean
def AngularDisintegration (n : ℕ) : Prop :=
  ∀ F : ℝ × ℝ × ℝ → ℝ≥0∞, Measurable F →
    let p := ((n : ℝ)-4)/2
    (∫⁻ z : Sphere n × Sphere n × Sphere n,
      F (inner ℝ (z.1 : Ambient n) (z.2.1 : Ambient n),
         inner ℝ (z.1 : Ambient n) (z.2.2 : Ambient n),
         inner ℝ (z.2.1 : Ambient n) (z.2.2 : Ambient n))
      ∂(uniform n).prod ((uniform n).prod (uniform n))) =
      ∫⁻ a, ∫⁻ b, weight (p+1/2) a * weight (p+1/2) b *
        ∫⁻ t, weight p t * F (a,b,angularThird a b t)
~~~

~~~lean
theorem tripleLaw_of_angularDisintegration {n : ℕ} (hn : 3 ≤ n)
    (h : AngularDisintegration n) : TripleLaw n
~~~

~~~lean
theorem domainProbability_probability {n : ℕ} (μ : Measure (SL n)) (D : Set (SL n))
    (hpos : μ D ≠ 0) (hfin : μ D ≠ ∞) : IsProbabilityMeasure (domainProbability μ D)
~~~

~~~lean
theorem domainProbability_invariant {n : ℕ} (μ : Measure (SL n))
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {D : Set (SL n)}
    (hD : IsFundamentalDomain (integerGroup n).op D μ) :
    SMulInvariantMeasure (SL n) (LatticeSpace n) (domainProbability μ D)
~~~

~~~lean
theorem siegel_of_domain_unfolding {n : ℕ} (μ : Measure (SL n)) (D : Set (SL n))
    (hpos : μ D ≠ 0) (hfin : μ D ≠ ∞) (f : E n → ℝ≥0∞)
    (hm : Measurable (tupleWorkload (fun v : Fin 1 → E n ↦ f (v 0))))
    (hu : ∫⁻ g in D, tupleWorkload (fun v : Fin 1 → E n ↦ f (v 0))
      (QuotientGroup.mk g) ∂μ = μ D * ∫⁻ x, f x) :
    (∫⁻ L, tupleWorkload (fun v : Fin 1 → E n ↦ f (v 0)) L ∂domainProbability μ D) =
      ∫⁻ x, f x
~~~

~~~lean
theorem capSection_volume (m : ℕ) {t u : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    volume {w : Ambient m | u^2 + ‖w‖^2 < 1 ∧ t * Real.sqrt (u^2 + ‖w‖^2) ≤ u} =
      ENNReal.ofReal (min (u * (Real.sqrt (1-t^2) / t)) (Real.sqrt (1-u^2))) ^ m *
        volume (Metric.ball (0 : Ambient m) 1)
~~~

~~~lean
theorem capRadius_integral (m : ℕ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (∫ u in (0 : ℝ)..1,
      min (u * (Real.sqrt (1-t^2) / t)) (Real.sqrt (1-u^2)) ^ m) =
      capSlice (m+1) t
~~~

~~~lean
theorem axialCap_volume (m : ℕ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    volume {z : ℝ × Ambient m | z.1 ∈ Ioo (0 : ℝ) 1 ∧
      z.1^2 + ‖z.2‖^2 < 1 ∧ t * Real.sqrt (z.1^2 + ‖z.2‖^2) ≤ z.1} =
      ENNReal.ofReal (capSlice (m+1) t) * volume (Metric.ball (0 : Ambient m) 1)
~~~

~~~lean
theorem cone_positive_volume (m : ℕ) (pole : Sphere (m+1)) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    volume (cone pole (Ici t)) =
      ENNReal.ofReal (capSlice (m+1) t) * volume (Metric.ball (0 : Ambient m) 1)
~~~

~~~lean
theorem capSlice_tail {d t : ℝ} (hd : 3 ≤ d) (ht : t ∈ Icc (0 : ℝ) 1) :
    capSlice d t = ((d-1)/d) * ∫ u in t..1, (1-u^2)^((d-3)/2)
~~~

~~~lean
theorem capSlice_normalized {d t : ℝ} (hd : 3 ≤ d) (ht : t ∈ Icc (0 : ℝ) 1) :
    (volume.withDensity (weight ((d-3)/2))) (Ici t) =
      ENNReal.ofReal (normalizer ((d-3)/2) * (d/(d-1)) * capSlice d t)
~~~

~~~lean
theorem normalizer_gamma {p : ℝ} (hp : -1 < p) :
    normalizer p = Real.Gamma (p + 1 + 1/2) / (Real.sqrt Real.pi * Real.Gamma (p+1))
~~~

~~~lean
theorem transverse_ball_volume (m : ℕ) (hm : 2 ≤ m) :
    volume (Metric.ball (0 : Ambient m) 1) =
      ENNReal.ofReal (normalizer (((m:ℝ)+1-3)/2) * ((m+1)/m)) *
        volume (Metric.ball (0 : Ambient (m+1)) 1)
~~~

~~~lean
theorem normalized_positive_cap (m : ℕ) (hm : 2 ≤ m) (pole : Sphere (m+1))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (uniform (m+1)).map (fun y : Sphere (m+1) ↦ inner ℝ (pole : Ambient (m+1)) y) (Ici t) =
      (volume.withDensity (weight (((m:ℝ)+1-3)/2))) (Ici t)
~~~

~~~lean
theorem pole_law (m : ℕ) (hm : 2 ≤ m) (pole : Sphere (m+1)) :
    (uniform (m+1)).map (fun y : Sphere (m+1) ↦ inner ℝ (pole : Ambient (m+1)) y) =
      volume.withDensity (weight (((m:ℝ)+1-3)/2))
~~~

~~~lean
theorem pair_law {n : ℕ} (hn : 3 ≤ n) : PairLaw n
~~~

~~~lean
theorem axial_pair_law (m : ℕ) (hm : 2 ≤ m) (pole : Sphere (m+1)) :
    let f := fun y : Sphere (m+1) ↦ inner ℝ (pole : Ambient (m+1)) y
    let ν := volume.withDensity (weight (((m:ℝ)+1-3)/2))
    ((uniform (m+1)).prod (uniform (m+1))).map (Prod.map f f) = ν.prod ν
~~~

~~~lean
theorem transverse_inner {n : ℕ} (x y z : Sphere n) :
    let a := inner ℝ (x : Ambient n) y
    let b := inner ℝ (x : Ambient n) z
    let u := (y : Ambient n) - a • (x : Ambient n)
    let v := (z : Ambient n) - b • (x : Ambient n)
    inner ℝ (y : Ambient n) z =
      angularThird a b (inner ℝ (‖u‖⁻¹ • u) (‖v‖⁻¹ • v))
~~~

~~~lean
theorem tupleWorkload_measurable {n k : ℕ} {F : (Fin k → E n) → ℝ≥0∞} (hF : Measurable F) :
    Measurable (tupleWorkload F)
~~~

~~~lean
theorem domain_mass_ne_zero {n : ℕ} (μ : Measure (SL n)) [μ.IsMulRightInvariant]
    (hμ : μ ≠ 0) {D : Set (SL n)} (hD : IsFundamentalDomain (integerGroup n).op D μ) :
    μ D ≠ 0
~~~

~~~lean
theorem siegel_of_measurable_unfolding {n : ℕ} (μ : Measure (SL n)) [μ.IsMulRightInvariant]
    (hμ : μ ≠ 0) {D : Set (SL n)} (hD : IsFundamentalDomain (integerGroup n).op D μ)
    (hfin : μ D ≠ ∞) (f : E n → ℝ≥0∞) (hf : Measurable f)
    (hu : ∫⁻ g in D, tupleWorkload (fun v : Fin 1 → E n ↦ f (v 0))
      (QuotientGroup.mk g) ∂μ = μ D * ∫⁻ x, f x) :
    (∫⁻ L, tupleWorkload (fun v : Fin 1 → E n ↦ f (v 0)) L ∂domainProbability μ D) =
      ∫⁻ x, f x
~~~

~~~lean
theorem groupHaar_rightInvariant_of_perfect {n : ℕ} (h : commutator (SL n) = ⊤) :
    (groupHaar n).IsMulRightInvariant
~~~

~~~lean
theorem groupHaar_two_rightInvariant : (groupHaar 2).IsMulRightInvariant
~~~

## Lean axiom audit

```text
'SigabaNeo.Rogers.denominator_dvd_rowIndex' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.coefficient_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.coefficient_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.classicalRogersFormula_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.Gram.weight_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.Gram.det3_fiber' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.Gram.fiber_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.Gram.uniform_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.Gram.pairLaw_of_coneVolumes' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.Gram.triple_marginal' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.Gram.triple_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.points_mk' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.fullRank_denominator' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.sieveWorkload' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.diagramSum_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.siegel_of_rogers' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.Gram.cone_volume_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.Gram.pairLaw_of_pole' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.Gram.cone_Ici_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.Gram.capSlice_derivative' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.Gram.pairLaw_of_capVolumes' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.Gram.triple_fiber_test' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.Gram.tripleLaw_of_angularDisintegration' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.domainProbability_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.domainProbability_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.siegel_of_domain_unfolding' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.Gram.capSection_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.Gram.capRadius_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.Gram.axialCap_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.Gram.cone_positive_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.Gram.capSlice_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.Gram.capSlice_normalized' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.Gram.normalizer_gamma' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.Gram.transverse_ball_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.Gram.normalized_positive_cap' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.Gram.pole_law' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.Gram.pair_law' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.Gram.axial_pair_law' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.Gram.transverse_inner' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.tupleWorkload_measurable' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.domain_mass_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.siegel_of_measurable_unfolding' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.groupHaar_rightInvariant_of_perfect' depends on axioms: [propext, Classical.choice, Quot.sound]
'SigabaNeo.Rogers.groupHaar_two_rightInvariant' depends on axioms: [propext, Classical.choice, Quot.sound]
```
