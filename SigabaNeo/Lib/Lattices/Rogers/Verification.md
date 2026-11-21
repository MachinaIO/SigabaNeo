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

1. For pairs, the Lean obligation is the single-pole cap volume in
   `pairLaw_of_capVolumes` for all real thresholds. Rotation invariance,
   reduction to half-lines, the geometric cap description, and the derivative
   of the proposed slice integral are proved for dimensions n ≥ 3. The
   slicing calculation and its normalization below still need Lean proofs.
   For triples, the sole hypothesis of `tripleLaw_of_angularDisintegration`
   is `AngularDisintegration n`. It identifies the two axial cosines and the
   relative transverse cosine with independent scalar variables of exponents
   (n−3)/2, (n−3)/2, and (n−4)/2. The subsequent Jacobian and integration
   against arbitrary nonnegative measurable tests are proved for n ≥ 3.
   The general-s law and transport to the archive remain open.
2. `groupHaar` constructs Haar measure on SL from local compactness.
   `domainProbability` projects its normalized restriction to a domain.
   Positive finite domain mass gives a probability measure. For a genuine
   fundamental domain and bi-invariant group measure, quotient invariance
   follows from Mathlib's quotient theorem. The proof supplies Polishness,
   countability and closedness of the integral subgroup. An application to
   `groupHaar` still requires its right invariance and an arithmetic
   fundamental domain of finite positive mass.
3. `siegel_of_domain_unfolding` accounts for the exact domain mass. The
   missing inputs are measurability of the order-one workload and its
   unnormalized integral on that domain for the prescribed tests. The local
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
Reflection gives the same constant on (−1,0). The cones at the endpoints
are rays and the equator lies in a hyperplane, all of zero ambient volume.
The fundamental theorem of calculus on interior intervals therefore gives
the whole measure. Its mass one and `weight_integral` uniquely determine
the coefficient as `normalizer ((n−3)/2)`. Integrating the fixed-pole
law over the independent first point yields the pair law.

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
```
