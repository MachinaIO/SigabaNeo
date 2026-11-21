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

1. Evaluate the solid cone volumes in `pairLaw_of_coneVolumes` to identify the
   actual pair pushforward. For triples, identify the transverse angular
   coordinate with the lower-dimensional scalar sphere law and establish the
   joint disintegration for the actual sphere samples. The general-s
   pushforward and the conversion to the archive's normalized determinant
   measure on transverse spaces remain open.
2. Supply finite positive covolume for the arithmetic subgroup in the real
   special linear group, construct the induced normalized invariant quotient
   measure and instantiate it in the mean-value theorem. Mathlib provides
   generic fundamental-domain and quotient-measure invariance lemmas in
   `Mathlib.MeasureTheory.Measure.Haar.Quotient`.
3. Establish Siegel's normalized unfolding identity on that measure. For
   higher orders one needs the integral tuple-orbit decomposition, orbit
   measures with their stabilizer covolumes, and the resulting weights for
   primitive and dependent tuples. The modular-index bound alone does not
   identify Haar integrals. Neither the k=2,3 workload equality nor the
   arbitrary-order equality used by the growing-moment theorem is proved.
4. The statements use a local presentation of the quotient workload. The
   point set is proved independent of the representative. A formal transport
   to the archive's measurable basis-coordinate sum and its definitions
   remains open. No archive module has been modified or rebuilt.

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
theorem pairLaw_of_coneVolumes {n : ℕ} (hn : 4 ≤ n)
    (h : ∀ (x : Sphere n) (s : Set ℝ), MeasurableSet s →
      ((volume : Measure (Ambient n)).toSphere univ)⁻¹ *
        (n * volume (Ioo (0:ℝ) 1 • (Subtype.val ''
          {y : Sphere n | inner ℝ (x : Ambient n) (y : Ambient n) ∈ s}))) =
        (volume.withDensity (weight (((n:ℝ)-3)/2))) s) : PairLaw n
```

```lean
theorem triple_marginal (n : ℕ) (hn : 5 ≤ n) (a b : ℝ) :
    ∫⁻ c, tripleWeight n (a,b,c) =
      weight (((n:ℝ)-4)/2+1/2) a * weight (((n:ℝ)-4)/2+1/2) b
```

```lean
theorem triple_integral (n : ℕ) (hn : 5 ≤ n) : ∫⁻ x, tripleWeight n x = 1
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
```
