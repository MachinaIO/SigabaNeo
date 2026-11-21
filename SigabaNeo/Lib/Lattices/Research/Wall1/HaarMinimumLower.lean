import SigabaNeo.Lib.Lattices.Research.Wall1.HaarMinimumTails

/-! Divisor incidences for the two-content sieve on independent ordered lattice pairs. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SigabaNeo.Wall1
open SigabaNeo.Rogers

private def scaleVec {n : ℕ} (k : ℕ) (v : NonzeroIntVector n) : NonzeroIntVector n :=
  ⟨((k + 1 : ℕ) : ℤ) • v.val, smul_ne_zero (by positivity) v.property⟩

private theorem scale_indep {n : ℕ} (k : Fin 2 → ℕ) (z : OrderTwoPair n)
    (hz : z ∈ orderTwoIndependent n) : (fun i ↦ scaleVec (k i) (z i)) ∈ orderTwoIndependent n :=
  (show LinearIndependent ℤ _ from hz).smul_of_isRightRegular
    (w := fun i ↦ ((k i + 1 : ℕ) : ℤ)) (fun i ↦ fun _ _ h ↦ mul_right_cancel₀ (by positivity) h)

private theorem unscale_indep {n : ℕ} (k : Fin 2 → ℕ) (z : OrderTwoPair n)
    (hz : (fun i ↦ scaleVec (k i) (z i)) ∈ orderTwoIndependent n) :
    z ∈ orderTwoIndependent n := by
  let u := fun i ↦ ((k i + 1 : ℕ) : ℤ)
  have h := scale_indep (fun i ↦ k (1 - i)) _ hz
  change LinearIndependent ℤ (fun i ↦ u (1-i) • u i • (z i).val) at h
  have e : (fun i ↦ u (1-i) • u i • (z i).val) =
      ![(u 1 * u 0) • (z 0).val, (u 1 * u 0) • (z 1).val] := by
    funext i
    fin_cases i <;> simp [mul_comm, mul_left_comm, mul_assoc]
  rw [e, LinearIndependent.pair_smul_iff (by dsimp [u]; positivity)] at h
  change LinearIndependent ℤ (fun i ↦ (z i).val)
  convert h using 1
  funext i
  fin_cases i <;> rfl

/-- Independent ordered pairs in which column i has content divisible by k i + 1. -/
abbrev divisiblePairs (n : ℕ) (k : Fin 2 → ℕ) :=
  {z : orderTwoIndependent n // ∀ i, k i + 1 ∣ vectorContent (z.val i)}

private def scalePair {n : ℕ} (k : Fin 2 → ℕ) (z : orderTwoIndependent n) :
    divisiblePairs n k :=
  ⟨⟨fun i ↦ scaleVec (k i) (z.val i), scale_indep k z.val z.property⟩, fun i ↦ by
    change k i + 1 ∣ Finset.univ.gcd (fun j ↦ (((k i + 1 : ℕ) : ℤ) * (z.val i).val j).natAbs)
    rw [scaledContent]
    exact dvd_mul_right _ _⟩

private theorem scalePair_bijective {n : ℕ} (k : Fin 2 → ℕ) :
    Function.Bijective (scalePair (n := n) k) := by
  constructor
  · intro a b h
    apply Subtype.ext
    funext i
    apply Subtype.ext
    funext j
    have e := congrArg (fun z : divisiblePairs n k ↦ (z.val.val i).val j) h
    change ((k i + 1 : ℕ) : ℤ) * _ = ((k i + 1 : ℕ) : ℤ) * _ at e
    exact mul_left_cancel₀ (by positivity) e
  · intro z
    have hd (i j) : ((k i + 1 : ℕ) : ℤ) ∣ (z.val.val i).val j :=
      Int.natCast_dvd.mpr ((z.property i).trans (Finset.gcd_dvd (Finset.mem_univ j)))
    choose v hv using hd
    have nz (i) : v i ≠ 0 := by
      intro h
      exact (z.val.val i).property (funext fun j ↦ by simp [hv, h])
    let w : OrderTwoPair n := fun i ↦ ⟨v i, nz i⟩
    have he : (fun i ↦ scaleVec (k i) (w i)) = z.val.val :=
      funext fun i ↦ Subtype.ext (funext fun j ↦ (hv i j).symm)
    exact ⟨⟨w, unscale_indep k w (he ▸ z.val.property)⟩, Subtype.ext (Subtype.ext he)⟩

private def box {n : ℕ} (r : Fin 2 → ℝ) := Set.univ.pi fun i ↦ Metric.ball (0 : E n) (r i)

private theorem box_meas {n : ℕ} (r : Fin 2 → ℝ) : MeasurableSet (box (n := n) r) :=
  MeasurableSet.univ_pi fun _ ↦ measurableSet_ball

/-- Normalized mean of every joint divisibility incidence used in the primitive sieve. -/
theorem divisiblePairs_mean {n : ℕ} (hn : 2 < n) (D : Set (SL n))
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    (hp : groupHaar n D ≠ 0) (hf : groupHaar n D ≠ ⊤) (k : Fin 2 → ℕ) (r : ℝ) :
    (∑' z : divisiblePairs n k, orderTwoOrbit D
      ((Set.univ.pi (fun _ : Fin 2 ↦ Metric.ball (0 : E n) r)).indicator 1) z.val.val) /
        groupHaar n D = ∏ i, dilationWeight n (k i) * volume (Metric.ball (0 : E n) r) := by
  classical
  let s := fun i ↦ (((k i + 1 : ℕ) : ℝ))⁻¹ * r
  let F := (box (n := n) s).indicator (1 : (Fin 2 → E n) → ℝ≥0∞)
  have mF : Measurable F := measurable_one.indicator (box_meas s)
  rw [← (Equiv.ofBijective _ (scalePair_bijective (n := n) k)).tsum_eq]
  have term (z : orderTwoIndependent n) :
      orderTwoOrbit D ((box (n := n) (fun _ ↦ r)).indicator 1) (scalePair k z).val.val =
        orderTwoOrbit D F z.val := by
    apply lintegral_congr
    intro g
    let x := fun i ↦ WithLp.toLp 2 (g • fun j ↦ ((z.val i).val j : ℝ))
    have e (i) : WithLp.toLp 2 (g • fun j ↦ (((scalePair k z).val.val i).val j : ℝ)) =
        ((k i + 1 : ℕ) : ℝ) • x i := by
      apply WithLp.ofLp_injective 2
      change g.val.mulVec _ = ((k i + 1 : ℕ) : ℝ) • g.val.mulVec _
      rw [← Matrix.mulVec_smul]
      congr 1
      funext j
      exact Int.cast_mul _ _
    simp_rw [e]
    change (box _).indicator 1 _ = (box s).indicator 1 x
    have mem : (fun i ↦ ((k i + 1 : ℕ) : ℝ) • x i) ∈ box (fun _ ↦ r) ↔ x ∈ box s := by
      simp only [box, Set.mem_univ_pi]
      apply forall_congr'
      intro i
      simp only [Metric.mem_ball, dist_zero_right, norm_smul,
        Real.norm_eq_abs, abs_of_pos (by positivity : 0 < ((k i + 1 : ℕ) : ℝ)), s]
      rw [← div_eq_inv_mul, lt_div_iff₀ (by positivity), mul_comm]
    simp only [Set.indicator_apply, mem, Pi.one_apply]
  change (∑' z, orderTwoOrbit D _ (scalePair k z).val.val) / _ = _
  unfold box at term
  rw [tsum_congr term]
  rw [← independentPairMeasure_lintegral D F mF]
  obtain ⟨C, hC⟩ := independentPairMeasure_proportional hn hd hf
  rw [hC, independentPairMeasure_scalar_calibration hn hd hf hC, lintegral_smul_measure,
    smul_eq_mul, mul_comm, ENNReal.mul_div_cancel_right hp hf]
  rw [show (∫⁻ a, F a ∂Measure.pi (fun _ ↦ volume)) = (Measure.pi (fun _ : Fin 2 ↦ (volume : Measure (E n)))) (box (n := n) s) by
    simp [F, lintegral_indicator (box_meas s)], box, Measure.pi_pi]
  apply Finset.prod_congr rfl
  intro i _
  rw [Measure.addHaar_ball_mul_of_pos _ _ (by positivity : 0 < (((k i + 1 : ℕ) : ℝ))⁻¹)]
  simp [dilationWeight, inv_pow, abs_of_pos (by positivity : 0 < (k i : ℝ) + 1)]

private def multiples (k : ℕ) : Set ℕ := {a | k + 1 ∣ a}

private def rect (k : Fin 2 → ℕ) : Set (ℕ × ℕ) := multiples (k 0) ×ˢ multiples (k 1)

private theorem primitive_atom {μ ν : Measure (ℕ × ℕ)} [IsFiniteMeasure μ]
    (he : ∀ k, μ (rect k) = ν (rect k)) : μ {(1,1)} = ν {(1,1)} := by
  have allMeas (s : Set (ℕ × ℕ)) : MeasurableSet s := s.to_countable.measurableSet
  let C := Set.range rect
  have hpi : IsPiSystem C := by
    rintro _ ⟨k,rfl⟩ _ ⟨l,rfl⟩ _
    use fun i ↦ (Nat.lcm (k i + 1) (l i + 1)) - 1
    ext p
    have eq (i) : (Nat.lcm (k i + 1) (l i + 1)) - 1 + 1 = _ :=
      Nat.sub_add_cancel (Nat.lcm_pos (Nat.succ_pos _) (Nat.succ_pos _))
    simp only [rect, multiples, Set.mem_prod, Set.mem_ofPred_eq, eq, Nat.lcm_dvd_iff,
      Set.mem_inter_iff]
    tauto
  let m := MeasurableSpace.generateFrom C
  have basic (k) : MeasurableSet[m] (rect k) :=
    MeasurableSpace.measurableSet_generateFrom ⟨k,rfl⟩
  have atom : MeasurableSet[m] ({(1,1)} : Set (ℕ × ℕ)) := by
    let : MeasurableSpace (ℕ × ℕ) := m
    have eq : ({(1,1)} : Set (ℕ × ℕ)) =
        (⋃ k : ℕ, rect ![k+1,0] ∪ rect ![0,k+1])ᶜ := by
      ext ⟨a,b⟩
      simp only [Set.mem_singleton_iff, Prod.mk.injEq, Set.mem_compl_iff, Set.mem_iUnion,
        Set.mem_union, rect, multiples, Set.mem_prod, Set.mem_ofPred_eq, Matrix.cons_val_zero,
        Matrix.cons_val_one, zero_add, one_dvd, and_true, true_and]
      constructor
      · rintro ⟨rfl,rfl⟩ ⟨k,h | h⟩ <;> have := Nat.dvd_one.mp h <;> omega
      · intro h
        have one (a : ℕ) (ha : ∀ k : ℕ, ¬ k+1+1 ∣ a) : a = 1 := by
          cases a with
          | zero => exact (ha 0 (dvd_zero _)).elim
          | succ a => cases a with
            | zero => rfl
            | succ a => exact (ha a dvd_rfl).elim
        exact ⟨one a fun k hk ↦ h ⟨k, Or.inl hk⟩, one b fun k hk ↦ h ⟨k, Or.inr hk⟩⟩
    rw [eq]
    exact (MeasurableSet.iUnion fun k ↦ (basic _).union (basic _)).compl
  apply ext_on_measurableSpace_of_generate_finite (μ := μ) (ν := ν) _ C _ _ rfl hpi _ atom
  · rintro _ ⟨k,rfl⟩
    exact he k
  · exact fun s _ ↦ allMeas s
  · simpa [rect, multiples] using he (fun _ ↦ 0)

private def atoms {ι α : Type*} [MeasurableSpace α] (f : ι → α) (w : ι → ℝ≥0∞) :=
  Measure.sum fun i ↦ w i • Measure.dirac (f i)

private theorem atoms_apply {ι α : Type*} [MeasurableSpace α] (f : ι → α) (w : ι → ℝ≥0∞)
    (s : Set α) (hs : MeasurableSet s) :
    atoms f w s = ∑' i : {i // f i ∈ s}, w i.val := by
  classical
  rw [atoms, Measure.sum_apply _ hs]
  change _ = ∑' i : (f ⁻¹' s), w i.val
  rw [tsum_subtype]
  apply tsum_congr
  intro i
  by_cases h : f i ∈ s <;> simp [Measure.smul_apply, Measure.dirac_apply' _ hs,
    h, Set.mem_preimage]

private def weightMeasure (n : ℕ) := atoms (fun k : ℕ ↦ k+1) (dilationWeight n)

private theorem weightMeasure_multiples (n k : ℕ) :
    weightMeasure n (multiples k) = dilationWeight n k * ∑' j, dilationWeight n j := by
  rw [weightMeasure, atoms_apply _ _ _ (Set.to_countable _).measurableSet]
  let f (j : ℕ) : {i : ℕ // i+1 ∈ multiples k} :=
    ⟨(k+1)*(j+1)-1, by
      change k+1 ∣ (k+1)*(j+1)-1+1
      rw [Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos k) (Nat.succ_pos j))]
      exact dvd_mul_right _ _⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      have e := congrArg Subtype.val h
      dsimp [f] at e
      have ha : 0 < (k+1)*(a+1) := by positivity
      have hb : 0 < (k+1)*(b+1) := by positivity
      have := Nat.eq_of_mul_eq_mul_left (Nat.succ_pos k) (show (k+1)*(a+1) = (k+1)*(b+1) by omega)
      omega
    · rintro ⟨i,j,hj⟩
      cases j with
      | zero => simp at hj
      | succ j => exact ⟨j, Subtype.ext (by dsimp [f]; omega)⟩
  rw [← (Equiv.ofBijective f hf).tsum_eq, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro j
  change dilationWeight n ((k+1)*(j+1)-1) = _
  simp only [dilationWeight, Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos k) (Nat.succ_pos j)),
    Nat.cast_mul, mul_pow, mul_inv_rev, abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
  exact mul_comm _ _


private def contents {n : ℕ} (z : orderTwoIndependent n) :=
  (vectorContent (z.val 0), vectorContent (z.val 1))

/-- Ordered independent pairs with primitive columns. -/
abbrev primitiveIndependentPairs (n : ℕ) :=
  {z : orderTwoIndependent n // vectorContent (z.val 0) = 1 ∧ vectorContent (z.val 1) = 1}

/-- The exact normalized second intensity for ordered independent primitive vectors.
Divisibility rectangles form a π-system, so their intensities determine the primitive atom. -/
theorem primitiveIndependentPairs_mean {n : ℕ} (hn : 2 < n) (D : Set (SL n))
    (hm : MeasurableSet D) (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    (hp : groupHaar n D ≠ 0) (hf : groupHaar n D ≠ ⊤) (r : ℝ) :
    (∑' z : primitiveIndependentPairs n, orderTwoOrbit D
      ((Set.univ.pi (fun _ : Fin 2 ↦ Metric.ball (0 : E n) r)).indicator 1) z.val.val) /
      groupHaar n D = (volume (Metric.ball (0 : E n) r) / ∑' k, dilationWeight n k)^2 := by
  classical
  let V := volume (Metric.ball (0 : E n) r)
  let Z := ∑' k, dilationWeight n k
  obtain ⟨C, _, mass⟩ := siegel_primitive_orbit_covolume n (by omega) D hm hd hf
  have hc : C ≠ 0 := fun h ↦ hp (by simpa [h] using mass.symm)
  have hz : Z ≠ 0 := fun h ↦ hp (by change _ * Z = _ at mass; simpa [h] using mass.symm)
  have hzf : Z ≠ ⊤ := fun h ↦ hf (by rw [← mass]; change C * Z = ⊤; simp [h,hc])
  let w (z : orderTwoIndependent n) := orderTwoOrbit D
    ((Set.univ.pi (fun _ : Fin 2 ↦ Metric.ball (0 : E n) r)).indicator 1) z.val
  let μ := atoms contents (fun z ↦ w z / groupHaar n D)
  let ρ := weightMeasure n
  have total : ρ Set.univ = Z := by
    simpa [ρ, multiples, dilationWeight, Z] using weightMeasure_multiples n 0
  let : IsFiniteMeasure ρ := ⟨total.trans_lt (lt_top_iff_ne_top.mpr hzf)⟩
  let ν := (V / Z)^2 • ρ.prod ρ
  have actual (s : Set (ℕ × ℕ)) : μ s =
      (∑' z : {z : orderTwoIndependent n // contents z ∈ s}, w z.val) / groupHaar n D := by
    rw [show μ s = _ from atoms_apply _ _ s s.to_countable.measurableSet]
    simp only [div_eq_mul_inv, ENNReal.tsum_mul_right]
  have incidence (k) : μ (rect k) = ∏ i, dilationWeight n (k i) * V := by
    rw [actual, ← divisiblePairs_mean hn D hd hp hf k r]
    congr 1
    let e := Equiv.subtypeEquivRight fun z : orderTwoIndependent n ↦
      (show contents z ∈ rect k ↔ ∀ i, k i + 1 ∣ vectorContent (z.val i) from
        by rw [Fin.forall_fin_two]; rfl)
    exact e.tsum_eq (fun z ↦ w z.val)
  have μtotal : μ Set.univ = V^2 := by
    simpa [rect, multiples, dilationWeight, Fin.prod_univ_two, pow_two] using incidence (fun _ ↦ 0)
  let : IsFiniteMeasure μ := ⟨μtotal.trans_lt (by dsimp [V]; finiteness)⟩
  have eq := primitive_atom (μ := μ) (ν := ν) (fun k ↦ by
    rw [incidence, show ν (rect k) = _ from Measure.smul_apply _ _ _, rect, Measure.prod_prod,
      show ρ = weightMeasure n from rfl, weightMeasure_multiples, weightMeasure_multiples]
    change _ = (V / Z)^2 * ((dilationWeight n (k 0) * Z) * (dilationWeight n (k 1) * Z))
    rw [Fin.prod_univ_two, div_eq_mul_inv, pow_two]
    have cancel := ENNReal.inv_mul_cancel hz hzf
    calc
      _ = (dilationWeight n (k 0) * V * (dilationWeight n (k 1) * V)) * (Z⁻¹ * Z)^2 := by
        rw [cancel]; simp
      _ = _ := by rw [pow_two]; ac_rfl)
  have atomOne : ρ {1} = 1 := by
    change atoms _ _ _ = _
    rw [atoms, Measure.sum_apply _ (measurableSet_singleton _), tsum_eq_single 0]
    · simp [dilationWeight]
    · intro j hj
      simp [Measure.smul_apply, hj]
  rw [actual, show ν {(1,1)} = _ from Measure.smul_apply _ _ _,
    ← Set.singleton_prod_singleton, Measure.prod_prod, atomOne, mul_one, smul_eq_mul, mul_one] at eq
  apply Eq.trans _ eq
  congr 1

private def opposite {n} (v : ContentFiber n 1) : ContentFiber n 1 :=
  ⟨⟨-v.val.val, neg_ne_zero.mpr v.val.property⟩, by simpa [vectorContent] using v.property⟩

private theorem opposite_ne {n} (v : ContentFiber n 1) : opposite v ≠ v := by
  intro h
  apply v.val.property
  funext i
  have := congrArg (fun z : ContentFiber n 1 ↦ z.val.val i) h
  change -(v.val.val i) = v.val.val i at this
  change v.val.val i = 0
  omega

private def indep {n} (p : ContentFiber n 1 × ContentFiber n 1) :=
  LinearIndependent ℤ ![p.1.val.val, p.2.val.val]

private theorem prim_indep_iff {n} (v w : ContentFiber n 1) :
    indep (v,w) ↔ w ≠ v ∧ w ≠ opposite v := by
  rw [indep, LinearIndependent.pair_iff]
  constructor
  · intro h
    constructor
    · rintro rfl
      have := (h 1 (-1) (by simp)).1
      omega
    · rintro rfl
      have := (h 1 1 (by simp [opposite])).1
      omega
  · intro ⟨hne,hop⟩ a b hab
    have e := eq_neg_of_add_eq_zero_left hab
    have eq (j) : a * v.val.val j = (-b) * w.val.val j := by
      simpa using congrFun e j
    have content (c : ℤ) (u : ContentFiber n 1) :
        (Finset.univ.gcd fun j ↦ (c * u.val.val j).natAbs) = c.natAbs := by
      simp only [Int.natAbs_mul, Finset.gcd_mul_left, normalize_eq]
      change _ * vectorContent u.val = _
      rw [u.property, mul_one]
    have absEq := content a v
    simp_rw [eq] at absEq
    rw [content, Int.natAbs_neg] at absEq
    by_cases hb : b = 0
    · subst b
      exact ⟨by omega, rfl⟩
    exfalso
    rcases Int.natAbs_eq_natAbs_iff.mp absEq with h | h
    · apply hop
      apply Subtype.ext ∘ Subtype.ext
      funext j
      change w.val.val j = -v.val.val j
      apply mul_left_cancel₀ hb
      have := eq j
      rw [← h] at this
      linarith only [this, neg_mul b (w.val.val j), mul_neg b (v.val.val j)]
    · apply hne
      apply Subtype.ext ∘ Subtype.ext
      funext j
      apply mul_left_cancel₀ hb
      have := eq j
      have hh : b = -a := h
      simpa [hh, neg_mul] using this.symm

private def eval {n} (v : ContentFiber n 1) (g : SL n) : E n :=
  WithLp.toLp 2 (g • fun j ↦ (v.val.val j : ℝ))

private def hit {n} (r : ℝ) (v : ContentFiber n 1) (g : SL n) : ℝ≥0∞ :=
  (Metric.ball (0 : E n) r).indicator 1 (eval v g)

private theorem meas_hit {n} (r : ℝ) (v : ContentFiber n 1) : Measurable (hit r v) := by
  apply (measurable_one.indicator measurableSet_ball).comp
  let : BorelSpace (SL n) := ⟨rfl⟩
  apply Continuous.measurable
  apply (PiLp.continuous_toLp 2 _).comp
  change Continuous (fun g : SL n ↦ g.val.mulVec (fun j ↦ (v.val.val j : ℝ)))
  unfold Matrix.mulVec dotProduct
  fun_prop

private theorem hit_opp {n} (r : ℝ) (v : ContentFiber n 1) (g : SL n) :
    hit r (opposite v) g = hit r v g := by
  have e : eval (opposite v) g = -eval v g := by
    unfold eval
    rw [show (fun j ↦ (((opposite v).val.val j : ℤ) : ℝ)) =
      -(fun j ↦ (v.val.val j : ℝ)) by funext j; simp [opposite], smul_neg]
    rfl
  classical
  unfold hit
  rw [e, Set.indicator_apply, Set.indicator_apply]
  simp [Metric.mem_ball]

private def primEquiv (n) : {p : ContentFiber n 1 × ContentFiber n 1 // indep p} ≃
    primitiveIndependentPairs n where
  toFun p := ⟨⟨![p.val.1.val,p.val.2.val], by
    change LinearIndependent ℤ _
    convert (show LinearIndependent ℤ ![p.val.1.val.val,p.val.2.val.val] from p.property) using 1
    change _ = ![_,_]
    funext i; fin_cases i <;> rfl⟩, p.val.1.property,p.val.2.property⟩
  invFun z := ⟨(⟨z.val.val 0,z.property.1⟩,⟨z.val.val 1,z.property.2⟩), by
    change LinearIndependent ℤ _
    convert (show LinearIndependent ℤ (fun i ↦ (z.val.val i).val) from z.val.property) using 1
    change _ = (fun i ↦ (z.val.val i).val)
    funext i; fin_cases i <;> rfl⟩
  left_inv _ := rfl
  right_inv z := Subtype.ext (Subtype.ext (funext fun i ↦ by fin_cases i <;> rfl))


private def signedTotal {n} (r : ℝ) (g : SL n) := ∑' v, hit r v g

private def indepTotal {n} (r : ℝ) (g : SL n) :=
  ∑' p : {p : ContentFiber n 1 × ContentFiber n 1 // indep p},
    hit r p.val.1 g * hit r p.val.2 g

private theorem signed_square {n} (r : ℝ) (g : SL n) :
    signedTotal r g ^ 2 = 2 * signedTotal r g + indepTotal r g := by
  classical
  let f := fun v : ContentFiber n 1 ↦ hit r v g
  let t := fun p : ContentFiber n 1 × ContentFiber n 1 ↦ f p.1 * f p.2
  let S := {p : ContentFiber n 1 × ContentFiber n 1 | indep p}
  have point (v w : ContentFiber n 1) : f v * f w =
      ((if w = v then f v else 0) + (if w = opposite v then f v else 0)) +
      S.indicator t (v,w) := by
    have idem : f v * f v = f v := by
      dsimp [f,hit]
      rw [Set.indicator_apply]
      split <;> simp
    by_cases a : w = v <;> by_cases b : w = opposite v
    · exact (opposite_ne v (b.symm.trans a)).elim
    · simp [S, prim_indep_iff, a, opposite_ne v |>.symm, idem]
    · simp [S, prim_indep_iff, b, opposite_ne v, f, hit_opp] at *
      exact idem
    · simp [S, prim_indep_iff, a, b, t]
  change (∑' v, f v)^2 = 2 * (∑' v, f v) + ∑' p : S, t p.val
  rw [pow_two, ← ENNReal.tsum_mul_right]
  have row (v) : f v * (∑' w, f w) = (f v + f v) + ∑' w, S.indicator t (v,w) := by
    rw [← ENNReal.tsum_mul_left, tsum_congr (point v)]
    simp [tsum_add]
  rw [tsum_congr row, tsum_add, tsum_add]
  rw [tsum_subtype, tsum_prod']
  rw [two_mul]

private theorem indepTotal_mean {n} (hn : 2 < n) (D : Set (SL n))
    (hm : MeasurableSet D) (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    (hp : groupHaar n D ≠ 0) (hf : groupHaar n D ≠ ⊤) (r : ℝ) :
    (∫⁻ g in D, indepTotal r g ∂groupHaar n) / groupHaar n D =
      (volume (Metric.ball (0 : E n) r) / ∑' k, dilationWeight n k)^2 := by
  classical
  unfold indepTotal
  rw [lintegral_tsum, ← primitiveIndependentPairs_mean hn D hm hd hp hf r, ← (primEquiv n).tsum_eq]
  · congr 1
    apply tsum_congr
    intro p
    apply lintegral_congr
    intro g
    change hit r p.val.1 g * hit r p.val.2 g = (box (fun _ ↦ r)).indicator 1 _
    simp only [hit, Set.indicator_apply, Pi.one_apply, box, Set.mem_univ_pi, Fin.forall_fin_two]
    change (if eval p.val.1 g ∈ _ then 1 else 0) * (if eval p.val.2 g ∈ _ then 1 else 0) =
      if eval p.val.1 g ∈ _ ∧ eval p.val.2 g ∈ _ then 1 else 0
    split_ifs <;> simp_all
  · exact fun p ↦ ((meas_hit r p.val.1).mul (meas_hit r p.val.2)).aemeasurable


private theorem meas_pairs {n} (r : ℝ) : Measurable (@primitiveBallPairs n r) :=
  measurable_const.mul (Measurable.tsum (meas_hit r))

private theorem pairs_square {n} (r : ℝ) (g : SL n) :
    primitiveBallPairs r g ^ 2 = primitiveBallPairs r g + (2 : ℝ≥0∞)⁻¹^2 * indepTotal r g := by
  change ((2 : ℝ≥0∞)⁻¹ * signedTotal r g)^2 = _
  rw [mul_pow, signed_square, mul_add, ← mul_assoc]
  congr 1
  change ((2 : ℝ≥0∞)⁻¹^2 * 2) * _ = 2⁻¹ * _
  have h : (2 : ℝ≥0∞)⁻¹^2 * 2 = 2⁻¹ := by
    rw [sq, mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by simp), mul_one]
  rw [h]
  rfl

/-- The normalized raw second moment of the primitive sign-pair count is m + m². -/
theorem primitiveBallPairs_secondMoment {n} (hn : 2 < n) (D : Set (SL n))
    (hm : MeasurableSet D) (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    (hp : groupHaar n D ≠ 0) (hf : groupHaar n D ≠ ⊤) (r : ℝ) :
    let m := volume (Metric.ball (0 : E n) r) / (2 * ∑' k, dilationWeight n k)
    (∫⁻ g in D, primitiveBallPairs r g ^ 2 ∂groupHaar n) / groupHaar n D = m + m^2 := by
  dsimp only
  simp_rw [pairs_square]
  have mi : Measurable (@indepTotal n r) := Measurable.tsum
    (fun (p : {p : ContentFiber n 1 × ContentFiber n 1 // indep p}) ↦
      (meas_hit r p.val.1).mul (meas_hit r p.val.2))
  rw [lintegral_add_left (meas_pairs r), lintegral_const_mul _ mi, div_eq_mul_inv, add_mul,
    ← div_eq_mul_inv, mul_assoc, ← div_eq_mul_inv, primitiveBallPairs_mean (by omega) D hm hd hp hf,
    indepTotal_mean hn D hm hd hp hf]
  congr 1
  rw [← mul_pow]
  congr 1
  simp [div_eq_mul_inv, ENNReal.mul_inv, mul_assoc, mul_comm]

private theorem ennreal_hit {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (M : Ω → ℝ≥0∞) (hM : Measurable M) (m : ℝ≥0∞) (hf : m ≠ ⊤)
    (h₁ : ∫⁻ x, M x ∂μ = m) (h₂ : ∫⁻ x, M x ^ 2 ∂μ = m + m^2) :
    m / (1+m) ≤ μ {x | 0 < M x} := by
  classical
  let s := {x | 0 < M x}
  have hs : MeasurableSet s := measurableSet_lt measurable_const hM
  let I := s.indicator (1 : Ω → ℝ≥0∞)
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (p := 2) (q := 2)
    (Real.holderConjugate_iff.mpr (by norm_num)) hM.aemeasurable
    ((measurable_one.indicator hs : Measurable I).aemeasurable)
  have e : M * I = M := by
    funext x
    by_cases hx : 0 < M x
    · simp [I,s,hx]
    · simp [I,s,nonpos_iff_eq_zero.mp (le_of_not_gt hx)]
  have ee (x) : I x ^ (2 : ℝ) = I x := by
    by_cases hx : x ∈ s <;> simp [I, hx]
  have hi : ∫⁻ x, I x ∂μ = μ s := by simp [I, lintegral_indicator hs]
  change (∫⁻ x, (M * I) x ∂μ) ≤ (∫⁻ x, M x ^ (2 : ℝ) ∂μ) ^ (1/(2:ℝ)) *
    (∫⁻ x, I x ^ (2 : ℝ) ∂μ) ^ (1/(2:ℝ)) at h
  rw [e,h₁] at h
  simp only [ee, hi, ENNReal.rpow_two, h₂, one_div] at h
  have hsq := pow_le_pow_left' h 2
  have root (a : ℝ≥0∞) : (a ^ ((2 : ℝ)⁻¹)) ^ 2 = a := by
    simpa using ENNReal.rpow_inv_natCast_pow (n := 2) (by decide) a
  rw [mul_pow, root, root] at hsq
  by_cases hz : m = 0
  · simp [hz]
  have hprod : m * m ≤ m * ((1 + m) * μ s) := by
    simpa only [pow_two, ← mul_assoc, mul_add, mul_one] using hsq
  have hcancel := (ENNReal.mul_le_mul_iff_right hz hf).mp hprod
  exact (ENNReal.div_le_iff (by simp) (by simp [hf])).mpr (mul_comm (μ s) _ ▸ hcancel)

/-- Haar lower tail for the hit event of primitive sign pairs in an open ball. -/
theorem primitiveBallPairs_hit_lower {n} (hn : 2 < n) (D : Set (SL n))
    (hm : MeasurableSet D) (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    (hp : groupHaar n D ≠ 0) (hf : groupHaar n D ≠ ⊤) (r : ℝ) :
    let m := volume (Metric.ball (0 : E n) r) / (2 * ∑' k, dilationWeight n k)
    m / (1+m) ≤ (groupHaar n).restrict D {g | 0 < primitiveBallPairs r g} / groupHaar n D := by
  let μ := (groupHaar n D)⁻¹ • (groupHaar n).restrict D
  have normal (f : SL n → ℝ≥0∞) : ∫⁻ g, f g ∂μ = (∫⁻ g in D, f g ∂groupHaar n) / groupHaar n D := by
    dsimp only [μ]
    rw [lintegral_smul_measure, smul_eq_mul, div_eq_mul_inv, mul_comm]
  obtain ⟨C, _, mass⟩ := siegel_primitive_orbit_covolume n (by omega) D hm hd hf
  have hz : (∑' k, dilationWeight n k) ≠ 0 := fun h ↦ hp (by simpa [h] using mass.symm)
  have h := ennreal_hit μ (primitiveBallPairs r) (meas_pairs r) _
    (ENNReal.div_ne_top (by finiteness) (mul_ne_zero (by norm_num) hz))
    ((normal _).trans (primitiveBallPairs_mean (by omega) D hm hd hp hf r))
    ((normal _).trans (primitiveBallPairs_secondMoment hn D hm hd hp hf r))
  simpa only [μ, Measure.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm] using h

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.divisiblePairs_mean
#print axioms SigabaNeo.Wall1.primitiveIndependentPairs_mean
#print axioms SigabaNeo.Wall1.primitiveBallPairs_secondMoment
#print axioms SigabaNeo.Wall1.primitiveBallPairs_hit_lower
