import SigabaNeo.Lib.Lattices.Research.Wall1.PrimitiveUnfolding

/-! Extracting the primitive atom from all divisibility incidences. -/

noncomputable section
open MeasureTheory SigabaNeo.Rogers
open scoped ENNReal
namespace SigabaNeo.Wall1.RankTwo

abbrev zetaFactor (n : ℕ) : ℝ≥0∞ := ∑' k, dilationWeight n k

theorem zetaFactor_ne_zero (n : ℕ) : zetaFactor n ≠ 0 := by
  have h := le_tsum (dilationWeight n) 0
  intro hz
  change _ ≤ zetaFactor n at h
  simp [hz, dilationWeight] at h

theorem zetaFactor_ne_top {n : ℕ} (h : 1 < n) : zetaFactor n ≠ ⊤ := by
  apply Summable.tsum_ofReal_ne_top
  have hs := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr h)
  apply hs.congr
  intro k
  rw [abs_of_nonneg (by positivity), one_div]

def multiples (k : ℕ) : Set ℕ := {a | k+1 ∣ a}

private theorem singleton_generate :
    MeasurableSet[MeasurableSpace.generateFrom (Set.range multiples)] ({1} : Set ℕ) := by
  let : MeasurableSpace ℕ := MeasurableSpace.generateFrom (Set.range multiples)
  have h : ({1} : Set ℕ) = (⋃ k, multiples (k+1))ᶜ := by
    ext a
    simp only [Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion, multiples,
      Set.mem_ofPred_eq, not_exists]
    constructor
    · rintro rfl k hk
      have := Nat.dvd_one.mp hk
      omega
    · intro h
      rcases a with _ | (_ | a)
      · exact (h 0 (dvd_zero _)).elim
      · rfl
      · exact (h a dvd_rfl).elim
  rw [h]
  exact (MeasurableSet.iUnion fun k ↦
    MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self (k+1))).compl

def atoms {ι : Type*} (c : ι → ℕ) (w : ι → ℝ≥0∞) : Measure ℕ :=
  Measure.sum fun i ↦ w i • Measure.dirac (c i)

theorem atoms_apply {ι : Type*} (c : ι → ℕ) (w : ι → ℝ≥0∞) (s : Set ℕ) :
    atoms c w s = ∑' i : {i // c i ∈ s}, w i.val := by
  classical
  rw [atoms, Measure.sum_apply _ s.to_countable.measurableSet]
  change _ = ∑' i : (c ⁻¹' s), w i.val
  rw [tsum_subtype]
  apply tsum_congr
  intro i
  by_cases h : c i ∈ s <;> simp [Measure.smul_apply,
    Measure.dirac_apply' _ s.to_countable.measurableSet, h, Set.mem_preimage]

/-- Multiplication on the positive integers, indexed starting at zero. -/
def times (k : ℕ) (i : ℕ) := (k+1)*(i+1)-1

@[simp] theorem times_succ (k i : ℕ) : times k i + 1 = (k+1)*(i+1) :=
  Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))

def multipleEquiv (k : ℕ) : ℕ ≃ {i : ℕ // k+1 ∣ i+1} :=
  Equiv.ofBijective (fun i ↦ ⟨times k i, by rw [times_succ]; exact dvd_mul_right ..⟩) (by
    constructor
    · intro a b h
      have he := congrArg (fun x : {i : ℕ // k+1 ∣ i+1} ↦ x.val+1) h
      simp only [times_succ, Nat.mul_right_inj (Nat.succ_ne_zero k)] at he
      omega
    · rintro ⟨i, j, hj⟩
      rcases j with _ | j
      · simp at hj
      · exact ⟨j, Subtype.ext (by change times k j = i; have := times_succ k j; omega)⟩)

private theorem reference_mul (n k : ℕ) :
    atoms Nat.succ (dilationWeight n) (multiples k) = dilationWeight n k * zetaFactor n := by
  rw [atoms_apply]
  change (∑' i : {i : ℕ // k+1 ∣ i+1}, dilationWeight n i.val) = _
  unfold zetaFactor
  rw [← (multipleEquiv k).tsum_eq, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro j
  change dilationWeight n (times k j) = _
  simp only [dilationWeight, times_succ, Nat.cast_mul, mul_pow, mul_inv_rev, abs_mul,
    ENNReal.ofReal_mul (abs_nonneg _)]
  exact mul_comm _ _

/-- A finite intensity with divisor-d incidence M/d^n has primitive intensity M/ζ(n). -/
theorem primitive_atom {n : ℕ} (hn : 1 < n) (μ : Measure ℕ) (M : ℝ≥0∞) (hf : M ≠ ⊤)
    (h : ∀ k, μ (multiples k) = dilationWeight n k * M) : μ {1} = M / zetaFactor n := by
  have h0 : multiples 0 = Set.univ := by ext; simp [multiples]
  have total : μ Set.univ = M := by simpa [h0, dilationWeight] using h 0
  let : IsFiniteMeasure μ := ⟨total.trans_lt hf.lt_top⟩
  let ρ := atoms Nat.succ (dilationWeight n)
  let ν := (M / zetaFactor n) • ρ
  have same (k : ℕ) : μ (multiples k) = ν (multiples k) := by
    rw [h, Measure.smul_apply, show ρ (multiples k) = _ from reference_mul n k,
      smul_eq_mul, mul_left_comm, ENNReal.div_mul_cancel (zetaFactor_ne_zero n)
        (zetaFactor_ne_top hn)]
  have piSys : IsPiSystem (Set.range multiples) := by
    rintro _ ⟨k,rfl⟩ _ ⟨l,rfl⟩ _
    refine ⟨(k+1).lcm (l+1)-1, ?_⟩
    ext a
    simp only [multiples, Set.mem_ofPred_eq, Set.mem_inter_iff,
      Nat.sub_add_cancel (Nat.lcm_pos (Nat.succ_pos _) (Nat.succ_pos _)), Nat.lcm_dvd_iff]
  have he : μ {1} = ν {1} := by
    apply ext_on_measurableSpace_of_generate_finite (μ := μ) (ν := ν) _
      (Set.range multiples) _ _ rfl piSys _ singleton_generate
    · rintro _ ⟨k,rfl⟩; exact same k
    · exact fun s _ ↦ s.to_countable.measurableSet
    · simpa [h0] using same 0
  have atom : ρ {1} = 1 := by
    change atoms Nat.succ (dilationWeight n) {1} = 1
    rw [atoms, Measure.sum_apply _ (measurableSet_singleton _),
      tsum_eq_single 0]
    · simp [dilationWeight]
    · intro j hj; simp [Measure.smul_apply, hj]
  simpa [ν, Measure.smul_apply, atom] using he

theorem sieve_series {n : ℕ} (hn : 1 < n) (w : ℕ → ℝ≥0∞) (M : ℝ≥0∞) (hf : M ≠ ⊤)
    (h : ∀ k, (∑' i, w (times k i)) = dilationWeight n k * M) :
    w 0 = M / zetaFactor n := by
  have he := primitive_atom hn (atoms Nat.succ w) M hf (fun k ↦ by
    rw [atoms_apply]
    change (∑' i : {i : ℕ // k+1 ∣ i+1}, w i.val) = _
    rw [← (multipleEquiv k).tsum_eq]
    exact h k)
  have atom : atoms Nat.succ w {1} = w 0 := by
    rw [atoms, Measure.sum_apply _ (measurableSet_singleton _), tsum_eq_single 0]
    · simp
    · intro j hj; simp [Measure.smul_apply, hj]
  exact atom ▸ he

end SigabaNeo.Wall1.RankTwo

#print axioms SigabaNeo.Wall1.RankTwo.primitive_atom
