module

public import SigabaNeo.Lib.Lattices.Research.Wall1.AdrsPoisson
public import CslibFrontier.Probability.Conditioning
public import CslibFrontier.Probability.IID
import Mathlib.Tactic

/-! # A countable coupling for Part 140, Lemma 4.3a

Starting from independent marginals, move the same amount of mass from cells (i,j) and
(j,i) onto (i,i) and (j,j). This preserves each marginal and clears the smaller off-diagonal
cell. The likelihood-ratio bound determines which cell is cleared throughout the cutoff.
-/

public section

noncomputable section

namespace SigabaNeo.Wall1.ADRS

open MeasureTheory ProbabilityTheory Cslib.Probability.PMF
open scoped ENNReal NNReal

/-- A coupling which assigns zero mass to (i,j) whenever its independent product weight
is the smaller of the two transposed off-diagonal weights. -/
theorem exists_ordered_cells_coupling {α : Type*} (P Q : PMF α) :
    ∃ J : PMF (α × α), J.map Prod.fst = P ∧ J.map Prod.snd = Q ∧
      ∀ i j, i ≠ j → P i * Q j ≤ P j * Q i → J (i,j) = 0 := by
  classical
  let d i j := min (P i * Q j) (P j * Q i)
  let w (z : α × α) := P z.1 * Q z.2 - d z.1 z.2 +
    if z.1 = z.2 then ∑' k, d z.1 k else 0
  have hd (i j) : d i j ≤ P i * Q j := min_le_left ..
  have hs (i j) : d i j = d j i := min_comm ..
  have row (i) : ∑' j, w (i,j) = P i := by
    simp only [w, tsum_add, tsum_ite_eq']
    rw [← tsum_add]
    simp only [tsub_add_cancel_of_le (hd ..), ENNReal.tsum_mul_left, Q.tsum_coe, mul_one]
  have col (j) : ∑' i, w (i,j) = Q j := by
    simp only [w, tsum_add, tsum_ite_eq]
    conv_lhs => rhs; arg 1; ext i; rw [hs j i]
    rw [← tsum_add]
    simp only [tsub_add_cancel_of_le (hd ..), ENNReal.tsum_mul_right, P.tsum_coe, one_mul]
  let J : PMF (α × α) := ⟨w, CompleteLattice.summable.hasSum_iff.mpr
    (by rw [tsum_prod', show (fun i ↦ ∑' j, w (i,j)) = P from funext row, P.tsum_coe])⟩
  refine ⟨J, ?_, ?_, ?_⟩
  · ext i
    rw [map_fst_apply]
    exact row i
  · ext j
    rw [PMF.map_apply, tsum_prod', tsum_comm, tsum_eq_single j]
    · simp only [ite_true]; exact col j
    · intro k hk
      simp [Ne.symm hk]
  · intro i j hij hle
    change w (i,j) = 0
    simp [w, d, min_eq_left hle, hij]

/-- Lemma 4.3a. The first coordinate has law Pois(a), the second has law Pois(θa²/A).
Failure probability is at most the sum of the two marginal tails. -/
theorem poisson_pair_coupling (a : ℝ≥0) {A θ : ℝ} (ha : 0 < (a : ℝ)) (haA : (a : ℝ) ≤ A)
    (hθ : 0 < θ) {m : ℕ} (hm : m = ⌊A/(4*θ) - 1/2⌋₊) (hm₁ : 1 ≤ m) :
    let b : ℝ≥0 := ⟨θ*(a : ℝ)^2/A, (by have := ha.trans_le haA; positivity)⟩
    ∃ J : PMF (ℕ × ℕ), J.map Prod.fst = (poissonMeasure a).toPMF ∧
      J.map Prod.snd = (poissonMeasure b).toPMF ∧
      J.toOuterMeasure {z | z.1 / 2 < z.2} ≤
        poissonMeasure b {k | m < k} + poissonMeasure a {n | m < n / 2} := by
  intro b
  let N := (poissonMeasure a).toPMF
  let K := (poissonMeasure b).toPMF
  let half (n : ℕ) := n / 2
  let Q := N.map half
  have hK (j) : K j = ENNReal.ofReal (poissonMass b j) := poissonMeasure_singleton ..
  have hQ (j) : Q j = ENNReal.ofReal (halfMass a j) := by
    rw [halfMass_eq, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    change (N.map half) j = _
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    rw [← N.toMeasure_apply_eq_toOuterMeasure_apply MeasurableSet.of_discrete]
    simp [N, half, Set.preimage]
  have hpos (j) : 0 < halfMass a j := by unfold halfMass poissonMass; positivity
  obtain ⟨J₀, hfst, hsnd, hz⟩ := exists_ordered_cells_coupling Q K
  have clear (i j : ℕ) (hij : i < j) (hj : j ≤ m) : J₀ (i,j) = 0 := by
    apply hz i j hij.ne
    simp only [hQ, hK, ← ENNReal.ofReal_mul (hpos _).le]
    apply ENNReal.ofReal_le_ofReal
    have hr := likelihoodRatio_antitone ha haA hθ hm hm₁
      (show i ∈ Set.Iic m from hij.le.trans hj) hj hij.le
    change poissonMass b j / halfMass a j ≤ poissonMass b i / halfMass a i at hr
    have := (div_le_div_iff₀ (hpos _) (hpos _)).mp hr
    linarith
  let J := N.bind fun n ↦ (conditionalSnd J₀ (half n)).map (n, ·)
  let project (z : ℕ × ℕ) := (half z.1, z.2)
  have hproj : J.map project = J₀ := by
    rw [← bind_conditionalSnd J₀, hfst, PMF.bind_map]
    simp only [J, PMF.map_bind, PMF.map_comp, Function.comp_def, project]
  have hn : J.map Prod.fst = N := by
    simp only [J, PMF.map_bind, PMF.map_comp, Function.comp_def]
    change (N.bind fun n ↦ (conditionalSnd J₀ (half n)).map (Function.const ℕ n)) = N
    simp
  have hk : J.map Prod.snd = K := by
    rw [← hsnd, ← hproj, PMF.map_comp]
    rfl
  refine ⟨J, hn, hk, ?_⟩
  let badK : Set (ℕ × ℕ) := Prod.snd ⁻¹' {k : ℕ | m < k}
  let badN : Set (ℕ × ℕ) := Prod.fst ⁻¹' {n : ℕ | m < n / 2}
  calc J.toOuterMeasure {z | z.1 / 2 < z.2} ≤ J.toOuterMeasure (badK ∪ badN) := by
         apply J.toOuterMeasure_mono
         intro z hz'
         by_contra h
         have hj : z.2 ≤ m := by
           by_contra! h'
           exact h (Or.inl h')
         have hs : project z ∈ J₀.support := by
           rw [← hproj]
           exact (PMF.mem_support_map_iff ..).2 ⟨z, hz'.2, rfl⟩
         exact (PMF.mem_support_iff ..).mp hs (clear _ _ hz'.1 hj)
       _ ≤ J.toOuterMeasure badK + J.toOuterMeasure badN := measure_union_le _ _
       _ = _ := by
         change J.toOuterMeasure (Prod.snd ⁻¹' _) + J.toOuterMeasure (Prod.fst ⁻¹' _) = _
         rw [← PMF.toOuterMeasure_map_apply, ← PMF.toOuterMeasure_map_apply, hn, hk,
           ← K.toMeasure_apply_eq_toOuterMeasure_apply MeasurableSet.of_discrete,
           ← N.toMeasure_apply_eq_toOuterMeasure_apply MeasurableSet.of_discrete]
         simp [K, N]

/-- Lemma 4.3b's count coupling and explicit failure bound. The joint distribution across
bins is the independent product of the exhibited couplings. -/
theorem poisson_bins_failure {r : ℕ} (a : Fin r → ℝ≥0) {A θ : ℝ} (hA : 0 < A)
    (ha : ∀ c, 0 < (a c : ℝ)) (haA : ∀ c, (a c : ℝ) ≤ A) (hθ : 0 < θ)
    {m : ℕ} (hm : m = ⌊A/(4*θ) - 1/2⌋₊) (hm₁ : 1 ≤ m) :
    let b (c : Fin r) : ℝ≥0 := ⟨θ*(a c : ℝ)^2/A, by positivity⟩
    ∃ J : Fin r → PMF (ℕ × ℕ),
      (∀ c, (J c).map Prod.fst = (poissonMeasure (a c)).toPMF ∧
        (J c).map Prod.snd = (poissonMeasure (b c)).toPMF) ∧
      (piFin J).toOuterMeasure {z | ∃ c, (z c).1 / 2 < (z c).2} ≤ ENNReal.ofReal
        ((∑ c, (b c : ℝ)) * (Real.exp (3/2) * (4*Real.exp 1*θ^2)^m / (m+1)) +
         (∑ c, (a c : ℝ)) * (Real.exp 2 * (2*Real.exp 1*θ)^(2*m+1) / (2*m+2))) := by
  intro b
  choose J hN hK htail using fun c ↦ poisson_pair_coupling (a c) (ha c) (haA c) hθ hm hm₁
  refine ⟨J, fun c ↦ ⟨hN c, hK c⟩, ?_⟩
  let bad : Set (ℕ × ℕ) := {z | z.1 / 2 < z.2}
  have h₁ : {k : ℕ | m < k} = Set.Ici (m+1) := by ext k; simp
  have h₂ : {n : ℕ | m < n / 2} = Set.Ici (2*m+2) := by ext n; simp; omega
  have prob (x : ℝ≥0) (t : ℕ) :
      poissonMeasure x (Set.Ici t) = ENNReal.ofReal (poissonTail x t) := by
    rw [poissonTail_eq, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hcut : A ≤ 4*θ*((m : ℝ)+1+1/2) := by
    have hh : A/(4*θ) - 1/2 < (m : ℝ)+1 := hm ▸ Nat.lt_floor_add_one _
    have hh' := (div_lt_iff₀ (show 0 < 4*θ by positivity)).mp
      (show A/(4*θ) < (m : ℝ)+1+1/2 by linarith)
    linarith
  have hbA (c) : (b c : ℝ) ≤ θ*A := by
    change θ*(a c : ℝ)^2/A ≤ θ*A
    rw [div_le_iff₀ hA]
    nlinarith [mul_nonneg hθ.le (mul_nonneg (sub_nonneg.mpr (haA c))
      (add_nonneg hA.le (ha c).le))]
  have tails_nn (x : ℝ≥0) (t : ℕ) : 0 ≤ poissonTail x t := by
    rw [poissonTail_eq]; exact measureReal_nonneg
  calc _ = (piFin J).toOuterMeasure (⋃ c, (fun z ↦ z c) ⁻¹' bad) := by
             congr 1; ext; simp [bad]
       _ ≤ ∑ c, (piFin J).toOuterMeasure ((fun z ↦ z c) ⁻¹' bad) := measure_iUnion_fintype_le _ _
       _ ≤ ∑ c, ENNReal.ofReal (poissonTail (b c) (m+1) + poissonTail (a c) (2*m+2)) := by
             apply Finset.sum_le_sum
             intro c _
             rw [← PMF.toOuterMeasure_map_apply, piFin_map_eval,
               ENNReal.ofReal_add (tails_nn ..) (tails_nn ..)]
             rw [← prob (b c), ← prob (a c), ← h₁, ← h₂]
             exact htail c
       _ ≤ _ := by
             rw [← ENNReal.ofReal_sum_of_nonneg (fun c _ ↦ add_nonneg (tails_nn ..) (tails_nn ..))]
             exact ENNReal.ofReal_le_ofReal (sum_poissonTails_explicit Finset.univ
               (fun c ↦ (a c : ℝ)) (fun c ↦ (b c : ℝ)) hA.le hθ.le (fun c _ ↦ (ha c).le)
               (fun c _ ↦ (b c).property) (fun c _ ↦ haA c) (fun c _ ↦ hbA c) m hcut)

end SigabaNeo.Wall1.ADRS

#print axioms SigabaNeo.Wall1.ADRS.exists_ordered_cells_coupling
#print axioms SigabaNeo.Wall1.ADRS.poisson_pair_coupling
#print axioms SigabaNeo.Wall1.ADRS.poisson_bins_failure
