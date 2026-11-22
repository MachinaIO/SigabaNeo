module

public import SigabaNeo.Lib.Lattices.Research.Wall1.AdrsHistory
public import SigabaNeo.Lib.Lattices.Research.Wall1.AdrsCosetLaw
import Mathlib.Tactic

/-! # One Poissonized combiner step with independent within-bin averages -/

@[expose] public section

noncomputable section

namespace SigabaNeo.Wall1.ADRS

open Cslib.Probability.PMF ProbabilityTheory MeasureTheory ZLattice
open scoped ENNReal NNReal

variable {C V W : Type*} {r : ℕ}

/-- All pair slots, labelled by the coset from which the two endpoints came. -/
def halfBag [Fintype C] [DecidableEq C] (s : Multiset C) : Multiset C :=
  countsBag fun c ↦ s.count c / 2

theorem halfBag_mono [Fintype C] [DecidableEq C] : Monotone (halfBag (C := C)) := by
  intro s t h
  apply Multiset.le_iff_count.mpr
  intro c
  simp only [halfBag, count_countsBag]
  exact Nat.div_le_div_right (Multiset.le_iff_count.mp h c)

/-- Value-oblivious maximal pairing at the level of independent within-bin marks. -/
def maximalMarks [Fintype C] [DecidableEq C] (M : C → PMF W) (s : Multiset C) :=
  mark M (halfBag s)

theorem maximalMarks_mono [Fintype C] [DecidableEq C] (M : C → PMF W) (s t : Multiset C) :
    ∃ J : PMF (Multiset W × Multiset W), J.map Prod.fst = maximalMarks M s ∧
      J.map Prod.snd = maximalMarks M t ∧ (s ≤ t → ∀ z ∈ J.support, z.1 ≤ z.2) := by
  obtain ⟨J,h₁,h₂,ho⟩ := mark_submultiset_coupling M (halfBag s) (halfBag t)
  exact ⟨J,h₁,h₂,fun h ↦ ho (halfBag_mono h)⟩

theorem piFin_map_values (p : Fin r → PMF V) (f : V → W) :
    (piFin p).map (fun x i ↦ f (x i)) = piFin (fun i ↦ (p i).map f) := by
  induction r with
  | zero =>
    simp only [piFin, PMF.pure_map]
    congr 1
    funext i; exact i.elim0
  | succ r ih =>
    simp only [piFin, PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def, ← ih]
    congr 1
    funext a
    congr 1
    funext x i
    exact Fin.cases rfl (fun _ ↦ rfl) i

/-- Lift a joint count law to whole lists. Excess ideal slots get fresh phantom marks. -/
theorem counts_domination {T : Type*} (P : PMF T) (k n : T → Fin r → ℕ)
    (M : Fin r → PMF V) (ε : ℝ≥0∞) (h : P.toOuterMeasure {t | ∃ c, n t c < k t c} ≤ ε) :
    Dominated (P.bind fun t ↦ mark M (countsBag (k t)))
      (P.bind fun t ↦ mark M (countsBag (n t))) ε := by
  choose J h₁ h₂ horder using fun t ↦ mark_submultiset_coupling M (countsBag (k t)) (countsBag (n t))
  refine ⟨P.bind J, by simp [PMF.map_bind, h₁], by simp [PMF.map_bind, h₂], ?_⟩
  apply le_trans (toOuterMeasure_bind_le_add P J {t | ∃ c, n t c < k t c} _ 0 ?_)
  · simpa using h
  · intro t _ ht
    rw [le_zero_iff, PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
    have ho : countsBag (k t) ≤ countsBag (n t) := by
      apply Multiset.le_iff_count.mpr
      simpa only [count_countsBag] using fun c ↦ Nat.le_of_not_gt (fun h ↦ ht ⟨c,h⟩)
    exact fun v hv hb ↦ hb (horder t ho v hv)

/-- Expected output size, with A equal to the largest input-bin intensity. -/
def nextRate (rate : ℝ≥0) (q : PMF (Fin r)) (θ A : ℝ≥0) : ℝ≥0 :=
  θ * rate^2 * (collisionMass q).toNNReal / A

/-- The explicit sum-of-tails upper bound from Lemma 4.3b(3). -/
def stepError (rate outRate θ : ℝ≥0) (m : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((outRate : ℝ) * (Real.exp (3/2) * (4*Real.exp 1*(θ:ℝ)^2)^m / (m+1)) +
    (rate : ℝ) * (Real.exp 2 * (2*Real.exp 1*θ)^(2*m+1) / (2*m+2)))

/-- Lemma 4.3b(2), for arbitrary marks attached to disjoint within-bin pairs. Both the
clipped selection and the maximal pairing dominate the exact ideal Poisson list. -/
theorem poisson_selected_marks (rate θ A : ℝ≥0) (q : PMF (Fin r)) (M : Fin r → PMF V)
    (hratePos : 0 < rate) (hθ : 0 < θ) (hA : 0 < A) (hq : ∀ c, q c ≠ 0)
    (hmax : ∀ c, rate * (q c).toNNReal ≤ A) {m : ℕ}
    (hm : m = ⌊(A:ℝ)/(4*θ) - 1/2⌋₊) (hm₁ : 1 ≤ m) :
    let a := fun c ↦ rate * (q c).toNNReal
    let outRate := nextRate rate q θ A
    let b := fun c ↦ outRate * (squaredLabels q c).toNNReal
    let ideal := poissonList outRate ((squaredLabels q).bind M)
    ∃ J : Fin r → PMF (ℕ × ℕ),
      (∀ c, (J c).map Prod.fst = (poissonMeasure (a c)).toPMF ∧
        (J c).map Prod.snd = (poissonMeasure (b c)).toPMF) ∧
      (piFin J).toOuterMeasure {z | ∃ c, (z c).1 / 2 < (z c).2} ≤ stepError rate outRate θ m ∧
      Dominated ideal ((piFin J).bind fun z ↦ mark M (countsBag fun c ↦ min (z c).2 ((z c).1/2)))
        (stepError rate outRate θ m) ∧
      Dominated ideal ((poissonList rate q).bind (maximalMarks M)) (stepError rate outRate θ m) := by
  intro a outRate b ideal
  have hpos (c) : 0 < (a c : ℝ) :=
    mul_pos hratePos (ENNReal.toReal_pos (hq c) (PMF.apply_ne_top _ _))
  have hrate (c) : (b c : ℝ) = θ*(a c : ℝ)^2/A := by
    have hc := (ENNReal.toReal_pos (collisionMass_ne_zero q) (collisionMass_ne_top q)).ne'
    simp only [b, outRate, nextRate, a, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_pow,
      ENNReal.coe_toNNReal_eq_toReal, squaredLabels_apply, ENNReal.toReal_div, ENNReal.toReal_pow]
    field_simp [hc]
  obtain ⟨J,hJ,hbad⟩ := poisson_bins_failure a (A := (A : ℝ)) (θ := (θ : ℝ)) hA hpos
    (fun c ↦ by exact_mod_cast hmax c) hθ hm hm₁
  have hbin (c) : (⟨(θ:ℝ)*(a c : ℝ)^2/A, by positivity⟩ : ℝ≥0) = b c := NNReal.eq (hrate c).symm
  simp only [hbin] at hJ hbad
  have sum_rate (t : ℝ≥0) (p : PMF (Fin r)) : ∑ c, (t : ℝ) * (p c).toReal = t := by
    rw [← Finset.mul_sum, ← ENNReal.toReal_sum (fun c _ ↦ PMF.apply_ne_top p c),
      show (∑ c, p c) = 1 from (tsum_fintype _).symm.trans p.tsum_coe, ENNReal.toReal_one, mul_one]
  change _ ≤ ENNReal.ofReal ((∑ c, (outRate:ℝ) * (squaredLabels q c).toReal) * _ +
    (∑ c, (rate:ℝ) * (q c).toReal) * _) at hbad
  rw [sum_rate, sum_rate] at hbad
  have hi : (piFin J).bind (fun z ↦ mark M (countsBag fun c ↦ (z c).2)) = ideal := by
    dsimp only [ideal]
    rw [← poisson_marked_bins outRate (squaredLabels q) M]
    rw [← show (piFin J).map (fun z c ↦ (z c).2) = _ from
      (piFin_map_values J Prod.snd).trans (congrArg piFin (funext fun c ↦ (hJ c).2))]
    rw [PMF.bind_map]; rfl
  have ha : (piFin J).bind (fun z ↦ mark M (countsBag fun c ↦ (z c).1/2)) =
      (poissonList rate q).bind (maximalMarks M) := by
    have hcounts := poisson_split_bins rate q
    have hfst := (piFin_map_values J Prod.fst).trans (congrArg piFin (funext fun c ↦ (hJ c).1))
    have hstep (k : Fin r → ℕ) :
        maximalMarks M (countsBag k) = mark M (countsBag fun c ↦ k c/2) := by
      simp [maximalMarks, halfBag]
    have hp : (piFin J).bind (fun z ↦ mark M (countsBag fun c ↦ (z c).1/2)) =
        ((piFin J).map (fun z c ↦ (z c).1)).bind (fun k ↦ maximalMarks M (countsBag k)) := by
      simp only [PMF.bind_map, Function.comp_def, hstep]
    rw [hp]
    rw [hfst, ← hcounts, PMF.bind_bind]
    simp only [PMF.bind_map, Function.comp_def, countsBag_binCounts, poissonList, PMF.bind_bind,
      tupleBag]
  refine ⟨J,hJ,hbad,?_,?_⟩
  · rw [← hi]
    apply counts_domination
    simpa only [stepError, min_lt_iff, lt_self_iff_false, false_or] using hbad
  · rw [← hi, ← ha]
    exact counts_domination _ _ _ _ _ hbad

end SigabaNeo.Wall1.ADRS

#print axioms SigabaNeo.Wall1.ADRS.poisson_selected_marks
