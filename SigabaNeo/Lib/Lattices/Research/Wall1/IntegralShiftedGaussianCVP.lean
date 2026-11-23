module

public import SigabaNeo.Lib.Lattices.Research.Wall1.IntegralMidpointMass
public import SigabaNeo.Lib.Lattices.Research.Wall1.ShiftedGaussianSchedule
import all SigabaNeo.Lib.Lattices.Research.Wall1.AdrsMidpoint
import Mathlib.Tactic

/-! Exact closest-point correctness of the fixed-width shifted mathematical sampler
on an integer-coordinate lattice. Input sampler accuracy is stated as a one-draw
coupling. An empty final list counts as a failure and any closest point is accepted. -/

@[expose] public section
noncomputable section
namespace SigabaNeo.Wall1.CVP638

open SigabaNeo.SampleDeletion SigabaNeo.Wall1.ADRS ProbabilityTheory ZLattice Cslib.Probability.PMF
open scoped ENNReal NNReal

set_option exponentiation.threshold 1200

private theorem step_variance (s : ℝ) (h : s^2 = variance 0) (j : ℕ) :
    (stepWidth s j)^2 = variance j := by
  induction j with
  | zero => exact h
  | succ j ih =>
    rw [stepWidth, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), ih]
    unfold variance
    rw [pow_succ (2:ℝ), div_div]

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
variable (L : Submodule ℤ E) (b : Module.Basis ι ℤ L) (e : (ι → ZMod 2) ≃ Fin (2^638))
variable [FiniteDimensional ℝ E] [DiscreteTopology L] {s : ℝ} (hs : 0 < s) (t : E)

/-- A faithful additive realization of the lattice and the squared residual norm in
integer coordinates. Only the target needs to admit the given integral shift. -/
structure IntegralCoordinates where
  coordinates : L →+ (Fin 638 → ℤ)
  injective : Function.Injective coordinates
  shift : Fin 638 → ℤ
  distance_sq : ∀ x : L, ‖(x:E)-t‖^2 = normSq (coordinates x - shift)

variable (I : IntegralCoordinates L t)

def residualCoords (x : L) := I.coordinates x - I.shift

private theorem terminal_ratio (hscale : s^2 = variance 0) (x₀ : L)
    (hmin : ∀ x, normSq (residualCoords L t I x₀) ≤ normSq (residualCoords L t I x)) :
    let w := stepWidth s 36
    let hw := stepWidth_pos hs 36
    let q := labelLaw L b hw t e
    (peakProb q:ℝ) ≤ 16/15 * ((discreteGaussian L w hw t).toOuterMeasure {x₀}).toReal := by
  classical
  intro w hw q
  let V := discreteGaussian L w hw t
  let c := peak q
  let key := binLabel L b e
  let F := {x : L // key x = c}
  let f (x : F) := residualCoords L t I x.val
  let C := Set.range f
  let D := normSq (residualCoords L t I x₀)
  let u := Real.exp (-(Real.pi / variance levels))
  have weight (x : L) : gaussianWeight w ((x:E)-t) = u^normSq (residualCoords L t I x) := by
    rw [gaussianWeight, I.distance_sq, step_variance s hscale]
    unfold u
    rw [← Real.exp_nat_mul]
    congr 1
    change -Real.pi * (normSq (residualCoords L t I x):ℝ) / variance levels =
      normSq (residualCoords L t I x) * -(Real.pi / variance levels)
    ring
  have inj : Function.Injective f := by
    intro x y h
    exact Subtype.ext (I.injective (sub_left_injective (b := I.shift) h))
  have hmid : ∀ x ∈ C, ∀ y ∈ C, ∃ h : Fin 638 → ℤ, (∀ i, y i = x i + 2*h i) ∧
      D ≤ normSq (fun i ↦ x i + h i) := by
    rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩
    have hm : (x.val,y.val) ∈ parityMatch L b := e.injective (x.property.trans y.property.symm)
    rw [← endpoints_range] at hm
    obtain ⟨⟨a,v⟩,he⟩ := hm
    have hx : a+v = x.val := congrArg Prod.fst he
    have hy : a-v = y.val := congrArg Prod.snd he
    refine ⟨-I.coordinates v, ?_, ?_⟩
    · intro i
      simp only [f, residualCoords, ← hx, ← hy, map_sub, map_add, Pi.sub_apply, Pi.add_apply, Pi.neg_apply]
      ring
    · convert hmin a using 2
      funext i
      simp only [f, residualCoords, ← hx, map_add, Pi.sub_apply, Pi.add_apply, Pi.neg_apply]
      ring
  have hmass := terminal_parity_mass C D hmid
  have hkernel : q c = ∑' x : F, V x.val := by
    change (V.map key) c = _
    rw [PMF.map_apply]
    trans ∑' x : L, {a : L | key a = c}.indicator (fun a ↦ V a) x
    swap
    · exact (tsum_subtype {a : L | key a = c} (fun a ↦ V a)).symm
    apply tsum_congr
    intro x
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    simp [eq_comm]
  change (q c).toReal ≤ _
  rw [hkernel, ENNReal.tsum_toReal_eq (fun x ↦ PMF.apply_ne_top _ _),
    PMF.toOuterMeasure_apply_singleton]
  simp only [V, discreteGaussian_apply_toReal, weight, tsum_div_const]
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (gaussianMass_pos L _ hw t).le
  have heq := (Equiv.ofInjective f inj).tsum_eq (fun z : C ↦ u^normSq z.val)
  change (∑' x : F, u^normSq (f x)) = _ at heq
  exact heq.le.trans (hmass.trans_eq (mul_comm ..))

private theorem least_of_bag_hit {V : Type*} (items : SampleList V) (energy : V → ℕ)
    {z : V} (hz : z ∈ sampleBag items) :
    ∃ best, (List.ofFn items.2).minOn? energy = some best ∧ energy best ≤ energy z := by
  have hm : z ∈ List.ofFn items.2 := by
    simpa [sampleBag, tupleBag, List.mem_ofFn] using hz
  exact ⟨_, List.minOn?_eq_some_minOn (List.ne_nil_of_mem hm), List.apply_minOn_le_of_mem hm⟩

/-- Pair using the fixed input order, then return the first least-energy point or none. -/
def selectMinimum {n : ℕ} (v : Fin n → L) : Option L :=
  let out := (stablePair (binLabel L b e) (latticeMidpoint L))^[36] ⟨n,v⟩
  (List.ofFn out.2).minOn? (fun x ↦ normSq (residualCoords L t I x))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 12000 in
/-- A single call returns a Euclidean closest point except with probability < 2^-168.
The finite-precision coupling is the Part 141, Lemma 8 hypothesis on one draw. -/
theorem closest_point_failure (hscale : s^2 = variance 0) (P : PMF L)
    (initial_sampler : ∃ J : PMF (L × L), J.map Prod.fst = P ∧
      J.map Prod.snd = discreteGaussian L s hs t ∧
      J.toOuterMeasure {z | z.1 ≠ z.2} ≤ ENNReal.ofReal (1/(2:ℝ)^923)) :
    (iid P sampleCount).toOuterMeasure {v | ¬ ∃ x : L, selectMinimum L b e t I v = some x ∧
      ∀ y : L, ‖(x:E)-t‖ ≤ ‖(y:E)-t‖} < ENNReal.ofReal (1/(2:ℝ)^168) := by
  classical
  let energy (x : L) := normSq (residualCoords L t I x)
  have hex : ∃ n, ∃ x : L, energy x = n := ⟨_,0,rfl⟩
  obtain ⟨x₀,hx₀⟩ := Nat.find_spec hex
  have hmin (y : L) : energy x₀ ≤ energy y := by
    rw [hx₀]
    exact Nat.find_min' hex (show ∃ x : L, energy x = energy y from ⟨y,rfl⟩)
  have hr := scheduled_miss L b e hs t P {x₀} initial_sampler
    (terminal_ratio L b e hs t I hscale x₀ hmin)
  apply lt_of_le_of_lt ((iid P sampleCount).toOuterMeasure.mono ?_) hr
  intro v hbad z hz hopt
  have eqOpt : z = x₀ := hopt
  rw [eqOpt] at hz
  let out := (stablePair (binLabel L b e) (latticeMidpoint L))^[36] ⟨sampleCount,v⟩
  change x₀ ∈ sampleBag out at hz
  obtain ⟨best,hbest,hle⟩ := least_of_bag_hit out energy hz
  apply hbad
  refine ⟨best,hbest,fun y ↦ ?_⟩
  have best_le : energy best ≤ energy y := hle.trans (hmin y)
  have hd : ‖(best:E)-t‖^2 ≤ ‖(y:E)-t‖^2 := by
    rw [I.distance_sq, I.distance_sq]
    exact_mod_cast best_le
  nlinarith only [hd, norm_nonneg ((best:E)-t), norm_nonneg ((y:E)-t)]

end SigabaNeo.Wall1.CVP638

#print axioms SigabaNeo.Wall1.CVP638.closest_point_failure
