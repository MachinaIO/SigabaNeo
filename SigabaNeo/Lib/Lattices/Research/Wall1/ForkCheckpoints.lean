module

public import SigabaNeo.Lib.Lattices.Research.Wall1.AttackLattice
public import SigabaNeo.Lib.Lattices.Research.Wall1.PlantAveragingNecessity
import all SigabaNeo.Lib.Lattices.Research.Wall1.PlantAveragingNecessity
import all SigabaNeo.Lib.Lattices.Research.Wall1.ConditionalReduction
import all SigabaNeo.Lib.Lattices.Research.Wall1.UniquenessProbability
import all SigabaNeo.Lib.Lattices.Research.Wall1.CBDTail
import Mathlib.Tactic

/-! # Plant-free checkpoints (Part 135, audited Proposition 2.3 and Theorems 4.4–4.5)

A single design includes all coins of the null run. Every look uses the same independent
CBD plant. Verification can stop the run early, but the full list of potential looks is
determined by the design. All numerical bounds on the null trajectory are left open. -/

public section
namespace SigabaNeo.Wall1.ForkCheckpoints

open AttackLattice DecoupledDecoder RestartLift BabaiLift SampleDeletion CBDTail CBDQuadratic
open Classical
open scoped NNReal

variable {D O : Type*} {N n r q d K : ℕ}

abbrev Plant (N : ℕ) := Fin N → Digit 3
abbrev Rows (r n q : ℕ) := Fin r → Fin n → ZMod q

/-- Probability mass of an event on a finite sample space. -/
noncomputable def mass {S : Type*} [Fintype S] (w : S → ℝ) (E : S → Prop) : ℝ :=
  ∑ s with E s, w s

/-- The observation law tested against any output event, sampling a design and then a witness
for the right-hand side. Both the observed right-hand side and the coins are present in the input. -/
noncomputable def outputLaw [Fintype D] {S B : Type*} [Fintype S] (μ : D → ℝ) (ν : S → ℝ)
    (rhs : D → S → B) (stat : D × B → O) (E : O → Prop) : ℝ :=
  ∑ a, μ a * mass ν (fun s ↦ E (stat (a, rhs a s)))

/-- Proposition 2.3. Equality of the whole output laws, hence also of the rejection mass for
any rejection event. The design can encode correlated matrix/coin data with arbitrary weights. -/
theorem planted_null_outputLaw [Fintype D] [NeZero q] {C : Type*} (μ : D → ℝ)
    (A : D → Rows r n q) (coins : D → C) (σ : Fin N ≃ Fin n ⊕ Fin r)
    (reduce : AddSubgroup (EuclideanSpace ℝ (Fin N)) → C → O) :
    let stat := fun p : D × (Fin r → ZMod q) ↦ reduce (nullLattice (A p.1) σ) (coins p.1)
    outputLaw μ jointWeight (fun a (x : Plant N) ↦ residue (A a) σ (fun c ↦ centered (x c))) stat =
      outputLaw μ (fun _ : Fin r → ZMod q ↦ (Fintype.card (Fin r → ZMod q) : ℝ)⁻¹)
        (fun _ b ↦ b) stat := by
  intro stat
  funext E
  apply Finset.sum_congr rfl
  intro a _
  by_cases he : E (reduce (nullLattice (A a) σ) (coins a))
  · simp [stat, mass, he, joint_mass, Finset.card_univ]
  · simp [stat, mass, he]

private theorem plant_nonneg (x : Plant N) : 0 ≤ jointWeight x := by
  unfold jointWeight weight
  positivity

private theorem mass_mono {E F : Plant N → Prop} (h : ∀ x, E x → F x) :
    mass jointWeight E ≤ mass jointWeight F := by
  unfold mass
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun x hx ↦
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, h x (Finset.mem_filter.mp hx).2⟩)
    fun x _ _ ↦ plant_nonneg x

private theorem mass_le_one (E : Plant N → Prop) : mass jointWeight E ≤ 1 := by
  simpa [mass, joint_mass] using mass_mono (F := fun _ ↦ True) (fun x (_ : E x) ↦ trivial)

private theorem mass_or_le (E F : Plant N → Prop) :
    mass jointWeight (fun x ↦ E x ∨ F x) ≤ mass jointWeight E + mass jointWeight F := by
  simp only [mass, Finset.sum_filter, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun x _ ↦ by
    by_cases he : E x <;> by_cases hf : F x <;> simp [he, hf, plant_nonneg]

/-- Independent design and plant. The same plant is shared by all checkpoints. -/
noncomputable def joint [Fintype D] (μ : D → ℝ) (E : D → Plant N → Prop) : ℝ :=
  ∑ a, μ a * mass jointWeight (E a)

/-- Data at a checkpoint on the null trajectory. -/
structure Checkpoint (N d : ℕ) where
  block : FinalBlock N d
  pre : PrefixData N
  length : ℕ

def Checkpoint.Good (c : Checkpoint N d) (g L gp : ℝ) : Prop :=
  c.block.Good g L ∧ ∀ m < c.length, gp ≤ ‖c.pre.bs m‖

/-- An exact check against the image of the bounded integer box in the observed coset. -/
def Verified (A : Rows r n q) (σ : Fin N ≃ Fin n ⊕ Fin r) (b : Fin r → ZMod q)
    (v : Amb N) : Prop :=
  ∃ y : Plant N, v = plantVec y ∧ residue A σ (fun c ↦ centered (y c)) = b

abbrev observedRhs (A : Rows r n q) (σ : Fin N ≃ Fin n ⊕ Fin r) (x : Plant N) :=
  residue A σ (fun c ↦ centered (x c))

/-- An admissible vector other than the true one passes the same exact check. -/
def Collision (A : Rows r n q) (σ : Fin N ≃ Fin n ⊕ Fin r) (x : Plant N) : Prop :=
  ∃ v, Verified A σ (observedRhs A σ x) v ∧ v ≠ plantVec x

/-- First verified output in chronological order, including the empty-checkpoint case. -/
noncomputable def firstVerified {V : Type*} (v : Fin K → V) (ok : V → Prop) : Option V :=
  let hits := Finset.univ.filter fun i ↦ ok (v i)
  if h : hits.Nonempty then some (v (hits.min' h)) else none

private theorem firstVerified_correct {V : Type*} (v : Fin K → V) (ok : V → Prop) (u : V)
    (hu : ok u) (only : ∀ z, ok z → z = u) {i : Fin K} (hi : v i = u) :
    firstVerified v ok = some u := by
  unfold firstVerified
  have h : (Finset.univ.filter fun j ↦ ok (v j)).Nonempty := ⟨i, by simp [hi, hu]⟩
  rw [dite_eq_left h, only _ (Finset.mem_filter.mp (Finset.min'_mem _ h)).2]

abbrev SVP (N : ℕ) := Set (Amb N) → Amb N
abbrev Lift (N : ℕ) := (Amb N → Amb N) → Set (Amb N) → Amb N → Amb N

/-- Observable decoder output at one checkpoint, before exact verification. -/
noncomputable def attempt (c : Checkpoint N d) (svp : SVP N) (lift : Lift N)
    (A : Rows r n q) (σ : Fin N ≃ Fin n ⊕ Fin r) (b : Fin r → ZMod q) : Amb N :=
  decode svp lift c.pre c.length (attackLattice A σ b)

private theorem attempt_error (c : Checkpoint N d) (A : Rows r n q) (σ : Fin N ≃ Fin n ⊕ Fin r)
    {svp : SVP N} {lift : Lift N} (hs : SVPOracle svp) (hl : LiftOracle lift)
    {g L gp : ℝ} (hg : 0 < g) (hL : 0 ≤ L) (hgp : 0 ≤ gp)
    (gap : 0 < L^2 - 1 - (3/2)*(d : ℝ)) (good : c.Good g L gp)
    (compat : Compatible (nullLattice₀ A σ) c.pre c.length c.block) :
    mass jointWeight (fun x ↦ attempt c svp lift A σ (observedRhs A σ x) ≠ plantVec x) ≤
      reductionError N d g L + ∑ _m ∈ Finset.range c.length, 2 * Real.exp (-gp^2/12) := by
  let B := c.block
  let unq := fun x ↦ allHeightsUnique (horizontalLattice B.V B.basis) (projectedCBD B.Q x)
  let bad := fun x ↦ LiftFail c.pre.b c.pre.bs c.length (plantVec x)
  have hu := uniquenessProbability _ B.symmetric B.idempotent B.trace_eq _ B.fixed _
    hg good.1.1 hL good.1.2 gap
  have hfail : mass jointWeight (fun x ↦ ¬ unq x) ≤ reductionError N d g L := by
    have hp := B.failure_add_success
    have bound : 1 - reductionError N d g L ≤ B.success := by
      simpa only [FinalBlock.success, reductionError, B] using hu
    have hm : mass jointWeight (fun x ↦ ¬ unq x) = B.failure := by
      simp only [mass, FinalBlock.failure, unq]
    linarith
  refine (mass_mono (F := fun x ↦ ¬ unq x ∨ bad x) ?_).trans
    ((mass_or_le _ _).trans (add_le_add hfail
      (prefix_liftFail_le c.pre c.length (fun _ ↦ gp) (fun _ _ ↦ hgp) good.2)))
  intro x hf
  by_contra! h
  apply hf
  rw [attempt, observedRhs, attackLattice_plantVec]
  exact decode_eq compat hs hl x h.1 h.2

/-- Theorem 4.4. The first good index depends only on the design and coins. A verified
answer at any earlier look is correct outside the single global collision event. -/
theorem fork_failure_le [Fintype D] (μ : D → ℝ) (hμ : ∀ a, 0 ≤ μ a) (h1 : ∑ a, μ a = 1)
    (A : D → Rows r n q) (σ : Fin N ≃ Fin n ⊕ Fin r) (run : D → Fin K → Checkpoint N d)
    {svp : SVP N} {lift : Lift N} (hs : SVPOracle svp) (hl : LiftOracle lift)
    {g L gp εlift : ℝ} (hg : 0 < g) (hL : 0 ≤ L) (hgp : 0 ≤ gp) (he : 0 ≤ εlift)
    (gap : 0 < L^2 - 1 - (3/2)*(d : ℝ))
    (compat : ∀ a i, (run a i).Good g L gp →
      Compatible (nullLattice₀ (A a) σ) (run a i).pre (run a i).length (run a i).block)
    (liftBound : ∀ a i, (run a i).Good g L gp →
      (∑ _m ∈ Finset.range (run a i).length, 2 * Real.exp (-gp^2/12)) ≤ εlift) :
    joint μ (fun a x ↦
      let b := observedRhs (A a) σ x
      firstVerified (fun i ↦ attempt (run a i) svp lift (A a) σ b) (Verified (A a) σ b) ≠
        some (plantVec x)) ≤
      mass μ (fun a ↦ ∀ i, ¬ (run a i).Good g L gp) + reductionError N d g L + εlift +
        joint μ (fun a x ↦ Collision (A a) σ x) := by
  let noneGood := fun a ↦ ∀ i, ¬ (run a i).Good g L gp
  let err := reductionError N d g L + εlift
  have herr : 0 ≤ err := add_nonneg (RestartReduction.reductionError_nonneg hg) he
  change _ ≤ mass μ noneGood + reductionError N d g L + εlift + _
  have total : (∑ a, μ a * ((if noneGood a then 1 else 0) + err +
      mass jointWeight (Collision (A a) σ))) =
      mass μ noneGood + reductionError N d g L + εlift + joint μ (fun a x ↦ Collision (A a) σ x) := by
    simp only [joint, mass, Finset.sum_filter, err, mul_add, mul_ite, mul_one, mul_zero,
      Finset.sum_add_distrib, ← Finset.sum_mul, h1, one_mul, add_assoc]
    congr 1
    exact Finset.sum_congr rfl fun a _ ↦ by by_cases h : noneGood a <;> simp [h]
  rw [← total]
  apply Finset.sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_left _ (hμ a)
  by_cases hn : noneGood a
  · rw [ite_eq_left hn]
    exact (mass_le_one _).trans (by
      have hc : 0 ≤ mass jointWeight (Collision (A a) σ) := Finset.sum_nonneg fun x _ ↦ plant_nonneg x
      linarith)
  rw [ite_eq_right hn, zero_add]
  let s := Finset.univ.filter fun i ↦ (run a i).Good g L gp
  have hex : ∃ i, (run a i).Good g L gp := by simpa [noneGood] using hn
  have hne : s.Nonempty := by obtain ⟨i, hi⟩ := hex; exact ⟨i, by simp [s, hi]⟩
  let i := s.min' hne
  have hi := (Finset.mem_filter.mp (s.min'_mem hne)).2
  let miss := fun x ↦ attempt (run a i) svp lift (A a) σ (observedRhs (A a) σ x) ≠ plantVec x
  refine (mass_mono (F := fun x ↦ miss x ∨ Collision (A a) σ x) ?_).trans
    ((mass_or_le _ _).trans (add_le_add_left
      ((attempt_error _ _ _ hs hl hg hL hgp gap hi (compat a i hi)).trans
        (add_le_add_right (liftBound a i hi) _)) _))
  intro x hf
  by_contra! h
  apply hf
  apply firstVerified_correct _ _ _ ⟨x, rfl, rfl⟩ _ (not_ne_iff.mp h.1)
  exact fun z hz ↦ by_contra fun hne ↦ h.2 ⟨z, hz, hne⟩

/-- The projected lattice, with horizontal part H and the projected plant at height one. -/
noncomputable def lookLattice (B : FinalBlock N d) (x : Plant N) : AddSubgroup (Amb N) :=
  decoupled ((horizontalLattice B.V B.basis).map (horiz N).toAddMonoidHom)
    (snocE (projectedCBD B.Q x) 1)

/-- The audited success model for a look, including ties resolved in the plant's favor. -/
def Hit (B : FinalBlock N d) (x : Plant N) (v : Amb N) : Prop :=
  v = snocE (projectedCBD B.Q x) 1 ∨ v = -snocE (projectedCBD B.Q x) 1

private theorem hit_short {B : FinalBlock N d} {x : Plant N} {v : Amb N} {ℓ : ℝ}
    (hs : IsShortest (lookLattice B x) v) (hit : Hit B x v) (low : B.ShortVector (ℓ^2)) :
    1 + quadratic B.Q x ≤ ℓ^2 := by
  obtain ⟨h, hh, hn, hℓ⟩ := low
  have hmem : horiz N h.val ∈ lookLattice B x :=
    AddSubgroup.mem_sup_left ⟨h.val, ⟨h, hh, rfl⟩, rfl⟩
  have hne : horiz N h.val ≠ 0 := fun hz ↦
    hn (Subtype.ext (horiz_injective (hz.trans (map_zero (horiz N)).symm)))
  have hc := hs.2.2 _ hmem hne
  have hnorm : ‖v‖ = ‖snocE (projectedCBD B.Q x) 1‖ := by rcases hit with h | h <;> simp [h]
  rw [hnorm, horiz_apply] at hc
  have hsq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hc
  rw [norm_sq_snocE, norm_sq_snocE, projectedCBD_norm_sq _ B.symmetric B.idempotent] at hsq
  change ‖h.val‖ ^ 2 ≤ ℓ ^ 2 at hℓ
  linarith

private theorem mass_exists_le (E : Fin K → Plant N → Prop) :
    mass jointWeight (fun x ↦ ∃ i, E i x) ≤ ∑ i, mass jointWeight (E i) := by
  simp only [mass, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  by_cases h : ∃ i, E i x
  · rw [ite_eq_left h]
    obtain ⟨i, hi⟩ := h
    simpa [hi] using Finset.single_le_sum (f := fun i ↦ if E i x then jointWeight x else 0)
      (fun j _ ↦ by split <;> simp [plant_nonneg]) (Finset.mem_univ i)
  · simp [show ∀ i, ¬ E i x from fun i hi ↦ h ⟨i, hi⟩]

/-- Theorem 4.5. For a nonnegative radius, the low event is that *every* horizontal lattice
has a nonzero vector of length at most the radius. The per-look hypothesis concerns only
the lower tail of projected energy for a fixed null trajectory. -/
theorem fork_success_le [Fintype D] (μ : D → ℝ) (hμ : ∀ a, 0 ≤ μ a)
    (run : D → Fin K → FinalBlock N d) (out : D → Fin K → Plant N → Amb N)
    (shortest : ∀ a i x, IsShortest (lookLattice (run a i) x) (out a i x))
    (radius : ℝ≥0) (τ : ℝ≥0 → ℝ)
    (tail : ∀ a i, (run a i).ShortVector ((radius : ℝ)^2) →
      mass jointWeight (fun x ↦ 1 + quadratic (run a i).Q x ≤ (radius : ℝ)^2) ≤ τ radius) :
    let low := fun a ↦ ∀ i, (run a i).ShortVector ((radius : ℝ)^2)
    joint μ (fun a x ↦ ∃ i, Hit (run a i) x (out a i x)) ≤
      mass μ (fun a ↦ ¬ low a) + K * τ radius * mass μ low := by
  intro low
  rw [mul_comm _ (mass μ low)]
  unfold joint
  conv_rhs => simp only [mass, Finset.sum_filter, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  by_cases h : low a
  · simp only [h, not_true_eq_false, ite_false, ite_true, zero_add]
    apply mul_le_mul_of_nonneg_left _ (hμ a)
    apply (mass_exists_le _).trans
    calc
      _ ≤ ∑ _i : Fin K, τ radius := Finset.sum_le_sum fun i _ ↦
        (mass_mono fun x hit ↦ hit_short (shortest a i x) hit (h i)).trans (tail a i (h i))
      _ = _ := by simp
  · simp only [h, not_false_eq_true, ite_false, ite_true, zero_mul, add_zero]
    simpa using mul_le_mul_of_nonneg_left
      (mass_le_one (fun x ↦ ∃ i, Hit (run a i) x (out a i x))) (hμ a)

end SigabaNeo.Wall1.ForkCheckpoints

#print axioms SigabaNeo.Wall1.ForkCheckpoints.planted_null_outputLaw
#print axioms SigabaNeo.Wall1.ForkCheckpoints.fork_failure_le
#print axioms SigabaNeo.Wall1.ForkCheckpoints.fork_success_le
