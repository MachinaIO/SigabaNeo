import SigabaNeo.Trusted.Benchmark
import Cslib.Probability.PMF
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Pi

/-!
# Diversity of certified generators

What the diversity clause of `Benchmark.Certified` means, and lemmas to prove it. Counting is by
`Nat.card`; nothing enumerates the `2^k` seeds.

* **Counting interpretation.** For a uniform seed `R`, the probability that `gen d R` is the same
  problem as a given task is `|fiber| / 2^k ≤ 2^-h` (`Certified.uniform_sameProblem_le`); so is the
  probability of every class (`Certified.uniform_class_le`, min-entropy at least `h` modulo
  `SameProblem`), and the collision probability of two independent seeds
  (`Certified.uniform_collision_le`, `Certified.uniform_collision_le'`).
* **Injective modulo equivalence**: `h = k` (`certified_of_injective`).
* **Partial seed recovery**: if the same problem forces the same value of a map whose fibers have
  at most `2^(k-h)` seeds, the bound holds at `h` (`diversity_of_recovery`); for the first `h` seed
  bits (`diversity_of_prefix`, `certified_of_prefix`).
* **Bounded fiber**: a fiber that injects into a type of at most `2^(k-h)` elements
  (`diversity_of_injection`).
* **Constant generators**: a generator whose seeds all give the same problem at some level is not
  certified for `h > 0` (`not_certified_of_sameProblem`, `not_certified_const`).
* **Decision problems**: swapping real and ideal keeps every gain (`gain_decision_swap`), so the
  two are the same attack problem (`AttackAdapter.sameAttack_of_swap`).
-/

namespace SigabaNeo.Benchmark

open Cslib.Probability ENNReal

/-! ### Counting interpretation -/

section Uniform

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-- The uniform law of a set: its size over the size of the space. -/
theorem uniform_toOuterMeasure (S : Set Ω) :
    (PMF.uniformOfFintype Ω).toOuterMeasure S = (Nat.card S : ℝ≥0∞) / Fintype.card Ω := by
  classical
  rw [PMF.toOuterMeasure_apply, tsum_fintype]
  simp only [Set.indicator, PMF.uniformOfFintype_apply]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    div_eq_mul_inv]
  congr 2
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- A set with `2^h · |S| ≤ |Ω|` has uniform probability at most `2^-h`. -/
theorem uniform_le_of_card {S : Set Ω} {h : ℕ} (hS : 2 ^ h * Nat.card S ≤ Fintype.card Ω) :
    (PMF.uniformOfFintype Ω).toOuterMeasure S ≤ ((2 : ℝ≥0∞) ^ h)⁻¹ := by
  rw [uniform_toOuterMeasure, ENNReal.div_le_iff_le_mul (Or.inl (by exact_mod_cast
    Fintype.card_ne_zero)) (Or.inl (ENNReal.natCast_ne_top _))]
  have h0 : (2 : ℝ≥0∞) ^ h ≠ 0 := pow_ne_zero _ two_ne_zero
  have ht : (2 : ℝ≥0∞) ^ h ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  calc (Nat.card S : ℝ≥0∞) = ((2 : ℝ≥0∞) ^ h)⁻¹ * (2 ^ h * Nat.card S) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul]
    _ ≤ ((2 : ℝ≥0∞) ^ h)⁻¹ * Fintype.card Ω := by gcongr; exact_mod_cast hS

end Uniform

/-- The seeds that give the same problem as the seed `r` at level `d`. -/
abbrev fiber (F : Family) {L k : ℕ} (gen : Fin L → Seed k → F.Task) (d : Fin L) (r : Seed k) :
    Set (Seed k) :=
  {s | F.SameProblem (gen d r) (gen d s)}

theorem card_seed (k : ℕ) : Fintype.card (Seed k) = 2 ^ k := by simp

variable {F : Family} {L k h : ℕ} {gen : Fin L → Seed k → F.Task}

/-- The diversity clause of a certificate, for one level and seed. -/
theorem Certified.card_fiber (hc : Certified F L k h gen) (d : Fin L) (r : Seed k) :
    2 ^ h * Nat.card (fiber F gen d r) ≤ 2 ^ k :=
  hc.2.2.2 d r

/-- **Counting interpretation.** For a uniform seed, the probability that the task is the same
problem as the task of the seed `r` is at most `2^-h`. -/
theorem Certified.uniform_sameProblem_le (hc : Certified F L k h gen) (d : Fin L) (r : Seed k) :
    (PMF.uniformOfFintype (Seed k)).toOuterMeasure (fiber F gen d r) ≤ ((2 : ℝ≥0∞) ^ h)⁻¹ :=
  uniform_le_of_card (by rw [card_seed]; exact hc.card_fiber d r)

/-- **Min-entropy.** For a uniform seed, every class of tasks (the tasks that are the same
problem as `y`) has probability at most `2^-h`: a class with a seed in it is that seed's fiber. -/
theorem Certified.uniform_class_le (hc : Certified F L k h gen) (d : Fin L) (y : F.Task) :
    (PMF.uniformOfFintype (Seed k)).toOuterMeasure {s | F.SameProblem y (gen d s)} ≤
      ((2 : ℝ≥0∞) ^ h)⁻¹ := by
  by_cases hy : ∃ r, F.SameProblem y (gen d r)
  · obtain ⟨r, hr⟩ := hy
    have he := F.sameProblem_equiv
    have : {s | F.SameProblem y (gen d s)} = fiber F gen d r := by
      ext s
      exact ⟨fun hs => he.trans (he.symm hr) hs, fun hs => he.trans hr hs⟩
    rw [this]
    exact hc.uniform_sameProblem_le d r
  · have : {s | F.SameProblem y (gen d s)} = ∅ :=
      Set.eq_empty_of_forall_notMem fun s hs => hy ⟨s, hs⟩
    rw [this]
    simp

/-- The pairs of seeds that give the same problem, counted: `2^h · |pairs| ≤ 2^k · 2^k`. -/
theorem Certified.card_collision (hc : Certified F L k h gen) (d : Fin L) :
    2 ^ h * Nat.card {p : Seed k × Seed k | F.SameProblem (gen d p.1) (gen d p.2)} ≤
      Fintype.card (Seed k × Seed k) := by
  classical
  have e : {p : Seed k × Seed k | F.SameProblem (gen d p.1) (gen d p.2)} ≃
      Σ r : Seed k, fiber F gen d r :=
    { toFun := fun p => ⟨p.1.1, p.1.2, p.2⟩
      invFun := fun q => ⟨(q.1, q.2.1), q.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_sigma, Finset.mul_sum, Fintype.card_prod, card_seed]
  calc ∑ r : Seed k, 2 ^ h * Nat.card (fiber F gen d r) ≤ ∑ _r : Seed k, 2 ^ k :=
        Finset.sum_le_sum fun r _ => hc.card_fiber d r
    _ = 2 ^ k * 2 ^ k := by rw [Finset.sum_const, Finset.card_univ, card_seed, smul_eq_mul]

/-- **Collision probability.** Two independent uniform seeds give the same problem with
probability at most `2^-h` (the pair of independent seeds is uniform on pairs). -/
theorem Certified.uniform_collision_le (hc : Certified F L k h gen) (d : Fin L) :
    (PMF.uniformOfFintype (Seed k × Seed k)).toOuterMeasure
      {p | F.SameProblem (gen d p.1) (gen d p.2)} ≤ ((2 : ℝ≥0∞) ^ h)⁻¹ :=
  uniform_le_of_card (hc.card_collision d)

/-- The collision probability, with the two seeds drawn one after the other. -/
theorem Certified.uniform_collision_le' (hc : Certified F L k h gen) (d : Fin L) :
    ((PMF.uniformOfFintype (Seed k)).bind fun r =>
      (PMF.uniformOfFintype (Seed k)).map fun s => (r, s)).toOuterMeasure
      {p | F.SameProblem (gen d p.1) (gen d p.2)} ≤ ((2 : ℝ≥0∞) ^ h)⁻¹ := by
  rw [PMF.uniformOfFintype_prod]
  exact hc.uniform_collision_le d

/-! ### Proving diversity -/

/-- **Injective modulo equivalence**: if the same problem forces the same seed, the generator is
certified at `h = k`. -/
theorem certified_of_injective (hL : 0 < L) (hsol : ∀ d r, F.Solvable (gen d r))
    (hinj : ∀ d r s, F.SameProblem (gen d r) (gen d s) → r = s) : Certified F L k k gen := by
  refine ⟨hL, le_rfl, hsol, fun d r => ?_⟩
  have : Nat.card (fiber F gen d r) ≤ 1 := by
    have := Nat.card_le_card_of_injective (fun _ : fiber F gen d r => ())
      fun a b _ => Subtype.ext ((hinj d r a a.2).symm.trans (hinj d r b b.2))
    simpa using this
  calc 2 ^ k * Nat.card (fiber F gen d r) ≤ 2 ^ k * 1 := Nat.mul_le_mul_left _ this
    _ = 2 ^ k := mul_one _

/-- **Bounded fiber**: a fiber that injects into a type of at most `2^(k-h)` elements (as
`2^h · |T| ≤ 2^k`). -/
theorem diversity_of_injection {d : Fin L} {r : Seed k} {T : Type*} [Finite T]
    (g : fiber F gen d r → T) (hg : Function.Injective g) (hT : 2 ^ h * Nat.card T ≤ 2 ^ k) :
    2 ^ h * Nat.card (fiber F gen d r) ≤ 2 ^ k :=
  (Nat.mul_le_mul_left _ (Nat.card_le_card_of_injective g hg)).trans hT

/-- **Partial seed recovery**: if the same problem forces the same value of `f`, and every fiber
of `f` has at most `2^(k-h)` seeds, the bound holds at `h`. -/
theorem diversity_of_recovery {β : Type*} (f : Seed k → β)
    (hf : ∀ b, 2 ^ h * Nat.card {s // f s = b} ≤ 2 ^ k)
    (hrec : ∀ d r s, F.SameProblem (gen d r) (gen d s) → f r = f s) (d : Fin L) (r : Seed k) :
    2 ^ h * Nat.card (fiber F gen d r) ≤ 2 ^ k :=
  (Nat.mul_le_mul_left _ (Nat.card_le_card_of_injective
    (fun s : fiber F gen d r => (⟨s.1, (hrec d r s.1 s.2).symm⟩ : {s // f s = f r}))
    fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))).trans (hf (f r))

/-- The first `h` bits of a seed. -/
def seedPrefix (hk : h ≤ k) (s : Seed k) : Seed h := fun i => s (Fin.castLE hk i)

/-- A fiber of the prefix map has `2^(k-h)` seeds at most. -/
theorem card_seedPrefix_fiber (hk : h ≤ k) (b : Seed h) :
    2 ^ h * Nat.card {s : Seed k // seedPrefix hk s = b} ≤ 2 ^ k := by
  have hinj : Function.Injective fun s : {s : Seed k // seedPrefix hk s = b} =>
      (fun j : Fin (k - h) => s.1 ⟨h + j, by omega⟩) := by
    intro s t hst
    apply Subtype.ext
    funext i
    by_cases hi : i.1 < h
    · have hs := congrFun s.2 ⟨i, hi⟩
      have ht := congrFun t.2 ⟨i, hi⟩
      simp only [seedPrefix, Fin.castLE] at hs ht
      exact hs.trans ht.symm
    · have := congrFun hst ⟨i - h, by omega⟩
      simp only at this
      have e : (⟨h + (i.1 - h), by omega⟩ : Fin k) = i := Fin.ext (by simp; omega)
      rwa [e] at this
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card (α := Seed (k - h)), card_seed] at this
  calc 2 ^ h * Nat.card {s : Seed k // seedPrefix hk s = b} ≤ 2 ^ h * 2 ^ (k - h) :=
        Nat.mul_le_mul_left _ this
    _ = 2 ^ k := by rw [← pow_add, Nat.add_sub_cancel' hk]

/-- **Partial seed recovery, prefix form**: if the same problem forces the same first `h` seed
bits, the bound holds at `h`. -/
theorem diversity_of_prefix (hk : h ≤ k)
    (hrec : ∀ d r s, F.SameProblem (gen d r) (gen d s) → seedPrefix hk r = seedPrefix hk s)
    (d : Fin L) (r : Seed k) : 2 ^ h * Nat.card (fiber F gen d r) ≤ 2 ^ k :=
  diversity_of_recovery (seedPrefix hk) (card_seedPrefix_fiber hk) hrec d r

/-- A generator that recovers its first `h` seed bits from the problem is certified at `h`. -/
theorem certified_of_prefix (hL : 0 < L) (hk : h ≤ k) (hsol : ∀ d r, F.Solvable (gen d r))
    (hrec : ∀ d r s, F.SameProblem (gen d r) (gen d s) → seedPrefix hk r = seedPrefix hk s) :
    Certified F L k h gen :=
  ⟨hL, hk, hsol, diversity_of_prefix hk hrec⟩

/-! ### Constant generators -/

/-- A generator whose seeds all give the same problem at some level is certified only at
`h = 0`. -/
theorem not_certified_of_sameProblem (hh : 0 < h) (d : Fin L)
    (hall : ∀ r s, F.SameProblem (gen d r) (gen d s)) : ¬ Certified F L k h gen := by
  intro hc
  have hd := hc.card_fiber d (fun _ => false)
  have : Nat.card (fiber F gen d (fun _ => false)) = 2 ^ k := by
    have hu : fiber F gen d (fun _ => false) = Set.univ := Set.eq_univ_of_forall fun s => hall _ s
    rw [hu, Nat.card_congr (Equiv.Set.univ _),
      Nat.card_eq_fintype_card, card_seed]
  rw [this] at hd
  have h2 : 2 ≤ 2 ^ h := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) hh
  have hk : 0 < 2 ^ k := by positivity
  nlinarith

/-- A constant generator is certified only at `h = 0`. -/
theorem not_certified_const (hh : 0 < h) (hL : 0 < L) (x : F.Task) :
    ¬ Certified F L k h (fun _ _ => x) :=
  not_certified_of_sameProblem hh ⟨0, hL⟩ fun _ _ => F.sameProblem_equiv.refl x

/-! ### Decision problems -/

/-- Swapping real and ideal keeps the gain (the squared advantage). -/
theorem gain_decision_swap (real ideal : PMF (List Bool)) (M : Machine) :
    (Problem.decision real ideal).gain M = (Problem.decision ideal real).gain M := by
  simp only [Problem.gain]
  ring

/-- Attack tasks whose problems are a decision problem and its swap are the same problem. -/
theorem AttackAdapter.sameAttack_of_swap {A : AttackAdapter} {x y : A.Task}
    {real ideal : PMF (List Bool)} (hx : A.problem x = .decision real ideal)
    (hy : A.problem y = .decision ideal real) : A.SameAttack x y := fun M => by
  rw [hx, hy]
  exact gain_decision_swap real ideal M

/-! ### What earns no entropy (L10)

Diversity is about the problem, never about metadata: design tasks with the same parameters are
the same problem whatever their caps (or names, or any other field the propositions do not read),
and attack tasks with the same problem are the same problem whatever their bounds `c` or claimed
strengths. A generator that only varies such fields is not certified for any `h > 0`. -/

theorem DesignAdapter.sameDesign_of_params_eq (A : DesignAdapter) {x y : A.Task}
    (h : A.params x = A.params y) : A.SameDesign x y := fun I => by
  unfold DesignAdapter.SemanticAccept
  rw [h]

theorem AttackAdapter.sameAttack_of_problem_eq (A : AttackAdapter) {x y : A.Task}
    (h : A.problem x = A.problem y) : A.SameAttack x y := fun M => by rw [h]

theorem DesignAdapter.not_certified_of_params_const (A : DesignAdapter) {L k h : ℕ}
    {gen : Fin L → Seed k → A.Task} (hh : 0 < h) (d : Fin L)
    (hc : ∀ r s, A.params (gen d r) = A.params (gen d s)) : ¬ Certified A.family L k h gen :=
  not_certified_of_sameProblem hh d fun r s => A.sameDesign_of_params_eq (hc r s)

theorem AttackAdapter.not_certified_of_problem_const (A : AttackAdapter) {L k h : ℕ}
    {gen : Fin L → Seed k → A.Task} (hh : 0 < h) (d : Fin L)
    (hc : ∀ r s, A.problem (gen d r) = A.problem (gen d s)) : ¬ Certified A.family L k h gen :=
  not_certified_of_sameProblem hh d fun r s => A.sameAttack_of_problem_eq (hc r s)

end SigabaNeo.Benchmark
