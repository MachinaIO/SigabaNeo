import SigabaNeo.Lib.Lattices.Estimator.Usvp
import SigabaNeo.Lib.Lattices.Estimator.PrimalBdd
import SigabaNeo.Lib.Lattices.Estimator.PrimalHybrid
import SigabaNeo.Lib.Lattices.Estimator.Dual
import SigabaNeo.Lib.Lattices.Estimator.DualHybrid
import SigabaNeo.Lib.Lattices.Estimator.Bkw
import SigabaNeo.Lib.Lattices.Estimator.AroraGB
import SigabaNeo.Lib.Lattices.Estimator.Guess
import Mathlib.Tactic.Linarith
import Mathlib.Order.MinMax

/-!
# The attack models and the security function they define

An `AttackModel` is a named cost function `LWEParams → Cost` (the `log₂` of the estimator's `rop`,
fixed point; `none` = infinite). `attacks` lists the formalized attacks of the lattice estimator
(revision `53da598`, default cost model `RC.MATZOV`, GSA). `estimatorBits p` is the integer floor
of their minimum. By construction:

* `estimatorBits_le`: no attack costs less than `2^{estimatorBits p}`;
* `estimatorBits_tight`: some attack costs less than `2^{estimatorBits p + 1}`, so any larger
  claim is contradicted by a modelled attack.

Both are statements about the models: that a Turing machine achieves a modelled cost rests on the
heuristics listed in each attack's module (GSA, the 2016 estimate, the sieving cost fit, …) and is
not proved.
-/

namespace SigabaNeo.Lattices.Estimator

/-- A named attack cost model. -/
structure AttackModel where
  /-- The estimator's name for the attack. -/
  name : String
  /-- `log₂` of its cost (`none`: not applicable or infinite). -/
  cost : LWEParams → Cost

/-- The minimum cost over a list of attacks. -/
def minCost : List AttackModel → LWEParams → Cost
  | [], _ => none
  | a :: as, p => Cost.min (a.cost p) (minCost as p)

theorem Cost.min_some_le {a b : Cost} {c : Fx} (h : Cost.min a b = some c) :
    (∀ x, a = some x → c ≤ x) ∧ (∀ x, b = some x → c ≤ x) := by
  cases a with
  | none =>
    cases b with
    | none => cases h
    | some y =>
      have : y = c := Option.some.inj h
      subst this; exact ⟨fun _ hx => (by cases hx), fun _ hx => (by cases hx; exact le_refl _)⟩
  | some x =>
    cases b with
    | none =>
      have : x = c := Option.some.inj h
      subst this; exact ⟨fun _ hx => (by cases hx; exact le_refl _), fun _ hx => (by cases hx)⟩
    | some y =>
      have : Min.min x y = c := Option.some.inj h
      subst this
      exact ⟨fun _ hx => (by cases hx; exact min_le_left _ _),
        fun _ hx => (by cases hx; exact min_le_right _ _)⟩

theorem Cost.min_cases {a b : Cost} {c : Fx} (h : Cost.min a b = some c) :
    a = some c ∨ b = some c := by
  cases a with
  | none => exact Or.inr h
  | some x =>
    cases b with
    | none => exact Or.inl h
    | some y =>
      have : Min.min x y = c := Option.some.inj h
      subst this
      rcases le_total x y with h' | h'
      · left; rw [min_eq_left h']
      · right; rw [min_eq_right h']

theorem Cost.min_isSome {a b : Cost} (h : a.isSome) : (Cost.min a b).isSome := by
  cases a <;> cases b <;> simp_all [Cost.min]

/-- Every attack's cost is at least the minimum. -/
theorem minCost_le {as : List AttackModel} {a : AttackModel} (ha : a ∈ as) {p : LWEParams}
    {x : Fx} (hx : a.cost p = some x) : ∃ c, minCost as p = some c ∧ c ≤ x := by
  induction as with
  | nil => cases ha
  | cons b as ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · have hs : (minCost (a :: as) p).isSome := Cost.min_isSome (by simp [hx])
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hs
      exact ⟨c, hc, (Cost.min_some_le hc).1 x hx⟩
    · obtain ⟨c', hc', hle⟩ := ih ha
      cases hb : b.cost p with
      | none => exact ⟨c', by simp [minCost, hb, hc', Cost.min], hle⟩
      | some y =>
        refine ⟨Min.min y c', ?_, (min_le_right y c').trans hle⟩
        show Cost.min (b.cost p) (minCost as p) = _
        rw [hb, hc']; rfl

/-- The minimum is attained by an attack. -/
theorem minCost_attained {as : List AttackModel} {p : LWEParams} {c : Fx}
    (h : minCost as p = some c) : ∃ a ∈ as, a.cost p = some c := by
  induction as with
  | nil => simp [minCost] at h
  | cons b as ih =>
    rcases Cost.min_cases h with h1 | h1
    · exact ⟨b, List.mem_cons_self .., h1⟩
    · obtain ⟨a, ha, hc⟩ := ih h1
      exact ⟨a, List.mem_cons_of_mem _ ha, hc⟩

/-- The claim when every attack is infinite: `⌊log₂ RC.MATZOV(maxBeta, maxBeta)⌋` (4673).

A lattice attack is infinite when no block size `β < maxBeta` of its scan succeeds; a successful
attack would then need `β ≥ maxBeta`, which costs at least the reduction cost at `maxBeta`. The
claim is that cost, not more. Of the other attacks, exhaustive search is infinite above
`2^10000` (the estimator's `Cost.sanity_check`), which is above this value; coded-BKW is infinite
above `2^1024` (the estimator's binary64 cost overflows) and when its noise is too large;
Arora–GB, MITM and exhaustive search are also infinite when they lack samples. -/
def fallbackBits : ℕ := (Fx.floor (Reduction.matzovBits maxBeta maxBeta)).toNat

/-- The floor of the minimum over `as`, in bits. -/
def floorBits (as : List AttackModel) (p : LWEParams) : ℕ :=
  match minCost as p with
  | some c => (Fx.floor c).toNat
  | none => fallbackBits

/-- **Not refuted**: every attack in `as` costs at least `2^{floorBits}`. -/
theorem floorBits_le {as : List AttackModel} {a : AttackModel} (ha : a ∈ as) {p : LWEParams}
    {x : Fx} (hx : a.cost p = some x) : (floorBits as p : ℤ) ≤ max 0 (Fx.floor x) := by
  obtain ⟨c, hc, hle⟩ := minCost_le ha hx
  simp only [floorBits, hc]
  have : Fx.floor c ≤ Fx.floor x := by
    unfold Fx.floor
    rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide), Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
    exact Int.ediv_le_ediv (by decide) hle
  omega

/-- **Tight**: when some attack is finite, one of them costs less than `2^{floorBits + 1}`. -/
theorem floorBits_tight {as : List AttackModel} {p : LWEParams} (h : (minCost as p).isSome) :
    ∃ a ∈ as, ∃ x, a.cost p = some x ∧ x < ((floorBits as p : ℤ) + 1) * Fx.ONE := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨a, ha, hac⟩ := minCost_attained hc
  refine ⟨a, ha, c, hac, ?_⟩
  simp only [floorBits, hc]
  have h1 : c < (Fx.floor c + 1) * Fx.ONE := by
    unfold Fx.floor
    rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
    exact Int.lt_ediv_add_one_mul_self c (by decide)
  have h2 : Fx.floor c ≤ ((Fx.floor c).toNat : ℤ) := Int.self_le_toNat _
  have h3 : (0 : ℤ) < Fx.ONE := by decide
  nlinarith

/-- The LWE attacks of the lattice estimator: the eight of `LWE.estimate` (with their default
arguments) and the two guessing attacks of `lwe_guess.py`. -/
def attacks : List AttackModel :=
  [ ⟨"arora-gb", AroraGB.cost⟩,
    ⟨"bkw", Bkw.cost⟩,
    ⟨"usvp", Usvp.cost⟩,
    ⟨"bdd", PrimalBdd.cost⟩,
    ⟨"bdd_hybrid", PrimalHybrid.costBdd⟩,
    ⟨"bdd_mitm_hybrid", PrimalHybrid.costMitm⟩,
    ⟨"dual", Dual.cost⟩,
    ⟨"dual_hybrid", DualHybrid.cost⟩,
    ⟨"exhaustive_search", Guess.exhaustiveCost⟩,
    ⟨"mitm", Guess.mitmCost⟩ ]

/-- `⌊min over the estimator's attacks⌋`. -/
def estimatorBits (p : LWEParams) : ℕ := floorBits attacks p

theorem estimatorBits_le {a : AttackModel} (ha : a ∈ attacks) {p : LWEParams} {x : Fx}
    (hx : a.cost p = some x) : (estimatorBits p : ℤ) ≤ max 0 (Fx.floor x) :=
  floorBits_le ha hx

theorem estimatorBits_tight {p : LWEParams} (h : (minCost attacks p).isSome) :
    ∃ a ∈ attacks, ∃ x, a.cost p = some x ∧ x < ((estimatorBits p : ℤ) + 1) * Fx.ONE :=
  floorBits_tight h

end SigabaNeo.Lattices.Estimator
