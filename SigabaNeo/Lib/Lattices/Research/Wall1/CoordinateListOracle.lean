module

public import SigabaNeo.Lib.Lattices.Research.Wall1.CoordinateListMoment
public import SigabaNeo.Lib.Lattices.Research.Wall1.MultiBlockAttack
import all SigabaNeo.Lib.Lattices.Planted.Probability
import all SigabaNeo.Lib.Lattices.Research.Wall1.CoordinateListMoment

/-! Public coordinate-block lists and their signed height-one lifts (Part 137). -/

public section
namespace SigabaNeo.Wall1.CoordinateList

open Finset Matrix SigabaNeo.Planted
open scoped Classical

variable {n q r k j : ℕ} [Fact q.Prime]

/-- A block in column-split coordinates. The equivalence identifies its kept and deleted
columns in the common secret. Different blocks may use different splits. -/
structure Block (n q : ℕ) where
  r : ℕ
  k : ℕ
  j : ℕ
  coord : (Fin k ⊕ Fin j) ≃ Fin n
  A : Mat r k q
  D : Mat r j q
  R : ℝ
  nonneg : 0 ≤ R

def Block.keep (L : Block n q) {α : Type*} (c : Fin n → α) := fun i ↦ c (L.coord (.inl i))
def Block.drop (L : Block n q) {α : Type*} (c : Fin n → α) := fun i ↦ c (L.coord (.inr i))
def red (q : ℕ) {d : ℕ} (c : Fin d → ℤ) : Vec d q := fun i ↦ c i
def Block.sample (L : Block n q) (e : Fin L.r → ℤ) (s : Fin n → ℤ) : Vec L.r q :=
  red q e + L.A *ᵥ L.keep (red q s) + L.D *ᵥ L.drop (red q s)

def projected (A : Mat r k q) (D : Mat r j q) (b : Vec r q) (z : Point r k) : Prop :=
  ∃ w : Vec j q, (fun i ↦ (z (.inl i) : ZMod q)) +
    A *ᵥ (fun i ↦ (z (.inr (.inl i)) : ZMod q)) + D *ᵥ w = (height z : ZMod q) • b

/-- Public projected membership equals the discrepancy test used in the first moment. -/
theorem projected_iff (L : Block n q) (e : Fin L.r → ℤ) (s : Fin n → ℤ) (z : Point L.r L.k) :
    projected L.A L.D (L.sample e s) z ↔ incidence L.D L.A (errDiff q e z) (secDiff q (L.keep s) z) := by
  let t : ZMod q := height z
  have he : errDiff q e z = (fun i ↦ (z (.inl i) : ZMod q)) - t • red q e := by
    ext; simp [errDiff, t, red]
  have hs : secDiff q (L.keep s) z = (fun i ↦ (z (.inr (.inl i)) : ZMod q)) -
      t • L.keep (red q s) := by ext; simp [secDiff, t, Block.keep, red]
  rw [he, hs]
  simp only [projected, incidence, LinearMap.mem_range, mulVecLin_apply, mulVec_sub, mulVec_smul,
    Block.sample, smul_add]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨t • L.drop (red q s) - w, ?_⟩
    rw [mulVec_sub, mulVec_smul]
    change _ + _ + _ = t • _ + t • _ + t • _ at hw
    linear_combination (norm := abel) -hw
  · rintro ⟨w, hw⟩
    refine ⟨t • L.drop (red q s) - w, ?_⟩
    rw [mulVec_sub, mulVec_smul]
    change _ = t • _ + t • _ + t • _
    linear_combination (norm := abel) -hw

def inside {r k : ℕ} (R : ℝ) (z : Point r k) : Prop := ∑ i, (z i : ℝ)^2 ≤ R^2

abbrev Oracle (q : ℕ) := ∀ {r k j}, Mat r k q → Mat r j q → Vec r q → ℝ → Finset (Point r k)

def Exact (O : Oracle q) : Prop :=
  ∀ {r k j} (A : Mat r k q) (D : Mat r j q) b R, 0 ≤ R →
    ∀ z, z ∈ O A D b R ↔ inside R z ∧ projected A D b z

theorem exists_exact : ∃ O : Oracle q, Exact O := by
  refine ⟨fun A D b R ↦ (insert 0 (integerBall R)).filter (projected A D b), ?_⟩
  intro r k j A D b R hR z
  simp only [mem_filter, mem_insert, mem_integerBall hR, inside]
  by_cases hz : z = 0 <;> simp [hz, sq_nonneg]

def Block.plant (L : Block n q) (e : Fin L.r → ℤ) (s : Fin n → ℤ) : Point L.r L.k :=
  plantedPoint e (L.keep s)

theorem plant_projected (L : Block n q) (e : Fin L.r → ℤ) (s : Fin n → ℤ) :
    projected L.A L.D (L.sample e s) (L.plant e s) := by
  refine ⟨L.drop (red q s), ?_⟩
  simp [Block.plant, plantedPoint, height, Block.sample, Block.keep]
  rfl

/-- Residues in the CBD(3) support admit unique small integer representatives for q > 6. -/
def supported (c : Vec n q) : Prop := ∀ i, (c i).valMinAbs.natAbs ≤ 3

omit [Fact q.Prime] in
theorem supported_red (hq : 6 < q) {s : Fin n → ℤ} (hs : ∀ i, (s i).natAbs ≤ 3) :
    supported (red q s) := by
  intro i
  simpa [red, MultiBlock.Attack.valMinAbs_small (η := 3) hq _ (hs i)] using hs i

/-- The retained coordinates of the public residual and a candidate, at height one. -/
def Block.word (L : Block n q) (b : Vec L.r q) (c : Vec n q) : Coord L.r L.k → ZMod q
  | .inl i => (b - L.A *ᵥ L.keep c - L.D *ᵥ L.drop c) i
  | .inr (.inl i) => L.keep c i
  | .inr (.inr ()) => 1

theorem word_secret (L : Block n q) (e : Fin L.r → ℤ) (s : Fin n → ℤ) (i) :
    L.word (L.sample e s) (red q s) i = (L.plant e s i : ZMod q) := by
  rcases i with i | (i | u)
  · simp [Block.word, Block.sample, Block.plant, plantedPoint, red, add_sub_right_comm]
  · rfl
  · cases u; simp [Block.word, Block.plant, plantedPoint]

def unitHeight (z : Point r k) := height z = 1 ∨ height z = -1

/-- A residue read from one signed point. The full-column-rank guard implements the unique lift. -/
def Reads (L : Block n q) (b : Vec L.r q) (z : Point L.r L.k) (c : Vec n q) : Prop :=
  L.D.rank = L.j ∧ supported c ∧ unitHeight z ∧
    ∀ i, (z i : ZMod q) = (height z : ZMod q) * L.word b c i

theorem word_injective (L : Block n q) {b} (hrank : L.D.rank = L.j) :
    Function.Injective (L.word b) := by
  intro c d h
  have hw := congrFun h
  have hk : L.keep c = L.keep d := funext fun i ↦ hw (.inr (.inl i))
  have hr : b - L.A *ᵥ L.keep c - L.D *ᵥ L.drop c =
      b - L.A *ᵥ L.keep d - L.D *ᵥ L.drop d := funext fun i ↦ hw (.inl i)
  rw [hk] at hr
  have hdim := L.D.mulVecLin.finrank_range_add_finrank_ker
  change L.D.rank + _ = _ at hdim
  simp [hrank] at hdim
  have hinj := LinearMap.ker_eq_bot.mp hdim
  have hj : L.drop c = L.drop d := hinj (sub_right_inj.mp hr)
  funext i
  obtain ⟨a, rfl⟩ := L.coord.surjective i
  cases a with
  | inl a => exact congrFun hk a
  | inr a => exact congrFun hj a

theorem reads_unique (L : Block n q) {b z c d} (hc : Reads L b z c) (hd : Reads L b z d) :
    c = d := by
  have ht : (height z : ZMod q) ≠ 0 := by rcases hc.2.2.1 with h | h <;> simp [h]
  have hw i := mul_left_cancel₀ ht ((hc.2.2.2 i).symm.trans (hd.2.2.2 i))
  exact word_injective L hc.1 (funext hw)

def Block.points (L : Block n q) (O : Oracle q) (b : Vec L.r q) := O L.A L.D b L.R

noncomputable def candidates (L : Block n q) (O : Oracle q) (b : Vec L.r q) : Finset (Vec n q) :=
  (L.points O b).biUnion fun z ↦ univ.filter (Reads L b z)

theorem mem_candidates (L : Block n q) (O : Oracle q) (b : Vec L.r q) (c : Vec n q) :
    c ∈ candidates L O b ↔ ∃ z ∈ L.points O b, Reads L b z c := by simp [candidates]

theorem plant_listed {L : Block n q} {O : Oracle q} (hO : Exact O) {e s}
    (hs : supported (red q s)) (hRank : L.D.rank = L.j) (hIn : inside L.R (L.plant e s)) :
    red q s ∈ candidates L O (L.sample e s) := by
  apply (mem_candidates ..).mpr
  refine ⟨L.plant e s, (hO _ _ _ _ L.nonneg _).mpr ⟨hIn, plant_projected ..⟩, hRank, hs,
    Or.inl rfl, fun i ↦ ?_⟩
  simp [word_secret, Block.plant, height, plantedPoint]

noncomputable def competitors (L : Block n q) (O : Oracle q) (e : Fin L.r → ℤ) (s : Fin n → ℤ) :=
  (L.points O (L.sample e s)).filter fun z ↦
    unitHeight z ∧ z ≠ L.plant e s ∧ z ≠ -L.plant e s

theorem wrong_card_le (L : Block n q) (O : Oracle q) (e : Fin L.r → ℤ) (s : Fin n → ℤ) :
    ((candidates L O (L.sample e s)).erase (red q s)).card ≤ (competitors L O e s).card := by
  let T := competitors L O e s
  let F (z) := univ.filter (Reads L (L.sample e s) z)
  have hsub : (candidates L O (L.sample e s)).erase (red q s) ⊆ T.biUnion F := by
    intro c hc
    obtain ⟨hne, hc⟩ := mem_erase.mp hc
    obtain ⟨z, hz, hr⟩ := (mem_candidates ..).mp hc
    have hsame (h : z = L.plant e s ∨ z = -L.plant e s) : c = red q s := by
      have hword : ∀ i, L.word (L.sample e s) c i = L.word (L.sample e s) (red q s) i := by
        intro i
        have hci := hr.2.2.2 i
        rcases h with rfl | rfl <;>
          simpa [word_secret, height, Block.plant, plantedPoint] using hci.symm
      exact word_injective L hr.1 (funext hword)
    exact mem_biUnion.mpr ⟨z, mem_filter.mpr ⟨hz, hr.2.2.1, fun h ↦ hne (hsame (.inl h)),
      fun h ↦ hne (hsame (.inr h))⟩, mem_filter.mpr ⟨mem_univ _, hr⟩⟩
  calc
    _ ≤ ∑ z ∈ T, (F z).card := (card_le_card hsub).trans card_biUnion_le
    _ ≤ ∑ _ ∈ T, 1 := sum_le_sum fun _ _ ↦ card_le_one.mpr fun _ ha _ hb ↦
      reads_unique L (mem_filter.mp ha).2 (mem_filter.mp hb).2
    _ = _ := by simp [T]

/-- Audited no-wrap implication for the converse of Theorem 7. -/
theorem secret_implies_inside {L : Block n q} {O : Oracle q} (hO : Exact O) {e s B}
    (hB : ∀ i, i ≠ (.inr (.inr ()) : Coord L.r L.k) → |(L.plant e s i : ℝ)| ≤ B)
    (hq : L.R * Real.sqrt (1 + B^2) < q)
    (hc : red q s ∈ candidates L O (L.sample e s)) : inside L.R (L.plant e s) := by
  obtain ⟨z, hz, hr⟩ := (mem_candidates ..).mp hc
  have hin := ((hO _ _ _ _ L.nonneg _).mp hz).1
  have heq (i) : z i = height z * L.plant e s i := by
    by_cases hi : i = (.inr (.inr ()) : Coord L.r L.k)
    · subst i; simp [Block.plant, plantedPoint, height]
    have hsum := sum_le_univ_sum_of_nonneg (s := {i, (.inr (.inr ()) : Coord L.r L.k)})
      (fun a ↦ sq_nonneg (z a : ℝ))
    rw [sum_insert (by simpa using hi), sum_singleton] at hsum
    have hd := discrepancy L.nonneg (hsum.trans hin) (hB i hi) hq
    have hm : ((z i - height z * L.plant e s i : ℤ) : ZMod q) = 0 := by
      push_cast
      exact sub_eq_zero.mpr ((hr.2.2.2 i).trans (by rw [word_secret]))
    by_contra hn
    exact hd.not_ge (Int.le_of_dvd (abs_pos.mpr (sub_ne_zero.mpr hn))
      ((dvd_abs _ _).mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hm)))
  unfold inside at *
  calc
    _ = ∑ i, (z i : ℝ)^2 := sum_congr rfl fun i _ ↦ by
      rw [heq i]
      rcases hr.2.2.1 with h | h <;> simp [h]
    _ ≤ _ := hin

/-- In a fixed coordinate split the public sample changes when the design is resampled. -/
@[expose] def resample (L : Block n q) (A : Mat L.r L.k q) (D : Mat L.r L.j q) :=
  { L with A := A, D := D }

/-- Theorem 5 for an exact oracle's actual output, including zero. A point predicate can
select nonzero points, or precisely the signed height-one competitors counted in Theorems 6–7. -/
theorem expected_oracle_count (L : Block n q) {O : Oracle q} (hO : Exact O)
    (e : Fin L.r → ℤ) (s : Fin n → ℤ) (p : Point L.r L.k → Prop) :
    avg (fun D : Mat L.r L.j q ↦ avg fun A : Mat L.r L.k q ↦
      (((O A D ((resample L A D).sample e s) L.R).filter p).card : ℚ)) =
    ∑ z ∈ (insert 0 (integerBall L.R)).filter p,
      rankWeight L.j (errDiff q e z) (secDiff q (L.keep s) z) := by
  let S := (insert 0 (integerBall (ι := Coord L.r L.k) L.R)).filter p
  have memBall (z : Point L.r L.k) : z ∈ insert 0 (integerBall L.R) ↔ inside L.R z := by
    rw [mem_insert, mem_integerBall L.nonneg]
    by_cases hz : z = 0 <;> simp [hz, inside, sq_nonneg]
  have he (D : Mat L.r L.j q) (A : Mat L.r L.k q) :
      (O A D ((resample L A D).sample e s) L.R).filter p =
        S.filter (fun z ↦ incidence D A (errDiff q e z) (secDiff q (L.keep s) z)) := by
    ext z
    simp only [S, mem_filter, memBall]
    have hi := projected_iff (resample L A D) e s z
    change projected A D _ z ↔ incidence D A _ (secDiff q (L.keep s) z) at hi
    rw [hO A D ((resample L A D).sample e s) L.R L.nonneg z, hi]
    tauto
  simp_rw [he]
  exact expected_count e (L.keep s) S

end SigabaNeo.Wall1.CoordinateList

#print axioms SigabaNeo.Wall1.CoordinateList.projected_iff
#print axioms SigabaNeo.Wall1.CoordinateList.expected_oracle_count
#print axioms SigabaNeo.Wall1.CoordinateList.exists_exact
#print axioms SigabaNeo.Wall1.CoordinateList.plant_listed
#print axioms SigabaNeo.Wall1.CoordinateList.wrong_card_le
#print axioms SigabaNeo.Wall1.CoordinateList.secret_implies_inside
