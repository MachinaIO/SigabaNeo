module

public import SigabaNeo.Lib.Lattices.Research.Wall1.CoordinateListOracle
public import SigabaNeo.Lib.Lattices.Research.Wall1.CoordinateListRank
import all SigabaNeo.Lib.Lattices.Research.Wall1.CoordinateListOracle
import all SigabaNeo.Lib.Lattices.Research.Wall1.CoordinateListMoment

/-! Part 137, Theorems 6 and 7. The shared random input contains the plant and all
nonreserved data. A fresh uniform matrix supplies the common reserved rows. -/

public section
namespace SigabaNeo.Wall1.CoordinateList

open Finset Matrix MultiBlock SigabaNeo.Planted
open scoped Classical

variable {Ω I : Type*} [Fintype Ω] {n q v : ℕ} [Fact q.Prime]

structure Law (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℚ
  nonneg : ∀ ω, 0 ≤ mass ω
  total : ∑ ω, mass ω = 1

def Law.mean (P : Law Ω) (f : Ω → ℚ) := ∑ ω, P.mass ω * f ω
noncomputable def flag (p : Prop) : ℚ := if p then 1 else 0

private theorem avg_flag {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    avg (fun a ↦ flag (p a)) = ((univ.filter p).card : ℚ) / Fintype.card α := by
  simp only [avg, card_filter, Nat.cast_sum]
  congr 1
  apply sum_congr rfl
  intro a _
  by_cases h : p a <;> simp [flag, h]

private theorem avg_const_add {α : Type*} [Fintype α] [Nonempty α] (a : ℚ) (f : α → ℚ) :
    avg (fun x ↦ a + f x) = a + avg f := by
  simp [avg, sum_add_distrib, add_div, Fintype.card_ne_zero]

private theorem mean_mono (P : Law Ω) {f g : Ω → ℚ} (h : ∀ ω, f ω ≤ g ω) :
    P.mean f ≤ P.mean g := sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left (h ω) (P.nonneg ω)

private theorem mean_sum (P : Law Ω) (T : Finset I) (f : Ω → I → ℚ) :
    P.mean (fun ω ↦ ∑ i ∈ T, f ω i) = ∑ i ∈ T, P.mean (fun ω ↦ f ω i) := by
  simp only [Law.mean, mul_sum, sum_comm (s := (univ : Finset Ω)) (t := T)]

/-- The matrix-valued functions may read the same design rows across blocks. All fields
are fixed before the uniform reserved matrix is drawn. The row errors may also be conditioned on. -/
structure Family (Ω I : Type*) (n q v : ℕ) where
  r : I → ℕ
  k : I → ℕ
  j : I → ℕ
  coord : ∀ i, (Fin (k i) ⊕ Fin (j i)) ≃ Fin n
  R : I → ℝ
  radius_nonneg : ∀ i, 0 ≤ R i
  A : ∀ i, Ω → Mat (r i) (k i) q
  D : ∀ i, Ω → Mat (r i) (j i) q
  secret : Ω → Fin n → ℤ
  noise : ∀ i, Ω → Fin (r i) → ℤ
  reservedNoise : Ω → Vec v q
  small : ∀ ω i, (secret ω i).natAbs ≤ 3
  accepts_noise : ∀ ω a, accept (reservedNoise ω a)

namespace Family

variable (F : Family Ω I n q v)

@[expose] def block (i : I) (ω : Ω) : Block n q :=
  ⟨F.r i, F.k i, F.j i, F.coord i, F.A i ω, F.D i ω, F.R i, F.radius_nonneg i⟩

noncomputable def choices (O : Oracle q) (i : I) (ω : Ω) : Finset (Vec n q) :=
  let L := F.block i ω
  candidates L O (L.sample (F.noise i ω) (F.secret ω))

noncomputable def count (O : Oracle q) (i : I) (ω : Ω) : ℕ :=
  (competitors (F.block i ω) O (F.noise i ω) (F.secret ω)).card

def inRadius (i : I) (ω : Ω) : Prop :=
  inside (F.R i) ((F.block i ω).plant (F.noise i ω) (F.secret ω))

def miss (T : Finset I) (ω : Ω) : Prop := ∀ i ∈ T, ¬ F.inRadius i ω

def passes (ω : Ω) (V : Mat v n q) (c : Vec n q) : Prop :=
  ∀ a, accept (V a ⬝ᵥ red q (F.secret ω) + F.reservedNoise ω a - V a ⬝ᵥ c)

noncomputable def accepted (O : Oracle q) (T : Finset I) (ω : Ω) (V : Mat v n q) :=
  (T.biUnion fun i ↦ F.choices O i ω).filter (F.passes ω V)

/-- Failure means that the verified set is different from the singleton true residue. -/
noncomputable def failure (P : Law Ω) (O : Oracle q) (T : Finset I) :=
  P.mean fun ω ↦ avg fun V : Mat v n q ↦
    flag (F.accepted O T ω V ≠ {red q (F.secret ω)})

private noncomputable def wrong (O : Oracle q) (T : Finset I) (ω : Ω) :=
  (T.biUnion fun i ↦ F.choices O i ω).erase (red q (F.secret ω))

omit [Fintype Ω] in
private theorem wrong_bound (O : Oracle q) (T : Finset I) (ω : Ω) :
    (F.wrong O T ω).card ≤ ∑ i ∈ T, F.count O i ω := by
  let c := red q (F.secret ω)
  have hs : F.wrong O T ω ⊆ T.biUnion fun i ↦ (F.choices O i ω).erase c := by
    intro d hd
    obtain ⟨hn, hm⟩ := mem_erase.mp hd
    obtain ⟨i, hi, hm⟩ := mem_biUnion.mp hm
    exact mem_biUnion.mpr ⟨i, hi, mem_erase.mpr ⟨hn, hm⟩⟩
  exact ((card_le_card hs).trans card_biUnion_le).trans
    (sum_le_sum fun i _ ↦ wrong_card_le (F.block i ω) O (F.noise i ω) (F.secret ω))

private theorem flag_nonneg (p : Prop) : 0 ≤ flag p := by simp [flag]; split <;> norm_num

omit [Fintype Ω] in
private theorem conditional_split {O : Oracle q} (hO : Exact O) (hq : 6 < q) (T : Finset I) (ω : Ω)
    (V : Mat v n q) :
    flag (F.accepted O T ω V ≠ {red q (F.secret ω)}) ≤ flag (F.miss T ω) +
      (∑ i ∈ T, flag ((F.D i ω).rank ≠ F.j i)) +
      flag (∃ c ∈ F.wrong O T ω, F.passes ω V c) := by
  have h1 (p : Prop) : flag p ≤ 1 := by unfold flag; split <;> norm_num
  have hg := sum_nonneg (s := T) (fun i _ ↦ flag_nonneg ((F.D i ω).rank ≠ F.j i))
  have hf := flag_nonneg (∃ c ∈ F.wrong O T ω, F.passes ω V c)
  by_cases hm : F.miss T ω
  · rw [show flag (F.miss T ω) = 1 by simp [flag, hm]]
    linarith [h1 (F.accepted O T ω V ≠ {red q (F.secret ω)})]
  rw [show flag (F.miss T ω) = 0 by simp [flag, hm], zero_add]
  by_cases hd : ∃ i ∈ T, (F.D i ω).rank ≠ F.j i
  · obtain ⟨i, hi, hbad⟩ := hd
    have hh := single_le_sum (fun i (_ : i ∈ T) ↦ flag_nonneg ((F.D i ω).rank ≠ F.j i)) hi
    rw [show flag ((F.D i ω).rank ≠ F.j i) = 1 by simp [flag, hbad]] at hh
    linarith [h1 (F.accepted O T ω V ≠ {red q (F.secret ω)})]
  by_cases hw : ∃ c ∈ F.wrong O T ω, F.passes ω V c
  · rw [show flag (∃ c ∈ F.wrong O T ω, F.passes ω V c) = 1 by simp [flag, hw]]
    linarith [h1 (F.accepted O T ω V ≠ {red q (F.secret ω)})]
  have hex : ∃ i ∈ T, F.inRadius i ω := by simpa [miss] using hm
  obtain ⟨i, hi, hin⟩ := hex
  have hs : red q (F.secret ω) ∈ F.accepted O T ω V := by
    apply mem_filter.mpr
    refine ⟨mem_biUnion.mpr ⟨i, hi, plant_listed (L := F.block i ω) hO (supported_red hq (F.small ω))
      (by by_contra h; exact hd ⟨i, hi, h⟩) hin⟩, ?_⟩
    intro a
    simpa [add_sub_cancel_left] using F.accepts_noise ω a
  have heq : F.accepted O T ω V = {red q (F.secret ω)} := by
    ext c
    rw [mem_singleton]
    constructor
    · intro hc
      by_contra hn
      obtain ⟨hm, hp⟩ := mem_filter.mp hc
      exact hw ⟨c, mem_erase.mpr ⟨hn, hm⟩, hp⟩
    · rintro rfl; exact hs
  simp [flag, heq, hw] at hg ⊢
  exact hg

/-- Theorem 7, upper bound with the actual marginal rank-deficiency probabilities. -/
theorem joint_failure_le (P : Law Ω) {O : Oracle q} (hO : Exact O) (hq : 6 < q) (T : Finset I) :
    F.failure P O T ≤ P.mean (fun ω ↦ flag (F.miss T ω)) +
      (∑ i ∈ T, P.mean fun ω ↦ flag ((F.D i ω).rank ≠ F.j i)) +
      (∑ i ∈ T, P.mean fun ω ↦ (F.count O i ω : ℚ)) * (7/q)^v := by
  let W := F.wrong O T
  let E (ω : Ω) := avg fun V : Mat v n q ↦ flag (∃ c ∈ W ω, F.passes ω V c)
  have hv := verify_union_avg hq P.mass P.nonneg (fun ω ↦ red q (F.secret ω)) F.reservedNoise W
    (fun ω ↦ notMem_erase _ _)
  have hd : (Fintype.card (Mat v n q) : ℚ) = (q : ℚ)^(n*v) := by
    change ((Fintype.card (Fin v → Fin n → ZMod q) : ℕ) : ℚ) = _
    simp [← pow_mul]
  have hv' : P.mean E ≤ P.mean (fun ω ↦ ((W ω).card : ℚ)) * (7/q)^v := by
    have eqE (ω : Ω) : E ω = ((univ.filter fun V : Mat v n q ↦
        ∃ c ∈ W ω, ∀ a, accept (V a ⬝ᵥ red q (F.secret ω) + F.reservedNoise ω a - V a ⬝ᵥ c)).card : ℚ)
          / (q : ℚ)^(n*v) := by
      unfold E passes
      rw [← hd]
      exact avg_flag _
    simpa only [Law.mean, eqE] using hv
  have hcount : P.mean (fun ω ↦ ((W ω).card : ℚ)) ≤ ∑ i ∈ T, P.mean fun ω ↦ (F.count O i ω : ℚ) := by
    rw [← mean_sum]
    exact mean_mono _ fun ω ↦ by exact_mod_cast F.wrong_bound O T ω
  have split := mean_mono P (fun ω ↦
    div_le_div_of_nonneg_right (sum_le_sum (fun V (_ : V ∈ univ) ↦ F.conditional_split hO hq T ω V))
      (by positivity : 0 ≤ (Fintype.card (Mat v n q) : ℚ)))
  change F.failure P O T ≤ P.mean (fun ω ↦ avg fun V : Mat v n q ↦
    (flag (F.miss T ω) + ∑ i ∈ T, flag ((F.D i ω).rank ≠ F.j i)) +
    flag (∃ c ∈ W ω, F.passes ω V c)) at split
  simp only [avg_const_add] at split
  have hm (f g : Ω → ℚ) : P.mean (fun ω ↦ f ω + g ω) = P.mean f + P.mean g := by
    simp only [Law.mean, mul_add, sum_add_distrib]
  rw [hm, hm, mean_sum] at split
  exact split.trans (add_le_add le_rfl (hv'.trans (mul_le_mul_of_nonneg_right hcount (by positivity))))

/-- Theorem 7, audited converse. No rank or independence hypotheses on the blocks. -/
theorem norm_le_joint_failure (P : Law Ω) {O : Oracle q} (hO : Exact O) (T : Finset I)
    (B : I → Ω → ℝ)
    (hB : ∀ i ∈ T, ∀ ω a, a ≠ (.inr (.inr ()) : Coord (F.r i) (F.k i)) →
      |((F.block i ω).plant (F.noise i ω) (F.secret ω) a : ℝ)| ≤ B i ω)
    (hR : ∀ i ∈ T, ∀ ω, F.R i * Real.sqrt (1 + (B i ω)^2) < q) :
    P.mean (fun ω ↦ flag (F.miss T ω)) ≤ F.failure P O T := by
  apply mean_mono
  intro ω
  by_cases hm : F.miss T ω
  · have hh (V : Mat v n q) : F.accepted O T ω V ≠ {red q (F.secret ω)} := by
      intro heq
      have hc : red q (F.secret ω) ∈ F.accepted O T ω V := by rw [heq]; simp
      obtain ⟨i, hi, hc⟩ := mem_biUnion.mp (mem_filter.mp hc).1
      exact hm i hi (secret_implies_inside (L := F.block i ω) hO (hB i hi ω) (hR i hi ω) hc)
    simp [flag, hm, hh, avg_const]
  · rw [show flag (F.miss T ω) = 0 by simp [flag, hm]]
    exact div_nonneg (sum_nonneg fun _ _ ↦ flag_nonneg _) (by positivity)

/-- A uniform marginal is specified by its law against finite test functions. Other blocks
and the secret may share randomness, provided the stated marginal holds. -/
def uniformDeleted (P : Law Ω) (i : I) : Prop :=
  ∀ f : Mat (F.r i) (F.j i) q → ℚ, P.mean (fun ω ↦ f (F.D i ω)) = avg f

/-- Discharge the marginal assumption using a fixed row and column selection of a shared
uniform nonreserved design. The same ambient matrix can be used for every block. -/
theorem uniformDeleted_of_submatrix (P : Law Ω) (i : I) {m : ℕ} (A : Ω → Mat m n q)
    (rows : Fin (F.r i) ↪ Fin m) (cols : Fin (F.j i) ↪ Fin n)
    (hD : ∀ ω, F.D i ω = (A ω).submatrix rows cols)
    (hA : ∀ g : Mat m n q → ℚ, P.mean (fun ω ↦ g (A ω)) = avg g) :
    F.uniformDeleted P i := by
  intro f
  simp_rw [hD]
  exact (hA (fun M ↦ f (M.submatrix rows cols))).trans (submatrix_average rows cols f)

/-- Theorem 7 with the explicit projective-kernel term from the note. -/
theorem joint_uniform_le (P : Law Ω) {O : Oracle q} (hO : Exact O) (hq : 6 < q) (T : Finset I)
    (hu : ∀ i ∈ T, F.uniformDeleted P i) :
    F.failure P O T ≤ P.mean (fun ω ↦ flag (F.miss T ω)) +
      (∑ i ∈ T, ((q : ℚ)^(F.j i) - 1) / ((q-1) * q^(F.r i))) +
      (∑ i ∈ T, P.mean fun ω ↦ (F.count O i ω : ℚ)) * (7/q)^v := by
  have hr (i : I) (hi : i ∈ T) : P.mean (fun ω ↦ flag ((F.D i ω).rank ≠ F.j i)) ≤
      ((q : ℚ)^(F.j i) - 1) / ((q-1) * q^(F.r i)) := by
    calc _ = avg (fun D : Mat (F.r i) (F.j i) q ↦ flag (D.rank ≠ F.j i)) := hu i hi _
         _ ≤ _ := by
           convert! rankDefect_probability q (F.r i) (F.j i) using 2
           funext D
           by_cases h : D.rank = F.j i <;> simp [flag, h]
  exact (F.joint_failure_le P hO hq T).trans (add_le_add (add_le_add le_rfl (sum_le_sum hr)) le_rfl)

/-- Theorem 6, one block under any plant distribution, including a fixed plant. -/
theorem single_uniform_le (P : Law Ω) {O : Oracle q} (hO : Exact O) (hq : 6 < q) (i : I)
    (hu : F.uniformDeleted P i) :
    F.failure P O {i} ≤ P.mean (fun ω ↦ flag (¬ F.inRadius i ω)) +
      ((q : ℚ)^(F.j i) - 1) / ((q-1) * q^(F.r i)) +
      P.mean (fun ω ↦ (F.count O i ω : ℚ)) * (7/q)^v := by
  simpa [miss] using F.joint_uniform_le P hO hq {i} (by simpa using hu)

/-- On a full-rank distribution the only two terms are the norm tail and the signed-point
first moment times the reserved-row factor. This includes the case of no deletions. -/
theorem single_fullRank_le (P : Law Ω) {O : Oracle q} (hO : Exact O) (hq : 6 < q) (i : I)
    (hf : ∀ ω, (F.D i ω).rank = F.j i) :
    F.failure P O {i} ≤ P.mean (fun ω ↦ flag (¬ F.inRadius i ω)) +
      P.mean (fun ω ↦ (F.count O i ω : ℚ)) * (7/q)^v := by
  simpa [miss, hf, flag, Law.mean] using F.joint_failure_le P hO hq {i}

end Family

/-- Output-size part of Theorem 6 (Markov). Applied to the cardinality of the exact list. -/
theorem list_size_tail (P : Law Ω) {α : Type*} (list : Ω → Finset α) (L : ℚ) (hL : 0 < L) :
    P.mean (fun ω ↦ flag (L < (list ω).card)) ≤ P.mean (fun ω ↦ ((list ω).card : ℚ)) / L := by
  rw [le_div_iff₀ hL]
  unfold Law.mean
  rw [sum_mul]
  apply sum_le_sum
  intro ω _
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (P.nonneg ω)
  by_cases h : L < (list ω).card
  · simpa [flag, h] using h.le
  · simp [flag, h]

end SigabaNeo.Wall1.CoordinateList

#print axioms SigabaNeo.Wall1.CoordinateList.Family.joint_failure_le
#print axioms SigabaNeo.Wall1.CoordinateList.Family.norm_le_joint_failure
#print axioms SigabaNeo.Wall1.CoordinateList.Family.uniformDeleted_of_submatrix
#print axioms SigabaNeo.Wall1.CoordinateList.Family.joint_uniform_le
#print axioms SigabaNeo.Wall1.CoordinateList.Family.single_uniform_le
#print axioms SigabaNeo.Wall1.CoordinateList.Family.single_fullRank_le
#print axioms SigabaNeo.Wall1.CoordinateList.list_size_tail
