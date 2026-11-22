module

public import SigabaNeo.Lib.Lattices.Research.Wall1.StatDistance

/-!
# Inversion on a uniform word (Part 141, Lemma 3)

A table with `n + 1` entries has `n` interior cuts. Equal adjacent cuts give empty bins.
The labels may live in any type. Both raw and conditional prefix probabilities are supported.
-/

@[expose] public section

namespace SigabaNeo.Wall1

noncomputable section

/-- Only cuts 0 through n+1 are inspected. An ordinary finite table can be extended
constantly past its last cut. -/
structure CDT (n w : ℕ) where
  cut : ℕ → ℕ
  mono : Monotone cut
  first : cut 0 = 0
  last : cut (n + 1) = 2 ^ w

namespace CDT

variable {n w : ℕ} (t : CDT n w) {α : Type*}

theorem hit (u : Fin (2 ^ w)) : ∃ i, u.val < t.cut (i + 1) :=
  ⟨n, by rw [t.last]; exact u.isLt⟩

/-- The zero-based index of the first strict upper cut above the word. -/
def index (u : Fin (2 ^ w)) : ℕ := Nat.find (hit t u)

theorem index_le (u : Fin (2 ^ w)) : t.index u ≤ n :=
  Nat.find_min' _ (show u.val < t.cut (n + 1) by rw [t.last]; exact u.isLt)

theorem index_eq_iff (u : Fin (2 ^ w)) (i : ℕ) :
    t.index u = i ↔ t.cut i ≤ u.val ∧ u.val < t.cut (i + 1) := by
  constructor
  · rintro rfl
    refine ⟨?_, Nat.find_spec (hit t u)⟩
    cases h : t.index u with
    | zero => simp [t.first]
    | succ j =>
      have hj : j < Nat.find (hit t u) := by change j < t.index u; omega
      exact le_of_not_gt (Nat.find_min (hit t u) hj)
  · rintro ⟨hlo, hhi⟩
    apply le_antisymm (Nat.find_min' (hit t u) hhi)
    by_contra! h
    have : t.cut (t.index u + 1) ≤ t.cut i := t.mono h
    have : u.val < t.cut (t.index u + 1) := Nat.find_spec (hit t u)
    omega

/-- Output law obtained by applying the lookup to a uniformly distributed w-bit word. -/
def law (x : ℕ → α) : α → ℝ := push (fun u ↦ x (t.index u)) (fun _ ↦ 1 / (2 : ℝ)^w)

theorem law_hasSum (x : ℕ → α) : HasSum (t.law x) 1 := by
  apply push_hasSum _ (fun _ ↦ by positivity)
  simpa using hasSum_fintype (fun _ : Fin (2 ^ w) ↦ 1 / (2 : ℝ)^w)

private theorem law_eq_card [DecidableEq α] (x : ℕ → α) (a : α) :
    t.law x a = ((Finset.univ.filter (fun u ↦ x (t.index u) = a)).card : ℝ) / 2^w := by
  classical
  unfold law push
  rw [tsum_fintype]
  simp [← Finset.sum_filter, div_eq_mul_inv]

theorem law_off [DecidableEq α] (x : ℕ → α) (a : α)
    (ha : a ∉ (Finset.range (n+1)).image x) : t.law x a = 0 := by
  rw [law_eq_card t]
  have h : ∀ u, x (t.index u) ≠ a := fun u he ↦ ha
    (Finset.mem_image.mpr ⟨_, Finset.mem_range.mpr (Nat.lt_succ_of_le (t.index_le u)), he⟩)
  simp [h]

/-- Exact bin probability, including bins of width zero. -/
theorem law_entry [DecidableEq α] {x : ℕ → α} (hx : Set.InjOn x (Finset.range (n+1)))
    {i : ℕ} (hi : i ≤ n) :
    t.law x (x i) = ((t.cut (i+1) : ℝ) - t.cut i) / 2^w := by
  rw [law_eq_card t]
  have mem (u : Fin (2^w)) : x (t.index u) = x i ↔ u.val ∈ Finset.Ico (t.cut i) (t.cut (i+1)) := by
    rw [Finset.mem_Ico, ← t.index_eq_iff]
    exact ⟨hx (Finset.mem_range.mpr (Nat.lt_succ_of_le (t.index_le u)))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)), congrArg x⟩
  have hc : (Finset.univ.filter (fun u ↦ x (t.index u) = x i)).card =
      (Finset.Ico (t.cut i) (t.cut (i+1))).card := by
    apply Finset.card_bij (fun u _ ↦ u.val)
    · exact fun u hu ↦ (mem u).mp (Finset.mem_filter.mp hu).2
    · exact fun _ _ _ _ h ↦ Fin.ext h
    · intro a ha
      have hh := (Finset.mem_Ico.mp ha).2
      have hb := t.mono (Nat.succ_le_succ hi)
      rw [t.last] at hb
      let u : Fin (2^w) := ⟨a, hh.trans_le hb⟩
      exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem u).mpr ha⟩, rfl⟩
  rw [hc, Nat.card_Ico, Nat.cast_sub (t.mono (Nat.le_succ i))]

/-- Mass in the first j retained entries, before conditioning. -/
def prefixMass (P : α → ℝ) (x : ℕ → α) (j : ℕ) : ℝ := ∑ i ∈ Finset.range j, P (x i)

private theorem variation (e : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ Finset.range (m+1), |e (i+1) - e i| ≤
      |e 0| + 2 * ∑ i ∈ Finset.range m, |e (i+1)| + |e (m+1)| := by
  induction m with
  | zero => simpa [add_comm] using abs_sub (e 1) (e 0)
  | succ m ih =>
    rw [Finset.sum_range_succ _ (m+1), Finset.sum_range_succ (fun i ↦ |e (i+1)|) m]
    linarith [abs_sub (e (m+2)) (e (m+1))]

/-- With a common rescaling of the retained target masses, the endpoint discrepancy and
the change in those masses together cost exactly the omitted mass. -/
private theorem sdist_scaled [DecidableEq α] {P : α → ℝ} (hp : ∀ a, 0 ≤ P a)
    (hs : HasSum P 1) {x : ℕ → α} (hx : Set.InjOn x (Finset.range (n+1))) {g η : ℝ}
    (hg : 1 ≤ g) (hend : g * prefixMass P x (n+1) ≤ 1)
    (herr : ∀ i < n, |(t.cut (i+1) : ℝ) / 2^w - g * prefixMass P x (i+1)| ≤ η) :
    sdist (t.law x) P ≤ n * η + (1 - prefixMass P x (n+1)) := by
  let e (i : ℕ) := (t.cut i : ℝ) / 2^w - g * prefixMass P x i
  have h0 : e 0 = 0 := by simp [e, t.first, prefixMass]
  have hlast : e (n+1) = 1 - g * prefixMass P x (n+1) := by simp [e, t.last]
  have hunif : ∑ i ∈ Finset.range n, |e (i+1)| ≤ n * η := by
    simpa using Finset.sum_le_sum (s := Finset.range n)
      (fun i hi ↦ herr i (Finset.mem_range.mp hi))
  have hv := variation e n
  rw [h0, abs_zero, zero_add, hlast, abs_of_nonneg (sub_nonneg.mpr hend)] at hv
  have hbin : ∀ i ∈ Finset.range (n+1), |t.law x (x i) - P (x i)| ≤
      |e (i+1) - e i| + (g-1) * P (x i) := by
    intro i hi
    rw [t.law_entry hx (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
    have he : ((t.cut (i+1) : ℝ) - t.cut i) / 2^w - P (x i) =
        e (i+1) - e i + (g-1) * P (x i) := by
      simp only [e, prefixMass, Finset.sum_range_succ]
      ring
    rw [he]
    simpa only [abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hg) (hp (x i)))] using
      abs_add_le (e (i+1) - e i) ((g-1) * P (x i))
  have hsum := Finset.sum_le_sum hbin
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hid := sdist_finite_support hp hs (t.law_hasSum x).summable hx (t.law_off x)
  change _ ≤ _ + (g-1) * prefixMass P x (n+1) at hsum
  change _ = _ + (1 - prefixMass P x (n+1)) at hid
  linarith

/-- Lemma 3. If the interior cuts approximate the CDF conditional on the retained support
with error η, SD is at most nη plus the original mass outside that support. -/
theorem sdist_conditional [DecidableEq α] {P : α → ℝ} (hp : ∀ a, 0 ≤ P a)
    (hs : HasSum P 1) {x : ℕ → α} (hx : Set.InjOn x (Finset.range (n+1)))
    (hm : 0 < prefixMass P x (n+1)) {η : ℝ}
    (herr : ∀ i < n, |(t.cut (i+1) : ℝ) / 2^w - prefixMass P x (i+1) / prefixMass P x (n+1)| ≤ η) :
    sdist (t.law x) P ≤ n * η + (1 - prefixMass P x (n+1)) := by
  have hmass : prefixMass P x (n+1) ≤ 1 := sub_nonneg.mp (one_sub_sum_nonneg hp hs hx)
  apply sdist_scaled t hp hs hx (g := 1 / prefixMass P x (n+1))
  · exact (le_div_iff₀ hm).mpr (by simpa using hmass)
  · simp [hm.ne']
  · simpa [div_eq_mul_inv, mul_comm] using herr

/-- One unit of error in each integer cut relative to the raw scaled CDF costs at most
n/2^w plus the omitted mass, even when the last raw prefix is below one. -/
theorem sdist_one_unit [DecidableEq α] {P : α → ℝ} (hp : ∀ a, 0 ≤ P a)
    (hs : HasSum P 1) {x : ℕ → α} (hx : Set.InjOn x (Finset.range (n+1)))
    (herr : ∀ i < n, |(t.cut (i+1) : ℝ) - 2^w * prefixMass P x (i+1)| ≤ 1) :
    sdist (t.law x) P ≤ n * (1 / 2^w) + (1 - prefixMass P x (n+1)) := by
  apply sdist_scaled t hp hs hx (g := 1) le_rfl
  · simpa [prefixMass] using sub_nonneg.mp (one_sub_sum_nonneg hp hs hx)
  · intro i hi
    rw [one_mul, div_sub' (by positivity : (2 : ℝ)^w ≠ 0), abs_div, abs_of_pos (by positivity : 0 < (2 : ℝ)^w)]
    simpa [mul_comm] using div_le_div_of_nonneg_right (herr i hi) (by positivity : 0 ≤ (2 : ℝ)^w)

end CDT
end
end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.CDT.index_eq_iff
#print axioms SigabaNeo.Wall1.CDT.law_hasSum
#print axioms SigabaNeo.Wall1.CDT.law_entry
#print axioms SigabaNeo.Wall1.CDT.sdist_conditional
#print axioms SigabaNeo.Wall1.CDT.sdist_one_unit
