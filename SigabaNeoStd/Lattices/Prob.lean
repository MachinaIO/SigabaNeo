import SigabaNeoStd.Lattices.Gaussian
import CslibFrontier.Crypto.Computational.Basic
/-!
# Expectations over `PMF`s

`ev p f = Σ_a p(a) f(a)` for `f : α → ℝ≥0∞`, its rules (bind, pure, map, monotonicity, linearity,
Fubini, uniform distributions), the `0/1` indicator `ind`, union bounds for the samplers
(`sampleList`, `sampleMat`, `sampleOptList`), and their supports.
-/

namespace SigabaNeo.Lattices

open Cslib.Probability SigabaNeo.Lattices
open scoped ENNReal

/-- The expectation of `f` under `p`. -/
noncomputable def ev {α : Type*} (p : PMF α) (f : α → ℝ≥0∞) : ℝ≥0∞ := ∑' a, p a * f a

open Classical in
/-- The indicator of a proposition. -/
noncomputable def ind (P : Prop) : ℝ≥0∞ := if P then 1 else 0

section
variable {α β : Type*}

theorem ev_bind (p : PMF α) (g : α → PMF β) (f : β → ℝ≥0∞) :
    ev (p.bind g) f = ev p fun a => ev (g a) f := by
  unfold ev
  simp only [PMF.bind_apply, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left, mul_assoc]
  exact ENNReal.tsum_comm

theorem ev_pure (a : α) (f : α → ℝ≥0∞) : ev (PMF.pure a) f = f a := by
  unfold ev
  rw [tsum_eq_single a]
  · simp
  · intro b hb; simp [PMF.pure_apply, hb]

theorem ev_map (p : PMF α) (g : α → β) (f : β → ℝ≥0∞) : ev (p.map g) f = ev p (f ∘ g) := by
  rw [← PMF.bind_pure_comp, ev_bind]
  simp only [Function.comp_apply, ev_pure]
  rfl

theorem ev_mono (p : PMF α) {f g : α → ℝ≥0∞} (h : ∀ a, f a ≤ g a) : ev p f ≤ ev p g :=
  ENNReal.tsum_le_tsum fun a => by gcongr; exact h a

theorem ev_mono_supp (p : PMF α) {f g : α → ℝ≥0∞} (h : ∀ a ∈ p.support, f a ≤ g a) :
    ev p f ≤ ev p g := by
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ p.support
  · gcongr; exact h a ha
  · rw [PMF.mem_support_iff, not_not] at ha; simp [ha]

theorem ev_const (p : PMF α) (c : ℝ≥0∞) : ev p (fun _ => c) = c := by
  unfold ev; rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]

theorem ev_add (p : PMF α) (f g : α → ℝ≥0∞) : ev p (fun a => f a + g a) = ev p f + ev p g := by
  unfold ev; simp only [mul_add]; exact ENNReal.tsum_add

theorem ev_mul_left (p : PMF α) (c : ℝ≥0∞) (f : α → ℝ≥0∞) :
    ev p (fun a => c * f a) = c * ev p f := by
  unfold ev
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun a => by ring

theorem ev_comm (p : PMF α) (q : PMF β) (f : α → β → ℝ≥0∞) :
    ev p (fun a => ev q (f a)) = ev q (fun b => ev p fun a => f a b) := by
  unfold ev
  simp only [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun b => tsum_congr fun a => by ring

theorem ev_le_const (p : PMF α) {f : α → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ a, f a ≤ c) : ev p f ≤ c :=
  (ev_mono p h).trans (ev_const p c).le

theorem ev_uniform [Fintype α] [Nonempty α] (f : α → ℝ≥0∞) :
    ev (PMF.uniformOfFintype α) f = (∑ a, f a) / Fintype.card α := by
  unfold ev
  rw [tsum_fintype, ENNReal.div_eq_inv_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp

theorem ev_uniform_ind [Fintype α] [Nonempty α] (P : α → Prop) [DecidablePred P] :
    ev (PMF.uniformOfFintype α) (fun a => ind (P a)) =
      ((Finset.univ.filter P).card : ℝ≥0∞) / Fintype.card α := by
  classical
  rw [ev_uniform]
  congr 1
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold ind; split_ifs <;> simp

/-! ### Indicators -/

theorem ind_le_one (P : Prop) : ind P ≤ 1 := by unfold ind; split_ifs <;> simp

theorem ind_of_not {P : Prop} (h : ¬ P) : ind P = 0 := by unfold ind; simp [h]

theorem ind_of {P : Prop} (h : P) : ind P = 1 := by unfold ind; simp [h]

theorem ind_mono {P Q : Prop} (h : P → Q) : ind P ≤ ind Q := by
  unfold ind; split_ifs <;> simp_all

theorem ind_or_le (P Q : Prop) : ind (P ∨ Q) ≤ ind P + ind Q := by
  unfold ind; split_ifs <;> simp_all

theorem ind_exists_le {ι : Type*} (s : Finset ι) (P : ι → Prop) :
    ind (∃ i ∈ s, P i) ≤ ∑ i ∈ s, ind (P i) := by
  classical
  by_cases h : ∃ i ∈ s, P i
  · obtain ⟨i, hi, hP⟩ := h
    rw [ind_of ⟨i, hi, hP⟩]
    calc (1 : ℝ≥0∞) = ind (P i) := (ind_of hP).symm
      _ ≤ ∑ i ∈ s, ind (P i) := Finset.single_le_sum (f := fun i => ind (P i))
          (fun _ _ => zero_le) hi
  · rw [ind_of_not h]; exact zero_le

theorem ev_ind_exists_le {ι : Type*} (p : PMF α) (s : Finset ι) (P : ι → α → Prop) :
    ev p (fun a => ind (∃ i ∈ s, P i a)) ≤ ∑ i ∈ s, ev p (fun a => ind (P i a)) := by
  refine (ev_mono p fun a => ind_exists_le s fun i => P i a).trans (le_of_eq ?_)
  unfold ev
  simp only [Finset.mul_sum]
  exact Summable.tsum_finsetSum fun _ _ => ENNReal.summable

/-- The complement: `ev p (ind ¬P) = 1 − ev p (ind P)`, in the form `ev p (ind P) + ev p (ind ¬P) = 1`. -/
theorem ev_ind_add_not (p : PMF α) (P : α → Prop) :
    ev p (fun a => ind (P a)) + ev p (fun a => ind (¬ P a)) = 1 := by
  rw [← ev_add, ← ev_const p 1]
  congr 1; funext a
  unfold ind; split_ifs <;> simp_all

end

/-! ### The samplers -/

section
variable {α : Type}

theorem ev_sampleList_exists (d : PMF α) (bad : α → Prop) {ε : ℝ≥0∞}
    (hd : ev d (fun x => ind (bad x)) ≤ ε) :
    ∀ n, ev (sampleList d n) (fun l => ind (∃ x ∈ l, bad x)) ≤ n * ε
  | 0 => by
    simp only [sampleList, ev_pure, List.not_mem_nil, false_and, exists_false]
    rw [ind_of_not (by simp)]; exact zero_le
  | n + 1 => by
    simp only [sampleList, ev_bind, ev_map]
    calc ev d (fun a => ev (sampleList d n) ((fun l => ind (∃ x ∈ l, bad x)) ∘ (a :: ·)))
        ≤ ev d (fun a => ind (bad a) + ev (sampleList d n) (fun l => ind (∃ x ∈ l, bad x))) := by
          refine ev_mono d fun a => ?_
          calc _ ≤ ev (sampleList d n) (fun l => ind (bad a) + ind (∃ x ∈ l, bad x)) :=
                ev_mono _ fun l => by
                  simp only [Function.comp_apply, List.mem_cons, exists_eq_or_imp]
                  exact ind_or_le _ _
            _ = _ := by rw [ev_add, ev_const]
      _ = ev d (fun a => ind (bad a)) + ev (sampleList d n) (fun l => ind (∃ x ∈ l, bad x)) := by
          rw [ev_add, ev_const]
      _ ≤ ε + n * ε := add_le_add hd (ev_sampleList_exists d bad hd n)
      _ = (n + 1 : ℕ) * ε := by push_cast; ring

theorem ev_sampleMat_exists [Inhabited α] (d : PMF α) (bad : α → Prop) (hdef : ¬ bad default)
    {ε : ℝ≥0∞} (hd : ev d (fun x => ind (bad x)) ≤ ε) (r c : ℕ) :
    ev (sampleMat d r c) (fun M => ind (∃ i j, bad (M i j))) ≤ (r * c : ℕ) * ε := by
  have hm := ev_map (β := Matrix (Fin r) (Fin c) α) (sampleList d (r * c))
    (fun l i j => l.getD (i.val * c + j.val) default) (fun M => ind (∃ i j, bad (M i j)))
  unfold sampleMat
  refine (le_of_eq hm).trans ?_
  refine le_trans (ev_mono _ fun l => ind_mono ?_) (ev_sampleList_exists d bad hd (r * c))
  rintro ⟨i, j, h⟩
  simp only [List.getD_eq_getElem?_getD] at h
  cases hx : l[i.val * c + j.val]? with
  | none => rw [hx] at h; exact absurd h hdef
  | some x => rw [hx] at h; exact ⟨x, List.mem_of_getElem? hx, h⟩

/-- The union bound for `sampleOptList`. -/
theorem ev_sampleOptList_exists (bad : α → Prop) {ε : ℝ≥0∞} :
    ∀ (ds : List (Option (PMF α))), (∀ x ∈ ds, ∀ p, x = some p → ev p (fun a => ind (bad a)) ≤ ε) →
      ev (sampleOptList ds) (fun o => match o with
        | none => 0
        | some l => ind (∃ x ∈ l, bad x)) ≤ ds.length * ε
  | [], _ => by
    simp only [sampleOptList, ev_pure, List.not_mem_nil, false_and, exists_false]
    rw [ind_of_not (by simp)]; exact zero_le
  | none :: _, _ => by simp [sampleOptList, ev_pure]
  | some d :: ds, h => by
    simp only [sampleOptList, ev_bind, ev_map]
    have ih := ev_sampleOptList_exists bad ds fun x hx p hp => h x (List.mem_cons_of_mem _ hx) p hp
    have hd := h (some d) (List.mem_cons_self ..) d rfl
    calc _ ≤ ev d (fun a => ind (bad a) + ev (sampleOptList ds) (fun o => match o with
          | none => 0
          | some l => ind (∃ x ∈ l, bad x))) := by
          refine ev_mono d fun a => ?_
          rw [← ev_const (sampleOptList ds) (ind (bad a)), ← ev_add]
          refine ev_mono _ fun o => ?_
          cases o with
          | none => simp
          | some l =>
            simp only [Function.comp_apply, Option.map_some, List.mem_cons, exists_eq_or_imp]
            exact ind_or_le _ _
      _ = ev d (fun a => ind (bad a)) + _ := by rw [ev_add, ev_const]
      _ ≤ ε + ds.length * ε := add_le_add hd ih
      _ = (some d :: ds).length * ε := by simp; ring

/-- What `sampleOptList` can return. -/
theorem support_sampleOptList :
    ∀ (ds : List (Option (PMF α))) (o : Option (List α)), o ∈ (sampleOptList ds).support →
      match o with
      | none => none ∈ ds
      | some l => List.Forall₂ (fun x od => ∃ p, od = some p ∧ x ∈ p.support) l ds
  | [], o, ho => by
    simp only [sampleOptList, PMF.support_pure, Set.mem_singleton_iff] at ho
    subst ho; exact List.Forall₂.nil
  | none :: _, o, ho => by
    simp only [sampleOptList, PMF.support_pure, Set.mem_singleton_iff] at ho
    subst ho; simp
  | some d :: ds, o, ho => by
    simp only [sampleOptList, PMF.mem_support_bind_iff, PMF.support_map, Set.mem_image] at ho
    obtain ⟨a, ha, o', ho', rfl⟩ := ho
    have ih := support_sampleOptList ds o' ho'
    cases o' with
    | none => simp only [Option.map_none] at ih ⊢; exact List.mem_cons_of_mem _ ih
    | some l => exact List.Forall₂.cons ⟨d, rfl, ha⟩ ih

end

end SigabaNeo.Lattices
