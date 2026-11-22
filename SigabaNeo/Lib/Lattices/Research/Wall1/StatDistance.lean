module

public import SigabaNeo.Lib.Lattices.Research.Wall1.KleinFactorization

/-!
# Statistical-distance calculus (Wall 1, Part 141 §3 and Lemmas 8–9)

General facts about `sdist P Q = ½ ∑' |P - Q|` for probability mass functions on arbitrary
(countable or not) types, as used in the cost side of Part 141
(`docs/research/wall1_sampler_wordram.md`):

* `sdist_finite_support`: if `Q` vanishes off a finite injective list `x 0, …, x (N-1)`, then
  `2·SD(Q, D) = ∑_{i<N} |Q(xᵢ) - D(xᵢ)| + (1 - ∑_{i<N} D(xᵢ))`.
* `sdist_bind_le` (**hybrid / chain rule**): two-step processes `P₁(a) K(a)(b)` and `Q₁(a) L(a)(b)`
  satisfy `SD ≤ SD(P₁, Q₁) + ε` whenever `SD(K a, L a) ≤ ε` for every `a`.
* `seqLaw`, `sdist_seqLaw_le`: an `n`-step sequential sampler whose `m`-th kernel may depend on the
  whole past; replacing every kernel costs at most `∑_m ε_m` (Part 141 Lemma 8's hybrid step).
* `sdist_prod_le`, `sdist_pi_le`: SD of independent products is at most the sum of the SDs.
* `sdist_push_le` (**data processing**): SD does not increase under a deterministic map.
* `prob_le_prob_add_sdist`: `Pr_P[E] ≤ Pr_Q[E] + SD(P, Q)` (Lemma 9's "failure adds SD").
-/

@[expose] public section

namespace SigabaNeo.Wall1

open Real Function

noncomputable section

variable {α β : Type*}

/-! ### Basic facts -/

theorem summable_abs_sub {P Q : α → ℝ} (hP : Summable P) (hQ : Summable Q) :
    Summable (fun a ↦ |P a - Q a|) := (hP.sub hQ).abs

theorem sdist_nonneg (P Q : α → ℝ) : 0 ≤ sdist P Q :=
  mul_nonneg (by norm_num) (tsum_nonneg fun _ ↦ abs_nonneg _)

theorem sdist_comm (P Q : α → ℝ) : sdist P Q = sdist Q P := by
  unfold sdist; simp_rw [abs_sub_comm]

/-- SD is invariant under relabelling by an equivalence. -/
theorem sdist_comp_equiv (e : β ≃ α) (P Q : α → ℝ) :
    sdist (P ∘ e) (Q ∘ e) = sdist P Q := by
  unfold sdist
  exact congrArg _ (e.tsum_eq (fun a ↦ |P a - Q a|))

/-- `∑' |P - Q| ≤ 2` for probability mass functions. -/
theorem tsum_abs_sub_le_two {P Q : α → ℝ} (hP0 : ∀ a, 0 ≤ P a) (hQ0 : ∀ a, 0 ≤ Q a)
    (hP : HasSum P 1) (hQ : HasSum Q 1) : ∑' a, |P a - Q a| ≤ 2 := by
  have h : ∀ a, |P a - Q a| ≤ P a + Q a := fun a ↦ by
    rw [abs_le]; constructor <;> linarith [hP0 a, hQ0 a]
  calc ∑' a, |P a - Q a| ≤ ∑' a, (P a + Q a) :=
        (summable_abs_sub hP.summable hQ.summable).tsum_le_tsum h
          (hP.summable.add hQ.summable)
    _ = 2 := by rw [(hP.add hQ).tsum_eq]; norm_num

theorem sdist_le_one {P Q : α → ℝ} (hP0 : ∀ a, 0 ≤ P a) (hQ0 : ∀ a, 0 ≤ Q a)
    (hP : HasSum P 1) (hQ : HasSum Q 1) : sdist P Q ≤ 1 := by
  have := tsum_abs_sub_le_two hP0 hQ0 hP hQ
  unfold sdist; linarith

/-! ### Finitely supported laws -/

/-- Split a summable function into a finite part and its complement. -/
theorem tsum_eq_sum_add_tsum_compl [DecidableEq α] {g : α → ℝ} (hg : Summable g) (S : Finset α) :
    ∑' a, g a = ∑ a ∈ S, g a + ∑' a, (if a ∈ S then 0 else g a) := by
  classical
  have h1 : Summable (fun a ↦ if a ∈ S then g a else 0) :=
    summable_of_ne_finset_zero (s := S) fun a ha ↦ by simp [ha]
  have h2 : Summable (fun a ↦ if a ∈ S then 0 else g a) := by
    have := hg.sub h1
    refine this.congr fun a ↦ ?_
    by_cases ha : a ∈ S <;> simp [ha]
  have e : ∑' a, g a = ∑' a, ((if a ∈ S then g a else 0) + (if a ∈ S then 0 else g a)) :=
    tsum_congr fun a ↦ by by_cases ha : a ∈ S <;> simp [ha]
  rw [e, h1.tsum_add h2, tsum_eq_sum (s := S) (fun a ha ↦ by simp [ha])]
  congr 1
  exact Finset.sum_congr rfl fun a ha ↦ by simp [ha]

/-- **SD against a finitely supported law.** If `Q` vanishes off `{x i : i < N}` (with `x` injective
there) and `D` is a probability mass function, then
`2·SD(Q, D) = ∑_{i<N} |Q(xᵢ) - D(xᵢ)| + μ`, where `μ = ∑'_{a ∉ S} D a = 1 - ∑_{i<N} D(xᵢ)` is the
mass of `D` off the support. -/
theorem sdist_finite_support [DecidableEq α] {D Q : α → ℝ} (hD0 : ∀ a, 0 ≤ D a)
    (hD : HasSum D 1) (hQs : Summable Q) {x : ℕ → α} {N : ℕ} (hx : Set.InjOn x (Finset.range N))
    (hQ : ∀ a, a ∉ (Finset.range N).image x → Q a = 0) :
    2 * sdist Q D = ∑ i ∈ Finset.range N, |Q (x i) - D (x i)| +
      (1 - ∑ i ∈ Finset.range N, D (x i)) := by
  set S := (Finset.range N).image x
  have hsplit := tsum_eq_sum_add_tsum_compl (summable_abs_sub hQs hD.summable) S
  have hsplitD := tsum_eq_sum_add_tsum_compl hD.summable S
  rw [hD.tsum_eq] at hsplitD
  have e1 : ∑' a, (if a ∈ S then 0 else |Q a - D a|) = ∑' a, (if a ∈ S then 0 else D a) :=
    tsum_congr fun a ↦ by
      by_cases ha : a ∈ S
      · simp [ha]
      · simp [ha, hQ a ha, abs_of_nonneg (hD0 a)]
  have e2 : ∀ g : α → ℝ, ∑ a ∈ S, g a = ∑ i ∈ Finset.range N, g (x i) := fun g ↦
    Finset.sum_image fun i hi j hj h ↦ hx hi hj h
  rw [e2, e1] at hsplit
  rw [e2] at hsplitD
  rw [sdist, ← mul_assoc, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_mul, hsplit]
  linarith

/-- The off-support mass `1 - ∑_{i<N} D(xᵢ)` is nonnegative. -/
theorem one_sub_sum_nonneg [DecidableEq α] {D : α → ℝ} (hD0 : ∀ a, 0 ≤ D a)
    (hD : HasSum D 1) {x : ℕ → α} {N : ℕ} (hx : Set.InjOn x (Finset.range N)) :
    0 ≤ 1 - ∑ i ∈ Finset.range N, D (x i) := by
  have h := tsum_eq_sum_add_tsum_compl hD.summable ((Finset.range N).image x)
  rw [hD.tsum_eq, Finset.sum_image fun i hi j hj h ↦ hx hi hj h] at h
  have : 0 ≤ ∑' a, (if a ∈ (Finset.range N).image x then 0 else D a) :=
    tsum_nonneg fun a ↦ by split_ifs <;> simp [hD0 a]
  linarith

/-- If every point outside the list `x` lies in a set `B`, the off-support mass is at most the
`D`-mass of `B`. -/
theorem one_sub_sum_le_mass [DecidableEq α] {D : α → ℝ} (hD0 : ∀ a, 0 ≤ D a)
    (hD : HasSum D 1) {x : ℕ → α} {N : ℕ} (hx : Set.InjOn x (Finset.range N)) (B : α → Prop)
    [DecidablePred B] (hB : ∀ a, a ∉ (Finset.range N).image x → B a) :
    1 - ∑ i ∈ Finset.range N, D (x i) ≤ ∑' a, (if B a then D a else 0) := by
  have h := tsum_eq_sum_add_tsum_compl hD.summable ((Finset.range N).image x)
  rw [hD.tsum_eq, Finset.sum_image fun i hi j hj h ↦ hx hi hj h] at h
  have hle : ∑' a, (if a ∈ (Finset.range N).image x then 0 else D a) ≤
      ∑' a, (if B a then D a else 0) := by
    refine Summable.tsum_le_tsum (fun a ↦ ?_) ?_ ?_
    · by_cases ha : a ∈ (Finset.range N).image x
      · simp only [ha, ite_true]; split_ifs <;> simp [hD0 a]
      · simp [ha, hB a ha]
    · exact Summable.of_nonneg_of_le (fun a ↦ by split_ifs <;> simp [hD0 a])
        (fun a ↦ by split_ifs <;> simp [hD0 a]) hD.summable
    · exact Summable.of_nonneg_of_le (fun a ↦ by split_ifs <;> simp [hD0 a])
        (fun a ↦ by split_ifs <;> simp [hD0 a]) hD.summable
  linarith

/-! ### Two-step processes (the hybrid argument) -/

/-- **Chain rule / hybrid step.** Let `P₁, Q₁` be probability mass functions on `α` and `K, L`
probability kernels from `α` to `β`. If `SD(K a, L a) ≤ ε` for every `a`, then the joint laws
`P₁(a) K(a)(b)` and `Q₁(a) L(a)(b)` satisfy `SD ≤ SD(P₁, Q₁) + ε`. -/
theorem sdist_bind_le {P₁ Q₁ : α → ℝ} {K L : α → β → ℝ} {ε : ℝ}
    (_hP0 : ∀ a, 0 ≤ P₁ a) (hP : HasSum P₁ 1) (hQ0 : ∀ a, 0 ≤ Q₁ a) (hQ : HasSum Q₁ 1)
    (hK0 : ∀ a b, 0 ≤ K a b) (hK : ∀ a, HasSum (K a) 1)
    (hL0 : ∀ a b, 0 ≤ L a b) (hL : ∀ a, HasSum (L a) 1)
    (hε : ∀ a, sdist (K a) (L a) ≤ ε) :
    sdist (fun p : α × β ↦ P₁ p.1 * K p.1 p.2) (fun p ↦ Q₁ p.1 * L p.1 p.2) ≤
      sdist P₁ Q₁ + ε := by
  set B : α × β → ℝ := fun p ↦ |P₁ p.1 - Q₁ p.1| * K p.1 p.2 + Q₁ p.1 * |K p.1 p.2 - L p.1 p.2|
  set G : α → ℝ := fun a ↦ |P₁ a - Q₁ a| + Q₁ a * ∑' b, |K a b - L a b|
  have hB0 : 0 ≤ B := fun p ↦ add_nonneg (mul_nonneg (abs_nonneg _) (hK0 _ _))
    (mul_nonneg (hQ0 _) (abs_nonneg _))
  have hfib : ∀ a, HasSum (fun b ↦ B (a, b)) (G a) := fun a ↦ by
    have h1 := (hK a).mul_left |P₁ a - Q₁ a|
    have h2 := ((summable_abs_sub (hK a).summable (hL a).summable).hasSum).mul_left (Q₁ a)
    simpa [B, G] using h1.add h2
  have hGle : ∀ a, G a ≤ |P₁ a - Q₁ a| + Q₁ a * (2 * ε) := fun a ↦ by
    have : ∑' b, |K a b - L a b| ≤ 2 * ε := by
      have := hε a; unfold sdist at this; linarith
    have := mul_le_mul_of_nonneg_left this (hQ0 a)
    simp only [G]; linarith
  have hG0 : ∀ a, 0 ≤ G a := fun a ↦ add_nonneg (abs_nonneg _)
    (mul_nonneg (hQ0 a) (tsum_nonneg fun _ ↦ abs_nonneg _))
  have hGs : Summable G := by
    refine Summable.of_nonneg_of_le hG0 (fun a ↦ ?_)
      ((summable_abs_sub hP.summable hQ.summable).add (hQ.summable.mul_left 2))
    have : ∑' b, |K a b - L a b| ≤ 2 :=
      tsum_abs_sub_le_two (hK0 a) (hL0 a) (hK a) (hL a)
    have := mul_le_mul_of_nonneg_left this (hQ0 a)
    simp only [G]; linarith
  have hBs : HasSum B (∑' a, G a) := hasSum_prod_of_nonneg hB0 hfib hGs.hasSum
  have hpt : ∀ p : α × β, |P₁ p.1 * K p.1 p.2 - Q₁ p.1 * L p.1 p.2| ≤ B p := fun p ↦ by
    have e : P₁ p.1 * K p.1 p.2 - Q₁ p.1 * L p.1 p.2 =
        (P₁ p.1 - Q₁ p.1) * K p.1 p.2 + Q₁ p.1 * (K p.1 p.2 - L p.1 p.2) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (hK0 _ _), abs_of_nonneg (hQ0 _)]
  have hDs : Summable (fun p : α × β ↦ |P₁ p.1 * K p.1 p.2 - Q₁ p.1 * L p.1 p.2|) :=
    Summable.of_nonneg_of_le (fun _ ↦ abs_nonneg _) hpt hBs.summable
  have h1 : ∑' p : α × β, |P₁ p.1 * K p.1 p.2 - Q₁ p.1 * L p.1 p.2| ≤ ∑' a, G a :=
    hDs.tsum_le_tsum hpt hBs.summable |>.trans_eq hBs.tsum_eq
  have h2 : ∑' a, G a ≤ ∑' a, |P₁ a - Q₁ a| + 2 * ε := by
    calc ∑' a, G a ≤ ∑' a, (|P₁ a - Q₁ a| + Q₁ a * (2 * ε)) :=
          hGs.tsum_le_tsum hGle ((summable_abs_sub hP.summable hQ.summable).add
            (hQ.summable.mul_right _))
      _ = ∑' a, |P₁ a - Q₁ a| + 2 * ε := by
          rw [(summable_abs_sub hP.summable hQ.summable).tsum_add (hQ.summable.mul_right _),
            tsum_mul_right, hQ.tsum_eq, one_mul]
  unfold sdist
  linarith

/-- The joint law of a two-step process is a probability mass function. -/
theorem hasSum_bind {P₁ : α → ℝ} {K : α → β → ℝ} (hP0 : ∀ a, 0 ≤ P₁ a) (hP : HasSum P₁ 1)
    (hK0 : ∀ a b, 0 ≤ K a b) (hK : ∀ a, HasSum (K a) 1) :
    HasSum (fun p : α × β ↦ P₁ p.1 * K p.1 p.2) 1 :=
  hasSum_prod_of_nonneg (fun p ↦ mul_nonneg (hP0 _) (hK0 _ _))
    (fun a ↦ by simpa using (hK a).mul_left (P₁ a)) hP

/-- **Products.** `SD(P₁ ⊗ P₂, Q₁ ⊗ Q₂) ≤ SD(P₁, Q₁) + SD(P₂, Q₂)`. -/
theorem sdist_prod_le {P₁ Q₁ : α → ℝ} {P₂ Q₂ : β → ℝ}
    (hP0 : ∀ a, 0 ≤ P₁ a) (hP : HasSum P₁ 1) (hQ0 : ∀ a, 0 ≤ Q₁ a) (hQ : HasSum Q₁ 1)
    (hP0' : ∀ b, 0 ≤ P₂ b) (hP' : HasSum P₂ 1) (hQ0' : ∀ b, 0 ≤ Q₂ b) (hQ' : HasSum Q₂ 1) :
    sdist (fun p : α × β ↦ P₁ p.1 * P₂ p.2) (fun p ↦ Q₁ p.1 * Q₂ p.2) ≤
      sdist P₁ Q₁ + sdist P₂ Q₂ :=
  sdist_bind_le (K := fun _ ↦ P₂) (L := fun _ ↦ Q₂) hP0 hP hQ0 hQ (fun _ ↦ hP0') (fun _ ↦ hP')
    (fun _ ↦ hQ0') (fun _ ↦ hQ') (fun _ ↦ le_rfl)

/-! ### Sequential samplers -/

/-- `(Fin n → β) × β ≃ (Fin (n+1) → β)` by appending the last coordinate. -/
def snocEquiv' (β : Type*) (n : ℕ) : (Fin n → β) × β ≃ (Fin (n + 1) → β) where
  toFun p := Fin.snoc p.1 p.2
  invFun x := (Fin.init x, x (Fin.last n))
  left_inv p := by simp
  right_inv x := by simp

/-- The law of an `n`-step sequential sampler: coordinate `m` is drawn from the kernel
`k m (past)` where `past : Fin m → β` is the vector of the earlier coordinates. -/
def seqLaw (k : (m : ℕ) → (Fin m → β) → β → ℝ) : (n : ℕ) → (Fin n → β) → ℝ
  | 0, _ => 1
  | n + 1, x => seqLaw k n (Fin.init x) * k n (Fin.init x) (x (Fin.last n))

theorem seqLaw_snoc (k : (m : ℕ) → (Fin m → β) → β → ℝ) (n : ℕ) (p : (Fin n → β) × β) :
    seqLaw k (n + 1) (snocEquiv' β n p) = seqLaw k n p.1 * k n p.1 p.2 := by
  simp [seqLaw, snocEquiv']

theorem seqLaw_nonneg {k : (m : ℕ) → (Fin m → β) → β → ℝ} (hk0 : ∀ m p b, 0 ≤ k m p b) :
    ∀ n x, 0 ≤ seqLaw k n x
  | 0, _ => zero_le_one
  | n + 1, _ => mul_nonneg (seqLaw_nonneg hk0 n _) (hk0 _ _ _)

theorem seqLaw_hasSum {k : (m : ℕ) → (Fin m → β) → β → ℝ} (hk0 : ∀ m p b, 0 ≤ k m p b)
    (hk : ∀ m p, HasSum (k m p) 1) : ∀ n, HasSum (seqLaw k n) 1
  | 0 => by simp [seqLaw]
  | n + 1 => by
    rw [← (snocEquiv' β n).hasSum_iff]
    have := hasSum_bind (seqLaw_nonneg hk0 n) (seqLaw_hasSum hk0 hk n) (hk0 n) (hk n)
    simpa only [Function.comp_def, seqLaw_snoc] using this

/-- **Sequential hybrid bound** (Part 141 Lemma 8). If at every step `m < n` and for every past
`p` the kernels satisfy `SD(k m p, l m p) ≤ ε m`, then the two `n`-step samplers satisfy
`SD ≤ ∑_{m<n} ε m`. -/
theorem sdist_seqLaw_le {k l : (m : ℕ) → (Fin m → β) → β → ℝ} {ε : ℕ → ℝ}
    (hk0 : ∀ m p b, 0 ≤ k m p b) (hk : ∀ m p, HasSum (k m p) 1)
    (hl0 : ∀ m p b, 0 ≤ l m p b) (hl : ∀ m p, HasSum (l m p) 1)
    (hε : ∀ m p, sdist (k m p) (l m p) ≤ ε m) :
    ∀ n, sdist (seqLaw k n) (seqLaw l n) ≤ ∑ m ∈ Finset.range n, ε m
  | 0 => by simp [sdist, seqLaw]
  | n + 1 => by
    rw [← sdist_comp_equiv (snocEquiv' β n), Finset.sum_range_succ]
    have h := sdist_bind_le (seqLaw_nonneg hk0 n) (seqLaw_hasSum hk0 hk n)
      (seqLaw_nonneg hl0 n) (seqLaw_hasSum hl0 hl n) (hk0 n) (hk n) (hl0 n) (hl n) (hε n)
    have ih := sdist_seqLaw_le hk0 hk hl0 hl hε n
    simp only [Function.comp_def, seqLaw_snoc]
    linarith

/-- Independent coordinates are the special case of kernels that ignore the past. -/
theorem seqLaw_const (P : ℕ → β → ℝ) :
    ∀ n (x : Fin n → β), seqLaw (fun m _ ↦ P m) n x = ∏ i : Fin n, P i (x i)
  | 0, _ => by simp [seqLaw]
  | n + 1, x => by
    rw [seqLaw, seqLaw_const P n, Fin.prod_univ_castSucc]
    simp [Fin.init]

/-- **Independent products.** `SD(⊗ᵢ Pᵢ, ⊗ᵢ Qᵢ) ≤ ∑ᵢ SD(Pᵢ, Qᵢ)`. -/
theorem sdist_pi_le {P Q : ℕ → β → ℝ} (hP0 : ∀ m b, 0 ≤ P m b) (hP : ∀ m, HasSum (P m) 1)
    (hQ0 : ∀ m b, 0 ≤ Q m b) (hQ : ∀ m, HasSum (Q m) 1) (n : ℕ) :
    sdist (fun x : Fin n → β ↦ ∏ i : Fin n, P i (x i)) (fun x ↦ ∏ i : Fin n, Q i (x i)) ≤
      ∑ m ∈ Finset.range n, sdist (P m) (Q m) := by
  have := sdist_seqLaw_le (k := fun m _ ↦ P m) (l := fun m _ ↦ Q m) (ε := fun m ↦ sdist (P m) (Q m))
    (fun m _ ↦ hP0 m) (fun m _ ↦ hP m) (fun m _ ↦ hQ0 m) (fun m _ ↦ hQ m) (fun _ _ ↦ le_rfl) n
  simpa only [show seqLaw (fun m _ ↦ P m) n = _ from funext (seqLaw_const P n),
    show seqLaw (fun m _ ↦ Q m) n = _ from funext (seqLaw_const Q n)] using this

/-! ### Data processing -/

/-- The law of `f(X)` when `X ∼ P`. -/
def push (f : α → β) (P : α → ℝ) (b : β) : ℝ := by
  classical exact ∑' a, if f a = b then P a else 0

/-- Fiberwise summation along a map. -/
theorem hasSum_push_fiber [DecidableEq β] (f : α → β) {g : α → ℝ} (hg0 : ∀ a, 0 ≤ g a) (hg : Summable g) :
    HasSum (fun b ↦ ∑' a, (if f a = b then g a else 0 : ℝ)) (∑' a, g a) := by
  classical
  set F : α × β → ℝ := fun p ↦ if f p.1 = p.2 then g p.1 else 0
  have hF0 : 0 ≤ F := fun p ↦ by simp only [F]; split_ifs <;> simp [hg0]
  have hfib : ∀ a, HasSum (fun b ↦ F (a, b)) (g a) := fun a ↦ by
    simpa [F, eq_comm] using hasSum_ite_eq (f a) (g a)
  have hF : HasSum F (∑' a, g a) := hasSum_prod_of_nonneg hF0 hfib hg.hasSum
  have hF' : HasSum (F ∘ Equiv.prodComm β α) (∑' a, g a) := (Equiv.hasSum_iff _).mpr hF
  have hsl : ∀ b, Summable (fun a ↦ (F ∘ Equiv.prodComm β α) (b, a)) :=
    ((summable_prod_of_nonneg (fun (p : β × α) ↦ hF0 (Equiv.prodComm β α p))).1 hF'.summable).1
  exact hF'.prod_fiberwise fun b ↦ (hsl b).hasSum

theorem push_nonneg (f : α → β) {P : α → ℝ} (hP0 : ∀ a, 0 ≤ P a) (b : β) : 0 ≤ push f P b := by
  classical
  unfold push; exact tsum_nonneg fun a ↦ by split_ifs <;> simp [hP0]

theorem push_hasSum (f : α → β) {P : α → ℝ} (hP0 : ∀ a, 0 ≤ P a) (hP : HasSum P 1) :
    HasSum (push f P) 1 := by
  classical
  have := hasSum_push_fiber f hP0 hP.summable
  rw [hP.tsum_eq] at this
  exact this

/-- **Data-processing inequality.** `SD(f(X), f(Y)) ≤ SD(X, Y)` for any deterministic map `f`. -/
theorem sdist_push_le (f : α → β) {P Q : α → ℝ} (hP0 : ∀ a, 0 ≤ P a) (hP : Summable P)
    (hQ0 : ∀ a, 0 ≤ Q a) (hQ : Summable Q) : sdist (push f P) (push f Q) ≤ sdist P Q := by
  classical
  have hAbs := summable_abs_sub hP hQ
  have hfib := hasSum_push_fiber f (fun a ↦ abs_nonneg (P a - Q a)) hAbs
  have hsP : ∀ b, Summable (fun a ↦ if f a = b then P a else 0) := fun b ↦
    Summable.of_nonneg_of_le (fun a ↦ by split_ifs <;> simp [hP0]) (fun a ↦ by
      split_ifs <;> simp [hP0]) hP
  have hsQ : ∀ b, Summable (fun a ↦ if f a = b then Q a else 0) := fun b ↦
    Summable.of_nonneg_of_le (fun a ↦ by split_ifs <;> simp [hQ0]) (fun a ↦ by
      split_ifs <;> simp [hQ0]) hQ
  have hpt : ∀ b, |push f P b - push f Q b| ≤
      ∑' a, (if f a = b then |P a - Q a| else 0) := fun b ↦ by
    unfold push
    rw [← (hsP b).tsum_sub (hsQ b)]
    have hb := norm_tsum_le_tsum_norm (((hsP b).sub (hsQ b)).norm)
    simp only [Real.norm_eq_abs] at hb
    refine hb.trans_eq (tsum_congr fun a ↦ ?_)
    split_ifs <;> simp
  have hs : Summable (fun b ↦ |push f P b - push f Q b|) :=
    Summable.of_nonneg_of_le (fun _ ↦ abs_nonneg _) hpt hfib.summable
  unfold sdist
  gcongr
  exact (hs.tsum_le_tsum hpt hfib.summable).trans_eq hfib.tsum_eq

/-! ### Events -/

/-- **Failure probability transfers through SD.** For probability mass functions `P, Q` and any
event `E`, `Pr_P[E] ≤ Pr_Q[E] + SD(P, Q)`. -/
theorem prob_le_prob_add_sdist {P Q : α → ℝ} (hP0 : ∀ a, 0 ≤ P a) (hP : HasSum P 1)
    (hQ0 : ∀ a, 0 ≤ Q a) (hQ : HasSum Q 1) (E : α → Prop) [DecidablePred E] :
    ∑' a, (if E a then P a else 0) ≤ ∑' a, (if E a then Q a else 0) + sdist P Q := by
  have sE : ∀ R : α → ℝ, (∀ a, 0 ≤ R a) → Summable R → Summable (fun a ↦ if E a then R a else 0) :=
    fun R h0 hs ↦ Summable.of_nonneg_of_le (fun a ↦ by split_ifs <;> simp [h0])
      (fun a ↦ by split_ifs <;> simp [h0]) hs
  have sN : ∀ R : α → ℝ, (∀ a, 0 ≤ R a) → Summable R →
      Summable (fun a ↦ if E a then 0 else R a) :=
    fun R h0 hs ↦ Summable.of_nonneg_of_le (fun a ↦ by split_ifs <;> simp [h0])
      (fun a ↦ by split_ifs <;> simp [h0]) hs
  have split : ∀ R : α → ℝ, (∀ a, 0 ≤ R a) → HasSum R 1 →
      ∑' a, (if E a then R a else 0) + ∑' a, (if E a then 0 else R a) = 1 := fun R h0 hR ↦ by
    rw [← (sE R h0 hR.summable).tsum_add (sN R h0 hR.summable), ← hR.tsum_eq]
    exact tsum_congr fun a ↦ by split_ifs <;> simp
  have hA := summable_abs_sub hP.summable hQ.summable
  have h1 : ∑' a, (if E a then P a else 0) - ∑' a, (if E a then Q a else 0) ≤
      ∑' a, (if E a then |P a - Q a| else 0) := by
    rw [← (sE P hP0 hP.summable).tsum_sub (sE Q hQ0 hQ.summable)]
    refine ((sE P hP0 hP.summable).sub (sE Q hQ0 hQ.summable)).tsum_le_tsum (fun a ↦ ?_)
      (sE _ (fun _ ↦ abs_nonneg _) hA)
    split_ifs
    · exact le_abs_self _
    · simp
  have h2 : ∑' a, (if E a then 0 else Q a) - ∑' a, (if E a then 0 else P a) ≤
      ∑' a, (if E a then 0 else |P a - Q a|) := by
    rw [← (sN Q hQ0 hQ.summable).tsum_sub (sN P hP0 hP.summable)]
    refine ((sN Q hQ0 hQ.summable).sub (sN P hP0 hP.summable)).tsum_le_tsum (fun a ↦ ?_)
      (sN _ (fun _ ↦ abs_nonneg _) hA)
    split_ifs
    · simp
    · rw [abs_sub_comm]; exact le_abs_self _
  have h3 : ∑' a, (if E a then |P a - Q a| else 0) + ∑' a, (if E a then 0 else |P a - Q a|) =
      ∑' a, |P a - Q a| := by
    rw [← (sE _ (fun _ ↦ abs_nonneg _) hA).tsum_add (sN _ (fun _ ↦ abs_nonneg _) hA)]
    exact tsum_congr fun a ↦ by split_ifs <;> simp
  have hp := split P hP0 hP
  have hq := split Q hQ0 hQ
  unfold sdist
  linarith

end

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.sdist_nonneg
#print axioms SigabaNeo.Wall1.sdist_comm
#print axioms SigabaNeo.Wall1.sdist_le_one
#print axioms SigabaNeo.Wall1.sdist_finite_support
#print axioms SigabaNeo.Wall1.sdist_bind_le
#print axioms SigabaNeo.Wall1.sdist_prod_le
#print axioms SigabaNeo.Wall1.sdist_seqLaw_le
#print axioms SigabaNeo.Wall1.sdist_pi_le
#print axioms SigabaNeo.Wall1.sdist_push_le
#print axioms SigabaNeo.Wall1.prob_le_prob_add_sdist
