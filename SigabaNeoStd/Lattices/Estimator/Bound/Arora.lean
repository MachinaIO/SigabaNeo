import SigabaNeoStd.Lattices.Estimator.Bound.Primal

/-!
# Arora–Gröbner at a large dimension

`AroraGB.gb n d m s` computes the coefficients of the Hilbert series
`(1 − z^d)^m (1 − z^s)^n / (1 − z)^n` by their logarithmic derivative, keeping the sums of the
earlier coefficients per residue class mod `d` and mod `s`, and returns `2 log₂ C(n+k, k)` at the
first negative coefficient `k`. For a large `n`, the first coefficients grow by a factor `R` at
each step: the class sum read at step `k` was last updated `d − 1` steps earlier, so it is
`R^{d−1}` times smaller than the newest coefficient (`gb_ge`). Hence no negative coefficient comes
before `K₀`, and the cost is at least `2 log₂ C(n + K₀ + 1, K₀ + 1)`.
-/

namespace SigabaNeo.Lattices.Estimator

open Fx

/-! ### Ages of residue classes -/

/-- Before step `k`, the number of steps since the class `r` (mod `d`) was last updated. -/
def AroraGB.age (d k r : ℕ) : ℕ := (k + d - 2 - r) % d + 1

theorem AroraGB.age_read {d k : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k) : AroraGB.age d k (k % d) = d - 1 := by
  unfold AroraGB.age
  have h1 := Nat.div_add_mod k d
  have h2 := Nat.mod_lt k (by omega : 0 < d)
  have : k + d - 2 - k % d = d * (k / d) + (d - 2) := by omega
  rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]; omega

theorem AroraGB.age_upd {d k : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k) :
    AroraGB.age d k ((k - 1) % d) = d ∧ AroraGB.age d (k + 1) ((k - 1) % d) = 1 := by
  unfold AroraGB.age
  have h1 := Nat.div_add_mod (k - 1) d
  have h2 := Nat.mod_lt (k - 1) (by omega : 0 < d)
  constructor
  · have : k + d - 2 - (k - 1) % d = d * ((k - 1) / d) + (d - 1) := by omega
    rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]; omega
  · have : k + 1 + d - 2 - (k - 1) % d = d * ((k - 1) / d + 1) := by rw [mul_add]; omega
    rw [this, Nat.mul_mod_right]

theorem AroraGB.age_succ {d k r : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k) (hr : r < d) (hrc : r ≠ (k - 1) % d) :
    AroraGB.age d (k + 1) r = AroraGB.age d k r + 1 := by
  unfold AroraGB.age
  have h1 := Nat.div_add_mod (k - 1) d
  have h2 := Nat.mod_lt (k - 1) (by omega : 0 < d)
  set c := (k - 1) % d
  set q := (k - 1) / d
  rcases lt_or_gt_of_ne hrc with h | h
  · -- r < c
    have e1 : k + d - 2 - r = d * (q + 1) + (c - r - 1) := by rw [mul_add]; omega
    have e2 : k + 1 + d - 2 - r = d * (q + 1) + (c - r) := by rw [mul_add]; omega
    rw [e1, e2, Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]; omega
  · -- r > c
    have e1 : k + d - 2 - r = d * q + (c + d - 1 - r) := by omega
    have e2 : k + 1 + d - 2 - r = d * q + (c + d - r) := by omega
    rw [e1, e2, Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]; omega

/-! ### Arrays -/

theorem AroraGB.getElem!_eq (a : Array ℤ) (j : ℕ) : a[j]! = (a[j]?).getD 0 := by
  rw [getElem!_def]; cases a[j]? <;> rfl

theorem AroraGB.getElem!_modify (a : Array ℤ) (i j : ℕ) (f : ℤ → ℤ) :
    (a.modify i f)[j]! = if i = j ∧ j < a.size then f a[j]! else a[j]! := by
  rw [getElem!_eq, getElem!_eq, Array.getElem?_modify]
  by_cases h : i = j
  · subst h
    by_cases hj : i < a.size
    · simp [hj]
    · simp [hj]
  · simp [h]

theorem AroraGB.getElem!_oob (a : Array ℤ) {j : ℕ} (h : a.size ≤ j) : a[j]! = 0 := by
  rw [getElem!_eq, Array.getElem?_eq_none h]; rfl

/-- The bound kept on a residue array before step `k`. -/
def AroraGB.ArrOK (R : ℤ) (d k : ℕ) (arr : Array ℤ) (a : ℤ) : Prop :=
  ∀ r < arr.size, 0 ≤ arr[r]! ∧ arr[r]! * R ^ AroraGB.age d k r ≤ 2 * a

theorem AroraGB.mod_ne {d k : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k) : k % d ≠ (k - 1) % d := by
  intro h
  have := Nat.sub_mod_eq_zero_of_mod_eq h
  rw [show k - (k - 1) = 1 by omega, Nat.mod_eq_of_lt (by omega)] at this
  omega

/-- Reading the class of step `k` after the update: it is `R^{d−1}` times smaller. -/
theorem AroraGB.arr_read {R : ℤ} {d k : ℕ} {arr : Array ℤ} {a : ℤ} (hd : 2 ≤ d) (hk : 1 ≤ k)
    (ha : 0 ≤ a) (h : ArrOK R d k arr a) :
    0 ≤ (arr.modify ((k - 1) % d) (· + a))[k % d]! ∧
      (arr.modify ((k - 1) % d) (· + a))[k % d]! * R ^ (d - 1) ≤ 2 * a := by
  rw [getElem!_modify]
  have hne := mod_ne hd hk
  have hnc : ¬ ((k - 1) % d = k % d ∧ k % d < arr.size) := fun h' => hne h'.1.symm
  simp only [hnc, ↓reduceIte]
  by_cases hs : k % d < arr.size
  · have := h (k % d) hs; rwa [age_read hd hk] at this
  · rw [getElem!_oob arr (by omega)]; simp; omega

/-- The bound is kept by the update at step `k`. -/
theorem AroraGB.arr_next {R : ℤ} {d k : ℕ} {arr : Array ℤ} {a a' : ℤ} (hd : 2 ≤ d) (hk : 1 ≤ k)
    (hsz : arr.size ≤ d) (hR : 2 ≤ R) (ha : 1 ≤ a) (ha' : R * a ≤ a') (h : ArrOK R d k arr a) :
    ArrOK R d (k + 1) (arr.modify ((k - 1) % d) (· + a)) a' := by
  intro r hr
  rw [Array.size_modify] at hr
  have hR0 : (0 : ℤ) < R := by omega
  rw [getElem!_modify]
  split
  · rename_i hc
    obtain ⟨hc1, -⟩ := hc
    subst hc1
    obtain ⟨h0, h1⟩ := h _ hr
    rw [(age_upd hd hk).1] at h1
    rw [(age_upd hd hk).2, pow_one]
    have hpow : (2 : ℤ) ≤ R ^ (d - 1) := by
      calc (2 : ℤ) ≤ R := hR
        _ = R ^ 1 := (pow_one R).symm
        _ ≤ R ^ (d - 1) := pow_le_pow_right₀ (by omega) (by omega)
    have e : R ^ d = R * R ^ (d - 1) := by rw [← pow_succ']; congr 1; omega
    rw [e] at h1
    have hpos : (0 : ℤ) < R ^ (d - 1) := by positivity
    have h2 : arr[(k - 1) % d]! * R ≤ a := by
      by_contra hc; push Not at hc
      have : a * R ^ (d - 1) < arr[(k - 1) % d]! * R * R ^ (d - 1) :=
        Int.mul_lt_mul_of_pos_right hc hpos
      nlinarith
    constructor
    · linarith
    · nlinarith
  · rename_i hc
    have hrc : r ≠ (k - 1) % d := fun h' => hc ⟨h'.symm, hr⟩
    obtain ⟨h0, h1⟩ := h r hr
    refine ⟨h0, ?_⟩
    rw [age_succ hd hk (by omega) hrc, pow_succ]
    nlinarith

/-- Induction along `List.range'` for a loop that may stop early. -/
theorem forIn_range'_ind2 {β : Type} (s n : ℕ) (b : β) (f : ℕ → β → Id (ForInStep β))
    (I : ℕ → β → Prop) (Q : β → Prop) (h0 : I s b)
    (hf : ∀ i, s ≤ i → i < s + n → ∀ x, I i x →
      (∃ y, f i x = ForInStep.yield y ∧ I (i + 1) y) ∨ (∃ y, f i x = ForInStep.done y ∧ Q y)) :
    I (s + n) (forIn (m := Id) (List.range' s n) b f) ∨ Q (forIn (m := Id) (List.range' s n) b f) := by
  induction n generalizing s b with
  | zero => exact Or.inl h0
  | succ n ih =>
    rw [List.range'_succ, List.forIn_cons]
    rcases hf s le_rfl (by omega) b h0 with ⟨y, hy, hI⟩ | ⟨y, hy, hQ⟩
    · rw [hy]
      have := ih (s + 1) y hI (fun i h1 h2 => hf i (by omega) (by omega))
      rwa [show s + 1 + n = s + (n + 1) by omega] at this
    · rw [hy]; exact Or.inr hQ

/-- The bound kept by `gb` before step `k` (while `k ≤ K₀ + 1`). -/
def AroraGB.Num (R : ℤ) (n d s k : ℕ) (err sec : Array ℤ) (sum a : ℤ) : Prop :=
  1 ≤ a ∧ 0 ≤ sum ∧ err.size = min d (2 * n) ∧ sec.size = min s (2 * n) ∧
    ArrOK R d k err a ∧ (0 < s → ArrOK R s k sec a)

theorem choose_le_choose_succ_add (n k : ℕ) : (n + k).choose k ≤ (n + (k + 1)).choose (k + 1) := by
  rw [show n + (k + 1) = (n + k) + 1 by ring, Nat.choose_succ_succ]; omega

theorem choose_mono_k (n : ℕ) {k j : ℕ} (h : k ≤ j) : (n + k).choose k ≤ (n + j).choose j := by
  induction j with
  | zero => have : k = 0 := by omega
            subst this; rfl
  | succ j ih =>
    rcases Nat.lt_or_ge k (j + 1) with h' | h'
    · exact (ih (by omega)).trans (choose_le_choose_succ_add n j)
    · have : k = j + 1 := by omega
      subst this; rfl

/-- **No early negative coefficient.** With a growth factor `R` per step, `gb` does not stop before
step `K₀ + 1`, so it costs at least `2 log₂ C(n + K₀ + 1, K₀ + 1)`. -/
theorem AroraGB.gb_ge {n d m s K₀ R : ℕ} (hd : 2 ≤ d) (hs : s = 0 ∨ 2 ≤ s) (hR : 2 ≤ R)
    (hn : 2 * (K₀ + 1) * (R + 1) ≤ n) (hmd : 8 * m * d ≤ n * R ^ (d - 1))
    (hss : 0 < s → 8 * s ≤ R ^ (s - 1)) :
    CostGe (2 * log2Nat ((n + (K₀ + 1)).choose (K₀ + 1))) (AroraGB.gb n d m s) := by
  unfold gb
  simp only [Id.run_bind]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one]
  set Q : Option (Option Fx) × Array ℤ × Array ℤ × ℤ × ℤ → Prop := fun st =>
    ∃ j, K₀ < j ∧ st.1 = some (some (2 * log2Nat ((n + j).choose j))) with hQ
  set I : ℕ → Option (Option Fx) × Array ℤ × Array ℤ × ℤ × ℤ → Prop := fun k st =>
    st.1 = none ∧ (k ≤ K₀ + 1 → Num (R : ℤ) n d s k st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2) with hI
  generalize hr : (forIn (m := Id) (List.range' 1 (2 * n - 1))
    ((none : Option (Option Fx)), Array.replicate (min d (2 * n)) (0 : ℤ),
      Array.replicate (min s (2 * n)) (0 : ℤ), (0 : ℤ), (1 : ℤ)) _ :
    Id (Option (Option Fx) × Array ℤ × Array ℤ × ℤ × ℤ)) = r
  have key : I (1 + (2 * n - 1)) r ∨ Q r := by
    rw [← hr]
    refine forIn_range'_ind2 1 (2 * n - 1) _ _ I Q ?_ ?_
    · refine ⟨rfl, fun _ => ⟨le_rfl, le_rfl, by simp, by simp, ?_, ?_⟩⟩
      · intro r hr; simp at hr; simp [hr]
      · intro _ r hr; simp at hr; simp [hr]
    · intro k hk1 hk2 st ⟨hret, hnum⟩
      have hk2' : k < 2 * n := by omega
      by_cases hkK : k ≤ K₀
      · obtain ⟨ha, hsum, hesz, hssz, herr, hsec⟩ := hnum (by omega)
        obtain ⟨hE0, hE⟩ := arr_read (R := (R : ℤ)) hd hk1 (by omega) herr
        have hRz : (2 : ℤ) ≤ R := by exact_mod_cast hR
        have hmd' : (8 * m * d : ℤ) ≤ n * (R : ℤ) ^ (d - 1) := by exact_mod_cast hmd
        have hn' : (2 * (k + 1) * (R + 1) : ℤ) ≤ n := by
          have : 2 * (k + 1) * (R + 1) ≤ 2 * (K₀ + 1) * (R + 1) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
          exact_mod_cast this.trans hn
        have h1 : 4 * (m * d * (st.2.1.modify ((k - 1) % d) (· + st.2.2.2.2))[k % d]!) ≤
            (n : ℤ) * st.2.2.2.2 := by
          have hn0 : (0 : ℤ) ≤ n := by positivity
          nlinarith [mul_le_mul_of_nonneg_right hmd' hE0, mul_le_mul_of_nonneg_left hE hn0]
        have hgrow : ∀ X : ℤ, 0 ≤ X → 4 * ((n : ℤ) * X) ≤ (n : ℤ) * st.2.2.2.2 →
            (R : ℤ) * st.2.2.2.2 * k ≤ n * (st.2.2.2.1 + st.2.2.2.2) -
              m * d * (st.2.1.modify ((k - 1) % d) (· + st.2.2.2.2))[k % d]! - (n * X) := by
          intro X hX0 hX
          have hk0 : (0 : ℤ) ≤ k := by positivity
          nlinarith [mul_le_mul_of_nonneg_right hn' (show (0 : ℤ) ≤ st.2.2.2.2 by omega)]
        have hnext : ∀ v : ℤ, (R : ℤ) * st.2.2.2.2 * k ≤ v → (R : ℤ) * st.2.2.2.2 ≤ v / k := by
          intro v hv
          rw [Int.le_ediv_iff_mul_le (by exact_mod_cast (show 0 < k by omega))]; exact hv
        have hRa : 2 ≤ (R : ℤ) * st.2.2.2.2 := by nlinarith
        split
        · rename_i hspos
          have hs2 : 2 ≤ s := by rcases hs with h | h <;> omega
          obtain ⟨hS0, hS⟩ := arr_read (R := (R : ℤ)) hs2 hk1 (by omega) (hsec hspos)
          have hss' : (8 * s : ℤ) ≤ (R : ℤ) ^ (s - 1) := by exact_mod_cast hss hspos
          have h2 : 4 * ((n : ℤ) * (s * (st.2.2.1.modify ((k - 1) % s) (· + st.2.2.2.2))[k % s]!)) ≤
              (n : ℤ) * st.2.2.2.2 := by
            have hn0 : (0 : ℤ) ≤ n := by positivity
            have : 4 * (s * (st.2.2.1.modify ((k - 1) % s) (· + st.2.2.2.2))[k % s]!) ≤
                st.2.2.2.2 := by nlinarith [mul_le_mul_of_nonneg_right hss' hS0]
            nlinarith
          have hv := hnext _ (hgrow _ (by positivity) h2)
          have hlt : ¬ ((n * (st.2.2.2.1 + st.2.2.2.2) -
              m * d * (st.2.1.modify ((k - 1) % d) (· + st.2.2.2.2))[k % d]! -
              n * s * (st.2.2.1.modify ((k - 1) % s) (· + st.2.2.2.2))[k % s]!) / (k : ℤ) < 0) := by
            rw [mul_assoc (n : ℤ) s]; linarith
          simp only [hlt, ↓reduceIte]
          left
          refine ⟨_, rfl, rfl, fun _ => ⟨by rw [mul_assoc (n : ℤ) s]; linarith, by linarith, by simp [hesz],
            by simp [hssz], ?_, fun _ => ?_⟩⟩
          · exact arr_next hd hk1 (by rw [hesz]; exact min_le_left _ _) hRz ha
              (by rw [mul_assoc (n : ℤ) s]; exact hv) herr
          · exact arr_next hs2 hk1 (by rw [hssz]; exact min_le_left _ _) hRz ha
              (by rw [mul_assoc (n : ℤ) s]; exact hv) (hsec hspos)
        · rename_i hspos
          have hv := hnext _ (hgrow 0 le_rfl (by simp; nlinarith))
          simp only [mul_zero, sub_zero] at hv
          have hlt : ¬ ((n * (st.2.2.2.1 + st.2.2.2.2) -
              m * d * (st.2.1.modify ((k - 1) % d) (· + st.2.2.2.2))[k % d]!) / (k : ℤ) < 0) := by
            linarith
          simp only [hlt, ↓reduceIte]
          left
          refine ⟨_, rfl, rfl, fun _ => ⟨by linarith, by linarith, by simp [hesz], hssz, ?_,
            fun h => absurd h hspos⟩⟩
          exact arr_next hd hk1 (by rw [hesz]; exact min_le_left _ _) hRz ha hv herr
      · -- past `K₀`: a stop is a cost with `k > K₀`
        split <;> split
        · right; exact ⟨_, rfl, k, by omega, rfl⟩
        · left; exact ⟨_, rfl, rfl, fun h => absurd h (by omega)⟩
        · right; exact ⟨_, rfl, k, by omega, rfl⟩
        · left; exact ⟨_, rfl, rfl, fun h => absurd h (by omega)⟩
  have hmono : ∀ j, K₀ < j → 2 * log2Nat ((n + (K₀ + 1)).choose (K₀ + 1)) ≤
      2 * log2Nat ((n + j).choose j) := by
    intro j hj
    have := log2Nat_mono (choose_mono_k n (show K₀ + 1 ≤ j by omega))
    linarith
  rcases key with ⟨hnone, -⟩ | ⟨j, hj, hret⟩
  · have : (Id.run r).1 = none := hnone
    rw [this]; simp
  · have : (Id.run r).1 = some (some (2 * log2Nat ((n + j).choose j))) := hret
    rw [this]; intro x hx; cases hx; exact hmono j hj

end SigabaNeo.Lattices.Estimator

namespace SigabaNeo.Lattices.Estimator

open Fx NumMisc AroraGB

/-- The secret width `s` used by `AroraGB.single`. -/
def AroraGB.sOf (p : LWEParams) : ℕ :=
  if p.Xs.stddev > p.Xe.stddev then 0 else match p.Xs.kind with
    | .gauss v => (2*ceil (3*v)+1).toNat
    | _ => (floor (width p.Xs)).toNat

/-- `single` returns one of its `gb` values: the bounded-error system (degree `d₁`) or a Gaussian
tail truncation (degree `2t + 1`, `t ≥ ⌈σ⌉`), with at most the available samples. -/
theorem AroraGB.single_ge {K : Fx} {params : LWEParams}
    (hgb : ∀ d m' s', 7 ≤ d → (∀ M, params.normalize.m = some M → m' ≤ M) →
      s' = sOf params.normalize → CostGe K (gb params.normalize.n d m' s'))
    (hd₁ : 7 ≤ (floor (width params.normalize.Xe)).toNat)
    (hσ : 3 ≤ (ceil params.normalize.Xe.stddev).toNat) :
    CostGe K (single params) := by
  have hmin : ∀ c : Cost, Cost.min none c = c := fun c => by cases c <;> rfl
  have hloop : ∀ (lo hi : ℕ), 3 ≤ lo → ∀ (f : ℕ → Cost × ℕ → Id (ForInStep (Cost × ℕ))),
      (∀ t, lo ≤ t → ∀ st : Cost × ℕ, CostGe K st.1 → CostGe K (f t st).run.value.1) →
      CostGe K (forIn (m := Id) [lo:hi] ((none : Cost), (0 : ℕ)) f).1 := by
    intro lo hi hlo f hf
    apply forIn_inv (β := Cost × ℕ) (I := fun st => CostGe K st.1) _ _ _ (by simp)
    intro t ht st hst
    simp only [Std.Legacy.Range.size, List.mem_range'_1] at ht
    exact hf t ht.1 st hst
  have hbody : ∀ t, 3 ≤ t → ∀ st : Cost × ℕ, CostGe K st.1 →
      ∀ (m' : ℕ) (s' : ℕ) (b1 : Bool), s' = sOf params.normalize →
        (params.normalize.mGe m' = true) →
      CostGe K (match gb params.normalize.n (2 * t + 1) m' s' with
        | some v =>
          if Option.all (fun x => decide (v < x)) st.1 = true then
            (pure (ForInStep.yield (some v, 0)) : Id (ForInStep (Cost × ℕ)))
          else if (st.2 + 1 == 5) = true then pure (ForInStep.done (st.1, st.2 + 1))
            else pure (ForInStep.yield (st.1, st.2 + 1))
        | _ => pure (ForInStep.yield (st.1, st.2))).run.value.1 := by
    intro t ht st hst m' s' _ hs' hm
    have hm' : ∀ M, params.normalize.m = some M → m' ≤ M := by
      intro M hM; simp [LWEParams.mGe, hM] at hm; omega
    have hg := hgb (2 * t + 1) m' s' (by omega) hm' hs'
    split
    · rename_i v hv
      have hv' : K ≤ v := hg v hv
      split
      · intro x hx; simp at hx; rw [← hx]; exact hv'
      split
      · exact hst
      · exact hst
    · exact hst
  have hstep : ∀ t, (ceil params.normalize.Xe.stddev).toNat ≤ t → ∀ st : Cost × ℕ, CostGe K st.1 →
      CostGe K ((if (!params.normalize.mGe (samples ((ofInt ↑t).div params.normalize.Xe.stddev))) = true
        then (pure (ForInStep.done (st.1, st.2)) : Id (ForInStep (Cost × ℕ)))
        else if (decide (samples ((ofInt ↑t).div params.normalize.Xe.stddev) ≤ params.normalize.n) &&
            sOf params.normalize == 0) = true then pure (ForInStep.yield (st.1, st.2))
          else match gb params.normalize.n (2 * t + 1)
              (samples ((ofInt ↑t).div params.normalize.Xe.stddev)) (sOf params.normalize) with
            | some v =>
              if Option.all (fun x => decide (v < x)) st.1 = true then pure (ForInStep.yield (some v, 0))
              else if (st.2 + 1 == 5) = true then pure (ForInStep.done (st.1, st.2 + 1))
                else pure (ForInStep.yield (st.1, st.2 + 1))
            | _ => pure (ForInStep.yield (st.1, st.2))).run.value.1) := by
    intro t ht st hst
    split
    · exact hst
    rename_i hm
    simp only [Bool.not_eq_true'] at hm
    split
    · exact hst
    · exact hbody t (by omega) st hst _ _ false rfl (by simpa using hm)
  unfold single
  simp only []
  generalize hs0 : (if params.normalize.Xs.stddev > params.normalize.Xe.stddev then (0 : ℕ) else _ : ℕ) = s0
  have hs0' : s0 = sOf params.normalize := by rw [← hs0]; rfl
  subst hs0'
  split
  · split
    · simp only [hmin]
      exact hloop _ _ hσ _ (fun t ht st hst => hstep t ht st hst)
    · simp
  · split
    · split
      · apply CostGe.min
        · exact hgb _ _ _ hd₁ (fun M hM => by simp [hM]) rfl
        · exact hloop _ _ hσ _ (fun t ht st hst => hstep t ht st hst)
      · exact hgb _ _ _ hd₁ (fun M hM => by simp [hM]) rfl
    · split
      · simp only [hmin]
        exact hloop _ _ hσ _ (fun t ht st hst => hstep t ht st hst)
      · simp

end SigabaNeo.Lattices.Estimator

namespace SigabaNeo.Lattices.Estimator

open Fx NumMisc AroraGB

/-- **Arora–GB with guessing** costs at least `K` when each guess of `z < Z_A` coordinates leaves
a system costing `K`, and guessing `Z_A` coordinates of a dense secret already costs `K`. -/
theorem AroraGB.cost_ge {K : Fx} {params : LWEParams} (ZA : ℕ)
    (hns : params.normalize.Xs.isSparse = false) (hk : ∀ s, params.normalize.Xs.kind ≠ .gauss s)
    (hpen : K ≤ (ZA : ℤ) * log2Nat (floor (width params.normalize.Xs)).toNat)
    (h0 : CostGe K (single params.normalize))
    (hlow : ∀ z < ZA, CostGe K (single (LWEParams.mk' (params.normalize.n - z) params.normalize.q
      params.normalize.Xs params.normalize.Xe params.normalize.m)))
    (hnn : ∀ z, CostGe 0 (single (LWEParams.mk' (params.normalize.n - z) params.normalize.q
      params.normalize.Xs params.normalize.Xe params.normalize.m))) :
    CostGe K (AroraGB.cost params) := by
  have hg : (match params.normalize.Xs.kind with | .gauss _ => true | _ => false) = false := by
    cases h : params.normalize.Xs.kind with
    | gauss s => exact absurd h (hk s)
    | cbd _ => rfl
    | uniform _ _ => rfl
  have hlb := log2Nat_nonneg (floor (width params.normalize.Xs)).toNat
  have hcand : ∀ z, CostGe K ((single (LWEParams.mk' (params.normalize.n - z) params.normalize.q
      params.normalize.Xs params.normalize.Xe params.normalize.m)).bind fun v =>
        some (v + penalty params.normalize z (floor (width params.normalize.Xs)).toNat)) := by
    intro z
    apply CostGe.bind
    intro v hv x hx
    simp only [Option.some.injEq] at hx
    subst hx
    have hpz : penalty params.normalize z (floor (width params.normalize.Xs)).toNat =
        (z : ℤ) * log2Nat (floor (width params.normalize.Xs)).toNat := by
      unfold penalty; simp [hns]
    rw [hpz]
    rcases Nat.lt_or_ge z ZA with hz | hz
    · have := hlow z hz v hv
      have : 0 ≤ (z : ℤ) * log2Nat (floor (width params.normalize.Xs)).toNat := by positivity
      linarith
    · have := hnn z v hv
      have : (ZA : ℤ) * log2Nat (floor (width params.normalize.Xs)).toNat ≤
          (z : ℤ) * log2Nat (floor (width params.normalize.Xs)).toNat :=
        Int.mul_le_mul_of_nonneg_right (by exact_mod_cast hz) hlb
      linarith
  unfold AroraGB.cost
  simp only [hns, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.or_false, guard,
    Option.pure_def, Option.bind_eq_bind]
  apply CostGe.bind; intro _ _
  apply CostGe.bind; intro baseline _
  apply CostGe.bind; intro stop _
  split
  · exact h0
  · apply NumMisc.search_inv (Q := fun o => CostGe K (o.bind fun r => r))
    · simp
    · intro z; exact hcand z

end SigabaNeo.Lattices.Estimator

namespace SigabaNeo.Lattices.Estimator

open Fx NumMisc AroraGB

theorem AroraGB.gb_nonneg (n d m s : ℕ) : CostGe 0 (AroraGB.gb n d m s) := by
  unfold gb
  simp only [Id.run_bind]
  generalize hr : (forIn (m := Id) (_ : Std.Legacy.Range)
    ((none : Option (Option Fx)), Array.replicate (min d (2 * n)) (0 : ℤ),
      Array.replicate (min s (2 * n)) (0 : ℤ), (0 : ℤ), (1 : ℤ)) _ :
    Id (Option (Option Fx) × Array ℤ × Array ℤ × ℤ × ℤ)) = r
  have key : ∀ x, r.1 = some (some x) → 0 ≤ x := by
    rw [← hr]
    apply forIn_inv (β := Option (Option Fx) × Array ℤ × Array ℤ × ℤ × ℤ)
      (I := fun st => ∀ x, st.1 = some (some x) → 0 ≤ x)
    · simp
    · intro k _ st _
      split <;> split <;> intro x hx <;> simp at hx
      all_goals (subst hx; have := log2Nat_nonneg ((n + k).choose k); linarith)
  have key' : ∀ x, (Id.run r).1 = some (some x) → 0 ≤ x := key
  generalize (Id.run r).1 = o at key' ⊢
  rcases o with _ | _ | x
  · simp
  · simp
  · intro y hy; simp at hy; subst hy; exact key' x rfl

/-- `d ≤ 7 · 2^{d−7}` for `d ≥ 7`. -/
theorem AroraGB.le_pow_sub {d : ℕ} (hd : 7 ≤ d) : d ≤ 7 * 2 ^ (d - 7) := by
  induction d with
  | zero => omega
  | succ d ih =>
    rcases Nat.lt_or_ge d 7 with h | h
    · have : d = 6 := by omega
      subst this; norm_num
    · have := ih h
      rw [show d + 1 - 7 = (d - 7) + 1 by omega, pow_succ]; omega

/-- The degree condition of `gb_ge` for every `d ≥ 7` from the one at `d = 7`. -/
theorem AroraGB.hmd_of {n m M R : ℕ} (hR : 2 ≤ R) (hm : m ≤ M) (h : 56 * M ≤ n * R ^ 6) :
    ∀ d, 7 ≤ d → 8 * m * d ≤ n * R ^ (d - 1) := by
  intro d hd
  have h1 := le_pow_sub hd
  have h2 : 2 ^ (d - 7) ≤ R ^ (d - 7) := Nat.pow_le_pow_left hR _
  have e : R ^ (d - 1) = R ^ 6 * R ^ (d - 7) := by rw [← pow_add]; congr 1; omega
  calc 8 * m * d ≤ 8 * M * (7 * 2 ^ (d - 7)) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hm) h1
    _ = 56 * M * 2 ^ (d - 7) := by ring
    _ ≤ n * R ^ 6 * R ^ (d - 7) := Nat.mul_le_mul h h2
    _ = n * R ^ (d - 1) := by rw [e]; ring

end SigabaNeo.Lattices.Estimator
