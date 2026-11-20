import Solution.Attack

/-!
# The elimination finds a dependency

For columns `c_0, …, c_m < 2^m`, the fold of `elimStep` returns a mask `u ≠ 0` with
`u < 2^(m+1)` whose columns XOR to `0` (`elim_spec`, `depMask_spec`).

The basis is a list of triples `(p, v, mk)` with `v = ⨁_{j ∈ mk} c_j`, `v < 2^m`, `mk < 2^J`
(`J` columns processed), bit `p` of `v` set, `p < m`, and bit `p` clear in every later vector
(`Inv`). Reducing a column through the basis in order clears every pivot bit
(`reduceFold_spec`), so a nonzero remainder has a new pivot. There are at most `m` distinct
pivots below `m`, so a dependency appears among the first `m + 1` columns.
-/

namespace TestCase.EvLWE

open SigabaNeo.Lattices

open TestCase

/-! ### XOR combinations -/

/-- `⨁_{j < N, bit j of u set} f j`. -/
def xorSum (f : ℕ → ℕ) (N u : ℕ) : ℕ :=
  (List.range N).foldl (fun acc j => if u.testBit j then acc ^^^ f j else acc) 0

theorem xorSum_zero (f : ℕ → ℕ) (u : ℕ) : xorSum f 0 u = 0 := rfl

theorem xorSum_succ (f : ℕ → ℕ) (N u : ℕ) :
    xorSum f (N + 1) u = xorSum f N u ^^^ (if u.testBit N then f N else 0) := by
  unfold xorSum
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  split_ifs <;> simp

theorem xorSum_xor (f : ℕ → ℕ) (N a b : ℕ) :
    xorSum f N (a ^^^ b) = xorSum f N a ^^^ xorSum f N b := by
  induction N with
  | zero => simp [xorSum_zero]
  | succ N ih =>
    rw [xorSum_succ, xorSum_succ, xorSum_succ, ih, Nat.testBit_xor]
    cases a.testBit N <;> cases b.testBit N <;>
      simp [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]

/-- Bits of `u` at or above `N` do not matter. -/
theorem xorSum_of_testBit_eq (f : ℕ → ℕ) (N : ℕ) {u u' : ℕ}
    (h : ∀ i < N, u.testBit i = u'.testBit i) : xorSum f N u = xorSum f N u' := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [xorSum_succ, xorSum_succ, ih fun i hi => h i (by omega), h N (by omega)]

theorem xorSum_extend (f : ℕ → ℕ) {N N' u : ℕ} (hN : N ≤ N') (hu : u < 2 ^ N) :
    xorSum f N' u = xorSum f N u := by
  induction N' with
  | zero => have : N = 0 := by omega
            subst this; rfl
  | succ N' ih =>
    rcases Nat.lt_or_ge N' N with h | h
    · have : N = N' + 1 := by omega
      subst this; rfl
    · rw [xorSum_succ, ih h, Nat.testBit_lt_two_pow (lt_of_lt_of_le hu (Nat.pow_le_pow_right
        (by norm_num) h))]
      simp

theorem xorSum_two_pow (f : ℕ → ℕ) (j : ℕ) : xorSum f (j + 1) (2 ^ j) = f j := by
  rw [xorSum_succ, xorSum_of_testBit_eq f j (u' := 0) fun i hi => by
      simp [show j ≠ i by omega]]
  have : xorSum f j 0 = 0 := by
    induction j with
    | zero => rfl
    | succ j ih => rw [xorSum_succ, ih]; simp
  simp [this]

theorem xor_lt_two_pow {a b k : ℕ} (ha : a < 2 ^ k) (hb : b < 2 ^ k) : a ^^^ b < 2 ^ k :=
  Nat.xor_lt_two_pow ha hb

/-! ### The basis invariant -/

section
variable (c : ℕ → ℕ) (m : ℕ)

/-- The invariant after `J` columns. -/
def Inv (J : ℕ) (basis : List (ℕ × ℕ × ℕ)) : Prop :=
  (∀ t ∈ basis, t.2.1 = xorSum c J t.2.2 ∧ t.2.1 < 2 ^ m ∧ t.2.2 < 2 ^ J ∧
    t.2.1.testBit t.1 = true ∧ t.1 < m) ∧
  basis.Pairwise fun a b => b.2.1.testBit a.1 = false

/-- A bit that is clear in the accumulator and in every vector stays clear. -/
theorem reduceFold_bit_clear (M p : ℕ) (rest : List (ℕ × ℕ × ℕ)) (acc : ℕ × ℕ)
    (hacc : acc.1.testBit p = false) (hM : acc.1 < 2 ^ M)
    (hrest : ∀ t ∈ rest, t.2.1.testBit p = false ∧ t.2.1 < 2 ^ M) :
    (rest.foldl (reduceStep M) acc).1.testBit p = false := by
  induction rest generalizing acc with
  | nil => exact hacc
  | cons t rest ih =>
    simp only [List.foldl_cons]
    have ht := hrest t List.mem_cons_self
    apply ih
    · unfold reduceStep; split_ifs
      · rw [Nat.mod_eq_of_lt (xor_lt_two_pow hM ht.2), Nat.testBit_xor, hacc, ht.1]; rfl
      · exact hacc
    · unfold reduceStep; split_ifs
      · exact Nat.mod_lt _ (by positivity)
      · exact hM
    · exact fun t' h => hrest t' (List.mem_cons_of_mem _ h)

/-- Reducing `(x, mk)` with `x = ⨁_{mk} c` through a basis satisfying `Inv J` keeps that relation,
keeps the bounds, and clears every pivot bit. -/
theorem reduceFold_spec (J : ℕ) (hJ : J + 1 ≤ m + 1) (basis : List (ℕ × ℕ × ℕ))
    (hinv : Inv c m J basis) (acc : ℕ × ℕ) (hx : acc.1 = xorSum c (J + 1) acc.2)
    (hxb : acc.1 < 2 ^ m) (hmb : acc.2 < 2 ^ (J + 1)) :
    let r := basis.foldl (reduceStep (m + 1)) acc
    r.1 = xorSum c (J + 1) r.2 ∧ r.1 < 2 ^ m ∧ r.2 < 2 ^ (J + 1) ∧
      r.2.testBit J = acc.2.testBit J ∧ ∀ t ∈ basis, r.1.testBit t.1 = false := by
  obtain ⟨hall, hpw⟩ := hinv
  induction basis generalizing acc with
  | nil => exact ⟨hx, hxb, hmb, rfl, by simp⟩
  | cons t rest ih =>
    simp only [List.foldl_cons]
    have ht := hall t List.mem_cons_self
    obtain ⟨hv, hvb, hmkb, hpiv, -⟩ := ht
    have hmkb' : t.2.2 < 2 ^ (J + 1) := lt_of_lt_of_le hmkb (Nat.pow_le_pow_right (by norm_num)
      (by omega))
    have hmM : 2 ^ m ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hJM : 2 ^ (J + 1) ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) hJ
    -- One step.
    set acc1 := reduceStep (m + 1) acc t with hacc1
    have h1 : acc1.1 = xorSum c (J + 1) acc1.2 ∧ acc1.1 < 2 ^ m ∧ acc1.2 < 2 ^ (J + 1) ∧
        acc1.2.testBit J = acc.2.testBit J ∧ acc1.1.testBit t.1 = false := by
      rw [hacc1]; unfold reduceStep
      split_ifs with hb
      · have hx1 : acc.1 ^^^ t.2.1 < 2 ^ m := xor_lt_two_pow hxb hvb
        have hm1 : acc.2 ^^^ t.2.2 < 2 ^ (J + 1) := xor_lt_two_pow hmb hmkb'
        simp only [Nat.mod_eq_of_lt (lt_of_lt_of_le hx1 hmM), Nat.mod_eq_of_lt
          (lt_of_lt_of_le hm1 hJM)]
        refine ⟨?_, hx1, hm1, ?_, ?_⟩
        · rw [xorSum_xor, hx, hv, xorSum_extend c (N' := J + 1) (by omega) hmkb]
        · rw [Nat.testBit_xor, Nat.testBit_lt_two_pow hmkb]; simp
        · rw [Nat.testBit_xor, hb, hpiv]; rfl
      · exact ⟨hx, hxb, hmb, rfl, by simpa using hb⟩
    obtain ⟨h1x, h1xb, h1mb, h1J, h1piv⟩ := h1
    have hrest := ih acc1 h1x h1xb h1mb (fun t' h => hall t' (List.mem_cons_of_mem _ h))
      (List.pairwise_cons.mp hpw).2
    obtain ⟨r1, r2, r3, r4, r5⟩ := hrest
    refine ⟨r1, r2, r3, r4.trans h1J, ?_⟩
    intro t' ht'
    rcases List.mem_cons.mp ht' with rfl | ht'
    · -- The pivot of `t` stays clear: every later vector has it clear.
      exact reduceFold_bit_clear (m + 1) t'.1 rest acc1 h1piv (lt_of_lt_of_le h1xb hmM)
        fun t'' h => ⟨(List.pairwise_cons.mp hpw).1 t'' h,
          lt_of_lt_of_le (hall t'' (List.mem_cons_of_mem _ h)).2.1 hmM⟩
    · exact r5 t' ht'

end

theorem testBit_log_two {n : ℕ} (hn : n ≠ 0) : n.testBit (Nat.log 2 n) = true := by
  have h1 := Nat.pow_log_le_self 2 hn
  have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hq : n / 2 ^ Nat.log 2 n = 1 := by
    apply le_antisymm
    · rw [Nat.div_le_iff_le_mul_add_pred (by positivity)]
      rw [Nat.pow_succ] at h2; omega
    · exact (Nat.le_div_iff_mul_le (by positivity)).mpr (by omega)
  simp [hq]

theorem kBit_le (κ : ℕ) (word : List Bool) (r j : ℕ) : kBit κ word r j ≤ 1 := by
  unfold kBit; split_ifs <;> omega

theorem colVec_lt (κ : ℕ) (word : List Bool) (j : ℕ) : colVec κ word j < 2 ^ EvLWE.m κ := by
  unfold colVec
  generalize EvLWE.m κ = M
  induction M with
  | zero => simp
  | succ M ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    have := kBit_le κ word M j
    rw [Nat.pow_succ]
    nlinarith [Nat.mul_le_mul_right (2 ^ M) this]

/-! ### One column, and the whole fold -/

section
variable (κ : ℕ) (word : List Bool)

local notation "c" => colVec κ word
local notation "m" => EvLWE.m κ

/-- The state after `J` columns: no dependency yet and an invariant basis of `J` vectors, or a
dependency. -/
def StepInv (J : ℕ) (st : List (ℕ × ℕ × ℕ) × ℕ) : Prop :=
  (st.2 = 0 ∧ Inv c m J st.1 ∧ st.1.length = J) ∨
  (st.2 ≠ 0 ∧ st.2 < 2 ^ (m + 1) ∧ xorSum c (m + 1) st.2 = 0)

theorem stepInv_zero : StepInv κ word 0 ([], 0) := Or.inl ⟨rfl, ⟨by simp, by simp⟩, rfl⟩

theorem elimStep_inv (hc : ∀ j, c j < 2 ^ m) {j : ℕ} (hj : j ≤ m) (st : List (ℕ × ℕ × ℕ) × ℕ)
    (h : StepInv κ word j st) : StepInv κ word (j + 1) (elimStep κ word st j) := by
  have hmM : 2 ^ m ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hjM : 2 ^ (j + 1) ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases h with ⟨hs, hinv, hlen⟩ | ⟨hs, hb, hx⟩
  · have hred := reduceFold_spec c m j (by omega) st.1 hinv (c j, 2 ^ j)
      (by simp only; rw [xorSum_two_pow]) (hc j) (Nat.pow_lt_pow_right (by norm_num) (by omega))
    have hinit : (c j % 2 ^ (m + 1), 2 ^ j % 2 ^ (m + 1)) = (c j, 2 ^ j) := by
      rw [Nat.mod_eq_of_lt (lt_of_lt_of_le (hc j) hmM),
        Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))]
    unfold elimStep
    simp only [hs, beq_self_eq_true, ite_true, reduce, hinit]
    set r := st.1.foldl (reduceStep (m + 1)) (c j, 2 ^ j) with hr
    obtain ⟨r1, r2, r3, r4, r5⟩ := hred
    have hbit : r.2.testBit j = true := by
      rw [r4, Nat.testBit_two_pow_self]
    split_ifs with h0
    · right
      have h0' : r.1 = 0 := by simpa using h0
      refine ⟨fun h => by
        have h' : r.2 = 0 := h
        rw [h'] at hbit; simp at hbit, lt_of_lt_of_le r3 hjM, ?_⟩
      rw [xorSum_extend c (by omega) r3, ← r1, h0']
    · left
      have h0' : r.1 ≠ 0 := by simpa using h0
      refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
      rotate_left 2
      · show (st.1 ++ _).length = j + 1
        simp [hlen]
      · intro t ht
        rcases List.mem_append.mp ht with ht | ht
        · obtain ⟨hv, hvb, hmb, hp, hpm⟩ := hinv.1 t ht
          exact ⟨by rw [hv, xorSum_extend c (N' := j + 1) (by omega) hmb], hvb,
            lt_of_lt_of_le hmb (Nat.pow_le_pow_right (by norm_num) (by omega)), hp, hpm⟩
        · simp only [List.mem_singleton] at ht
          subst ht
          exact ⟨r1, r2, r3, testBit_log_two h0', Nat.log_lt_of_lt_pow h0' r2⟩
      · rw [List.pairwise_append]
        refine ⟨hinv.2, by simp, ?_⟩
        intro a ha b hb
        simp only [List.mem_singleton] at hb
        subst hb
        exact r5 a ha
  · right
    unfold elimStep
    have hs' : (st.2 == 0) = false := by simp [hs]
    simp only [hs', Bool.false_eq_true, ite_false]
    exact ⟨hs, hb, hx⟩

theorem foldl_inv (hc : ∀ j, c j < 2 ^ m) {J : ℕ} (hJ : J ≤ m + 1) :
    StepInv κ word J ((List.range J).foldl (elimStep κ word) ([], 0)) := by
  induction J with
  | zero => exact stepInv_zero κ word
  | succ J ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact elimStep_inv κ word hc (by omega) _ (ih (by omega))

/-- No invariant basis has `m + 1` vectors: their pivots are distinct and below `m`. -/
theorem not_inv_full (basis : List (ℕ × ℕ × ℕ)) (hinv : Inv c m (m + 1) basis)
    (hlen : basis.length = m + 1) : False := by
  have hnd : (basis.map (·.1)).Nodup := by
    refine List.pairwise_map.mpr (hinv.2.imp_of_mem fun {a b} _ hb hR => ?_)
    intro hab
    have := (hinv.1 b hb).2.2.2.1
    rw [← hab, hR] at this
    exact Bool.false_ne_true this
  have hsub : (basis.map (·.1)).toFinset ⊆ Finset.range m := by
    intro p hp
    simp only [List.mem_toFinset, List.mem_map] at hp
    obtain ⟨t, ht, rfl⟩ := hp
    exact Finset.mem_range.mpr (hinv.1 t ht).2.2.2.2
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, List.length_map, hlen, Finset.card_range] at this
  omega

theorem depMask_spec :
    depMask κ word ≠ 0 ∧ depMask κ word < 2 ^ (m + 1) ∧
      xorSum c (m + 1) (depMask κ word) = 0 := by
  have h := foldl_inv κ word (colVec_lt κ word) (le_refl (m + 1))
  unfold depMask
  rcases h with ⟨-, hinv, hlen⟩ | h
  · exact (not_inv_full κ word _ hinv hlen).elim
  · exact h

end

end TestCase.EvLWE