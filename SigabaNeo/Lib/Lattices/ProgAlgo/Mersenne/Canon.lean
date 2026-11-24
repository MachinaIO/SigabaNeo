import SigabaNeo.Lib.Lattices.ProgAlgo.Mersenne.Ring

/-!
# Canonical ring words modulo `2^K − 1`

A residue modulo `2^K − 1` has two `K`-bit words when it is `0` (all zeros, all ones). The
**canonical** word is the one in `[0, 2^K − 1)`: `encM K (decM K w)`. Canonicalizing replaces an
all-ones block by zeros:

* `canonB x y`: `x`, or zeros if `x = y` (with `y` the all-ones block); `canonB_ones`:
  `canonB w 1…1 = encM K (decM K w)` for `|w| = K`;
* `canonW N K x`: every block of `x` canonicalized; **`canonW_eq`**: `canonW N K x =
  encRM N K (decRM N K x)` for `|x| = N K`;
* `canonRP : Prog 28` (layout of `bzip`: `0` output, `1` the word, `2` the all-ones word of
  `N K` bits, `3` `4` templates `K`, `N`; scratch `5 … 27`): **`canonW`** (`run_canonRP`).
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices.Algo

variable {k : ℕ}

/-- `x`, or zeros if `x = y`. -/
def canonB (x y : List Bool) : List Bool := if x = y then zeroW x.length else x

@[simp] theorem length_canonB (x y : List Bool) : (canonB x y).length = x.length := by
  unfold canonB; split_ifs <;> simp

theorem val_replicate_true : ∀ K : ℕ, val (List.replicate K true) + 1 = 2 ^ K
  | 0 => rfl
  | K + 1 => by
    rw [List.replicate_succ, val_cons, pow_succ]
    have := val_replicate_true K
    simp only [Bool.toNat_true]
    omega

/-- **The canonical block.** -/
theorem canonB_ones {K : ℕ} (hK : 0 < K) {w : List Bool} (hw : w.length = K) :
    canonB w (List.replicate K true) = encM K (decM K w) := by
  have : NeZero (2 ^ K - 1) := ⟨by have := Nat.one_lt_two_pow (n := K) (by omega); omega⟩
  have hr := val_replicate_true K
  unfold canonB encM decM
  split_ifs with h
  · subst h
    have e : ((val (List.replicate K true) : ℕ) : ZMod (2 ^ K - 1)) = 0 := by
      rw [show val (List.replicate K true) = 2 ^ K - 1 by omega, ZMod.natCast_self]
    rw [e, ZMod.val_zero, List.length_replicate]
    have := toBits_val (zeroW K)
    rw [length_zeroW, val_zeroW] at this
    exact this.symm
  · have hlt : val w < 2 ^ K - 1 := by
      have h1 := val_lt w
      rw [hw] at h1
      rcases Nat.lt_or_ge (val w) (2 ^ K - 1) with h2 | h2
      · exact h2
      · exfalso; apply h
        have e : val w = val (List.replicate K true) := by omega
        rw [← toBits_val w, ← toBits_val (List.replicate K true), e, hw, List.length_replicate]
    rw [ZMod.val_natCast_of_lt hlt, ← hw, toBits_val]

/-- Every block canonicalized. -/
def canonW (N K : ℕ) (x : List Bool) : List Bool :=
  concatN N (fun i => canonB (block K i x) (List.replicate K true))

theorem length_canonW (N K : ℕ) {x : List Bool} (hx : x.length = N * K) :
    (canonW N K x).length = N * K :=
  length_concatN fun i hi => by rw [length_canonB, length_block hx hi]

/-- **Canonicalized words are the canonical words.** -/
theorem canonW_eq {N K : ℕ} (hK : 0 < K) {x : List Bool} (hx : x.length = N * K) :
    canonW N K x = encRM N K (decRM N K x) := by
  unfold canonW encRM
  apply concatN_congr
  intro i hi
  rw [canonB_ones hK (length_block hx hi), coefG_decRM _ hi]

theorem block_replicate {N K i : ℕ} (hi : i < N) (b : Bool) :
    block K i (List.replicate (N * K) b) = List.replicate K b := by
  simp only [block, List.drop_replicate, List.take_replicate]
  congr 1
  have : i * K + K ≤ N * K := by nlinarith
  omega

namespace Prog

open scoped Prog

/-- The carry from the last digit: some digit of the second word at or after this one is
`false` (or missing). -/
def anyFalseOp : DigitOp := fun _ y c => (c || !y, c || !y)

theorem carryOp_anyFalseOp_fst : ∀ xs ys : List Bool,
    (carryOp anyFalseOp xs ys).1 = true ↔ ∃ i < xs.length, ys.getD i false = false
  | [], _ => by simp
  | x :: xs, ys => by
    have ih := carryOp_anyFalseOp_fst xs ys.tail
    simp only [carryOp, anyFalseOp, List.length_cons, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true]
    rw [ih]
    rcases ys with _ | ⟨y, ys⟩
    · simp only [List.headD_nil]
      simp
      exact ⟨0, Nat.zero_le _⟩
    · simp only [List.headD_cons, List.tail_cons]
      constructor
      · rintro (⟨i, hi, h⟩ | h)
        · exact ⟨i + 1, by omega, h⟩
        · exact ⟨0, by omega, h⟩
      · rintro ⟨i, hi, h⟩
        rcases i with _ | i
        · exact Or.inr h
        · exact Or.inl ⟨i, by omega, h⟩

/-- The first digit of `carryOp anyFalseOp w w`: `w` has a `false` digit. -/
theorem hd_carryOp_anyFalseOp (w : List Bool) (hw : w ≠ []) :
    hd (carryOp anyFalseOp w w).2 = true ↔ w ≠ List.replicate w.length true := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hw
  have e : hd (carryOp anyFalseOp (x :: xs) (x :: xs)).2 =
      (carryOp anyFalseOp (x :: xs) (x :: xs)).1 := by
    simp [carryOp, anyFalseOp, hd]
  rw [e, carryOp_anyFalseOp_fst]
  constructor
  · rintro ⟨i, hi, h⟩ heq
    rw [heq, List.getD_eq_getElem _ _ (by simpa using hi)] at h
    simp at h
  · intro hne
    by_contra hall
    apply hne
    apply List.ext_getElem (by simp)
    intro i h1 h2
    have : ¬ (x :: xs).getD i false = false := fun h => hall ⟨i, h1, h⟩
    rw [List.getD_eq_getElem _ _ h1] at this
    simpa using this

/-- The canonical block of `x` (the second argument is ignored). -/
def canonB1 (x _y : List Bool) : List Bool := canonB x (List.replicate x.length true)

/-- The block program: `0 := canonB1 (s 1) _` (test on tape `3`: `s 1` has a `false` digit). -/
def canonBP : Prog 18 :=
  cp 3 1 ⨾ prim (.carry anyFalseOp 3 1) ⨾ ifBit 3 (cp 0 1) (cp 0 1 ⨾ setZero 0) ⨾ clr 3

theorem blockSpec_canonBP {K : ℕ} (hK : 0 < K) : BlockSpec K canonBP canonB1 := by
  intro t ht h1 _
  have h3 : t 3 = [] := ht 3 (by decide)
  have hne : t 1 ≠ [] := by intro h; rw [h] at h1; simp at h1; omega
  simp only [canonBP, run_seq, run_prim, Prim.apply, run_ifBit, run_copy, run_setZero, run_clear,
    Function.update_self]
  have e1 : Function.update t 3 (t 1) 1 = t 1 := by simp
  simp only [e1]
  have hiff := hd_carryOp_anyFalseOp _ hne
  by_cases h : t 1 = List.replicate (t 1).length true
  · have hd' : hd (carryOp anyFalseOp (t 1) (t 1)).2 = false := by
      cases hh : hd (carryOp anyFalseOp (t 1) (t 1)).2
      · rfl
      · exact absurd h (hiff.mp hh)
    rw [hd']
    simp only [Bool.false_eq_true, if_false]
    funext j
    simp only [Function.update_apply, canonB1, canonB]
    rw [if_pos h]
    clear hiff hd' h
    split_ifs <;> (try subst_vars) <;> simp_all [zeroW]
  · rw [hiff.mpr h]
    simp only [if_true]
    funext j
    simp only [Function.update_apply, canonB1, canonB]
    rw [if_neg h]
    clear hiff h
    split_ifs <;> (try subst_vars) <;> simp_all

/-- **Canonicalization of a ring word**: `bzip canonBP` (the second operand is ignored). -/
def canonRP : Prog 28 := bzip canonBP

theorem run_canonRP {K N : ℕ} (hK : 0 < K) (s : Store 28) (hs : BzClean s) (hK' : (s 3).length = K)
    (hN : (s 4).length = N) (hx : (s 1).length = N * K) (hy : (s 2).length = N * K) :
    run canonRP s = Function.update s 0 (canonW N K (s 1)) := by
  rw [canonRP, run_bzip (blockSpec_canonBP hK) (fun x y hx _ => by simp [canonB1, hx]) s hs hK' hN
    hx hy]
  congr 1
  apply concatN_congr
  intro i hi
  rw [canonB1, length_block hx hi]

theorem run_canonRP_map {u : Fin 28 → Fin k} (hu : Function.Injective u) {K N : ℕ} (hK : 0 < K)
    (s : Store k) (hs : ∀ i : Fin 28, 5 ≤ i.val → s (u i) = []) (hK' : (s (u 3)).length = K)
    (hN : (s (u 4)).length = N) (hx : (s (u 1)).length = N * K)
    (hy : (s (u 2)).length = N * K) :
    run (map u canonRP) s = Function.update s (u 0) (canonW N K (s (u 1))) :=
  run_map_eq_update hu _ s 0 _ (run_canonRP hK (s ∘ u) hs hK' hN hx hy)

theorem noGrow_canonRP : canonRP.NoGrow := rfl
theorem wf_canonRP : canonRP.WF := wf_of_wfB (by decide)

end Prog

end SigabaNeo.Tape
