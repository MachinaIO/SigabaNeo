import SigabaNeo.Lib.Lattices.ProgAlgo.Mersenne.VMLib
import SigabaNeo.Lib.Lattices.Homomorphic.BinaryDigits

/-!
# Ring words for the ring-word machine: digits of canonical words

* `rot1_iter_eq`, `digitRW_zero_rotBW`: the digit `0` of a word whose blocks were rotated `i`
  times is its digit `i`, so a loop over the digits rotates (`rotB` by one bit) instead of indexing;
* **`decRM_digitRW_canon`**: the binary digit `i` of the canonical word of `x` reads as
  `binaryDigit (decRM x) i`, the gadget digit of `ℤ_{2^K − 1}[X]/(X^N + 1)` (`binaryDigits`).
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG

theorem rot1_iter_eq (u : List Bool) : ∀ j ≤ u.length, rot1^[j] u = u.drop j ++ u.take j
  | 0, _ => by simp
  | j + 1, hj => by
    rw [Function.iterate_succ_apply', rot1_iter_eq u j (by omega)]
    obtain ⟨a, rest, hr⟩ : ∃ a rest, u.drop j = a :: rest := by
      cases h : u.drop j with
      | nil => simp at h; omega
      | cons a rest => exact ⟨a, rest, rfl⟩
    have ha : u[j]'(by omega) = a := by
      have := congrArg List.head? hr
      rw [List.head?_drop] at this
      simpa [List.getElem?_eq_getElem (show j < u.length by omega)] using this
    have hd : u.drop (j + 1) = rest := by
      rw [← List.drop_drop, hr]; rfl
    simp only [rot1, hr, List.cons_append, List.take_succ_cons, List.take_zero, List.tail_cons, hd]
    rw [List.take_succ, List.getElem?_eq_getElem (show j < u.length by omega), ha]
    simp

theorem getD_rot1_iter {u : List Bool} {j : ℕ} (hj : j < u.length) :
    (rot1^[j] u).getD 0 false = u.getD j false := by
  rw [rot1_iter_eq u j hj.le]
  obtain ⟨a, rest, hr⟩ : ∃ a rest, u.drop j = a :: rest := by
    cases h : u.drop j with
    | nil => simp at h; omega
    | cons a rest => exact ⟨a, rest, rfl⟩
  have := congrArg List.head? hr
  rw [List.head?_drop] at this
  rw [hr, List.cons_append, List.getD_cons_zero, List.getD_eq_getElem?_getD, this]
  rfl

theorem digitRW_zero_rotBW {N K i : ℕ} {x : List Bool} (hx : x.length = N * K) (hi : i < K) :
    digitRW N K 0 (rotBW N K i x) = digitRW N K i x := by
  unfold digitRW
  apply concatN_congr
  intro t ht
  rw [rotBW, block_concatN (fun t' ht' => by rw [length_rot1_iter, length_block hx ht']),
    if_pos ht, getD_rot1_iter (by rw [length_block hx ht]; exact hi)]

theorem getD_toBits : ∀ (K n i : ℕ), (toBits K n).getD i false = (decide (i < K) && n.testBit i)
  | 0, n, i => by simp [toBits]
  | K + 1, n, 0 => by simp [toBits, Nat.testBit_zero]
  | K + 1, n, i + 1 => by
    rw [toBits, List.getD_cons_succ, getD_toBits K (n / 2) i, Nat.testBit_div_two]
    simp

theorem block_encRM {N K t : ℕ} (a : Cslib.Negacyclic (ZMod (2 ^ K - 1)) N) (ht : t < N) :
    block K t (encRM N K a) = encM K (coefG a t) := by
  rw [encRM, block_concatN (fun _ _ => length_encM _ _), if_pos ht]

/-- **The digits of a canonical word are the gadget digits.** -/
theorem decRM_digitRW_canon {N K : ℕ} [NeZero (2 ^ K - 1)] (hK : 0 < K) {x : List Bool} (hx : x.length = N * K)
    (i : ℕ) : decRM N K (digitRW N K i (canonW N K x)) = binaryDigit (decRM N K x) i := by
  rw [decRM_digitRW hK, canonW_eq hK hx]
  ext t
  rw [Cslib.Negacyclic.coeffs_ofCoeffs, coeffs_binaryDigit, block_encRM _ t.isLt, encM,
    getD_toBits, coefG_val]
  have hv : (((decRM N K x).coeffs t).val) < 2 ^ K := by
    have := ZMod.val_lt ((decRM N K x).coeffs t)
    have : 2 ^ K - 1 < 2 ^ K := Nat.sub_lt (by positivity) one_pos
    omega
  by_cases hi : i < K
  · simp [hi]
  · simp only [hi, decide_false, Bool.false_and]
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega)))]

end SigabaNeo.Tape
